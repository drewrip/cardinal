//! Static claims about SQL output cardinality.
//!
//! A query is parsed and optimized into a DataFusion `LogicalPlan`, every operator
//! gets a Z3 integer for its output cardinality, and each operator contributes
//! constraints relating its output to its inputs. We then ask Z3 whether the root's
//! cardinality must be at most the sum of all base-table scan cardinalities.

mod analyzer;
mod bounds;
mod domain;
mod origin;
mod validate;

pub use bounds::{Bounds, Linear, TableBound};

use std::collections::HashMap;
use std::sync::Arc;

use datafusion::catalog::TableProvider;
use datafusion::common::TableReference;
use datafusion::common::tree_node::TreeNodeRecursion;
use datafusion::datasource::cte_worktable::CteWorkTable;
use datafusion::datasource::source_as_provider;
use datafusion::logical_expr::LogicalPlan;
use datafusion::logical_expr::logical_plan::TableScan;
use datafusion::prelude::SessionContext;
use z3::SatResult;
use z3::ast::Int;

use analyzer::{Analyzer, Node, ScanKind};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    DataFusion(#[from] datafusion::error::DataFusionError),
    /// A bug in this library, e.g. constraints that failed to round-trip.
    #[error("internal error: {0}")]
    Internal(String),
}

pub type Result<T> = std::result::Result<T, Error>;

/// Outcome of checking `O_root <= Σ scans`: can the query output more rows
/// than it reads?
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// Proven: the output never has more rows than the scans read, for every
    /// assignment satisfying the constraints.
    Reduces,
    /// Not provable: a counterexample satisfies every constraint yet outputs
    /// more rows than the scans read. Either the query really can grow its
    /// input (e.g. a cross join, or `count(*)` on an empty table), or the
    /// constraints are too weak to rule it out.
    MightGrow(Counterexample),
    /// Z3 could not decide (e.g. nonlinear `l * r` terms, or the solver timed
    /// out); holds its reason.
    Unknown(String),
}

/// Cardinalities satisfying every constraint while violating the claim.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Counterexample {
    /// Row count of each base table, by table name.
    pub tables: HashMap<String, i64>,
    /// Row count of each operator variable (scans included), by variable name.
    pub vars: HashMap<String, i64>,
}

impl Counterexample {
    /// The row count of table `name`. Panics if there is no such table.
    pub fn table(&self, name: &str) -> i64 {
        self.tables[name]
    }

    /// The value of operator variable `name`. Panics if there is no such variable.
    pub fn var(&self, name: &str) -> i64 {
        self.vars[name]
    }
}

#[derive(Debug, Clone)]
pub struct Analysis {
    pub verdict: Verdict,
    /// The constraint set `S` plus the negated claim, in SMT-LIB form.
    pub smtlib: String,
    /// Name of the root operator's variable.
    pub root: String,
    /// Each base-table scan as (scan variable, table name), in visit order.
    pub scans: Vec<(String, String)>,
    /// The optimized plan that was analyzed, for display.
    pub plan: String,
    /// The constraint set `S` alone, without the claim, and how many assertions
    /// it holds (to check that it parses back completely).
    constraints: String,
    assertions: usize,
    /// Every plan node, children before parents.
    nodes: Vec<Node>,
    /// Each base table as (table name, Z3 symbol), sorted by name.
    tables: Vec<(String, String)>,
}

/// Result of checking a real execution against the constraint set `S`.
#[derive(Debug, Clone)]
pub struct Validation {
    /// Actual output rows of every evaluated plan node, by variable name.
    pub rows: HashMap<String, u64>,
    /// The first operator (children before parents) whose actual row count
    /// contradicts `S` given the counts below it. `None` means every evaluated
    /// node is consistent with `S`.
    pub violation: Option<String>,
    /// True if Z3 could not decide consistency at some step.
    pub undecided: bool,
}

impl Analysis {
    /// Evaluates the analyzed plan against `ctx`'s data and checks that the
    /// actual row count of every operator satisfies `S`.
    ///
    /// The plan is evaluated once, bottom-up: each operator runs over its
    /// children's materialized output, so every count comes from one consistent
    /// execution even with `random()`, ties under `LIMIT`, and so on. The plan is
    /// executed as analyzed, without re-optimizing it. Operators with side effects
    /// (DML, DDL, `COPY`, ...) are never executed, and operators that cannot run
    /// on their own (e.g. inside a correlated subquery) are left unconstrained.
    ///
    /// A sound analysis admits every real execution, so a `violation` names an
    /// operator whose constraint real data breaks. Beware that DataFusion does
    /// not enforce declared primary keys: data that breaks a declared key can
    /// break a constraint derived from it.
    pub async fn validate(&self, ctx: &SessionContext) -> Result<Validation> {
        let counts = validate::evaluate(&self.nodes, ctx).await;
        validate::check(&self.constraints, self.assertions, &counts)
    }

    /// Proves bounds on the output cardinality relative to the source relations:
    /// a constant bound, a bound relative to the total rows scanned, and one
    /// relative to each table. See [`Bounds`].
    ///
    /// This runs many solver checks (each limited to one second), so it is
    /// separate from the analysis itself. It depends only on the query, not on
    /// the data.
    pub fn bounds(&self) -> Result<Bounds> {
        let (search, parsed) = bounds::Search::new(&self.constraints, &self.root);
        if parsed != self.assertions {
            return Err(Error::Internal(format!(
                "constraints parsed back to {parsed} assertions, expected {}",
                self.assertions
            )));
        }
        let constant = search.constant();
        let scans: Vec<Int> = self
            .scans
            .iter()
            .map(|(s, _)| Int::new_const(s.as_str()))
            .collect();
        let sum = if scans.is_empty() {
            None
        } else {
            search.linear(&Int::add(&scans)).map(|(b, _)| b)
        };
        let tables = self
            .tables
            .iter()
            .filter_map(|(name, symbol)| {
                let (bound, exact) = search.linear(&Int::new_const(symbol.as_str()))?;
                Some(TableBound {
                    table: name.clone(),
                    bound,
                    exact,
                })
            })
            .collect();
        Ok(Bounds {
            constant,
            sum,
            tables,
        })
    }
}

/// Settings for an analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Options {
    /// The most distinct-count factors multiplied in one constraint, e.g. the
    /// columns of a GROUP BY or DISTINCT. Such products are nonlinear, so a
    /// larger cap can give tighter bounds at the cost of slower and less often
    /// decisive solving. Larger products are dropped, which is sound but weaker.
    /// Defaults to 3.
    pub max_product: usize,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            max_product: analyzer::DEFAULT_MAX_PRODUCT,
        }
    }
}

/// Parses and optimizes `sql` with `ctx`, then analyzes the resulting plan,
/// with default [`Options`].
///
/// A scan counts as a base table only if its provider is the one registered in
/// `ctx`'s catalog under that name. Every spelling of a table's name
/// (`users`, `public.users`, ...) therefore maps to one variable, and work tables
/// and table functions such as `generate_series` are not counted as input.
pub async fn analyze_sql(ctx: &SessionContext, sql: &str) -> Result<Analysis> {
    analyze_sql_with(ctx, sql, Options::default()).await
}

/// [`analyze_sql`] with explicit [`Options`].
pub async fn analyze_sql_with(
    ctx: &SessionContext,
    sql: &str,
    options: Options,
) -> Result<Analysis> {
    let state = ctx.state();
    let plan = state.create_logical_plan(sql).await?;
    let plan = state.optimize(&plan)?;

    let catalog = state.config().options().catalog.clone();
    let (default_catalog, default_schema) = (catalog.default_catalog, catalog.default_schema);

    let mut scans = Vec::new();
    plan.apply_with_subqueries(|p| {
        if let LogicalPlan::TableScan(scan) = p {
            scans.push(scan.clone());
        }
        Ok(TreeNodeRecursion::Continue)
    })?;
    let mut base = HashMap::new();
    for scan in scans {
        let Ok(registered) = ctx.table_provider(scan.table_name.clone()).await else {
            continue;
        };
        let Ok(scanned) = source_as_provider(&scan.source) else {
            continue;
        };
        if provider_ptr(&registered) == provider_ptr(&scanned) {
            let kind = base_kind(&scan.table_name, &default_catalog, &default_schema);
            base.insert(provider_ptr(&scanned), kind);
        }
    }

    let resolve = |scan: &TableScan| {
        source_as_provider(&scan.source)
            .ok()
            .and_then(|p| base.get(&provider_ptr(&p)).cloned())
            .unwrap_or(ScanKind::NonBase)
    };
    Ok(analyze_with(&plan, &resolve, options))
}

/// Analyzes an already-built logical plan, with default [`Options`].
///
/// With no catalog to consult, every scan except a recursive CTE's work table
/// counts as a base table, and names are resolved against DataFusion's default
/// catalog and schema (`datafusion.public`).
pub fn analyze_plan(plan: &LogicalPlan) -> Analysis {
    analyze_plan_with(plan, Options::default())
}

/// [`analyze_plan`] with explicit [`Options`].
pub fn analyze_plan_with(plan: &LogicalPlan, options: Options) -> Analysis {
    let resolve = |scan: &TableScan| {
        let is_work_table = source_as_provider(&scan.source)
            .map(|p| p.downcast_ref::<CteWorkTable>().is_some())
            .unwrap_or(false);
        if is_work_table {
            ScanKind::NonBase
        } else {
            base_kind(&scan.table_name, "datafusion", "public")
        }
    };
    analyze_with(plan, &resolve, options)
}

/// Identity of a provider object. An address, not a pointer, so futures holding
/// it stay `Send`.
fn provider_ptr(p: &Arc<dyn TableProvider>) -> usize {
    Arc::as_ptr(p) as *const () as usize
}

/// Canonical identity and display name for a base table reference.
fn base_kind(name: &TableReference, default_catalog: &str, default_schema: &str) -> ScanKind {
    let r = name.clone().resolve(default_catalog, default_schema);
    let key = format!("{}\0{}\0{}", r.catalog, r.schema, r.table);
    let display = if *r.catalog == *default_catalog && *r.schema == *default_schema {
        r.table.to_string()
    } else {
        r.to_string()
    };
    ScanKind::Base { key, display }
}

fn analyze_with(
    plan: &LogicalPlan,
    resolve: &dyn Fn(&TableScan) -> ScanKind,
    options: Options,
) -> Analysis {
    let mut a = Analyzer::new(resolve, options.max_product);
    let root = a.visit(plan).card;
    a.assert_partitions();
    let root_name = a.name_of(&root);
    let constraints = a.solver.to_string();
    let assertions = a.solver.get_assertions().len();

    let scan_vars: Vec<&Int> = a.scans.iter().map(|(_, _, v)| v).collect();
    let total = if scan_vars.is_empty() {
        Int::from_i64(0)
    } else {
        Int::add(&scan_vars)
    };
    // Prove the claim by showing its negation is unsatisfiable. The push makes
    // Z3 use its incremental SMT core, as in `bounds` and `validate`: its
    // one-shot strategy portfolio tries bit-blasting first once domains bound
    // many variables, which is far slower.
    a.solver.push();
    a.solver.assert(root.le(&total).not());
    let smtlib = a.solver.to_string();

    // If the incremental core gives up, fall back to the one-shot portfolio.
    let mut result = a.solver.check();
    let portfolio = analyzer::new_solver();
    let solver = if result == SatResult::Unknown {
        portfolio.from_string(smtlib.as_str());
        result = portfolio.check();
        &portfolio
    } else {
        &a.solver
    };
    let verdict = match result {
        SatResult::Unsat => Verdict::Reduces,
        SatResult::Unknown => Verdict::Unknown(
            solver
                .get_reason_unknown()
                .unwrap_or_else(|| "unknown".to_string()),
        ),
        SatResult::Sat => {
            // Z3's SMT core may pick values too large to report; look for a
            // counterexample with small ones first.
            let cap = Int::from_i64(1 << 40);
            solver.push();
            for (_, v) in &a.vars {
                solver.assert(v.le(&cap));
            }
            for t in a.tables.values() {
                solver.assert(t.var.le(&cap));
            }
            if solver.check() != SatResult::Sat {
                solver.pop(1);
                solver.check();
            }
            let model = solver.get_model().expect("sat result has a model");
            let value = |v: &Int| model.eval(v, true).and_then(|x| x.as_i64());
            Verdict::MightGrow(Counterexample {
                tables: a
                    .tables
                    .values()
                    .filter_map(|t| Some((t.display.clone(), value(&t.var)?)))
                    .collect(),
                vars: a
                    .vars
                    .iter()
                    .filter_map(|(name, v)| Some((name.clone(), value(v)?)))
                    .collect(),
            })
        }
    };

    let mut tables: Vec<(String, String)> = a
        .tables
        .values()
        .map(|t| (t.display.clone(), t.symbol.clone()))
        .collect();
    tables.sort();

    Analysis {
        verdict,
        smtlib,
        root: root_name,
        scans: a
            .scans
            .iter()
            .map(|(s, t, _)| (s.clone(), t.clone()))
            .collect(),
        plan: plan.display_indent().to_string(),
        constraints,
        assertions,
        nodes: a.nodes,
        tables,
    }
}
