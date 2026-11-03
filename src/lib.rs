//! Proven bounds on SQL output cardinality.
//!
//! A query is parsed and optimized into a DataFusion `LogicalPlan`, every operator
//! gets a Z3 integer for its output cardinality, and constraints relate them
//! ([`Analysis`]). We then ask Z3 for the tightest `lower <= X <= upper` it can
//! prove on the root's cardinality `X` ([`Analysis::bounds`]).
//!
//! The constraints come from three places:
//!
//! - [`rules`]: each operator's output given its inputs, one rule per operator.
//! - [`axioms`]: what holds of any rows whatever made them, on each relation and
//!   between rows named the same way ([`rows`]), in every analysis.
//! - [`facts`]: counts read off plans that ran, added as claims on the
//!   query's operators ([`Analysis::with_facts`]).

pub mod analysis;
pub mod axioms;
mod bounds;
mod domain;
mod keys;
pub mod facts;
pub mod observed;
mod origin;
pub mod rows;
pub mod rules;
pub mod trace;
mod validate;

pub use bounds::{Bounds, SearchStats};
pub use facts::Facts;
pub use trace::{Constraint, FactInfo, FactRef, Proof, ProofStatus, Trace, TraceNode};

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

use analysis::{Analyzer, Node, ScanKind};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    DataFusion(#[from] datafusion::error::DataFusionError),
    /// A bug in this library, e.g. constraints that failed to round-trip.
    #[error("internal error: {0}")]
    Internal(String),
    /// A formula was evaluated without the row count of a table it mentions.
    #[error("no row count given for table {0}")]
    UnknownTable(String),
    /// An engine's plan profile that could not be read.
    #[error("unreadable plan profile: {0}")]
    Observed(String),
}

pub type Result<T> = std::result::Result<T, Error>;

/// A query's operators, each with a Z3 variable for its output cardinality,
/// and the constraints `S` relating them.
#[derive(Debug, Clone)]
pub struct Analysis {
    /// Name of the root operator's variable.
    pub root: String,
    /// Each base-table scan as (scan variable, table name), in visit order.
    pub scans: Vec<(String, String)>,
    /// The optimized plan that was analyzed, for display.
    pub plan: String,
    /// Every constraint with the plan node and analyzer line it comes from,
    /// if [`Options::trace`] is set.
    pub trace: Option<Trace>,
    /// The constraint set `S`, and how many assertions it holds (to check
    /// that it parses back completely).
    constraints: String,
    assertions: usize,
    /// Every plan node, children before parents.
    nodes: Vec<Node>,
}

/// Result of checking a real execution against the constraint set `S`.
#[derive(Debug, Clone)]
pub struct Validation {
    /// Actual output rows of every evaluated plan node, by variable name.
    pub rows: HashMap<String, u64>,
    /// The first operator (children before parents) whose actual row count
    /// contradicts `S` given the counts below it; or, first, the first
    /// operator whose rows break a functional dependency the rules relied
    /// on, with how. `None` means every evaluated node is consistent with `S`.
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
        let (counts, ends, broken) = validate::evaluate(&self.nodes, ctx).await;
        let mut v = validate::check(&self.constraints, self.assertions, &counts, &ends)?;
        // A broken dependency explains the counts that contradict `S`.
        if broken.is_some() {
            v.violation = broken;
        }
        Ok(v)
    }

    /// Proves the tightest `lower <= X <= upper` on the output cardinality.
    ///
    /// This runs many solver checks (each limited to one second), so it is
    /// separate from the analysis itself. Without facts it depends only on
    /// the query, not on the data.
    pub fn bounds(&self) -> Result<Bounds> {
        Ok(self.search()?.bounds())
    }

    /// [`Analysis::bounds`], and how its solver checks went.
    #[doc(hidden)]
    pub fn bounds_with_stats(&self) -> Result<(Bounds, SearchStats)> {
        let search = self.search()?;
        Ok((search.bounds(), search.stats()))
    }

    /// The constraints `S`, in SMT-LIB.
    pub fn constraints(&self) -> &str {
        &self.constraints
    }

    pub(crate) fn search(&self) -> Result<bounds::Search> {
        let (search, parsed) = bounds::Search::new(&self.constraints, &self.root);
        if parsed != self.assertions {
            return Err(Error::Internal(format!(
                "constraints parsed back to {parsed} assertions, expected {}",
                self.assertions
            )));
        }
        Ok(search)
    }

    /// This analysis with what `facts` know among its constraints: every row
    /// count, distinct count and least or greatest value they give of an
    /// operator's rows, exact or a bound, as a claim on its variable. A claim
    /// that contradicts the constraints, or whose consistency Z3 cannot
    /// decide, is left out.
    ///
    /// The facts must describe the data the bounds are for: a fact read off
    /// a plan of other data gives bounds about that data.
    pub fn with_facts(&self, facts: &Facts) -> Result<Analysis> {
        facts::apply::apply(self, facts)
    }

    /// Proves each side of `bounds` again, with a minimal set of the
    /// constraints that proves it: which operators, rules and facts a bound
    /// comes from. Needs [`Options::trace`].
    ///
    /// Proof names are `lower` and `upper`; a side with nothing to prove
    /// (`X >= 0`, no upper bound) has none.
    pub fn explain(&self, bounds: &Bounds) -> Result<Vec<Proof>> {
        let Some(trace) = &self.trace else {
            return Err(Error::Internal("explain needs Options::trace".into()));
        };
        trace.explain(&trace::claims(&self.root, bounds))
    }
}

/// A foreign key: each row of `table` has `columns` never NULL and equal to
/// `referenced` of exactly one row of `references`. Tables are named as the
/// analysis shows them (bare in the default schema). Declared keys are
/// trusted, like primary keys: data that breaks one can break a bound.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForeignKey {
    pub table: String,
    pub columns: Vec<String>,
    pub references: String,
    pub referenced: Vec<String>,
}

impl ForeignKey {
    /// `table(columns)` referencing `references(referenced)`, column for column.
    pub fn new(table: &str, columns: &[&str], references: &str, referenced: &[&str]) -> ForeignKey {
        assert_eq!(columns.len(), referenced.len(), "a foreign key pairs its columns");
        let names = |cs: &[&str]| cs.iter().map(|c| c.to_string()).collect();
        ForeignKey {
            table: table.to_string(),
            columns: names(columns),
            references: references.to_string(),
            referenced: names(referenced),
        }
    }

    /// The pairs of referencing and referenced columns, in order.
    pub(crate) fn pairs(&self) -> Vec<(&str, &str)> {
        let mut pairs: Vec<(&str, &str)> =
            self.columns.iter().map(String::as_str).zip(self.referenced.iter().map(String::as_str)).collect();
        pairs.sort();
        pairs
    }
}

/// Settings for an analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Options {
    /// The most distinct-count factors multiplied in one constraint, e.g. the
    /// columns of a GROUP BY or DISTINCT. Such products are nonlinear, so a
    /// larger cap can give tighter bounds at the cost of slower and less often
    /// decisive solving. Larger products are dropped, which is sound but weaker.
    /// Defaults to 3.
    pub max_product: usize,
    /// Foreign keys the data satisfies. A join on exactly one, against every
    /// row of the table it references, keeps each referencing row exactly
    /// once. DataFusion has no foreign key constraints, so they are declared
    /// here. Defaults to none.
    pub foreign_keys: Vec<ForeignKey>,
    /// Keep every constraint with the plan node and analyzer line it comes
    /// from ([`Analysis::trace`]), to inspect or explain the analysis.
    /// Defaults to false.
    pub trace: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            max_product: analysis::DEFAULT_MAX_PRODUCT,
            foreign_keys: Vec::new(),
            trace: false,
        }
    }
}

/// Parses and optimizes `sql` with `ctx`, then analyzes the resulting plan.
///
/// A scan counts as a base table only if its provider is the one registered in
/// `ctx`'s catalog under that name. Every spelling of a table's name
/// (`users`, `public.users`, ...) therefore maps to one variable, and work tables
/// and table functions such as `generate_series` are not counted as input.
pub async fn analyze_sql(ctx: &SessionContext, sql: &str, options: Options) -> Result<Analysis> {
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

/// Analyzes an already-built logical plan.
///
/// With no catalog to consult, every scan except a recursive CTE's work table
/// counts as a base table, and names are resolved against DataFusion's default
/// catalog and schema (`datafusion.public`).
pub fn analyze_plan(plan: &LogicalPlan, options: Options) -> Analysis {
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

/// Analyzes `plan`, the plan an engine chose for a query, in place of the
/// plan DataFusion would choose. Its operators keep the engine's order, so
/// their rows are the ones the engine's profiles count: see
/// [`observed::Catalog::to_logical`]. The plan's row counts, if any, are not
/// read.
pub fn analyze_observed(catalog: &observed::Catalog, plan: &observed::ObservedPlan, options: Options) -> Result<Analysis> {
    let plan = catalog.to_logical(plan)?;
    // Every scan is of a table in the catalog, by its bare name.
    let resolve = |scan: &TableScan| base_kind(&scan.table_name, "datafusion", "public");
    Ok(analyze_with(&plan, &resolve, options))
}

/// [`analyze_observed`] on DuckDB's plan for `sql`, as printed by `EXPLAIN
/// (FORMAT JSON)` (or by `EXPLAIN (ANALYZE, FORMAT JSON)`).
pub fn analyze_duckdb(catalog: &observed::Catalog, json: &str, sql: Option<&str>, options: Options) -> Result<Analysis> {
    let plan = observed::from_duckdb_explain(catalog, "", json, sql)?;
    analyze_observed(catalog, &plan, options)
}

/// [`analyze_observed`] on PostgreSQL's plan for `sql`, as printed by
/// `EXPLAIN (VERBOSE, FORMAT JSON)` (or with `ANALYZE`, too).
pub fn analyze_postgres(catalog: &observed::Catalog, json: &str, sql: Option<&str>, options: Options) -> Result<Analysis> {
    let plan = observed::from_postgres_explain(catalog, "", json, sql)?;
    analyze_observed(catalog, &plan, options)
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

/// The analyzer's nodes for `plan`, and each base-table scan as (scan
/// variable, table name), as [`analyze_observed`] builds them.
pub(crate) fn nodes(plan: &LogicalPlan, options: &Options) -> (Vec<Node>, Vec<(String, String)>) {
    let resolve = |scan: &TableScan| base_kind(&scan.table_name, "datafusion", "public");
    let mut a = Analyzer::new(&resolve, options.max_product, &options.foreign_keys, false).with_ranges(plan);
    a.visit(plan);
    let scans = a.scans.iter().map(|(s, t, _)| (s.clone(), t.clone())).collect();
    (a.nodes, scans)
}

fn analyze_with(
    plan: &LogicalPlan,
    resolve: &dyn Fn(&TableScan) -> ScanKind,
    options: Options,
) -> Analysis {
    let mut a = Analyzer::new(resolve, options.max_product, &options.foreign_keys, options.trace).with_ranges(plan);
    let root = a.visit(plan).card;
    a.disjoint();
    a.named_rows();
    let root_name = a.name_of(&root);
    let constraints = a.solver.to_string();
    let assertions = a.solver.get_assertions().len();

    let mut tables: Vec<(String, String)> = a
        .tables
        .values()
        .map(|t| (t.display.clone(), t.symbol.clone()))
        .collect();
    tables.sort();

    let scans: Vec<(String, String)> = a
        .scans
        .iter()
        .map(|(s, t, _)| (s.clone(), t.clone()))
        .collect();
    let trace = options.trace.then(|| Trace::build(&a, &constraints, &root_name, &scans, &tables));
    if let Some(t) = &trace {
        assert_eq!(t.constraints.len(), assertions, "every assertion is traced");
    }

    Analysis {
        root: root_name,
        scans,
        plan: plan.display_indent().to_string(),
        trace,
        constraints,
        assertions,
        nodes: a.nodes,
    }
}
