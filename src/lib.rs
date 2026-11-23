//! Proven bounds on SQL output cardinality.
//!
//! A query is parsed and optimized into a DataFusion `LogicalPlan`, every operator
//! gets a Z3 integer for its output cardinality, and constraints relate them
//! ([`Analysis`]). We then ask Z3 for the tightest `lower <= X <= upper` it can
//! prove on the root's cardinality `X` ([`Analysis::bounds`]), or on every
//! operator's and their sum ([`Analysis::plan_bounds`]).
//!
//! An analysis is made by a [`Builder`]: the query to bound
//! ([`Analysis::sql`], [`Analysis::plan`], ...), then what is known of the
//! data it runs on: executed plans of other queries
//! ([`Builder::with_plans`]) and tables' row counts
//! ([`Builder::with_cardinalities`]).
//!
//! ```ignore
//! let a = Analysis::sql(&ctx, sql).await?
//!     .options(options)
//!     .with_plans(&profiles)
//!     .with_cardinalities([("lineitem", 6001215)])
//!     .build()?;
//! ```
//!
//! A [`Batch`] analyzes several queries with the same options, plans and
//! row counts ([`Analysis::sqls`], [`Analysis::batch`]).
//!
//! The constraints come from these passes, in order:
//!
//! 1. [`rules`]: a walk over the plan, and over the reference plans' parts
//!    the query could share rows with ([`joint`]), one rule per operator,
//!    asserting what the operator adds. Where the plan's shape relates rows
//!    (an operator and its input, one op output), the
//!    rules apply [`properties`] of rows.
//! 2. [`link`]: the same properties, and disjointness, between operators
//!    off one path, through an e-graph of every plan: select-project-join
//!    subtrees whose predicates Z3 relates, and other operators (GROUP BY,
//!    semi, anti and outer joins, limits) over the same or nested inputs.
//! 3. [`joint`]: each operator of a reference plan pinned to the rows it
//!    was counted with, and each table given a row count held to it; the
//!    plans' own variables then substituted away.
//!
//! ```text
//!       query: SQL ─parse, optimize─▶ LogicalPlan      reference plans
//!                                               │      (ObservedPlan)
//! ┌─ 1. rules: Analyzer::visit ─────────────────▼──────────▼─┐
//! │ bottom-up, one rule per operator, the query's, then the  │
//! │ plans' parts over its tables                             │
//! │   each count          ≥ 0                                │
//! │   each operator       what it adds: X ≤ l·r, X = Σ, …    │──┐
//! │   with its input      same rows, subset, wider           │  │
//! │   each op output      ndv ≤ X, domains, keys             │  │
//! └─────────────────────────────────────────────┬────────────┘  │
//!                            op outputs, nodes  │               │
//! ┌─ 2. link: link::link_all ───────────────────▼────────────┐  │
//! │ e-graph, bottom-up: SPJ subtrees by predicates, other    │  ├─▶ Z3
//! │ operators by inputs and keys; same rows, subset,         │  │
//! │ disjoint, fewer, split                                   │  │
//! └─────────────────────────────────────────────┬────────────┘  │
//! ┌─ 3. pins: joint, Builder::with_cardinalities▼────────────┐  │
//! │ a counted operator X = rows (≥ where a runtime filter    │  │
//! │ pruned), a given table |T| = rows; then the plans'       │  │
//! │ variables substituted out                                │──┘
//! └─────────────────────────────────────────────┬────────────┘
//!                  Analysis: constraints, nodes │
//!                                               ▼
//!                          bounds search: Analysis::bounds, plan_bounds
//! ```

pub mod analysis;
pub mod link;
mod batch;
mod bounds;
mod builder;
mod domain;
mod keys;
mod predicates;
pub mod joint;
pub mod observed;
pub mod properties;
pub mod rules;
pub mod trace;
mod validate;

pub use batch::Batch;
pub use bounds::{Bounds, NodeBounds, PlanBounds, SearchStats};
pub use builder::Builder;
pub use trace::{Constraint, FactInfo, FactRef, Proof, ProofStatus, Trace, TraceNode};

use std::collections::HashMap;
use std::sync::OnceLock;

use datafusion::prelude::SessionContext;
use z3::ast::{Bool, Int};
use z3::{Solver, Synchronized};

use analysis::Node;

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
    /// Reference plans given for a query with no catalog to read them
    /// against ([`Analysis::logical`]).
    #[error("reference plans need a catalog: make the query with Analysis::sql or Analysis::plan")]
    NoCatalog,
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
    /// The constraint set `S`, as terms in a Z3 context of their own: the
    /// bounds search starts from them.
    constraints: Synchronized<Vec<Bool>>,
    /// `S` in SMT-LIB, printed on first use ([`Analysis::constraints`]),
    /// and how many assertions it holds (to check that it parses back
    /// completely).
    text: OnceLock<String>,
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
        let mut v = validate::check(self.constraints(), self.assertions, &counts, &ends)?;
        // A broken dependency explains the counts that contradict `S`.
        if broken.is_some() {
            v.violation = broken;
        }
        Ok(v)
    }

    /// Proves the tightest `lower <= X <= upper` on the output cardinality.
    ///
    /// This runs many solver checks, each limited to a fixed amount of
    /// solver work (most often under a second; more for the first, which
    /// loads the constraints), so it is separate from the analysis itself.
    /// The limit is not a time, so the bounds do not depend on the
    /// machine's load. Without facts they depend only on the query, not on
    /// the data.
    pub fn bounds(&self) -> Result<Bounds> {
        Ok(self.with_search(|s| s.bounds()))
    }

    /// [`Analysis::bounds`], and how its solver checks went.
    #[doc(hidden)]
    pub fn bounds_with_stats(&self) -> Result<(Bounds, SearchStats)> {
        Ok(self.with_search(|s| (s.bounds(), s.stats())))
    }

    /// Proves the tightest range on every operator's output cardinality,
    /// as [`Analysis::bounds`] does on the root's, and on their sum: how many
    /// rows the plan's operators produce in all. Every node counts, those that
    /// pass their input's rows through (a projection, an alias) too, and a
    /// subquery's operators count once.
    ///
    /// This runs a search per operator, so it costs more than
    /// [`Analysis::bounds`]; an operator proven to output its input's rows
    /// shares its input's range.
    pub fn plan_bounds(&self) -> Result<PlanBounds> {
        Ok(self.plan_bounds_with_stats()?.0)
    }

    /// [`Analysis::plan_bounds`], and how its solver checks went.
    #[doc(hidden)]
    pub fn plan_bounds_with_stats(&self) -> Result<(PlanBounds, SearchStats)> {
        let vars: Vec<&str> = self.nodes.iter().map(|n| n.var.as_str()).collect();
        let same: Vec<Option<usize>> = self
            .nodes
            .iter()
            .map(|n| match n.inputs[..] {
                [i] => Some(i),
                _ => None,
            })
            .collect();
        let (ranges, total, stats) = self.with_search(|search| {
            let cards: Vec<Int> = vars.iter().map(|v| Int::new_const(*v)).collect();
            let (ranges, total) = search.plan(&cards, &same);
            (ranges, total, search.stats())
        });
        let nodes = self
            .nodes
            .iter()
            .zip(ranges)
            .map(|(n, bounds)| NodeBounds {
                var: n.var.clone(),
                operator: n.plan.display().to_string(),
                inputs: n.inputs.clone(),
                bounds,
            })
            .collect();
        Ok((PlanBounds { nodes, total }, stats))
    }

    /// The constraints `S`, in SMT-LIB. Printed on the first call, which
    /// can take a while for a large analysis.
    pub fn constraints(&self) -> &str {
        self.text.get_or_init(|| {
            in_own_context(|| {
                let solver = Solver::new();
                self.constraints.recover().iter().for_each(|f| solver.assert(f));
                solver.to_string()
            })
        })
    }

    /// Runs `f` on a search over the constraints, in a Z3 context of its
    /// own ([`in_own_context`]).
    fn with_search<R: Send + Sync>(&self, f: impl FnOnce(&bounds::Search) -> R + Send + Sync) -> R {
        in_own_context(|| f(&bounds::Search::new(&self.constraints.recover(), &self.root)))
    }

    /// Proves each side of `bounds` again, with a minimal set of the
    /// constraints that proves it: which operators, rules and pins a bound
    /// comes from. Needs [`Options::trace`].
    ///
    /// Proof names are `lower` and `upper`; a side with nothing to prove
    /// (`X >= 0`, no upper bound) has none.
    pub fn explain(&self, bounds: &Bounds) -> Result<Vec<Proof>> {
        let Some(trace) = &self.trace else {
            return Err(Error::Internal("explain needs Options::trace".into()));
        };
        trace.explain(&trace::claims(&self.root, "", "X", bounds))
    }

    /// [`Analysis::explain`] for every operator's bounds: each node's proofs,
    /// by node id, named `n{id}.lower` and `n{id}.upper`. A node with nothing
    /// to prove has none. Every claim is proven with one solver, so this costs
    /// far less than as many calls of [`Analysis::explain`].
    pub fn explain_plan(&self, plan: &PlanBounds) -> Result<Vec<Vec<Proof>>> {
        let Some(trace) = &self.trace else {
            return Err(Error::Internal("explain_plan needs Options::trace".into()));
        };
        let per: Vec<Vec<(String, String, String)>> = plan
            .nodes
            .iter()
            .enumerate()
            .map(|(id, n)| trace::claims(&n.var, &format!("n{id}."), &format!("|#{id}|"), &n.bounds))
            .collect();
        let mut proofs = trace.explain(&per.concat())?.into_iter();
        Ok(per.iter().map(|c| proofs.by_ref().take(c.len()).collect()).collect())
    }
}

/// Runs `f` in a new Z3 context, which every Z3 object it makes must stay
/// in.
///
/// Z3 reuses the ids of freed terms, and its search heuristics order by
/// id. In the thread's context, the terms an analysis made and freed (link's
/// checks, most of all) leave the constraints copied in with other ids,
/// which can make every check of a search far slower. A new context gives
/// the same constraints the same ids each time.
///
/// Nothing run in one calls into rayon ([`Batch`]): a task stolen while
/// waiting would run in this context, not its own.
pub(crate) fn in_own_context<R: Send + Sync>(f: impl FnOnce() -> R + Send + Sync) -> R {
    z3::with_z3_config(&z3::Config::new(), f)
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
