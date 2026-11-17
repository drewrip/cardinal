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
//! ([`Builder::with_plans`]) and facts given by hand
//! ([`Builder::with_facts`]).
//!
//! ```ignore
//! let a = Analysis::sql(&ctx, sql).await?
//!     .options(options)
//!     .with_plans(&profiles)
//!     .with_facts(&facts)
//!     .build()?;
//! ```
//!
//! The constraints come from these passes, in order:
//!
//! 1. [`rules`]: a walk over the plan, and over the reference plans' parts
//!    the query could share rows with ([`joint`]), one rule per operator,
//!    asserting what the operator adds and recording each relation it makes
//!    and how its rows are its inputs'.
//! 2. [`axioms`]: what holds of any rows whatever made them, asserted over
//!    those records and between [contexts](rows), in every analysis.
//! 3. [`joint`]: each operator of a reference plan pinned to the rows it
//!    was counted with; the plans' own variables then substituted away.
//! 4. [`facts`]: facts given by hand, added as claims on the query's
//!    operators, assumed consistent with the rest unless
//!    [`Options::check_facts`] asks to check.
//! 5. [`postprocess`]: when bounds are searched for, constraints that
//!    cannot move them are left out, if [`Options::postprocess`] asks.
//!
//! ```text
//!       query: SQL ─parse, optimize─▶ LogicalPlan      reference plans
//!                                               │      (ObservedPlan)
//! ┌─ 1. rules: Analyzer::visit ─────────────────▼──────────▼─┐
//! │ bottom-up, one rule per operator, the query's, then the  │
//! │ plans' parts over its tables                             │
//! │   asserts what the operator adds   X ≤ l·r, X = Σ, …     │──┐
//! │   records each relation            Relation: variables,  │  │
//! │                                    domains, keys, origin │  │
//! │   records how relations relate     Link: same rows,      │  │
//! │                                    subset, wider rows    │  │
//! └─────────────────────────────────────────────┬────────────┘  │
//!                       relations, links, nodes │               │
//! ┌─ 2. axioms: axioms::assert_all ─────────────▼────────────┐  │
//! │ every count     ≥ 0                                      │  │
//! │ each relation   ndv ≤ X, keys, domains, row facts        │  │
//! │ each link       X ≤ l, ndv ≤ ndv_l, ranges within        │  ├─▶ Z3
//! │ one table       disjoint filters split it                │  │
//! │ contexts        ⊆, fewer, joins, semi + anti, …          │  │
//! └─────────────────────────────────────────────┬────────────┘  │
//! ┌─ 3. pins: joint ────────────────────────────▼────────────┐  │
//! │ a counted operator X = rows (≥ where a runtime filter    │  │
//! │ pruned); dead columns, then the plans' variables, out    │──┘
//! └─────────────────────────────────────────────┬────────────┘
//!                  Analysis: constraints, nodes │
//! ┌─ 4. facts: Builder::with_facts ─────────────▼────────────┐
//! │ a claim on an operator; checked against 1–3 if asked     │──▶ Z3
//! └─────────────────────────────────────────────┬────────────┘
//!                                               ▼
//!                  5. postprocess: dead columns left out, if asked
//!                                               ▼
//!                          bounds search: Analysis::bounds, plan_bounds
//! ```

pub mod analysis;
pub mod axioms;
mod bounds;
mod builder;
mod domain;
mod keys;
pub mod facts;
pub mod joint;
pub mod observed;
mod origin;
pub mod postprocess;
pub mod rows;
pub mod rules;
pub mod trace;
mod validate;

pub use bounds::{Bounds, NodeBounds, PlanBounds, SearchStats};
pub use builder::Builder;
pub use facts::Facts;
pub use postprocess::Postprocess;
pub use trace::{Constraint, FactInfo, FactRef, Proof, ProofStatus, Trace, TraceNode};

use std::collections::HashMap;

use datafusion::prelude::SessionContext;
use z3::ast::Int;

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
    /// The constraint set `S`, and how many assertions it holds (to check
    /// that it parses back completely).
    constraints: String,
    assertions: usize,
    /// Every plan node, children before parents.
    nodes: Vec<Node>,
    /// [`Options::check_facts`].
    check_facts: bool,
    /// [`Options::postprocess`].
    postprocess: Postprocess,
    /// Every assertion with its role, for [`postprocess`]; none for an
    /// analysis it cannot read.
    parts: Option<postprocess::Assertions>,
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
        let search = self.search()?;
        let cards: Vec<Int> = self.nodes.iter().map(|n| Int::new_const(n.var.as_str())).collect();
        let same: Vec<Option<usize>> = self
            .nodes
            .iter()
            .map(|n| match n.inputs[..] {
                [i] => Some(i),
                _ => None,
            })
            .collect();
        let (ranges, total) = search.plan(&cards, &same);
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
        Ok((PlanBounds { nodes, total }, search.stats()))
    }

    /// The constraints `S`, in SMT-LIB.
    pub fn constraints(&self) -> &str {
        &self.constraints
    }

    /// A search over the constraints, [postprocessed](postprocess) as
    /// [`Options::postprocess`] asks.
    pub(crate) fn search(&self) -> Result<bounds::Search> {
        match &self.parts {
            Some(parts) if self.postprocess.dead_columns => {
                let (script, n) = parts.pruned();
                search_of(&script, n, &self.root)
            }
            _ => self.search_all(),
        }
    }

    /// Whether each constraint, in order, is solved with when
    /// [`Options::postprocess`] leaves out dead columns; `None` if the
    /// analysis cannot tell.
    #[doc(hidden)]
    pub fn kept_constraints(&self) -> Option<Vec<bool>> {
        self.parts.as_ref().map(|p| p.kept())
    }

    /// A search over every constraint.
    pub(crate) fn search_all(&self) -> Result<bounds::Search> {
        search_of(&self.constraints, self.assertions, &self.root)
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

/// A search over `constraints`, checked to hold all `n` assertions.
fn search_of(constraints: &str, n: usize, root: &str) -> Result<bounds::Search> {
    let (search, parsed) = bounds::Search::new(constraints, root);
    if parsed != n {
        return Err(Error::Internal(format!("constraints parsed back to {parsed} assertions, expected {n}")));
    }
    Ok(search)
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
    /// Check each claim [`Builder::with_facts`] adds against the
    /// constraints, one solver check per claim, and leave out those that
    /// contradict them. Off, facts are assumed consistent. Defaults to false.
    pub check_facts: bool,
    /// Simplifications of the constraints before the bounds search. Defaults
    /// to none.
    pub postprocess: Postprocess,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            max_product: analysis::DEFAULT_MAX_PRODUCT,
            foreign_keys: Vec::new(),
            trace: false,
            check_facts: false,
            postprocess: Postprocess::default(),
        }
    }
}
