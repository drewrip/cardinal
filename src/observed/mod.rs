//! Plans as an engine ran them, with the rows each operator produced.
//!
//! An [`ObservedPlan`] is a common form for the profiles engines print
//! (`EXPLAIN ANALYZE`): a tree of operators, each with the row count it output
//! and the columns it carries. Predicates and keys are DataFusion [`Expr`]s
//! over base-table columns, whatever projections sat in between, so the same
//! predicate reads the same in every plan and every engine. Whatever an engine
//! prints that cannot be read that way is kept as text and marked unresolved,
//! never guessed.

mod duckdb;

pub use duckdb::from_duckdb;

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use datafusion::arrow::datatypes::SchemaRef;
use datafusion::common::{DFSchema, JoinType};
use datafusion::execution::SessionState;
use datafusion::logical_expr::Expr;
use datafusion::prelude::SessionContext;

use crate::Result;

/// An executed plan: its operators, children before parents.
#[derive(Debug, Clone)]
pub struct ObservedPlan {
    /// The query's name, for provenance.
    pub name: String,
    pub nodes: Vec<ONode>,
    pub root: usize,
}

#[derive(Debug, Clone)]
pub struct ONode {
    pub op: Op,
    /// Rows the operator output.
    pub rows: u64,
    pub children: Vec<usize>,
    /// The columns of its output.
    pub columns: Vec<OutCol>,
    /// Whether `columns` are in output order, so positional references
    /// resolve. An engine may drop or reorder a join's columns unseen.
    pub ordered: bool,
    /// The engine's own name for the operator, e.g. `PERFECT_HASH_GROUP_BY`.
    pub engine_op: String,
}

#[derive(Debug, Clone)]
pub enum Op {
    /// A base-table scan, with the predicates applied in it.
    Scan {
        table: String,
        filters: Vec<Pred>,
        /// Filters the engine derived at run time from a join's other side
        /// (min/max, IN lists, bloom filters). They drop rows of this scan
        /// that have no join partner.
        runtime_filters: Vec<RuntimeFilter>,
    },
    /// Keeps the rows satisfying every conjunct.
    Filter { predicate: Vec<Pred> },
    Project,
    Sort,
    Window,
    /// GROUP BY `keys`, or no grouping when empty. `None` is a key that did
    /// not resolve. Keys are only good for counting distinct values: a key
    /// may be an engine's reversible encoding of the expression shown.
    Aggregate { keys: Vec<Option<Expr>> },
    /// `children[0]` is the probe (left) side, `children[1]` the build side.
    Join { kind: JoinType, on: Vec<Pred> },
    TopN { fetch: u64 },
    /// A limit, which may stop its input early.
    Limit,
    Union,
    /// Anything without a model here (correlated-subquery plumbing, CTEs, a
    /// join kind DataFusion has no name for, ...).
    Other,
}

/// A predicate as the engine printed it, and as an expression over base
/// columns if it could be read.
#[derive(Debug, Clone)]
pub struct Pred {
    pub expr: Option<Expr>,
    pub text: String,
    /// The engine may or may not have applied it: it only prunes, and
    /// something above enforces it.
    pub optional: bool,
}

#[derive(Debug, Clone)]
pub struct RuntimeFilter {
    /// The `table.column` it filters, if known.
    pub column: Option<String>,
    pub text: String,
}

#[derive(Debug, Clone)]
pub struct OutCol {
    pub name: String,
    pub lineage: Lineage,
}

/// What an output column holds, in terms of base-table columns.
#[derive(Debug, Clone)]
pub enum Lineage {
    /// Exactly this expression.
    Exact(Expr),
    /// A one-to-one encoding of this expression (DuckDB compresses columns
    /// before joins and aggregates), so it has as many distinct values.
    Bijective(Expr),
    Unknown,
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Op::Scan { table, .. } => write!(f, "Scan {table}"),
            Op::Filter { .. } => write!(f, "Filter"),
            Op::Project => write!(f, "Project"),
            Op::Sort => write!(f, "Sort"),
            Op::Window => write!(f, "Window"),
            Op::Aggregate { .. } => write!(f, "Aggregate"),
            Op::Join { kind, .. } => write!(f, "{kind} Join"),
            Op::TopN { fetch } => write!(f, "TopN {fetch}"),
            Op::Limit => write!(f, "Limit"),
            Op::Union => write!(f, "Union"),
            Op::Other => write!(f, "Other"),
        }
    }
}

impl fmt::Display for ObservedPlan {
    /// The tree, one operator per line, root first.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn go(p: &ObservedPlan, i: usize, depth: usize, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let n = &p.nodes[i];
            writeln!(f, "{:w$}#{i} {} ({}) rows={}", "", n.op, n.engine_op, n.rows, w = depth * 2)?;
            for &c in &n.children {
                go(p, c, depth + 1, f)?;
            }
            Ok(())
        }
        go(self, self.root, 0, f)
    }
}

/// The tables plans are read against, from a [`SessionContext`] with them
/// registered (they may be empty: only schemas are used).
pub struct Catalog {
    state: SessionState,
    tables: HashMap<String, SchemaRef>,
    /// Every table's columns, qualified by table name.
    all: Arc<DFSchema>,
}

impl Catalog {
    pub async fn from_context(ctx: &SessionContext) -> Result<Catalog> {
        let mut tables = HashMap::new();
        let mut all = DFSchema::empty();
        let mut names = vec![];
        for catalog in ctx.catalog_names() {
            let Some(c) = ctx.catalog(&catalog) else { continue };
            for schema in c.schema_names() {
                let Some(s) = c.schema(&schema) else { continue };
                for name in s.table_names() {
                    if let Some(t) = s.table(&name).await? {
                        names.push((name, t.schema()));
                    }
                }
            }
        }
        names.sort_by(|a, b| a.0.cmp(&b.0));
        for (name, schema) in names {
            if tables.contains_key(&name) {
                continue;
            }
            all.merge(&DFSchema::try_from_qualified_schema(name.as_str(), &schema)?);
            tables.insert(name, schema);
        }
        Ok(Catalog { state: ctx.state(), tables, all: Arc::new(all) })
    }

    /// Every table's columns, qualified by table name.
    pub fn schema(&self) -> &Arc<DFSchema> {
        &self.all
    }
}
