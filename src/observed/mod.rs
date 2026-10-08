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
mod sql;

pub use duckdb::from_duckdb;
pub use sql::QueryText;

use std::collections::{BTreeSet, HashMap};
use std::fmt;
use std::sync::Arc;

use datafusion::arrow::datatypes::{DataType, SchemaRef};
use datafusion::common::tree_node::{Transformed, TreeNode};
use datafusion::common::{Column, DFSchema, JoinType, ScalarValue, TableReference};
use datafusion::execution::SessionState;
use datafusion::logical_expr::{BinaryExpr, Expr, ExprSchemable, Operator};
use datafusion::logical_expr::simplify::SimplifyContext;
use datafusion::functions::string::expr_fn::{contains, ends_with, starts_with};
use datafusion::optimizer::simplify_expressions::ExprSimplifier;
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
    /// A base-table scan, with the predicates applied in it. Its columns
    /// are qualified by `instance`, `table#node`, which tells apart two
    /// scans of one table.
    Scan {
        table: String,
        instance: String,
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
    /// `values` are the aggregates, which its output columns after the keys
    /// hold, as [`Lineage::Exact`] columns of relation `@{node}`.
    Aggregate { keys: Vec<Option<Expr>>, values: Vec<Option<Expr>> },
    /// `children[0]` is the probe (left) side, `children[1]` the build side.
    Join { kind: JoinType, on: Vec<Pred> },
    /// Keeps the rows of a mark join (`children[0]`) whose mark is true, or
    /// with `negated`, not true: `IN`/`EXISTS` and `NOT IN`.
    MarkFilter { negated: bool },
    /// Another operator's output (`children[0]`), read again: a CTE scan, or
    /// a delim join's input. Its columns' instances get `suffix`, as an
    /// independent copy. `checked` if its own row count was reported.
    Reuse { suffix: String, checked: bool },
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
            Op::MarkFilter { negated } => write!(f, "MarkFilter{}", if *negated { " not" } else { "" }),
            Op::Reuse { .. } => write!(f, "Reuse"),
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

    pub fn has_column(&self, table: &str, column: &str) -> bool {
        self.tables.get(table).is_some_and(|s| s.field_with_name(column).is_ok())
    }
}

/// The table a scan instance (`lineitem#3`, or a copy `lineitem#3~r9`)
/// reads, or `None` for a relation that is not an instance.
pub fn base_table(relation: &str) -> Option<&str> {
    relation.split_once('#').map(|(t, _)| t)
}

/// The relation a column belongs to, as written.
pub(crate) fn relation(c: &Column) -> Option<&str> {
    c.relation.as_ref().map(TableReference::table)
}

/// `table.column`, with the relation as written.
pub(crate) fn column_key(c: &Column) -> String {
    format!("{}.{}", relation(c).unwrap_or(""), c.name)
}

pub(crate) fn qualified(relation: &str, name: &str) -> Expr {
    Expr::Column(Column::new(Some(TableReference::bare(relation)), name))
}

/// `e` as DataFusion's optimizer writes it: types coerced as for execution,
/// so a literal takes its column's type (`l_quantity < 10.00` reads
/// `Decimal128(10.00,15,2)`, as in an optimized plan), then simplified
/// (constants folded). `schema` gives the columns of each relation: an
/// instance's table's, or an aggregate's values. Facts read off any engine's
/// plan, and the plans they are matched against, pass through here, so that
/// one predicate reads one way. An expression over a relation without a
/// schema does not type-check, and is only simplified.
pub(crate) fn normalize(e: Expr, schema: &dyn Fn(&str) -> Option<SchemaRef>) -> Expr {
    let mut columns = DFSchema::empty();
    let relations: BTreeSet<String> = e.column_refs().into_iter().filter_map(relation).map(str::to_string).collect();
    for r in &relations {
        let Some(s) = schema(r) else { continue };
        match DFSchema::try_from_qualified_schema(r.as_str(), &s) {
            Ok(s) => columns.merge(&s),
            Err(_) => return e,
        }
    }
    let schema = columns;
    let schema = Arc::new(schema);
    let simplifier = ExprSimplifier::new(SimplifyContext::builder().with_schema(schema.clone()).build());
    let coerced = simplifier.coerce(e.clone(), &schema).unwrap_or_else(|_| e.clone());
    let simplified = simplifier.simplify(coerced).unwrap_or(e);
    simplified
        .clone()
        .transform_up(|e| date_comparison(e, &schema).transform_data(|e| Ok(like(e))))
        .map(|t| t.data)
        .unwrap_or(simplified)
}

/// `x LIKE 'abc%'`, `'%abc'` and `'%abc%'` as `starts_with`, `ends_with`
/// and `contains`, as DuckDB prints them.
fn like(e: Expr) -> Transformed<Expr> {
    let Expr::Like(l) = &e else { return Transformed::no(e) };
    let Expr::Literal(ScalarValue::Utf8(Some(p)) | ScalarValue::Utf8View(Some(p)) | ScalarValue::LargeUtf8(Some(p)), _) =
        l.pattern.as_ref()
    else {
        return Transformed::no(e);
    };
    if l.case_insensitive || l.escape_char.is_some() {
        return Transformed::no(e);
    }
    let literal = |s: &str| !s.is_empty() && !s.contains(['%', '_', '\\']);
    let (x, text) = (*l.expr.clone(), |s: &str| Expr::Literal(ScalarValue::Utf8(Some(s.to_string())), None));
    let call = if let Some(middle) = p.strip_prefix('%').and_then(|r| r.strip_suffix('%')).filter(|m| literal(m)) {
        contains(x, text(middle))
    } else if let Some(end) = p.strip_prefix('%').filter(|r| literal(r)) {
        ends_with(x, text(end))
    } else if let Some(start) = p.strip_suffix('%').filter(|r| literal(r)) {
        starts_with(x, text(start))
    } else {
        return Transformed::no(e);
    };
    Transformed::yes(if l.negated { Expr::Not(Box::new(call)) } else { call })
}

/// `CAST(d AS TIMESTAMP) op t`, for a date `d` and a time-zone-free
/// timestamp `t` at midnight, as `d op date(t)`: DuckDB computes
/// `date '1998-12-01' - interval '90' day` as a timestamp, where DataFusion
/// folds it to a date. At midnight the two comparisons agree.
fn date_comparison(e: Expr, schema: &DFSchema) -> Transformed<Expr> {
    let Expr::BinaryExpr(BinaryExpr { left, op, right }) = &e else { return Transformed::no(e) };
    if !matches!(op, Operator::Lt | Operator::LtEq | Operator::Gt | Operator::GtEq | Operator::Eq | Operator::NotEq) {
        return Transformed::no(e);
    }
    let date = |side: &Expr| match side {
        Expr::Cast(c)
            if matches!(c.field.data_type(), DataType::Timestamp(_, None))
                && c.expr.get_type(schema).is_ok_and(|t| t == DataType::Date32) =>
        {
            Some((*c.expr).clone())
        }
        _ => None,
    };
    let midnight = |side: &Expr| {
        let Expr::Literal(v, _) = side else { return None };
        let (v, per_day) = match v {
            ScalarValue::TimestampSecond(Some(v), None) => (*v, 86_400),
            ScalarValue::TimestampMillisecond(Some(v), None) => (*v, 86_400_000),
            ScalarValue::TimestampMicrosecond(Some(v), None) => (*v, 86_400_000_000),
            ScalarValue::TimestampNanosecond(Some(v), None) => (*v, 86_400_000_000_000),
            _ => return None,
        };
        let days = i32::try_from(v.div_euclid(per_day)).ok()?;
        (v.rem_euclid(per_day) == 0).then(|| Expr::Literal(ScalarValue::Date32(Some(days)), None))
    };
    let (l, r) = match (date(left), midnight(right), midnight(left), date(right)) {
        (Some(d), Some(t), _, _) => (d, t),
        (_, _, Some(t), Some(d)) => (t, d),
        _ => return Transformed::no(e),
    };
    Transformed::yes(Expr::BinaryExpr(BinaryExpr::new(Box::new(l), *op, Box::new(r))))
}

/// `e` with each column's relation renamed by `f`, where it gives a name.
pub(crate) fn requalify(e: &Expr, f: &dyn Fn(&str) -> Option<String>) -> Expr {
    e.clone()
        .transform_up(|e| match e {
            Expr::Column(c) => match relation(&c).and_then(f) {
                Some(r) => Ok(Transformed::yes(qualified(&r, &c.name))),
                None => Ok(Transformed::no(Expr::Column(c))),
            },
            e => Ok(Transformed::no(e)),
        })
        .map(|t| t.data)
        .unwrap_or_else(|e| panic!("renaming columns cannot fail: {e}"))
}
