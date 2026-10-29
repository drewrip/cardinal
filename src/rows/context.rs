//! Terms and contexts: predicates and the rows they select, written
//! canonically.

use std::collections::BTreeSet;
use std::fmt;

use datafusion::common::tree_node::{Transformed, TreeNode};
use datafusion::common::JoinType;
use datafusion::logical_expr::utils::{conjunction, disjunction, split_conjunction_owned};
use datafusion::logical_expr::{BinaryExpr, Expr, Operator};
use datafusion::sql::unparser::Unparser;
use std::sync::{Arc, LazyLock};

use datafusion::execution::TaskContext;
use datafusion::prelude::SessionContext;
use datafusion_proto::logical_plan::DefaultLogicalExtensionCodec;
use datafusion_proto::logical_plan::from_proto::parse_expr;
use datafusion_proto::logical_plan::to_proto::serialize_expr;
use datafusion_proto::protobuf::LogicalExprNode;
use serde::de::Error as _;
use serde::ser::Error as _;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::rewrite;
use crate::observed::requalify;

/// An expression in canonical form, ordered and compared by its text.
#[derive(Debug, Clone)]
pub struct Term {
    pub expr: Expr,
    key: String,
}

impl Term {
    pub fn new(expr: Expr) -> Term {
        let expr = canonical(expr);
        Term { key: expr.to_string(), expr }
    }

    /// The term of `expr`, already in canonical form.
    pub(crate) fn canonical(expr: Expr) -> Term {
        Term { key: expr.to_string(), expr }
    }

    /// The canonical text, which identifies the term.
    pub fn key(&self) -> &str {
        &self.key
    }

    /// The term with its columns' relations renamed by `f`.
    pub fn rename(&self, f: &dyn Fn(&str) -> Option<String>) -> Term {
        Term::new(requalify(&self.expr, f))
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}
impl Eq for Term {}
impl PartialOrd for Term {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Term {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.key.cmp(&other.key)
    }
}
impl std::hash::Hash for Term {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.key.hash(state)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match Unparser::default().with_pretty(true).expr_to_sql(&self.expr) {
            Ok(sql) => write!(f, "{sql}"),
            Err(_) => write!(f, "{}", self.key),
        }
    }
}

/// Rewrites `expr` so that equivalent spellings coincide: a literal goes on
/// the right of a comparison, the sides of a symmetric one in text order,
/// `x IN (a, b)` becomes `x = a OR x = b`, and the operands of `AND`/`OR`
/// are flattened and sorted.
fn canonical(expr: Expr) -> Expr {
    let rewritten = expr.transform_up(|e| {
        Ok(match e {
            Expr::Alias(a) => Transformed::yes(*a.expr),
            Expr::InList(l) if !l.negated && !l.list.is_empty() => {
                let parts = l.list.into_iter().map(|v| (*l.expr.clone()).eq(v));
                Transformed::yes(canonical_or(parts.collect()))
            }
            Expr::BinaryExpr(BinaryExpr { left, op, right }) => {
                let (l, r) = (*left, *right);
                Transformed::yes(match op {
                    Operator::And => conjunction(sorted(split(l, Operator::And).chain(split(r, Operator::And)))).unwrap(),
                    Operator::Or => canonical_or(split(l, Operator::Or).chain(split(r, Operator::Or)).collect()),
                    op => {
                        let literal = (matches!(l, Expr::Literal(..)), matches!(r, Expr::Literal(..)));
                        let swap = match op.swap() {
                            Some(_) if literal == (true, false) => true,
                            Some(s) if s == op && literal == (false, false) => l.to_string() > r.to_string(),
                            _ => false,
                        };
                        match swap {
                            true => Expr::BinaryExpr(BinaryExpr::new(Box::new(r), op.swap().unwrap(), Box::new(l))),
                            false => Expr::BinaryExpr(BinaryExpr::new(Box::new(l), op, Box::new(r))),
                        }
                    }
                })
            }
            e => Transformed::no(e),
        })
    });
    rewritten.map(|t| t.data).unwrap_or_else(|e| panic!("canonicalizing an expression cannot fail: {e}"))
}

fn split(e: Expr, op: Operator) -> Box<dyn Iterator<Item = Expr>> {
    match e {
        Expr::BinaryExpr(BinaryExpr { left, op: o, right }) if o == op => Box::new(split(*left, op).chain(split(*right, op))),
        e => Box::new(std::iter::once(e)),
    }
}

fn sorted(parts: impl Iterator<Item = Expr>) -> Vec<Expr> {
    let mut parts: Vec<(String, Expr)> = parts.map(|e| (e.to_string(), e)).collect();
    parts.sort_by(|a, b| a.0.cmp(&b.0));
    parts.dedup_by(|a, b| a.0 == b.0);
    parts.into_iter().map(|(_, e)| e).collect()
}

fn canonical_or(parts: Vec<Expr>) -> Expr {
    let parts: Vec<Expr> = parts.into_iter().flat_map(|p| split(p, Operator::Or)).collect();
    disjunction(sorted(parts.into_iter())).unwrap()
}

/// Canonical conjuncts of `exprs`.
pub fn terms(exprs: impl IntoIterator<Item = Expr>) -> BTreeSet<Term> {
    exprs.into_iter().flat_map(split_conjunction_owned).map(Term::new).collect()
}

/// A set of rows, named by how they derive from the base tables.
///
/// Contexts are built in a normal form (`facts::rewrite`), so that plans
/// computing the same rows in a different order name them the same: inner
/// joins, filters, and semi and anti joins all flatten into one
/// [`Context::Spj`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Context {
    /// The rows of the cross product of `tables` and `atoms` satisfying every
    /// predicate in `preds` and every condition in `exists`. No two inputs
    /// draw on the same instance, and no atom is itself an `Spj`.
    Spj { tables: BTreeSet<String>, atoms: BTreeSet<Context>, preds: BTreeSet<Term>, exists: BTreeSet<Exists> },
    /// Any other rows: those of operator `op` with arguments `args` over
    /// `inputs` (an outer join, a GROUP BY, ...). Precise, but specific.
    Derived { op: String, args: Vec<Term>, inputs: Vec<Context> },
}

/// A condition on each row of a context: whether it has a partner in
/// `other` under `on`. This is what a semi or anti join keeps.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Exists {
    pub kind: ExistsKind,
    pub on: BTreeSet<Term>,
    pub other: Context,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ExistsKind {
    /// Has a partner (a semi join, `EXISTS`, `IN`).
    Semi,
    /// Has none (an anti join, `NOT EXISTS`).
    Anti,
    /// `NOT IN`: has none, and `other` has no NULL to compare with.
    NotIn,
}

impl Context {
    pub fn table(table: &str) -> Context {
        Context::Spj {
            tables: [table.to_string()].into(),
            atoms: BTreeSet::new(),
            preds: BTreeSet::new(),
            exists: BTreeSet::new(),
        }
    }

    /// The rows of `self` satisfying `preds`.
    pub fn filter(&self, preds: &BTreeSet<Term>) -> Context {
        if preds.is_empty() {
            return self.clone();
        }
        let mut s = rewrite::Spj::of(self);
        s.preds.extend(preds.iter().cloned());
        s.build()
    }

    /// The cross product of two contexts over different tables, or `None`
    /// if they share one (a self-join, whose columns would be ambiguous).
    pub fn cross(&self, other: &Context) -> Option<Context> {
        if !self.tables().is_disjoint(&other.tables()) {
            return None;
        }
        let mut s = rewrite::Spj::of(self);
        s.merge(rewrite::Spj::of(other));
        Some(s.build())
    }

    /// The rows of `self` with (or, by `kind`, without) a partner in `other`
    /// under `on`.
    pub fn exists(&self, kind: ExistsKind, on: BTreeSet<Term>, other: Context) -> Context {
        let mut s = rewrite::Spj::of(self);
        s.exists.insert(rewrite::decorrelate(self, Exists { kind, on, other }));
        s.build()
    }

    /// The rows of a join other than an inner one, on `on`. A right join
    /// is named as the left join with its inputs swapped, and a full join's
    /// inputs are in order, so that each reads one way whichever side an
    /// engine built. A semi or anti join keeps its kept side's rows that
    /// pass an [`Exists`] condition, and a left join is in the normal form
    /// `rewrite::left_join` gives.
    pub fn join(kind: JoinType, on: BTreeSet<Term>, l: Context, r: Context) -> Context {
        let (kind, mut inputs) = match kind {
            JoinType::Right => (JoinType::Left, vec![r, l]),
            JoinType::RightSemi => (JoinType::LeftSemi, vec![r, l]),
            JoinType::RightAnti => (JoinType::LeftAnti, vec![r, l]),
            JoinType::RightMark => (JoinType::LeftMark, vec![r, l]),
            kind => (kind, vec![l, r]),
        };
        match kind {
            JoinType::LeftSemi | JoinType::LeftAnti => {
                let exists = if kind == JoinType::LeftSemi { ExistsKind::Semi } else { ExistsKind::Anti };
                let other = inputs.pop().unwrap();
                return inputs[0].exists(exists, on, other);
            }
            JoinType::Left => {
                let r = inputs.pop().unwrap();
                return rewrite::left_join(on, inputs.pop().unwrap(), r);
            }
            JoinType::Full => inputs.sort(),
            _ => {}
        }
        Context::Derived { op: format!("{kind} join"), args: on.into_iter().collect(), inputs }
    }

    /// The context with its table instances renamed by `f`, in normal form
    /// for its new names.
    pub fn rename(&self, f: &dyn Fn(&str) -> Option<String>) -> Context {
        let terms = |ts: &BTreeSet<Term>| ts.iter().map(|t| t.rename(f)).collect::<BTreeSet<_>>();
        match self {
            Context::Spj { tables, atoms, preds, exists } => rewrite::Spj {
                tables: tables.iter().map(|t| f(t).unwrap_or_else(|| t.clone())).collect(),
                atoms: atoms.iter().map(|a| a.rename(f)).collect(),
                preds: terms(preds),
                exists: exists
                    .iter()
                    .map(|e| Exists { kind: e.kind, on: terms(&e.on), other: e.other.rename(f) })
                    .collect(),
            }
            .build(),
            Context::Derived { op, args, inputs } => {
                let mut inputs: Vec<Context> = inputs.iter().map(|i| i.rename(f)).collect();
                // A GROUP BY's keys stay as written: what reads its rows names
                // them so.
                let args: BTreeSet<Term> = args.iter().map(|a| a.rename(f)).collect();
                if op == "Left join" {
                    let r = inputs.pop().unwrap();
                    return rewrite::left_join(args, inputs.pop().unwrap(), r);
                }
                if op == "Full join" {
                    inputs.sort();
                }
                Context::Derived { op: op.clone(), args: args.into_iter().collect(), inputs }
            }
        }
    }

    /// Every table instance the rows draw on.
    pub fn tables(&self) -> BTreeSet<String> {
        match self {
            Context::Spj { tables, atoms, exists, .. } => tables
                .iter()
                .cloned()
                .chain(atoms.iter().flat_map(Context::tables))
                .chain(exists.iter().flat_map(|e| e.other.tables()))
                .collect(),
            Context::Derived { inputs, .. } => inputs.iter().flat_map(Context::tables).collect(),
        }
    }
}

impl fmt::Display for Exists {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let kind = match self.kind {
            ExistsKind::Semi => "exists",
            ExistsKind::Anti => "not exists",
            ExistsKind::NotIn => "not in",
        };
        write!(f, "{kind}[{}]({})", join(&self.on, " and "), self.other)
    }
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Context::Spj { tables, atoms, preds, exists } => {
                let inputs: Vec<String> = tables.iter().cloned().chain(atoms.iter().map(ToString::to_string)).collect();
                write!(f, "{}", inputs.join(" × "))?;
                let conds: Vec<String> =
                    std::iter::once(join(preds, " and ")).filter(|s| !s.is_empty()).chain(exists.iter().map(ToString::to_string)).collect();
                if !conds.is_empty() {
                    write!(f, " where {}", conds.join(" and "))?;
                }
                Ok(())
            }
            Context::Derived { op, args, inputs } => {
                write!(f, "{op}")?;
                if !args.is_empty() {
                    write!(f, "[{}]", join(args, ", "))?;
                }
                write!(f, "({})", inputs.iter().map(ToString::to_string).collect::<Vec<_>>().join(", "))
            }
        }
    }
}

/// `terms` separated by `sep`, a disjunction parenthesized.
pub(crate) fn join<'a>(terms: impl IntoIterator<Item = &'a Term>, sep: &str) -> String {
    let show = |t: &Term| match &t.expr {
        Expr::BinaryExpr(BinaryExpr { op: Operator::Or, .. }) => format!("({t})"),
        _ => t.to_string(),
    };
    terms.into_iter().map(show).collect::<Vec<_>>().join(sep)
}

// Saved and read back with serde: everything but a term's expression derives
// its form. An expression goes as DataFusion's protobuf message for it, read
// back with the functions a default session knows.

static FUNCTIONS: LazyLock<Arc<TaskContext>> = LazyLock::new(|| SessionContext::new().task_ctx());

impl Serialize for Term {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        serialize_expr(&self.expr, &DefaultLogicalExtensionCodec {}).map_err(S::Error::custom)?.serialize(s)
    }
}

impl<'de> Deserialize<'de> for Term {
    /// The term as it was: its expression was canonical when written.
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Term, D::Error> {
        let node = LogicalExprNode::deserialize(d)?;
        let expr = parse_expr(&node, &FUNCTIONS, &DefaultLogicalExtensionCodec {}).map_err(D::Error::custom)?;
        Ok(Term::canonical(expr))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use datafusion::prelude::{col, lit};

    #[test]
    fn literal_goes_right() {
        assert_eq!(Term::new(lit(10).gt(col("t.a"))), Term::new(col("t.a").lt(lit(10))));
    }

    #[test]
    fn symmetric_sides_are_ordered() {
        assert_eq!(Term::new(col("t.a").eq(col("u.b"))), Term::new(col("u.b").eq(col("t.a"))));
        assert_ne!(Term::new(col("t.a").lt(col("u.b"))), Term::new(col("u.b").lt(col("t.a"))));
    }

    #[test]
    fn in_list_is_a_disjunction() {
        let a = col("t.a").in_list(vec![lit("x"), lit("y")], false);
        let b = col("t.a").eq(lit("y")).or(col("t.a").eq(lit("x")));
        assert_eq!(Term::new(a), Term::new(b));
    }

    #[test]
    fn conjunctions_are_sets() {
        let p = col("t.a").gt(lit(1));
        let q = col("t.b").lt(lit(2));
        assert_eq!(terms([p.clone().and(q.clone())]), terms([q, p.clone(), p]));
    }

    #[test]
    fn joins_read_one_way() {
        let on = terms([col("t.a").eq(col("u.b"))]);
        let (t, u) = (Context::table("t"), Context::table("u"));
        let join = |kind, l: &Context, r: &Context| Context::join(kind, on.clone(), l.clone(), r.clone());
        assert_eq!(join(JoinType::Right, &t, &u), join(JoinType::Left, &u, &t));
        assert_eq!(join(JoinType::RightSemi, &t, &u), join(JoinType::LeftSemi, &u, &t));
        assert_eq!(join(JoinType::Full, &t, &u), join(JoinType::Full, &u, &t));
        assert_ne!(join(JoinType::Left, &t, &u), join(JoinType::Left, &u, &t));
    }

    #[test]
    fn filters_commute() {
        let p = terms([col("t.a").gt(lit(1))]);
        let q = terms([col("t.b").lt(lit(2))]);
        let t = Context::table("t");
        assert_eq!(t.filter(&p).filter(&q), t.filter(&q).filter(&p));
        let u = Context::table("u");
        assert_eq!(t.filter(&p).cross(&u), u.cross(&t).map(|c| c.filter(&p)));
        assert_eq!(t.cross(&t.filter(&p)), None);
    }
}
