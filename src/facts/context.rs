//! The input distribution a fact holds for, and how it flows through a plan.
//!
//! A selectivity or distinct count is a property of the rows it is measured
//! over. Many plans produce the same rows in different ways: a filter pushed
//! into a scan or applied above a projection, joins in either order. A
//! [`Context`] names those rows canonically, so that facts from different
//! plans meet. Rows that are not a reproducible function of the data (a scan
//! cut short by a `LIMIT`, or pruned by a join's runtime filter) get no
//! context at all, so they yield no facts.

use std::collections::BTreeSet;
use std::fmt;

use datafusion::common::tree_node::{Transformed, TreeNode};
use datafusion::common::{DataFusionError, JoinType};
use datafusion::logical_expr::utils::{conjunction, disjunction, split_conjunction_owned};
use datafusion::logical_expr::{BinaryExpr, Expr, Operator};
use datafusion::sql::unparser::Unparser;
use serde::{Deserialize, Serialize};

use super::{FactKind, rewrite};
use crate::observed::{ObservedPlan, Op, Pred, base_table, column_key, qualified, relation, requalify};

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
    pub(super) fn canonical(expr: Expr) -> Term {
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
/// Contexts are built in a normal form ([`super::rewrite`]), so that plans
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
    /// [`rewrite::left_join`] gives.
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

/// Why an operator's rows have no context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Taint {
    /// Below a `LIMIT`, or the probe side of a join whose build side was
    /// empty: the engine may have stopped reading early.
    EarlyStop,
    /// Pruned by an optional or runtime filter that nothing above enforced.
    Pruned(String),
    /// A predicate, key or condition that did not resolve.
    Unresolved(String),
    /// A predicate whose value changes between runs, like `random()`.
    Volatile(String),
    /// Both sides of a join read the same rows of one table instance.
    SelfJoin,
    /// An operator without a model.
    Unsupported(String),
}

impl fmt::Display for Taint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Taint::EarlyStop => write!(f, "may have stopped early"),
            Taint::Pruned(t) => write!(f, "pruned by {t}"),
            Taint::Unresolved(t) => write!(f, "unresolved {t}"),
            Taint::Volatile(t) => write!(f, "volatile {t}"),
            Taint::SelfJoin => write!(f, "self-join"),
            Taint::Unsupported(t) => write!(f, "unsupported {t}"),
        }
    }
}

/// A filter that pruned an operator's rows and is yet to be enforced.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Pending {
    /// A runtime filter on `table.column`, from a join on it. The join's
    /// output is the same whether or not it pruned, since it only removes
    /// rows without a partner. `subset` while the rows are still among the
    /// context's: every operator since the scan keeps fewer rows for fewer
    /// input. `expr` is its predicate, if it read as one (a bloom filter's
    /// does not). `superset` while the rows still hold every row of the
    /// context satisfying it: it drops no row with a partner, and every
    /// operator since the scan keeps more rows for more input.
    Join { column: Option<String>, text: String, subset: bool, expr: Option<Term>, superset: bool },
    /// An optional filter pushed into a scan, which may have let through rows
    /// that fail it: the rows are all of the context's, and maybe more, until
    /// a filter above checks the same predicate. `None` if it did not resolve.
    Filter { term: Option<Term>, text: String },
}

impl Pending {
    fn rename(&self, f: &dyn Fn(&str) -> Option<String>) -> Pending {
        match self {
            Pending::Join { column, text, subset, expr, superset } => Pending::Join {
                column: column.as_ref().map(|c| match c.rsplit_once('.') {
                    Some((r, n)) => format!("{}.{n}", f(r).unwrap_or_else(|| r.to_string())),
                    None => c.clone(),
                }),
                text: text.clone(),
                subset: *subset,
                expr: expr.as_ref().map(|t| t.rename(f)),
                superset: *superset,
            },
            Pending::Filter { term, text } => Pending::Filter { term: term.as_ref().map(|t| t.rename(f)), text: text.clone() },
        }
    }

    /// This filter, once the rows may no longer be among the context's,
    /// nor hold all of those satisfying it.
    fn loosened(self) -> Pending {
        match self {
            Pending::Join { column, text, expr, .. } => Pending::Join { column, text, subset: false, expr, superset: false },
            p => p,
        }
    }

    /// This filter, once the rows may no longer hold every row of the
    /// context satisfying it.
    fn narrowed(self) -> Pending {
        match self {
            Pending::Join { column, text, subset, expr, .. } => Pending::Join { column, text, subset, expr, superset: false },
            p => p,
        }
    }
}

/// `pending`, once the rows may no longer be among the context's.
fn loosened(pending: BTreeSet<Pending>) -> BTreeSet<Pending> {
    pending.into_iter().map(Pending::loosened).collect()
}

/// `pending`, once the rows may no longer hold all of the context's that
/// satisfy its runtime filters.
fn narrowed(pending: BTreeSet<Pending>) -> BTreeSet<Pending> {
    pending.into_iter().map(Pending::narrowed).collect()
}

/// What an operator's rows are.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum State {
    Clean(Context),
    /// Rows of the context, once the pending filters are enforced. Until
    /// then, a pending runtime filter may have removed some of them, and a
    /// pending pushed filter may have let others through.
    Pending(Context, BTreeSet<Pending>),
    Tainted(Taint),
}

impl State {
    pub fn clean(&self) -> Option<&Context> {
        match self {
            State::Clean(c) => Some(c),
            _ => None,
        }
    }

    /// A context whose rows are among these: the rows are its, and maybe
    /// more, so `|context| <=` their count. Clean rows are exactly the
    /// context's. Pending ones hold all of the context's when every pending
    /// filter is a pushed filter that resolved, since none removed a row of
    /// it. A runtime filter may have removed some, but none that satisfy
    /// it: the rows hold those of the context satisfying every runtime
    /// filter's predicate, while each is `superset`.
    pub fn upper(&self) -> Option<Context> {
        match self {
            State::Clean(c) => Some(c.clone()),
            State::Pending(c, p) => {
                let mut runtime = BTreeSet::new();
                for p in p {
                    match p {
                        Pending::Filter { term: Some(_), .. } => {}
                        Pending::Join { expr: Some(t), superset: true, .. } => {
                            runtime.insert(t.clone());
                        }
                        _ => return None,
                    }
                }
                Some(c.filter(&runtime))
            }
            _ => None,
        }
    }

    /// A context these rows are among: `|context| >=` their count. Clean
    /// rows are exactly the context's; pending ones are a subset when every
    /// pending filter is a runtime filter, which only drops rows without a
    /// partner, and everything above it kept a subset.
    pub fn lower(&self) -> Option<&Context> {
        match self {
            State::Clean(c) => Some(c),
            State::Pending(c, p) if p.iter().all(|p| matches!(p, Pending::Join { subset: true, .. })) => Some(c),
            _ => None,
        }
    }

    fn with(ctx: Context, pending: BTreeSet<Pending>) -> State {
        match pending.is_empty() {
            true => State::Clean(ctx),
            false => State::Pending(ctx, pending),
        }
    }

    /// A state that must be clean to have a context; pending turns tainted.
    fn settle(self) -> std::result::Result<Context, Taint> {
        match self {
            State::Clean(c) => Ok(c),
            State::Pending(_, p) => Err(Taint::Pruned(p.iter().map(pending_text).collect::<Vec<_>>().join(", "))),
            State::Tainted(t) => Err(t),
        }
    }
}

fn pending_text(p: &Pending) -> String {
    match p {
        Pending::Join { text, .. } | Pending::Filter { text, .. } => text.clone(),
    }
}

/// A value computed by an aggregate, read as the column `"value"."{name}"`:
/// `aggregate` over the rows `over` (a GROUP BY's or an aggregate's), the
/// two named canonically together.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Value {
    pub name: String,
    pub aggregate: Term,
    pub over: Context,
}

/// Resolves references to values computed by aggregates (columns of
/// relation `@node`, as the reader writes them): each becomes an opaque
/// column named for the aggregate and the rows it ran over, so that it reads
/// the same in any plan.
pub(crate) struct Values<'a> {
    pub plan: &'a ObservedPlan,
    pub states: &'a [State],
    pub stopped: &'a [bool],
    /// What each operator's output may not read (see [`Hidden`]).
    pub hidden: &'a [Hidden],
}

/// Columns an operator's output holds but no context names: those of the
/// rows a first-row filter kept, beyond their partition columns, as
/// `(instances, partition)`. Which row of a partition the filter kept
/// depends on the window's order, so what reads them reads no context's
/// rows. A partition column is the group's key, unless a semi join took
/// the group out, after which it reads nothing either.
pub(crate) type Hidden = Vec<(BTreeSet<String>, Vec<Expr>)>;

/// True if `e` reads a hidden column, other than as a partition column.
fn reads_hidden(e: &Expr, hidden: &Hidden) -> bool {
    hidden.iter().any(|(instances, keys)| {
        let e = e
            .clone()
            .transform_down(|x| {
                Ok(if keys.contains(&x) { Transformed::yes(Expr::Literal(datafusion::common::ScalarValue::Null, None)) } else { Transformed::no(x) })
            })
            .map(|t| t.data)
            .unwrap_or_else(|_| e.clone());
        e.column_refs().iter().any(|c| c.relation.as_ref().is_some_and(|r| instances.contains(r.table())))
    })
}

impl Values<'_> {
    /// What the inputs of operator `at` may not read.
    fn inherited(&self, at: usize) -> Hidden {
        self.plan.nodes[at].children.iter().flat_map(|&c| self.hidden.get(c).cloned().unwrap_or_default()).collect()
    }

    fn settle(&self, at: usize, e: &Expr) -> Option<Expr> {
        // A window function's value depends on the rows it ran over, which
        // a context's predicates, in any order, do not say.
        if e.exists(|x| Ok(matches!(x, Expr::WindowFunction(_)))).unwrap_or(true) {
            return None;
        }
        if reads_hidden(e, &self.inherited(at)) {
            return None;
        }
        e.clone()
            .transform_up(|e| match e {
                Expr::Column(c) if relation(&c).is_some_and(|r| r.starts_with('@')) => {
                    let k: usize = relation(&c).unwrap()[1..].parse().map_err(|_| unresolved(&c.name))?;
                    let name = self.value(k, &c.name).ok_or_else(|| unresolved(&c.name))?;
                    Ok(Transformed::yes(qualified("value", &name)))
                }
                e => Ok(Transformed::no(e)),
            })
            .ok()
            .map(|t| t.data)
    }

    /// `{aggregate} of {rows}` for output column `name` of aggregate `k`.
    fn value(&self, k: usize, name: &str) -> Option<String> {
        self.definition(k, name).map(|d| d.name)
    }

    /// The value output as column `name` of aggregate `k`: its name, and the
    /// aggregate and the rows it ran over, named canonically together.
    fn definition(&self, k: usize, name: &str) -> Option<Value> {
        let node = &self.plan.nodes[k];
        let Op::Aggregate { keys, values } = &node.op else { return None };
        let i = node.columns.iter().position(|c| c.name == name)?.checked_sub(keys.len())?;
        // A value may be computed from another (`first(avg(x))`).
        let value = self.settle(k, values.get(i)?.as_ref()?)?;
        let over = self.states.get(k)?.clean().filter(|_| !self.stopped[k])?.clone();
        let FactKind::Distinct { keys, over } = (FactKind::Distinct { keys: [Term::new(value)].into(), over }).canonical()
        else {
            unreachable!()
        };
        let aggregate = keys.into_iter().next().unwrap();
        Some(Value { name: format!("{aggregate} of {over}"), aggregate, over })
    }

    /// Every value an aggregate of the plan outputs.
    pub(crate) fn definitions(&self) -> Vec<Value> {
        let mut out = vec![];
        for (k, node) in self.plan.nodes.iter().enumerate() {
            if let Op::Aggregate { .. } = node.op {
                out.extend(node.columns.iter().filter_map(|c| self.definition(k, &c.name)));
            }
        }
        out
    }

    /// Resolved, deterministic predicates, or why not.
    pub(crate) fn resolve(&self, at: usize, preds: &[Pred]) -> std::result::Result<BTreeSet<Term>, Taint> {
        let mut exprs = vec![];
        for p in preds {
            match p.expr.as_ref().map(|e| self.settle(at, e)) {
                None | Some(None) => return Err(Taint::Unresolved(p.text.clone())),
                Some(Some(e)) if e.is_volatile() => return Err(Taint::Volatile(p.text.clone())),
                Some(Some(e)) => exprs.push(e),
            }
        }
        Ok(terms(exprs))
    }

    /// Resolved grouping keys, or `None`.
    pub(crate) fn keys(&self, at: usize, keys: &[Option<Expr>]) -> Option<BTreeSet<Term>> {
        keys.iter().map(|k| k.as_ref().and_then(|k| self.settle(at, k)).map(Term::new)).collect()
    }
}

fn unresolved(name: &str) -> DataFusionError {
    DataFusionError::Plan(format!("unresolved value {name}"))
}

/// Operators that may not have run to completion: below a `LIMIT`, the
/// probe side of a join that output nothing, and a scan that says it was
/// cut short.
pub(crate) fn stopped(plan: &ObservedPlan) -> Vec<bool> {
    let mut stopped = vec![false; plan.nodes.len()];
    for i in (0..plan.nodes.len()).rev() {
        let node = &plan.nodes[i];
        let stops = match &node.op {
            Op::Limit { .. } => node.children.clone(),
            // A join that keeps only matched probe rows and output none may
            // have stopped probing: its build side was empty, or had no key
            // that could match (all NULL).
            Op::Join { kind, .. } if (empty(&plan.nodes[node.children[1]]) || empty(node)) && !preserves_probe(*kind) => {
                vec![node.children[0]]
            }
            _ => vec![],
        };
        stopped[i] |= node.cut_short;
        // A reused result was materialized in full before it was read, and
        // a blocking operator read all of its input: a read cut short leaves
        // it whole.
        if matches!(node.op, Op::Reuse { .. }) || node.blocking {
            continue;
        }
        for c in node.children.iter().copied() {
            stopped[c] |= stopped[i] || stops.contains(&c);
        }
    }
    stopped
}

/// Whether `node` was counted, and output nothing.
fn empty(node: &crate::observed::ONode) -> bool {
    node.counted && node.rows == 0
}

/// The state of every operator of `plan`, by index.
pub fn states(plan: &ObservedPlan) -> Vec<State> {
    states_hidden(plan).0
}

/// The state of every operator of `plan`, and what its output may not read
/// (see [`Hidden`]), by index.
pub(crate) fn states_hidden(plan: &ObservedPlan) -> (Vec<State>, Vec<Hidden>) {
    // The columns joined on above each operator. A runtime filter on a
    // column may come from any join on it, so only the highest enforces it.
    let mut above = vec![BTreeSet::<String>::new(); plan.nodes.len()];
    for i in (0..plan.nodes.len()).rev() {
        let mut keys = above[i].clone();
        if let Op::Join { on, .. } = &plan.nodes[i].op {
            keys.extend(join_keys(on));
        }
        for &c in &plan.nodes[i].children {
            above[c].extend(keys.iter().cloned());
        }
    }
    let stopped = stopped(plan);
    let mut states: Vec<State> = vec![];
    let mut hidden: Vec<Hidden> = vec![];
    // The partition of each operator's first rows, where its rows are a
    // first-row filter's.
    let mut first: Vec<Option<Vec<Expr>>> = vec![];
    for (i, above) in above.iter().enumerate() {
        let node = &plan.nodes[i];
        let inputs: Vec<State> = node.children.iter().map(|&c| states[c].clone()).collect();
        let values = Values { plan, states: &states, stopped: &stopped, hidden: &hidden };
        let mut h: Hidden = node.children.iter().flat_map(|&c| hidden[c].clone()).collect();
        let mut f = None;
        let s = if let Some((keys, true)) = first_rows(plan, i, &values) {
            // The same filter again, over its own rows: all of them.
            f = Some(keys);
            inputs[0].clone()
        } else if let Some((keys, false)) = first_rows(plan, i, &values) {
            // As many rows as a GROUP BY on the partition, and only its
            // partition columns name anything of them.
            let s = match inputs[0].clone().settle() {
                Ok(c) => {
                    h.push((c.tables(), keys.clone()));
                    let args = keys.iter().cloned().map(Term::new).collect::<BTreeSet<_>>();
                    State::Clean(Context::Derived { op: "group".into(), args: args.into_iter().collect(), inputs: vec![c] })
                }
                Err(t) => State::Tainted(t),
            };
            f = Some(keys);
            s
        } else {
            let mut s = state(plan, i, &inputs, above, &values, &stopped);
            match &node.op {
                Op::Project | Op::Sort | Op::Window => f = first[node.children[0]].clone(),
                // On exactly the partition of a side's first rows: a semi
                // join with the window's input. The partition columns then
                // name nothing either.
                Op::Join { kind: JoinType::Inner, on } => {
                    let side = (0..2).find(|&k| first[node.children[k]].as_ref().is_some_and(|p| on_partition(on, p)));
                    if let (Some(k), State::Clean(_) | State::Pending(..)) = (side, &s)
                        && let Ok(on_terms) = values.resolve(i, on)
                    {
                        let (l, _) = parts(&inputs[0]);
                        let (r, _) = parts(&inputs[1]);
                        let kind = if k == 1 { JoinType::LeftSemi } else { JoinType::RightSemi };
                        let ctx = Context::join(kind, on_terms, l, r);
                        s = match s {
                            State::Pending(_, p) => State::Pending(ctx, p),
                            _ => State::Clean(ctx),
                        };
                        let keys = first[node.children[k]].clone().unwrap();
                        for (_, ks) in h.iter_mut().filter(|(_, ks)| *ks == keys) {
                            ks.clear();
                        }
                    }
                }
                _ => {}
            }
            s
        };
        states.push(s);
        hidden.push(h);
        first.push(f);
    }
    // Rows that may be short are no context's, though what is computed from
    // them may still be (a join with an empty side is empty).
    for (s, stop) in states.iter_mut().zip(stopped) {
        if stop {
            *s = State::Tainted(Taint::EarlyStop);
        }
    }
    (states, hidden)
}

/// The partition of operator `i`'s `row_number()`, if it is a filter on
/// only `rn = 1` (or `rn <= 1`) of one computed over its input's rows: only
/// projections, sorts and windows, which keep every row, are in between.
/// And whether the same filter is in between too (PostgreSQL stops a window
/// at `rn <= 1`, and checks `rn = 1` above it): then its input's rows are
/// already the first ones.
fn first_rows(plan: &ObservedPlan, i: usize, values: &Values) -> Option<(Vec<Expr>, bool)> {
    let node = &plan.nodes[i];
    let Op::Filter { predicate } = &node.op else { return None };
    let w = first_row_test(predicate)?;
    let Expr::WindowFunction(f) = w else { return None };
    if f.fun.name() != "row_number" || f.params.filter.is_some() || f.params.partition_by.is_empty() {
        return None;
    }
    if !f.params.partition_by.iter().all(|p| matches!(p, Expr::Column(_))) {
        return None;
    }
    let mut c = *node.children.first()?;
    let mut again = false;
    loop {
        let n = &plan.nodes[c];
        match &n.op {
            Op::Window if n.columns.iter().any(|col| matches!(&col.lineage, crate::observed::Lineage::Exact(e) if e == w)) => break,
            Op::Window | Op::Project | Op::Sort => c = *n.children.first()?,
            Op::Filter { predicate } if first_row_test(predicate) == Some(w) => {
                again = true;
                c = *n.children.first()?;
            }
            _ => return None,
        }
    }
    let keys = f.params.partition_by.clone();
    keys.iter().all(|k| values.settle(i, k).as_ref() == Some(k)).then_some((keys, again))
}

/// The window function `predicate` tests, if it is only `w = 1` or `w <= 1`.
fn first_row_test(predicate: &[Pred]) -> Option<&Expr> {
    let [p] = predicate else { return None };
    let Some(Expr::BinaryExpr(BinaryExpr { left, op, right })) = &p.expr else { return None };
    let one = |e: &Expr| {
        matches!(e, Expr::Literal(v, _) if v.cast_to(&datafusion::arrow::datatypes::DataType::Int64).is_ok_and(|v| v == datafusion::common::ScalarValue::Int64(Some(1))))
    };
    match (op, left.as_ref(), right.as_ref()) {
        (Operator::Eq | Operator::LtEq, w @ Expr::WindowFunction(_), l) if one(l) => Some(w),
        (Operator::Eq | Operator::GtEq, l, w @ Expr::WindowFunction(_)) if one(l) => Some(w),
        _ => None,
    }
}

/// True if `on` is equalities of exactly the columns `partition` (of one
/// side) with columns of the other.
fn on_partition(on: &[Pred], partition: &[Expr]) -> bool {
    let mut seen = vec![];
    for p in on {
        let Some(Expr::BinaryExpr(BinaryExpr { left, op: Operator::Eq, right })) = &p.expr else { return false };
        match (partition.contains(left), partition.contains(right)) {
            (true, false) => seen.push(left.as_ref().clone()),
            (false, true) => seen.push(right.as_ref().clone()),
            _ => return false,
        }
    }
    !on.is_empty() && partition.iter().all(|k| seen.contains(k))
}

/// Join kinds whose output includes probe-side rows without a match.
fn preserves_probe(kind: JoinType) -> bool {
    matches!(kind, JoinType::Left | JoinType::Full | JoinType::LeftAnti | JoinType::LeftMark)
}

fn state(
    plan: &ObservedPlan,
    i: usize,
    inputs: &[State],
    above: &BTreeSet<String>,
    values: &Values,
    stopped: &[bool],
) -> State {
    let node = &plan.nodes[i];
    match &node.op {
        Op::Scan { instance, filters, runtime_filters, .. } => {
            // A required filter pushed into a scan is applied exactly: the
            // engine checks it nowhere else. An optional one may only prune
            // (skip blocks whose statistics rule it out), so the rows are the
            // context's and maybe more, until a filter above checks the same
            // predicate. It is in the context too, so that the rows are a
            // superset of the context's whether or not it was applied.
            let (optional, required): (Vec<Pred>, Vec<Pred>) = filters.iter().cloned().partition(|p| p.optional);
            let mut preds = match values.resolve(i, &required) {
                Ok(p) => p,
                Err(t) => return State::Tainted(t),
            };
            // DuckDB 1.5.0 pushes a bloom filter before it is filled, so it
            // may drop rows with a partner: beside one, no runtime filter
            // keeps every row satisfying it.
            let superset = runtime_filters.iter().all(|r| r.expr.is_some());
            let mut pending: BTreeSet<Pending> = runtime_filters
                .iter()
                .map(|r| {
                    let expr = r.expr.as_ref().and_then(|e| values.settle(i, e)).map(Term::new);
                    let superset = superset && expr.is_some();
                    Pending::Join { column: r.column.clone(), text: r.text.clone(), subset: true, expr, superset }
                })
                .collect();
            for p in optional {
                let term = p.expr.map(Term::new);
                preds.extend(term.clone());
                pending.insert(Pending::Filter { term, text: p.text });
            }
            State::with(Context::table(instance).filter(&preds), pending)
        }
        Op::Project | Op::Sort => inputs[0].clone(),
        // A window's values are computed over the rows it reads: over pruned
        // rows, they are no values of the context's rows.
        Op::Window => match inputs[0].clone() {
            State::Pending(c, p) => State::Pending(c, loosened(p)),
            s => s,
        },
        Op::Reuse { suffix, checked } => {
            let of = node.children[0];
            let (read, whole) = (node, &plan.nodes[of]);
            if stopped[of] || (*checked && read.counted && whole.counted && whole.rows != read.rows) {
                return State::Tainted(Taint::Unsupported(format!("{} of a short input", node.engine_op)));
            }
            let f = |r: &str| base_table(r).map(|_| format!("{r}{suffix}"));
            match &inputs[0] {
                State::Clean(c) => State::Clean(c.rename(&f)),
                State::Pending(c, p) => State::Pending(c.rename(&f), p.iter().map(|p| p.rename(&f)).collect()),
                State::Tainted(t) => State::Tainted(t.clone()),
            }
        }
        Op::Filter { predicate } => {
            let preds = match values.resolve(i, predicate) {
                Ok(p) => p,
                Err(t) => return State::Tainted(t),
            };
            match inputs[0].clone() {
                State::Tainted(t) => State::Tainted(t),
                State::Clean(c) => State::Clean(c.filter(&preds)),
                State::Pending(c, mut pending) => {
                    pending.retain(|p| !matches!(p, Pending::Filter { term: Some(t), .. } if preds.contains(t)));
                    State::with(c.filter(&preds), pending)
                }
            }
        }
        // IN and EXISTS keep the rows of a semi join. NOT IN's null
        // semantics have no other name here.
        Op::MarkFilter { negated } => {
            let (c, pending) = match &inputs[0] {
                State::Tainted(t) => return State::Tainted(t.clone()),
                s => parts(s),
            };
            match c {
                Context::Derived { op, args, mut inputs } if op == "LeftMark join" => {
                    let kind = if *negated { ExistsKind::NotIn } else { ExistsKind::Semi };
                    // NOT IN keeps the rows that pruning would have dropped.
                    let pending = if *negated { loosened(pending) } else { pending };
                    let other = inputs.pop().unwrap();
                    State::with(inputs[0].exists(kind, args.into_iter().collect(), other), pending)
                }
                _ => State::Tainted(Taint::Unsupported(node.engine_op.clone())),
            }
        }
        Op::Join { kind, on } => {
            let on_terms = match values.resolve(i, on) {
                Ok(p) => p,
                Err(t) => return State::Tainted(t),
            };
            let (l, lp, r, rp) = match (&inputs[0], &inputs[1]) {
                (State::Tainted(t), _) | (_, State::Tainted(t)) => return State::Tainted(t.clone()),
                (a, b) => {
                    let (l, lp) = parts(a);
                    let (r, rp) = parts(b);
                    (l, lp, r, rp)
                }
            };
            if !l.tables().is_disjoint(&r.tables()) {
                return State::Tainted(Taint::SelfJoin);
            }
            // Extra rows on a side give extra rows out only where the join
            // keeps more for more input: not on the other side of an anti
            // join, nor the padded side of an outer join, whose rows decide
            // which rows are padded.
            let (l_more, r_more) = match kind {
                JoinType::Inner | JoinType::LeftSemi | JoinType::RightSemi => (true, true),
                JoinType::LeftAnti | JoinType::Left => (true, false),
                JoinType::RightAnti | JoinType::Right => (false, true),
                _ => (false, false),
            };
            let loose = |p: &BTreeSet<Pending>| p.iter().any(|p| matches!(p, Pending::Filter { .. }));
            if (!l_more && loose(&lp)) || (!r_more && loose(&rp)) {
                let pending = if !l_more && loose(&lp) { &lp } else { &rp };
                return State::Tainted(Taint::Pruned(pending.iter().map(pending_text).collect::<Vec<_>>().join(", ")));
            }
            // Fewer rows on a side give a subset of the rows out only where
            // the join keeps fewer for fewer input: not on the padded side of
            // an outer join, where pruning adds padded rows, nor the other
            // side of an anti or mark join.
            let (l_sub, r_sub) = match kind {
                JoinType::Inner | JoinType::LeftSemi | JoinType::RightSemi => (true, true),
                JoinType::Left | JoinType::LeftAnti | JoinType::LeftMark => (true, false),
                JoinType::Right | JoinType::RightAnti | JoinType::RightMark => (false, true),
                JoinType::Full => (false, false),
            };
            let (lp, rp) = (if l_sub { lp } else { loosened(lp) }, if r_sub { rp } else { loosened(rp) });
            let (lp, rp) = (if l_more { lp } else { narrowed(lp) }, if r_more { rp } else { narrowed(rp) });
            // The join enforces the runtime filters on its keys, where the
            // rows it prunes are ones it would drop anyway.
            let mut pending: BTreeSet<Pending> = lp.union(&rp).cloned().collect();
            if matches!(kind, JoinType::Inner | JoinType::Right | JoinType::LeftSemi | JoinType::RightSemi | JoinType::RightAnti) {
                let keys = join_keys(on);
                pending.retain(|p| {
                    !matches!(p, Pending::Join { column: Some(c), .. } if keys.contains(c) && !above.contains(c))
                });
            }
            let ctx = match kind {
                JoinType::Inner => l.cross(&r).unwrap().filter(&on_terms),
                kind => Context::join(*kind, on_terms, l, r),
            };
            State::with(ctx, pending)
        }
        Op::Aggregate { keys, .. } => {
            let input = match inputs[0].clone().settle() {
                Ok(c) => c,
                Err(t) => return State::Tainted(t),
            };
            let Some(keys) = values.keys(i, keys) else {
                return State::Tainted(Taint::Unresolved("grouping key".into()));
            };
            // A GROUP BY and a DISTINCT on the same keys give as many rows,
            // whatever the aggregates.
            let op = if keys.is_empty() { "aggregate" } else { "group" };
            State::Clean(Context::Derived { op: op.into(), args: keys.into_iter().collect(), inputs: vec![input] })
        }
        Op::TopN { fetch, offset } => match inputs[0].clone().settle() {
            Ok(c) => State::Clean(Context::Derived {
                op: match offset {
                    0 => format!("top {fetch}"),
                    k => format!("top {fetch} offset {k}"),
                },
                args: vec![],
                inputs: vec![c],
            }),
            Err(t) => State::Tainted(t),
        },
        Op::Union => {
            let mut ctxs = vec![];
            for s in inputs {
                match s.clone().settle() {
                    Ok(c) => ctxs.push(c),
                    Err(t) => return State::Tainted(t),
                }
            }
            State::Clean(Context::Derived { op: "union".into(), args: vec![], inputs: ctxs })
        }
        Op::Limit { .. } => State::Tainted(Taint::EarlyStop),
        Op::Other => State::Tainted(Taint::Unsupported(node.engine_op.clone())),
    }
}

pub(super) fn join_keys(on: &[Pred]) -> BTreeSet<String> {
    on.iter()
        .filter_map(|p| p.expr.as_ref())
        .flat_map(|e| e.column_refs().into_iter().map(column_key).collect::<Vec<_>>())
        .collect()
}

fn parts(s: &State) -> (Context, BTreeSet<Pending>) {
    match s {
        State::Clean(c) => (c.clone(), BTreeSet::new()),
        State::Pending(c, p) => (c.clone(), p.clone()),
        State::Tainted(_) => unreachable!(),
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
