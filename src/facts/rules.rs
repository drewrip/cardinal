//! Rules reading facts off one operator of an executed plan.
//!
//! Each rule looks at an operator, its rows and its inputs' rows, and the
//! [`State`]s of all three, and emits the facts the counts establish. Rules
//! only read clean states: a count that may be short says nothing. An
//! operator whose rows an engine did not count still has the rows its state
//! says: its facts are named, without a value, for a query to count.

use datafusion::arrow::datatypes::DataType;
use datafusion::common::JoinType;
use datafusion::logical_expr::{BinaryExpr, Expr, Operator};

use super::context::{Context, State, Value, Values, join_keys, states_hidden, stopped};
use super::{Fact, FactKind, Origin, Ratio};
use crate::observed::{ObservedPlan, Op, column_key};

pub trait FactRule: Sync {
    fn name(&self) -> &'static str;
    /// The facts operator `node` shows: each with its value, or without
    /// where the operator has the fact's rows and they were not counted.
    fn apply(&self, obs: &Observation, node: usize, out: &mut Vec<(FactKind, Option<Ratio>)>);
}

pub static RULES: &[&dyn FactRule] = &[&Cardinality, &FilterSelectivity, &JoinSelectivity, &DistinctCount];

/// An executed plan, with every operator's state.
pub struct Observation<'a> {
    pub plan: &'a ObservedPlan,
    pub states: &'a [State],
    values: Values<'a>,
}

/// What the rules read off a plan, canonically named.
pub(crate) struct Observed {
    pub facts: Vec<Fact>,
    /// Upper bounds.
    pub bounds: Vec<Fact>,
    /// Lower bounds.
    pub floors: Vec<Fact>,
    /// The facts of operators whose rows were not counted: all of them,
    /// for a plan that was not run.
    pub unobserved: Vec<FactKind>,
    /// The definition of every value they may read.
    pub values: Vec<Value>,
}

pub(crate) fn observe(plan: &ObservedPlan) -> Observed {
    let (states, hidden) = states_hidden(plan);
    let stopped = stopped(plan);
    let obs = Observation { plan, states: &states, values: Values { plan, states: &states, stopped: &stopped, hidden: &hidden } };
    let mut facts = vec![];
    let mut bounds = vec![];
    let mut floors = vec![];
    let mut unobserved = vec![];
    let fact = |kind: FactKind, value, node, rule: &'static str| Fact {
        kind: kind.canonical(),
        value,
        origins: vec![Origin::Observed { query: plan.name.clone(), node, rule: rule.into() }],
    };
    let mut parents = vec![vec![]; plan.nodes.len()];
    for (i, n) in plan.nodes.iter().enumerate() {
        for &c in &n.children {
            parents[c].push(i);
        }
    }
    for node in 0..plan.nodes.len() {
        for rule in RULES {
            let mut out = vec![];
            rule.apply(&obs, node, &mut out);
            for (kind, value) in out {
                match value {
                    Some(value) => facts.push(fact(kind, value, node, rule.name())),
                    None => unobserved.push(kind.canonical()),
                }
            }
        }
        bounds.extend(upper_bound(&obs, node).map(|(kind, value)| fact(kind, value, node, "upper bound")));
        floors.extend(lower_bound(&obs, node).map(|(kind, value)| fact(kind, value, node, "lower bound")));
        for (kind, value, floor) in build_distinct(&obs, &parents, node) {
            let f = fact(kind, value, node, "build keys");
            if floor { floors.push(f) } else { bounds.push(f) }
        }
    }
    Observed { facts, bounds, floors, unobserved, values: obs.values.definitions() }
}

/// The rows operator `node` output, if they were counted.
fn rows(obs: &Observation, node: usize) -> Option<u64> {
    let n = &obs.plan.nodes[node];
    (obs.plan.counted && n.counted).then_some(n.rows)
}

/// `|ctx| <= rows` for an operator whose rows may include more than its
/// context's: those of a scan with a filter pushed into it, and of what
/// keeps all of them above. For a GROUP BY over such rows, its keys'
/// distinct values over them are at most its rows.
fn upper_bound(obs: &Observation, node: usize) -> Option<(FactKind, Ratio)> {
    let n = &obs.plan.nodes[node];
    let out = rows(obs, node)?;
    if let State::Pending(..) = obs.states[node] {
        let ctx = obs.states[node].upper()?;
        return Some((FactKind::Cardinality(ctx), Ratio::int(out)));
    }
    let Op::Aggregate { keys, .. } = &n.op else { return None };
    let input = &obs.states[n.children[0]];
    let (State::Pending(..), Some(over)) = (input, input.upper()) else { return None };
    let keys = obs.values.keys(node, keys).filter(|k| !k.is_empty())?;
    Some((FactKind::Distinct { keys, over }, Ratio::int(out)))
}

/// `|ctx| >= rows` for an operator whose rows may be fewer than its
/// context's: pruned by runtime filters, which only drop rows without a
/// partner, and kept a subset by everything above them.
fn lower_bound(obs: &Observation, node: usize) -> Option<(FactKind, Ratio)> {
    let out = rows(obs, node)?;
    let State::Pending(..) = obs.states[node] else { return None };
    let ctx = obs.states[node].lower()?;
    Some((FactKind::Cardinality(ctx.clone()), Ratio::int(out)))
}

/// The distinct keys of a join's build side, read off the runtime filters
/// it pushed into scan `node` on its probe side, as bounds (`false`) and
/// floors (`true`). The filters are built from every non-NULL build key: an
/// IN list holds each of them, `=k` the only one, and a range spans them.
/// So `ndv(y | build)` is at least an IN list's length, and at most one more
/// (NULL), or two more than an integer range's width. Only where one join
/// can have built them: the only join on the column above the scan, which
/// has it on its probe side, equal to a column of its build side.
fn build_distinct(obs: &Observation, parents: &[Vec<usize>], node: usize) -> Vec<(FactKind, Ratio, bool)> {
    let Op::Scan { runtime_filters, .. } = &obs.plan.nodes[node].op else { return vec![] };
    let mut out = vec![];
    let columns: std::collections::BTreeSet<&String> = runtime_filters.iter().filter_map(|r| r.column.as_ref()).collect();
    for column in columns {
        // The joins on the column above the scan, and whether the scan is on
        // each one's probe side. Above an operator read twice, any could be.
        let (mut at, mut joins) = (node, vec![]);
        let whole = loop {
            match &parents[at][..] {
                [] => break true,
                [p] => {
                    if let Op::Join { on, .. } = &obs.plan.nodes[*p].op
                        && join_keys(on).contains(column)
                    {
                        joins.push((*p, obs.plan.nodes[*p].children[0] == at));
                    }
                    at = *p;
                }
                _ => break false,
            }
        };
        let (true, [(j, true)]) = (whole, &joins[..]) else { continue };
        let Op::Join { kind: JoinType::Inner | JoinType::LeftSemi | JoinType::Right, on } = &obs.plan.nodes[*j].op else { continue };
        let Some(build) = obs.states[obs.plan.nodes[*j].children[1]].clean() else { continue };
        // The build side's column equal to this one, in the only condition
        // on it: another (`x < z`) pushes a filter of its own.
        let reads = |p: &crate::observed::Pred| p.expr.as_ref().is_some_and(|e| e.column_refs().iter().any(|c| column_key(c) == *column));
        if on.iter().filter(|p| reads(p)).count() != 1 {
            continue;
        }
        let key = on.iter().find_map(|p| match &p.expr {
            Some(Expr::BinaryExpr(BinaryExpr { left, op: Operator::Eq, right })) => match (left.as_ref(), right.as_ref()) {
                (Expr::Column(a), b @ Expr::Column(_)) if column_key(a) == *column => Some(b.clone()),
                (a @ Expr::Column(_), Expr::Column(b)) if column_key(b) == *column => Some(a.clone()),
                _ => None,
            },
            _ => None,
        });
        let Some(keys) = key.and_then(|k| obs.values.keys(*j, &[Some(k)])) else { continue };
        let (mut listed, mut lo, mut hi) = (None, None, None);
        for r in runtime_filters.iter().filter(|r| r.column.as_ref() == Some(column)) {
            match &r.expr {
                Some(Expr::InList(l)) if !l.negated && l.list.iter().all(|v| matches!(v, Expr::Literal(..))) => listed = Some(l.list.len() as u64),
                Some(Expr::BinaryExpr(BinaryExpr { op: Operator::Eq, right, .. })) if matches!(right.as_ref(), Expr::Literal(..)) => listed = Some(1),
                Some(Expr::BinaryExpr(BinaryExpr { op: Operator::GtEq, right, .. })) => lo = integer(right),
                Some(Expr::BinaryExpr(BinaryExpr { op: Operator::LtEq, right, .. })) => hi = integer(right),
                _ => {}
            }
        }
        let kind = FactKind::Distinct { keys, over: build.clone() };
        if let Some(n) = listed {
            if n > 1 {
                out.push((kind.clone(), Ratio::int(n), true));
            }
            out.push((kind, Ratio::int(n + 1), false));
        } else if let (Some(a), Some(b)) = (lo, hi)
            && a <= b
            && let Ok(width) = u64::try_from(b as i128 - a as i128 + 2)
        {
            out.push((kind, Ratio::int(width), false));
        }
    }
    out
}

/// The value of an integer literal.
fn integer(e: &Expr) -> Option<i64> {
    let Expr::Literal(v, _) = e else { return None };
    if !v.data_type().is_integer() {
        return None;
    }
    match v.cast_to(&DataType::Int64).ok()? {
        datafusion::common::ScalarValue::Int64(n) => n,
        _ => None,
    }
}

/// An input's clean context, and its rows, if they were counted.
type Input<'s> = (&'s Context, Option<u64>);

/// The clean contexts of `node` and of its inputs.
fn clean<'s>(obs: &Observation<'s>, node: usize) -> Option<(&'s Context, Vec<Input<'s>>)> {
    let out = obs.states[node].clean()?;
    let inputs = obs.plan.nodes[node].children.iter().map(|&c| Some((obs.states[c].clean()?, rows(obs, c)))).collect::<Option<Vec<_>>>()?;
    Some((out, inputs))
}

/// `num / den`, of counts: `None` if either was not counted, and no fact
/// at all of a share of no rows.
fn share(num: Option<u64>, den: Option<u64>) -> Option<Option<Ratio>> {
    match (num, den) {
        (Some(num), Some(den)) => Ratio::new(num, den).map(Some),
        (_, Some(0)) => None,
        _ => Some(None),
    }
}

/// `|ctx| = rows` for any operator whose rows have a context: base-table
/// sizes from unfiltered scans, filtered sizes from scans with pushed-down
/// predicates, and the sizes of joins. A GROUP BY's rows are its keys'
/// distinct values over its input, as a filter on its keys above it reads
/// once it goes below ([`DistinctCount`] reads the GROUP BY itself).
pub struct Cardinality;

impl FactRule for Cardinality {
    fn name(&self) -> &'static str {
        "cardinality"
    }

    fn apply(&self, obs: &Observation, node: usize, out: &mut Vec<(FactKind, Option<Ratio>)>) {
        let rows = rows(obs, node).map(Ratio::int);
        match obs.states[node].clean() {
            Some(Context::Derived { op, args, inputs }) if op == "group" => {
                let keys = args.iter().cloned().collect();
                out.push((FactKind::Distinct { keys, over: inputs[0].clone() }, rows));
            }
            Some(Context::Derived { op, .. }) if op == "aggregate" => {}
            Some(ctx) => out.push((FactKind::Cardinality(ctx.clone()), rows)),
            None => {}
        }
    }
}

/// `s(p | input) = rows / input rows` for a filter on `p`. Conjuncts the
/// input already satisfies (DuckDB re-checks some) are left out.
pub struct FilterSelectivity;

impl FactRule for FilterSelectivity {
    fn name(&self) -> &'static str {
        "filter selectivity"
    }

    fn apply(&self, obs: &Observation, node: usize, out: &mut Vec<(FactKind, Option<Ratio>)>) {
        let n = &obs.plan.nodes[node];
        let (Op::Filter { predicate }, Some((_, inputs))) = (&n.op, clean(obs, node)) else { return };
        let (input, before) = inputs[0];
        let Ok(mut pred) = obs.values.resolve(node, predicate) else { return };
        if let Context::Spj { preds, .. } = input {
            pred.retain(|p| !preds.contains(p));
        }
        if let (false, Some(s)) = (pred.is_empty(), share(rows(obs, node), before)) {
            out.push((FactKind::Selectivity { pred, over: input.clone() }, s));
        }
    }
}

/// For an inner join, `s(on | left × right) = rows / (left rows · right
/// rows)`. For a semi or anti join, the share `m` of the kept side's rows
/// with a partner.
pub struct JoinSelectivity;

impl FactRule for JoinSelectivity {
    fn name(&self) -> &'static str {
        "join selectivity"
    }

    fn apply(&self, obs: &Observation, node: usize, out: &mut Vec<(FactKind, Option<Ratio>)>) {
        let n = &obs.plan.nodes[node];
        let (Op::Join { kind, on }, Some((_, inputs))) = (&n.op, clean(obs, node)) else { return };
        let Ok(on) = obs.values.resolve(node, on) else { return };
        let [(l, lr), (r, rr)] = inputs[..] else { return };
        let joined = rows(obs, node);
        let fact = match kind {
            JoinType::Inner if !on.is_empty() => {
                // An inner join on a side's first rows keeps the rows of a
                // semi join (see `context::states`): the other side's share
                // with a partner, too.
                let this = obs.states[node].clean();
                let semi = [(JoinType::LeftSemi, l, r, lr), (JoinType::RightSemi, r, l, rr)].into_iter().find_map(|(k, kept, other, rows)| {
                    (this == Some(&Context::join(k, on.clone(), l.clone(), r.clone()))).then_some((kept, other, rows))
                });
                if let Some((kept, other, rows)) = semi {
                    out.extend(share(joined, rows).map(|m| (FactKind::Match { on: on.clone(), kept: kept.clone(), other: other.clone() }, m)));
                }
                l.cross(r).and_then(|over| {
                    let pairs = match lr.zip(rr) {
                        Some((lr, rr)) => Some(lr.checked_mul(rr)?),
                        None => None,
                    };
                    Some((FactKind::Selectivity { pred: on, over }, share(joined, pairs)?))
                })
            }
            JoinType::LeftSemi | JoinType::LeftAnti | JoinType::RightSemi | JoinType::RightAnti => {
                let left = matches!(kind, JoinType::LeftSemi | JoinType::LeftAnti);
                let (kept, other, rows) = if left { (l, r, lr) } else { (r, l, rr) };
                let matched = match kind {
                    JoinType::LeftSemi | JoinType::RightSemi => joined,
                    _ => rows.zip(joined).map(|(rows, joined)| rows.saturating_sub(joined)),
                };
                share(matched, rows).map(|m| (FactKind::Match { on, kept: kept.clone(), other: other.clone() }, m))
            }
            _ => None,
        };
        out.extend(fact);
    }
}

/// `ndv(keys | input) = rows` for a GROUP BY or DISTINCT.
pub struct DistinctCount;

impl FactRule for DistinctCount {
    fn name(&self) -> &'static str {
        "distinct count"
    }

    fn apply(&self, obs: &Observation, node: usize, out: &mut Vec<(FactKind, Option<Ratio>)>) {
        let n = &obs.plan.nodes[node];
        // Only its own rows are read: its input's need not have been counted.
        let Op::Aggregate { keys, .. } = &n.op else { return };
        let (Some(_), Some(input)) = (obs.states[node].clean(), obs.states[n.children[0]].clean()) else { return };
        let Some(keys) = obs.values.keys(node, keys) else { return };
        if !keys.is_empty() {
            out.push((FactKind::Distinct { keys, over: input.clone() }, rows(obs, node).map(Ratio::int)));
        }
    }
}
