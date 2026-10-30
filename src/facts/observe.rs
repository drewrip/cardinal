//! Reading facts off the operators of an executed plan.
//!
//! Stage 1 of the [pipeline](super#pipeline); notation as in
//! [the module](super#notation).
//!
//! # Spec
//!
//! - **Input**: one [`ObservedPlan`], each operator's [`State`]
//!   ([`super::states`]), and whether the engine counted its rows.
//! - **Output**: per operator, canonical facts, bounds and floors, each
//!   with [`Origin::Observed`] naming the plan,
//!   operator and rule. Where an exact rule applies but a count it needs
//!   is missing, the fact's kind without a value
//!   ([`FactSet::unobserved`](super::FactSet::unobserved)).
//! - **Guarantees**: an exact fact reads only [`State::Clean`] rows, whose
//!   count is exactly its context's. A [`State::Pending`] operator gives at
//!   most a bound ([`State::upper`]) or a floor ([`State::lower`]). A
//!   [`State::Tainted`] one (stopped early, unresolved, self-join, ...)
//!   gives nothing.
//! - **Not done**: nothing is combined across operators or plans; that is
//!   [`super::derive`]. Outer joins give no selectivity.
//!
//! The exact rules implement [`FactRule`] and are listed in [`RULES`]; the
//! bound and floor rules run after them on every operator.
//!
//! # Exact rules
//!
//! ## `cardinality`
//!
//! - **Claim**: `|C| = rows`. For a GROUP BY on keys `K` over input `I`,
//!   whose rows are its groups, `ndv(K | I) = rows` instead.
//! - **When**: the operator is clean with context `C`; not an aggregate
//!   without GROUP BY.
//! - **Why**: a clean operator outputs exactly `C`'s rows.
//!
//! ## `filter selectivity`
//!
//! - **Claim**: `s(P | I) = rows / input rows`.
//! - **When**: a filter, clean along with its input `I`; `P` is its
//!   predicate's conjuncts, less those already among `I`'s predicates
//!   (DuckDB re-checks some), and is not empty. No fact if the input had no
//!   rows.
//! - **Why**: the filter outputs exactly `I ∧ P`.
//!
//! ## `join selectivity`
//!
//! - **Claim**: inner join on `on` of `L` and `R`: `s(on | L × R) = rows /
//!   (|L| · |R|)`. Semi join keeping `K` against `O`: `m(on | K ⋉ O) =
//!   rows / |K|`; anti join: `m = (|K| − rows) / |K|`.
//! - **When**: the join and both inputs are clean, `on` resolves and, for
//!   an inner join, is not empty and the inputs share no table instance.
//!   An inner join on exactly the keys one side keeps only its first row
//!   per value of has a semi join's rows, and also gives its `m`.
//! - **Why**: an inner join outputs `(L × R) ∧ on`; a semi join the rows
//!   of `K` with a partner, an anti join the rest.
//!
//! ## `distinct count`
//!
//! - **Claim**: `ndv(K | I) = rows`.
//! - **When**: a GROUP BY or DISTINCT on non-empty keys `K` that resolve,
//!   clean along with its input `I`. Its input's rows need not be counted.
//! - **Why**: it outputs one row per distinct combination of `K` in `I`.
//!
//! # Bound and floor rules
//!
//! ## `upper bound`
//!
//! - **Claim**: `|U| ≤ rows`, a bound. Over a GROUP BY on `K` whose input
//!   is pending: `ndv(K | U) ≤ rows`, with `U` its input's.
//! - **When**: the operator's (or the GROUP BY's input's) rows are pending
//!   and [`State::upper`] gives `U`: every pending filter is a pushed filter
//!   that resolved, or a runtime filter that still holds every row
//!   satisfying it. `U` is the context with those runtime filters'
//!   predicates.
//! - **Why**: a pushed (optional) filter may let extra rows through, and a
//!   runtime filter drops only rows failing its predicate, so the rows hold
//!   all of `U`'s.
//!
//! ## `lower bound`
//!
//! - **Claim**: `|C| ≥ rows`, a floor.
//! - **When**: the operator is pending, and [`State::lower`] gives `C`:
//!   every pending filter is a runtime filter, and each operator since kept
//!   a subset of its input.
//! - **Why**: a runtime filter only drops rows (those without a partner),
//!   so the rows are among `C`'s.
//!
//! ## `build keys`
//!
//! - **Claim**: on `ndv(x | B)`, for the build side `B` of the join that
//!   pushed runtime filters on column `y` into a scan, joined on `y = x`:
//!   an IN list of `n` literals (or `y = k`, `n = 1`) gives the bound
//!   `≤ n + 1` and, if `n > 1`, the floor `≥ n`; a range `a ≤ y ≤ b` of
//!   integers gives the bound `≤ b − a + 2`.
//! - **When**: exactly one join on `y` is above the scan, with the scan on
//!   its probe side; it is an inner, left semi or right join with a clean
//!   build side, and `y = x` is its only condition reading `y`. Every
//!   operator above the scan has one parent, and none is a UNION or a join
//!   whose condition did not resolve (any could also have pushed a filter
//!   on `y`). Each filter form occurs once on `y`.
//! - **Why**: the filters are built from every non-NULL build key; one
//!   more value allows for NULL.
//!
//! ```text
//! lineitem scan, runtime filter l_suppkey IN (3, 7, 9)
//!   from: lineitem ⋈ σ(s_nation = 'X')(supplier) on l_suppkey = s_suppkey
//! ⇒ 3 ≤ ndv(s_suppkey | supplier ∧ s_nation = 'X') ≤ 4
//! ```
//!
//! ## `join domain`
//!
//! - **Claim**: for each column `y` with runtime filters pending on a side
//!   of this join, over its context `C`: `min(y | C) ≥ lo` (floor),
//!   `max(y | C) ≤ hi` (bound) and `ndv(y | C) ≤ n` (bound). `lo` and `hi`
//!   are the tightest ends the filters admit (`> k` admits from `k + 1`,
//!   `< k` up to `k − 1`), and `n` the fewest values one lists (`y = k`,
//!   an IN list, or an `OR` of such).
//! - **When**: an inner join (both sides), left semi (left side) or right
//!   semi (right side), clean. `lo` and `hi` only if non-negative integers;
//!   `n` only if this join has an equality on `y`, which drops NULL.
//! - **Why**: each filter admits every key of the join that built it, at
//!   or below this one, so every value of `y` here satisfies every filter,
//!   whether or not the scan applied it.
//!
//! ```text
//! orders scan, runtime filters o_custkey >= 5, o_custkey <= 90
//!   enforced by C = orders ⋈ customer on o_custkey = c_custkey
//! ⇒ min(o_custkey | C) ≥ 5, max(o_custkey | C) ≤ 90
//! ```
//!
//! ## `translated`
//!
//! Run by [`FactSet::observe_translated`](super::FactSet::observe_translated),
//! on the plan translated into a logical plan and named as a query's
//! operators are, which names rows these rules cannot (a theta join, a
//! GROUP BY on an expression).
//!
//! - **Claim**: `|C| = rows` for each operator's translated context `C`
//!   (`ndv(K | I) = rows` for a GROUP BY), as a fact, or as a floor `≥`.
//! - **When**: the plan translates, the operator was counted and did not
//!   stop early. A fact if no runtime or optional filter pruned at or below
//!   it (the translation leaves both out), or its state is clean; a floor
//!   if only runtime filters did ([`State::lower`]); nothing otherwise.
//! - **Why**: as `cardinality` and `lower bound`.

use std::collections::{BTreeSet, HashMap};

use datafusion::arrow::datatypes::DataType;
use datafusion::common::JoinType;
use datafusion::logical_expr::{BinaryExpr, Expr, LogicalPlan, Operator};

use super::state::{Pending, State, Value, Values, join_keys, states, states_hidden, stopped};
use super::{Fact, FactKind, Origin, Ratio, Term};
use crate::Options;
use crate::analysis::Node;
use crate::observed::{Catalog, ObservedPlan, Op, column_key};
use crate::rows::Context;
use crate::rows::logical::Logical;

/// A rule reading exact facts off one operator.
pub trait FactRule: Sync {
    /// The rule's name, as recorded in each fact's
    /// [`Origin::Observed`].
    fn name(&self) -> &'static str;
    /// The facts operator `node` shows: each with its value, or without
    /// where the operator has the fact's rows and they were not counted.
    fn apply(&self, obs: &Observation, node: usize, out: &mut Vec<(FactKind, Option<Ratio>)>);
}

/// The exact rules, in the order they run on each operator.
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
        for (kind, value, floor) in join_domain(&obs, node) {
            let f = fact(kind, value, node, "join domain");
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
/// has it on its probe side, equal to a column of its build side. DuckDB
/// also pushes through a UNION, and a join whose condition didn't resolve
/// may be on the column too, so neither may be above the scan; and one
/// join pushes one filter of each form.
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
                    match &obs.plan.nodes[*p].op {
                        Op::Union => break false,
                        Op::Join { on, .. } if on.iter().any(|p| p.expr.is_none()) => break false,
                        Op::Join { on, .. } if join_keys(on).contains(column) => {
                            joins.push((*p, obs.plan.nodes[*p].children[0] == at));
                        }
                        _ => {}
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
        let mut twice = false;
        fn set<T>(slot: &mut Option<T>, v: T, twice: &mut bool) {
            *twice |= slot.is_some();
            *slot = Some(v);
        }
        for r in runtime_filters.iter().filter(|r| r.column.as_ref() == Some(column)) {
            match &r.expr {
                Some(Expr::InList(l)) if !l.negated && l.list.iter().all(|v| matches!(v, Expr::Literal(..))) => {
                    set(&mut listed, l.list.len() as u64, &mut twice)
                }
                Some(Expr::BinaryExpr(BinaryExpr { op: Operator::Eq, right, .. })) if matches!(right.as_ref(), Expr::Literal(..)) => {
                    set(&mut listed, 1, &mut twice)
                }
                Some(Expr::BinaryExpr(BinaryExpr { op: Operator::GtEq, right, .. })) => set(&mut lo, integer(right), &mut twice),
                Some(Expr::BinaryExpr(BinaryExpr { op: Operator::LtEq, right, .. })) => set(&mut hi, integer(right), &mut twice),
                _ => {}
            }
        }
        let (lo, hi) = (lo.flatten(), hi.flatten());
        if twice {
            continue;
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

/// What the runtime filters a join enforces say of its rows, as bounds
/// (`false`) and floors (`true`). Each filter admits every key of the join
/// that built it, and that join is at or below this one, the highest on its
/// column: every value of the column here is one of those keys, so it
/// satisfies the filter, whether or not the scan applied it. So its least
/// value is at least a range's or list's least, its greatest at most their
/// greatest, and it takes at most as many values as a list holds. Only
/// non-negative integers are read, and only on an inner or semi join, of
/// the side a semi join keeps: elsewhere the column may be NULL, or gone.
fn join_domain(obs: &Observation, node: usize) -> Vec<(FactKind, Ratio, bool)> {
    let n = &obs.plan.nodes[node];
    let Op::Join { kind, on } = &n.op else { return vec![] };
    let sides = match kind {
        JoinType::Inner => &n.children[..],
        JoinType::LeftSemi => &n.children[..1],
        JoinType::RightSemi => &n.children[1..],
        _ => return vec![],
    };
    let Some(ctx) = obs.states[node].clean() else { return vec![] };
    // Each column's filters, as the least and greatest values and the
    // fewest listed values they admit.
    let mut columns: std::collections::BTreeMap<&String, (Option<i64>, Option<i64>, Option<u64>)> = Default::default();
    for &c in sides {
        let State::Pending(_, pending) = &obs.states[c] else { continue };
        for p in pending {
            let Pending::Join { column: Some(column), expr: Some(expr), .. } = p else { continue };
            let (lo, hi, listed) = columns.entry(column).or_default();
            let (from, to, values) = admits(&expr.expr);
            let tighter = |a: &mut Option<i64>, b: Option<i64>, f: fn(i64, i64) -> i64| *a = a.map_or(b, |a| Some(b.map_or(a, |b| f(a, b))));
            tighter(lo, from, i64::max);
            tighter(hi, to, i64::min);
            if let Some(v) = values {
                *listed = Some(listed.map_or(v, |l| l.min(v)));
            }
        }
    }
    let mut out = vec![];
    for (column, (lo, hi, listed)) in columns {
        let Some((instance, name)) = column.rsplit_once('.') else { continue };
        let key = Term::new(crate::observed::qualified(instance, name));
        if let Some(lo) = lo.and_then(|v| u64::try_from(v).ok()) {
            out.push((FactKind::Min { key: key.clone(), over: ctx.clone() }, Ratio::int(lo), true));
        }
        if let Some(hi) = hi.and_then(|v| u64::try_from(v).ok()) {
            out.push((FactKind::Max { key: key.clone(), over: ctx.clone() }, Ratio::int(hi), false));
        }
        // NULL is one more value, unless this join's equality on the column
        // drops it: another condition on it (`OR`, IS NOT DISTINCT FROM) may
        // not.
        let equal = on.iter().any(|p| match &p.expr {
            Some(Expr::BinaryExpr(BinaryExpr { left, op: Operator::Eq, right })) => {
                [left, right].iter().any(|e| matches!(e.as_ref(), Expr::Column(c) if column_key(c) == *column))
            }
            _ => false,
        });
        if let (Some(n), true) = (listed, equal) {
            out.push((FactKind::Distinct { keys: [key].into(), over: ctx.clone() }, Ratio::int(n), false));
        }
    }
    out
}

/// The values runtime filter `e` admits: the least and greatest, if they
/// are integers, and how many, if it lists them (`x = k` or an IN list,
/// which reads as `x = a OR x = b`).
fn admits(e: &Expr) -> (Option<i64>, Option<i64>, Option<u64>) {
    fn equal(e: &Expr) -> Option<&Expr> {
        match e {
            Expr::BinaryExpr(BinaryExpr { op: Operator::Eq, right, .. }) => Some(right.as_ref()),
            _ => None,
        }
    }
    let mut listed = vec![];
    let mut todo = vec![e];
    while let Some(e) = todo.pop() {
        match e {
            Expr::BinaryExpr(BinaryExpr { left, op: Operator::Or, right }) => todo.extend([left.as_ref(), right.as_ref()]),
            e => match equal(e) {
                Some(v @ Expr::Literal(..)) => listed.push(v),
                _ => {
                    listed.clear();
                    break;
                }
            },
        }
    }
    if !listed.is_empty() {
        let ints: Option<Vec<i64>> = listed.iter().map(|v| integer(v)).collect();
        let (lo, hi) = ints.map_or((None, None), |v| (v.iter().min().copied(), v.iter().max().copied()));
        return (lo, hi, Some(listed.len() as u64));
    }
    match e {
        Expr::BinaryExpr(BinaryExpr { op, right, .. }) => {
            let k = integer(right);
            match op {
                Operator::GtEq => (k, None, None),
                Operator::Gt => (k.and_then(|k| k.checked_add(1)), None, None),
                Operator::LtEq => (None, k, None),
                Operator::Lt => (None, k.and_then(|k| k.checked_sub(1)), None),
                _ => (None, None, None),
            }
        }
        _ => (None, None, None),
    }
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

/// `|C| = rows` for a clean operator. Spec: [`cardinality`](self#cardinality).
///
/// Gives base-table sizes from unfiltered scans, filtered sizes from scans
/// with pushed-down predicates, and the sizes of joins. Rows named as a
/// GROUP BY's, as a filter on its keys above it reads once it goes below,
/// are its keys' distinct values over its input ([`DistinctCount`] reads
/// the GROUP BY itself).
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

/// `s(P | I) = rows / |I|` for a filter. Spec:
/// [`filter selectivity`](self#filter-selectivity).
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

/// `s(on | L × R)` for an inner join, `m(on | K ⋉ O)` for a semi or anti
/// join. Spec: [`join selectivity`](self#join-selectivity).
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

/// `ndv(K | I) = rows` for a GROUP BY or DISTINCT. Spec:
/// [`distinct count`](self#distinct-count).
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

// The `translated` rule: facts read off an observed plan's logical form.
//
// The rules above name an executed operator's rows as the plan ran them
// (`states`). Some rows they cannot name, a query names
// all the same: a theta join, a GROUP BY on an expression. So each plan is
// also translated as it ran ([`Catalog::to_logical`]), its operators named
// as a query's are ([`Logical`]), and each operator's count is a fact on
// the rows it names:
//
// - exactly, if nothing at or below it was pruned by a runtime or optional
//   filter, which the translation leaves out, or if its rows are clean
//   ([`State::Clean`]);
// - at least (a floor), if only runtime filters pruned below it, keeping a
//   subset ([`State::lower`]);
// - not at all otherwise, or if it was not counted, or may have stopped
//   early.

/// Each fact `plan`'s counts give its translation's rows, and whether it is
/// a floor. None if the plan does not translate.
pub(crate) fn observe_translated(catalog: &Catalog, plan: &ObservedPlan, options: &Options) -> Vec<(Fact, bool)> {
    if !plan.counted {
        return vec![];
    }
    let Ok((root, built)) = catalog.to_logical_mapped(plan) else { return vec![] };
    let (nodes, scans) = crate::nodes(&root, options);
    let logical = Logical::new(&nodes, &scans);
    let mut out = vec![];
    for (m, j, floor) in counts(plan, &nodes, &built) {
        let kind = match &logical.contexts[m] {
            Ok(Context::Derived { op, args, inputs }) if op == "group" => {
                FactKind::Distinct { keys: args.iter().cloned().collect(), over: inputs[0].clone() }
            }
            Ok(Context::Derived { op, .. }) if op == "aggregate" => continue,
            Ok(ctx) => FactKind::Cardinality(ctx.clone()),
            Err(_) => continue,
        };
        let origin = Origin::Observed { query: plan.name.clone(), node: j, rule: "translated".into() };
        let fact = Fact { kind: kind.canonical(), value: Ratio::int(plan.nodes[j].rows), origins: vec![origin] };
        out.push((fact, floor));
    }
    out
}

/// Each analyzer node of `nodes` an operator of `plan` became, by `built`
/// (each operator and the subplans it became), with the operator and
/// whether its count is only a floor for the node's rows.
fn counts(plan: &ObservedPlan, nodes: &[Node], built: &[(usize, LogicalPlan)]) -> Vec<(usize, usize, bool)> {
    let states = states(plan);
    let stopped = stopped(plan);
    // Whether a runtime or optional filter pruned at or below each operator:
    // the translation leaves both out.
    let mut pruned = vec![false; plan.nodes.len()];
    for (j, n) in plan.nodes.iter().enumerate() {
        let own = match &n.op {
            Op::Scan { runtime_filters, filters, .. } => !runtime_filters.is_empty() || filters.iter().any(|f| f.optional),
            _ => false,
        };
        pruned[j] = own || n.children.iter().any(|&c| pruned[c]);
    }
    let mut by_plan: HashMap<&LogicalPlan, Vec<usize>> = HashMap::new();
    for (j, p) in built {
        by_plan.entry(p).or_default().push(*j);
    }
    let mut out = vec![];
    let mut done = BTreeSet::new();
    for (m, node) in nodes.iter().enumerate() {
        for &j in by_plan.get(&node.plan).into_iter().flatten() {
            if !plan.nodes[j].counted || stopped[j] || !done.insert((m, j)) {
                continue;
            }
            let floor = match &states[j] {
                _ if !pruned[j] => false,
                State::Clean(_) => false,
                s if s.lower().is_some() => true,
                _ => continue,
            };
            out.push((m, j, floor));
        }
    }
    out
}
