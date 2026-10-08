//! Rules reading facts off one operator of an executed plan.
//!
//! Each rule looks at an operator, its rows and its inputs' rows, and the
//! [`State`]s of all three, and emits the facts the counts establish. Rules
//! only read clean states: a count that may be short says nothing.

use datafusion::common::JoinType;

use super::context::{Context, State, Values, states, stopped};
use super::{Fact, FactKind, Origin, Ratio};
use crate::observed::{ObservedPlan, Op};

pub trait FactRule: Sync {
    fn name(&self) -> &'static str;
    /// The facts operator `node` shows.
    fn apply(&self, obs: &Observation, node: usize, out: &mut Vec<(FactKind, Ratio)>);
}

pub static RULES: &[&dyn FactRule] = &[&Cardinality, &FilterSelectivity, &JoinSelectivity, &DistinctCount];

/// An executed plan, with every operator's state.
pub struct Observation<'a> {
    pub plan: &'a ObservedPlan,
    pub states: &'a [State],
    values: Values<'a>,
}

/// Every fact the rules read off `plan`, canonically named.
pub(crate) fn observe(plan: &ObservedPlan) -> Vec<Fact> {
    let states = states(plan);
    let stopped = stopped(plan);
    let obs = Observation { plan, states: &states, values: Values { plan, states: &states, stopped: &stopped } };
    let mut facts = vec![];
    for node in 0..plan.nodes.len() {
        for rule in RULES {
            let mut out = vec![];
            rule.apply(&obs, node, &mut out);
            facts.extend(out.into_iter().map(|(kind, value)| Fact {
                kind: kind.canonical(),
                value,
                origins: vec![Origin::Observed { query: plan.name.clone(), node, rule: rule.name() }],
            }));
        }
    }
    facts
}

/// The clean contexts of `node` and of its inputs, with their row counts.
fn clean<'s>(obs: &Observation<'s>, node: usize) -> Option<(&'s Context, Vec<(&'s Context, u64)>)> {
    let n = &obs.plan.nodes[node];
    let out = obs.states[node].clean()?;
    let inputs = n
        .children
        .iter()
        .map(|&c| Some((obs.states[c].clean()?, obs.plan.nodes[c].rows)))
        .collect::<Option<Vec<_>>>()?;
    Some((out, inputs))
}

/// `|ctx| = rows` for any operator whose rows have a context: base-table
/// sizes from unfiltered scans, filtered sizes from scans with pushed-down
/// predicates, and the sizes of joins. Aggregates, and operators passing
/// their rows on, are left to [`DistinctCount`].
pub struct Cardinality;

impl FactRule for Cardinality {
    fn name(&self) -> &'static str {
        "cardinality"
    }

    fn apply(&self, obs: &Observation, node: usize, out: &mut Vec<(FactKind, Ratio)>) {
        let n = &obs.plan.nodes[node];
        let grouped = |c: &Context| matches!(c, Context::Derived { op, .. } if op == "group" || op == "aggregate");
        if let Some(ctx) = obs.states[node].clean().filter(|c| !grouped(c)) {
            out.push((FactKind::Cardinality(ctx.clone()), Ratio::int(n.rows)));
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

    fn apply(&self, obs: &Observation, node: usize, out: &mut Vec<(FactKind, Ratio)>) {
        let n = &obs.plan.nodes[node];
        let (Op::Filter { predicate }, Some((_, inputs))) = (&n.op, clean(obs, node)) else { return };
        let (input, rows) = inputs[0];
        let Ok(mut pred) = obs.values.resolve(predicate) else { return };
        if let Context::Spj { preds, .. } = input {
            pred.retain(|p| !preds.contains(p));
        }
        if let (false, Some(s)) = (pred.is_empty(), Ratio::new(n.rows, rows)) {
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

    fn apply(&self, obs: &Observation, node: usize, out: &mut Vec<(FactKind, Ratio)>) {
        let n = &obs.plan.nodes[node];
        let (Op::Join { kind, on }, Some((_, inputs))) = (&n.op, clean(obs, node)) else { return };
        let Ok(on) = obs.values.resolve(on) else { return };
        let [(l, lr), (r, rr)] = inputs[..] else { return };
        let fact = match kind {
            JoinType::Inner if !on.is_empty() => l.cross(r).and_then(|over| {
                let pairs = lr.checked_mul(rr)?;
                Some((FactKind::Selectivity { pred: on, over }, Ratio::new(n.rows, pairs)?))
            }),
            JoinType::LeftSemi | JoinType::LeftAnti | JoinType::RightSemi | JoinType::RightAnti => {
                let left = matches!(kind, JoinType::LeftSemi | JoinType::LeftAnti);
                let (kept, other, rows) = if left { (l, r, lr) } else { (r, l, rr) };
                let matched = match kind {
                    JoinType::LeftSemi | JoinType::RightSemi => n.rows,
                    _ => rows.saturating_sub(n.rows),
                };
                Ratio::new(matched, rows).map(|m| (FactKind::Match { on, kept: kept.clone(), other: other.clone() }, m))
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

    fn apply(&self, obs: &Observation, node: usize, out: &mut Vec<(FactKind, Ratio)>) {
        let n = &obs.plan.nodes[node];
        let (Op::Aggregate { keys, .. }, Some((_, inputs))) = (&n.op, clean(obs, node)) else { return };
        let Some(keys) = obs.values.keys(keys) else { return };
        if !keys.is_empty() {
            out.push((FactKind::Distinct { keys, over: inputs[0].0.clone() }, Ratio::int(n.rows)));
        }
    }
}
