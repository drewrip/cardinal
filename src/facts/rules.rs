//! Rules reading facts off one operator of an executed plan.
//!
//! Each rule looks at an operator, its rows and its inputs' rows, and the
//! [`State`]s of all three, and emits the facts the counts establish. Rules
//! only read clean states: a count that may be short says nothing.

use datafusion::common::JoinType;

use super::context::{Context, State, Term, resolve, states};
use super::{Fact, FactKind, Origin, Ratio};
use crate::observed::{ObservedPlan, Op};

pub trait FactRule: Sync {
    fn name(&self) -> &'static str;
    /// The facts operator `node` of `plan` shows, given every operator's state.
    fn apply(&self, plan: &ObservedPlan, node: usize, states: &[State], out: &mut Vec<(FactKind, Ratio)>);
}

pub static RULES: &[&dyn FactRule] = &[&Cardinality, &FilterSelectivity, &JoinSelectivity, &DistinctCount];

/// Every fact the rules read off `plan`.
pub(crate) fn observe(plan: &ObservedPlan) -> Vec<Fact> {
    let states = states(plan);
    let mut facts = vec![];
    for node in 0..plan.nodes.len() {
        for rule in RULES {
            let mut out = vec![];
            rule.apply(plan, node, &states, &mut out);
            facts.extend(out.into_iter().map(|(kind, value)| Fact {
                kind,
                value,
                origins: vec![Origin::Observed { query: plan.name.clone(), node, rule: rule.name() }],
            }));
        }
    }
    facts
}

/// The clean contexts of `node` and of its inputs, with their row counts.
fn clean<'s>(plan: &ObservedPlan, node: usize, states: &'s [State]) -> Option<(&'s Context, Vec<(&'s Context, u64)>)> {
    let n = &plan.nodes[node];
    let out = states[node].clean()?;
    let inputs = n
        .children
        .iter()
        .map(|&c| Some((states[c].clean()?, plan.nodes[c].rows)))
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

    fn apply(&self, plan: &ObservedPlan, node: usize, states: &[State], out: &mut Vec<(FactKind, Ratio)>) {
        let n = &plan.nodes[node];
        let grouped = |c: &Context| matches!(c, Context::Derived { op, .. } if op == "group" || op == "aggregate");
        if let Some(ctx) = states[node].clean().filter(|c| !grouped(c)) {
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

    fn apply(&self, plan: &ObservedPlan, node: usize, states: &[State], out: &mut Vec<(FactKind, Ratio)>) {
        let n = &plan.nodes[node];
        let (Op::Filter { predicate }, Some((_, inputs))) = (&n.op, clean(plan, node, states)) else { return };
        let (input, rows) = inputs[0];
        let Ok(mut pred) = resolve(predicate) else { return };
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

    fn apply(&self, plan: &ObservedPlan, node: usize, states: &[State], out: &mut Vec<(FactKind, Ratio)>) {
        let n = &plan.nodes[node];
        let (Op::Join { kind, on }, Some((_, inputs))) = (&n.op, clean(plan, node, states)) else { return };
        let Ok(on) = resolve(on) else { return };
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

    fn apply(&self, plan: &ObservedPlan, node: usize, states: &[State], out: &mut Vec<(FactKind, Ratio)>) {
        let n = &plan.nodes[node];
        let (Op::Aggregate { keys }, Some((_, inputs))) = (&n.op, clean(plan, node, states)) else { return };
        let Some(keys) = keys.iter().cloned().collect::<Option<Vec<_>>>() else { return };
        if !keys.is_empty() {
            let kind = FactKind::Distinct { keys: keys.into_iter().map(Term::new).collect(), over: inputs[0].0.clone() };
            out.push((kind, Ratio::int(n.rows)));
        }
    }
}
