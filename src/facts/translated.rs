//! Facts read off an observed plan's logical form.
//!
//! The rules name an executed operator's rows as the plan ran them
//! ([`super::context::states`]). Some rows they cannot name, a query names
//! all the same: a theta join, a GROUP BY on an expression. So each plan is
//! also translated as it ran ([`Catalog::to_logical`]), its operators named
//! as a query's are ([`Logical`]), and each operator's count is a fact on
//! the rows it names:
//!
//! - exactly, if nothing at or below it was pruned by a runtime or optional
//!   filter, which the translation leaves out, or if its rows are clean
//!   ([`State::Clean`]);
//! - at least (a floor), if only runtime filters pruned below it, keeping a
//!   subset ([`State::lower`]);
//! - not at all otherwise, or if it was not counted, or may have stopped
//!   early.

use std::collections::{BTreeSet, HashMap};

use datafusion::logical_expr::LogicalPlan;

use super::context::{Context, State, states, stopped};
use super::logical::Logical;
use super::{Fact, FactKind, Origin, Ratio};
use crate::Options;
use crate::analyzer::Node;
use crate::observed::{Catalog, ObservedPlan, Op};

/// Each fact `plan`'s counts give its translation's rows, and whether it is
/// a floor. None if the plan does not translate.
pub(crate) fn observe(catalog: &Catalog, plan: &ObservedPlan, options: &Options) -> Vec<(Fact, bool)> {
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
