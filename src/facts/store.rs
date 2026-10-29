//! Facts from a store, as claims on the quantities a query's rows have.
//!
//! Each operator of the query is named as facts name rows ([`Logical`]),
//! and its variables join the [`Space`] as the terms of its quantities: its
//! cardinality variable is `|ctx|`, its columns' NDV, min and max variables
//! those of `ctx`. Every exact fact, bound and floor whose rows are near the
//! query's is then a claim on its quantity's term, a variable of its own if
//! no operator has those rows, and the axioms relate them all. Z3 derives
//! what follows; nothing is combined here.

use std::collections::{BTreeSet, HashMap};
use std::time::Instant;

use datafusion::logical_expr::Expr;
use z3::ast::Int;

use super::axioms::{Axiom, Space, over};
use super::context::{Context, Term};
use super::logical::Logical;
use super::{FactKind, FactSet};
use crate::analyzer::Node;
use crate::grounded::{self, Grounded, Observations, Tracked};
use crate::trace::FactRef;
use crate::{Analysis, Result};

/// Adds the quantities of `nodes`' rows, named by `logical`, to `space`.
/// Returns each quantity's first node, and the contexts of the nodes' rows.
fn add_nodes(space: &mut Space, nodes: &[Node], logical: &Logical) -> (HashMap<FactKind, usize>, BTreeSet<Context>) {
    let mut node_of = HashMap::new();
    let mut contexts = BTreeSet::new();
    let mut add = |space: &mut Space, q: FactKind, var: &str, i: usize, contexts: &mut BTreeSet<Context>| {
        let q = q.canonical();
        contexts.insert(over(&q).clone());
        node_of.entry(q.clone()).or_insert(i);
        space.add(q, Int::new_const(var));
    };
    for (i, node) in nodes.iter().enumerate() {
        let schema = node.plan.schema();
        // A column `j` of the rows, if it is a column of a table and not a
        // float: the constraints count a float's values by bits, facts by
        // SQL equality.
        let column = |j: usize| -> Option<Term> {
            let Some(Some(e @ Expr::Column(_))) = logical.lineage[i].get(j) else { return None };
            (j < schema.fields().len() && !schema.field(j).data_type().is_floating()).then(|| Term::new(e.clone()))
        };
        let mut rows = vec![];
        if let (Some((raw, ndvs, _)), Some(instance)) = (&node.raw_scan, &logical.instances[i]) {
            rows.push((Context::table(instance), raw, ndvs, &node.raw_min_vars, &node.raw_max_vars));
        }
        if let Ok(ctx) = &logical.contexts[i] {
            rows.push((ctx.clone(), &node.var, &node.ndv_vars, &node.min_vars, &node.max_vars));
            // A grouping's rows are its keys' distinct values.
            if let Context::Derived { op, args, inputs } = ctx
                && op == "group"
            {
                let keys = args.iter().cloned().collect();
                add(space, FactKind::Distinct { keys, over: inputs[0].clone() }, &node.var, i, &mut contexts);
            }
        }
        for (ctx, card, ndvs, mins, maxs) in rows {
            add(space, FactKind::Cardinality(ctx.clone()), card, i, &mut contexts);
            for (j, ndv) in ndvs.iter().enumerate() {
                if let Some(key) = column(j) {
                    add(space, FactKind::Distinct { keys: [key].into(), over: ctx.clone() }, ndv, i, &mut contexts);
                }
            }
            for (j, (lo, hi)) in mins.iter().zip(maxs).enumerate() {
                let Some(key) = column(j) else { continue };
                if let Some(lo) = lo {
                    add(space, FactKind::Min { key: key.clone(), over: ctx.clone() }, lo, i, &mut contexts);
                }
                if let Some(hi) = hi {
                    add(space, FactKind::Max { key, over: ctx.clone() }, hi, i, &mut contexts);
                }
            }
        }
    }
    (node_of, contexts)
}

/// How a claim relates its quantity to a value.
#[derive(Debug, Clone, Copy)]
enum Rel {
    Eq,
    Le,
    Ge,
}

impl Rel {
    fn claim(self, term: &Int, n: u64) -> z3::ast::Bool {
        let n = Int::from_u64(n);
        match self {
            Rel::Eq => term.eq(&n),
            Rel::Le => term.le(&n),
            Rel::Ge => term.ge(&n),
        }
    }

    fn symbol(self) -> &'static str {
        match self {
            Rel::Eq => "=",
            Rel::Le => "<=",
            Rel::Ge => ">=",
        }
    }
}

/// `analysis` with the facts `facts` stores among its constraints.
pub(crate) fn with_store(analysis: &Analysis, facts: &FactSet) -> Result<Grounded> {
    let start = Instant::now();
    let logical = Logical::new(&analysis.nodes, &analysis.scans);
    let mut space = Space::default();
    let (node_of, seeds) = add_nodes(&mut space, &analysis.nodes, &logical);

    // Every fact's quantity, with a variable of its own where no operator
    // has its rows.
    let conflicted: BTreeSet<&FactKind> = facts.conflicts.iter().map(|c| &c.kind).collect();
    let claims: Vec<(&super::Fact, Rel)> = facts
        .iter()
        .map(|f| (f, Rel::Eq))
        .chain(facts.bounds().map(|f| (f, Rel::Le)))
        .chain(facts.floors().map(|f| (f, Rel::Ge)))
        .filter(|(f, _)| {
            !conflicted.contains(&f.kind)
                && matches!(f.kind, FactKind::Cardinality(_) | FactKind::Distinct { .. } | FactKind::Min { .. } | FactKind::Max { .. })
        })
        .collect();
    let mut own = vec![];
    for (f, _) in &claims {
        if space.term(&f.kind).is_none() {
            space.add(f.kind.clone(), Int::new_const(format!("fq_{}", own.len())));
            own.push(f.kind.clone());
        }
    }
    let relevant = space.relevant(&seeds);
    let mut axioms = space.axioms(&relevant);
    for q in &own {
        if relevant.contains(over(q)) && matches!(q, FactKind::Cardinality(_) | FactKind::Distinct { .. }) {
            let t = space.term(q).unwrap();
            axioms.push(Axiom { claim: t.ge(Int::from_u64(0)), rule: "non-negative" });
        }
    }
    let mut tracked = vec![];
    for (f, rel) in claims {
        let (Some(n), true) = (f.value.as_int(), relevant.contains(over(&f.kind))) else { continue };
        let term = space.term(&f.kind).unwrap();
        let source = match rel {
            Rel::Eq => "fact",
            Rel::Le => "bound",
            Rel::Ge => "floor",
        };
        let value = format!("{} {n}", rel.symbol());
        tracked.push(Tracked::new(rel.claim(term, n), node_of.get(&f.kind).copied(), source, vec![FactRef::of(f)], value));
    }
    let obs = Observations { axioms, tracked, setup: start.elapsed() };
    grounded::ground(analysis, obs)
}
