//! The trace of an analysis with reference plans and tables' row counts:
//! the plans' nodes beside the query's, a constraint for each pin and each
//! row count, with what it is read from, and proofs whose cores name the
//! pins a tighter bound needs.

mod fixtures;

use cardinal::observed::ObservedPlan;
use cardinal::{Analysis, Bounds, Builder, Options, ProofStatus, Trace};
use fixtures::{context, foreign_keys, plans, query};

/// TPC-H query `name` as DataFusion plans it, traced.
async fn traced(name: &str) -> Builder<'static> {
    let options = Options { trace: true, foreign_keys: foreign_keys(), ..Default::default() };
    Analysis::sql(&context(), &query("tpch", name)).await.unwrap().options(options)
}

/// The profile of TPC-H query `name`.
async fn profile(name: &str) -> ObservedPlan {
    plans("tpch").await.into_iter().find(|p| p.name == name).unwrap()
}

/// Every constraint of `t` loads back.
fn loads(t: &Trace) {
    let solver = z3::Solver::new();
    solver.from_string(t.to_smt2());
    assert_eq!(solver.get_assertions().len(), t.constraints.len());
}

#[tokio::test]
async fn reference_plans_are_traced() {
    let base = traced("q05").await.build().unwrap();
    let p = profile("q05").await;
    let a = traced("q05").await.with_plans([&p]).build().unwrap();
    let (base, t) = (base.trace.as_ref().unwrap(), a.trace.as_ref().unwrap());
    // The query's nodes first, as without the plan; then the plan's.
    let own = t.nodes.iter().take_while(|n| n.plan.is_none()).count();
    assert_eq!(own, base.nodes.len());
    assert!(t.nodes.iter().zip(&base.nodes).all(|(n, b)| n.label == b.label));
    assert!(t.nodes[own..].iter().all(|n| n.plan.as_deref() == Some("q05")), "{:?}", t.nodes[own..].iter().map(|n| &n.plan).collect::<Vec<_>>());
    assert!(own < t.nodes.len(), "no node of the plan");
    let pins: Vec<_> = t.constraints.iter().filter(|c| c.fact.is_some()).collect();
    assert!(!pins.is_empty(), "no pins");
    for c in &pins {
        let info = c.fact.as_ref().unwrap();
        assert!(info.source.starts_with("observed "), "{info:?}");
        assert!(info.facts[0].origins.iter().all(|o| o.starts_with("q05#")), "{info:?}");
        let node = c.node.expect("a pin's node");
        assert_eq!(t.nodes[node].plan.as_deref(), Some("q05"), "c{}", c.id);
        assert!(c.source.contains("joint/"), "{}", c.source);
    }
    loads(t);
    assert_eq!(t.without_facts().constraints.len(), t.constraints.len() - pins.len());
}

#[tokio::test]
async fn tighter_bound_needs_the_plan() {
    let p = profile("q04").await;
    let a = traced("q04").await.build().unwrap();
    let i = traced("q04").await.with_plans([&p]).build().unwrap();
    let bounds = i.bounds().unwrap();
    assert_ne!(Some(&bounds), a.bounds().ok().as_ref(), "the plan tightens nothing");
    let t = i.trace.as_ref().unwrap();
    let with = i.explain(&bounds).unwrap();
    let without = a.explain(&bounds).unwrap();
    assert_eq!(with.len(), without.len());
    let needs_pins = with.iter().zip(&without).any(|(w, wo)| {
        w.status == ProofStatus::Proven
            && w.core.iter().any(|&c| t.constraints[c].fact.is_some())
            && wo.status != ProofStatus::Proven
    });
    assert!(needs_pins, "no bound needs the pins: {with:#?}");
}

#[tokio::test]
async fn row_counts_are_traced() {
    let a = traced("q05").await.build().unwrap();
    let sizes = [("supplier", 100), ("nation", 25), ("no_such_table", 1)];
    let i = traced("q05").await.with_cardinalities(sizes).build().unwrap();
    let (base, t) = (a.trace.as_ref().unwrap(), i.trace.as_ref().unwrap());
    let given: Vec<_> = t.constraints.iter().filter(|c| c.fact.is_some()).collect();
    assert_eq!(t.constraints[..base.constraints.len()], base.constraints[..]);
    // One per table the query scans; the unknown one is ignored.
    assert_eq!(given.len(), 2);
    assert_eq!(t.constraints.len(), base.constraints.len() + given.len());
    let texts: Vec<&str> = given.iter().map(|c| c.fact.as_ref().unwrap().facts[0].text.as_str()).collect();
    assert_eq!(texts, ["|supplier|", "|nation|"]);
    for c in &given {
        let info = c.fact.as_ref().unwrap();
        assert_eq!(info.source, "given rows", "{info:?}");
        assert_eq!(info.facts[0].origins, ["given"], "{info:?}");
        assert!(c.function.starts_with("fact: "), "{}", c.function);
        assert!(c.source.contains("builder.rs:"), "{}", c.source);
    }
    loads(t);
    assert_eq!(t.without_facts(), *base);
    let b = i.bounds().unwrap();
    assert!(b.upper.is_some(), "{b}");
}

#[tokio::test]
async fn untraced_analysis_has_no_trace() {
    let p = profile("q03").await;
    let options = Options { foreign_keys: foreign_keys(), ..Default::default() };
    let i = Analysis::sql(&context(), &query("tpch", "q03")).await.unwrap().options(options).with_plans([&p]).build().unwrap();
    assert!(i.trace.is_none());
    assert!(i.explain(&Bounds::default()).is_err());
}
