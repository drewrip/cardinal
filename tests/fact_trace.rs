//! The trace of an analysis informed by facts: a constraint for each claim a
//! fact gave, with the facts it is read from, and proofs whose cores name
//! the facts a tighter bound needs.

mod fixtures;

use cardinal::facts::{Context, Fact, FactKind, FactSet, derive_facts};
use cardinal::observed::ObservedPlan;
use cardinal::{Analysis, Bounds, Facts, Options, ProofStatus};
use fixtures::{context, foreign_keys, plans, query};

/// TPC-H query `name` as DataFusion plans it, traced.
async fn traced(name: &str) -> Analysis {
    let options = Options { trace: true, foreign_keys: foreign_keys(), ..Default::default() };
    cardinal::analyze_sql(&context(), &query("tpch", name), options).await.unwrap()
}

/// The profiles of TPC-H queries `names`.
async fn profiles(names: &[&str]) -> Vec<ObservedPlan> {
    plans("tpch").await.into_iter().filter(|p| names.contains(&p.name.as_str())).collect()
}

fn check_trace(a: &Analysis, i: &Analysis) {
    let base = a.trace.as_ref().unwrap();
    let t = i.trace.as_ref().expect("an informed trace");
    let facts: Vec<_> = t.constraints.iter().filter(|c| c.fact.is_some()).collect();
    assert_eq!(t.constraints.len(), base.constraints.len() + facts.len());
    assert_eq!(t.constraints[..base.constraints.len()], base.constraints[..]);
    assert!(!facts.is_empty(), "no fact constraints");
    for c in &facts {
        let info = c.fact.as_ref().unwrap();
        assert!(!info.facts.is_empty(), "c{} has no facts", c.id);
        assert!(c.node.is_some(), "c{} has no node", c.id);
        assert!(c.function.starts_with("fact: "), "{}", c.function);
        assert!(c.source.contains("facts/apply.rs:"), "{}", c.source);
        assert!(!c.infix.contains("to_real"), "{}", c.infix);
    }
    // Every constraint loads back, the facts' too.
    let solver = z3::Solver::new();
    solver.from_string(t.to_smt2());
    assert_eq!(solver.get_assertions().len(), t.constraints.len());
    assert_eq!(t.without_facts(), *base);
}

#[tokio::test]
async fn fact_constraints_are_traced() {
    let a = traced("q05").await;
    let facts = Facts::new(derive_facts(&profiles(&["q05"]).await));
    let i = a.with_facts(&facts).unwrap();
    check_trace(&a, &i);
    let t = i.trace.as_ref().unwrap();
    let pinned = t.constraints.iter().filter_map(|c| c.fact.as_ref()).find(|f| f.source == "pinned rows");
    let pinned = pinned.expect("a pinned row count");
    assert!(pinned.facts[0].origins.iter().any(|o| o.starts_with("q05#")), "{pinned:?}");
}

#[tokio::test]
async fn tighter_bound_needs_facts() {
    // q04 is bounded by 5 with its facts.
    let a = traced("q04").await;
    let facts = Facts::new(derive_facts(&profiles(&["q04"]).await));
    let i = a.with_facts(&facts).unwrap();
    let bounds = i.bounds().unwrap();
    assert_ne!(Some(&bounds), a.bounds().ok().as_ref(), "the facts tighten nothing");
    let t = i.trace.as_ref().unwrap();
    let with = i.explain(&bounds).unwrap();
    let without = a.explain(&bounds).unwrap();
    assert_eq!(with.len(), without.len());
    let needs_facts = with.iter().zip(&without).any(|(w, wo)| {
        w.status == ProofStatus::Proven
            && w.core.iter().any(|&c| t.constraints[c].fact.is_some())
            && wo.status != ProofStatus::Proven
    });
    assert!(needs_facts, "no bound needs the facts: {with:#?}");
}

#[tokio::test]
async fn contradicting_facts_are_left_out() {
    let a = traced("q05").await;
    // q05's facts, but with no suppliers: the joins with them can't then
    // have the rows the profile shows.
    let mut facts = FactSet::default();
    let supplier = FactKind::Cardinality(Context::table("supplier")).canonical();
    for f in derive_facts(&profiles(&["q05"]).await).iter() {
        let value = if f.kind == supplier { cardinal::facts::Ratio::int(0) } else { f.value };
        facts.insert(Fact { value, ..f.clone() });
    }
    let i = a.with_facts(&Facts::new(facts)).unwrap();
    check_trace(&a, &i);
    // The facts kept are consistent with each other and the constraints.
    let solver = z3::Solver::new();
    solver.from_string(i.trace.as_ref().unwrap().to_smt2());
    assert_eq!(solver.check(), z3::SatResult::Sat);
    let all = a.with_facts(&Facts::new(derive_facts(&profiles(&["q05"]).await))).unwrap();
    let count = |a: &Analysis| a.trace.as_ref().unwrap().constraints.iter().filter(|c| c.fact.is_some()).count();
    assert!(count(&i) < count(&all), "nothing left out");
}

#[tokio::test]
async fn untraced_analysis_has_no_informed_trace() {
    let options = Options { foreign_keys: foreign_keys(), ..Default::default() };
    let a = cardinal::analyze_sql(&context(), &query("tpch", "q03"), options).await.unwrap();
    let i = a.with_facts(&Facts::new(derive_facts(&profiles(&["q03"]).await))).unwrap();
    assert!(i.trace.is_none());
    assert!(i.explain(&Bounds::default()).is_err());
}
