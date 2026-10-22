//! The trace of an analysis informed by facts: a constraint for each claim a
//! fact gave, with the facts it is read from, and proofs whose cores name
//! the facts a tighter bound needs.

mod fixtures;

use cardinal::facts::{Context, Fact, FactKind, FactSet, derive_facts};
use cardinal::observed::ObservedPlan;
use cardinal::{Analysis, FactMode, Informed, Options, ProofStatus};
use fixtures::{context, foreign_keys, plans, query};

/// TPC-H query `name` as DataFusion plans it, traced.
async fn traced(name: &str) -> Analysis {
    let options = Options { trace: true, selectivity: true, foreign_keys: foreign_keys(), ..Default::default() };
    cardinal::analyze_sql_with(&context(), &query("tpch", name), options).await.unwrap()
}

/// The profiles of TPC-H queries `names`.
async fn profiles(names: &[&str]) -> Vec<ObservedPlan> {
    plans("tpch").await.into_iter().filter(|p| names.contains(&p.name.as_str())).collect()
}

fn check_trace(a: &Analysis, i: &Informed) {
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
        assert!(c.source.contains("informed.rs:"), "{}", c.source);
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
    let facts = derive_facts(&profiles(&["q05"]).await);
    for mode in [FactMode::Ratios, FactMode::Pinned] {
        let i = a.with_facts(&facts, mode).unwrap();
        check_trace(&a, &i);
        if mode == FactMode::Pinned {
            let t = i.trace.as_ref().unwrap();
            let pinned = t.constraints.iter().filter_map(|c| c.fact.as_ref()).find(|f| f.source == "pinned rows");
            let pinned = pinned.expect("a pinned row count");
            assert!(pinned.facts[0].origins.iter().any(|o| o.starts_with("q05#")), "{pinned:?}");
        }
    }
}

#[tokio::test]
async fn tighter_bound_needs_facts() {
    let a = traced("q03").await;
    let facts = derive_facts(&profiles(&["q03"]).await);
    let i = a.with_facts(&facts, FactMode::Pinned).unwrap();
    let bounds = i.bounds().unwrap();
    assert_ne!(Some(&bounds), a.bounds().ok().as_ref(), "the facts tighten nothing");
    let t = i.trace.as_ref().unwrap();
    let with = i.explain(Some(&bounds)).unwrap();
    let without = i.explain_without_facts(Some(&bounds)).unwrap();
    assert_eq!(with.len(), without.len());
    let needs_facts = with.iter().zip(&without).any(|(w, wo)| {
        w.status == ProofStatus::Proven
            && w.core.iter().any(|&c| t.constraints[c].fact.is_some())
            && wo.status != ProofStatus::Proven
    });
    assert!(needs_facts, "no bound needs the facts: {with:#?}");
}

#[tokio::test]
async fn contradicting_facts_are_rejected_not_traced() {
    let a = traced("q05").await;
    // q05's facts, but with no suppliers: the joins with them can't then
    // have the rows the profile shows.
    let mut facts = FactSet::default();
    let supplier = FactKind::Cardinality(Context::table("supplier")).canonical();
    for f in derive_facts(&profiles(&["q05"]).await).iter() {
        let value = if f.kind == supplier { cardinal::facts::Ratio::int(0) } else { f.value };
        facts.insert(Fact { value, ..f.clone() });
    }
    let i = a.with_facts(&facts, FactMode::Pinned).unwrap();
    assert!(!i.rejected.is_empty(), "nothing rejected: {i} pinned {:?} unchecked {:?}", i.pinned, i.unchecked);
    // A rejected floor is not among the constraints.
    let t = i.trace.as_ref().unwrap();
    let (var, why) = i.rejected.iter().find(|(_, why)| why.starts_with("at least")).expect("a rejected floor");
    let floor = t.constraints.iter().find(|c| {
        c.fact.as_ref().is_some_and(|f| f.source == "floor") && c.vars == [var.clone()]
    });
    assert!(floor.is_none(), "{var} rejected ({why}) yet floored by c{}", floor.unwrap().id);
    check_trace(&a, &i);
}

#[tokio::test]
async fn untraced_analysis_has_no_informed_trace() {
    let options = Options { selectivity: true, foreign_keys: foreign_keys(), ..Default::default() };
    let a = cardinal::analyze_sql_with(&context(), &query("tpch", "q03"), options).await.unwrap();
    let i = a.with_facts(&derive_facts(&profiles(&["q03"]).await), FactMode::Ratios).unwrap();
    assert!(i.trace.is_none());
    assert!(i.explain(None).is_err());
    assert!(i.report().matched.iter().all(|m| m.facts.iter().all(|f| f.origins.is_empty())));
}
