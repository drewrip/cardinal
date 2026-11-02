//! The trace of an analysis: every constraint with its node and source line,
//! and minimal sets of constraints that prove each bound.

mod common;

use cardinal::{Analysis, Bounds, Options, Proof, ProofStatus, Trace, analyze_sql};
use datafusion::prelude::SessionContext;

/// `users(id PRIMARY KEY, age)` and `orders(id PRIMARY KEY, user_id)`,
/// declared in SQL.
async fn shop() -> SessionContext {
    let ctx = SessionContext::new();
    for ddl in [
        "CREATE TABLE users (id BIGINT PRIMARY KEY, age BIGINT)",
        "CREATE TABLE orders (id BIGINT PRIMARY KEY, user_id BIGINT)",
    ] {
        ctx.sql(ddl).await.unwrap();
    }
    ctx
}

async fn traced(sql: &str) -> Analysis {
    let options = Options { trace: true, ..Default::default() };
    analyze_sql(&shop().await, sql, options).await.unwrap()
}

fn node_of<'a>(t: &'a Trace, kind: &str) -> usize {
    t.nodes.iter().position(|n| n.label.starts_with(kind)).unwrap_or_else(|| panic!("no {kind} in {t:#?}"))
}

#[tokio::test]
async fn untraced_analysis_has_no_trace() {
    let a = analyze_sql(&shop().await, "SELECT * FROM users", Options::default()).await.unwrap();
    assert!(a.trace.is_none());
    assert!(a.explain(&Bounds::default()).is_err());
}

#[tokio::test]
async fn every_constraint_has_a_source_and_every_node_constraints() {
    let a = traced("SELECT u.age, count(*) FROM users u JOIN orders o ON u.id = o.user_id WHERE u.age > 30 GROUP BY u.age").await;
    let t = a.trace.as_ref().unwrap();
    for c in &t.constraints {
        assert!(c.node.is_none_or(|n| n < t.nodes.len()), "{c:?}");
        let sources = ["src/analysis.rs:", "src/axioms.rs:", "src/keys.rs:", "src/rules/"];
        assert!(sources.iter().any(|s| c.source.contains(s)), "{c:?}");
        assert!(!c.function.is_empty(), "{c:?}");
        assert!(!c.vars.is_empty(), "{c:?}");
    }
    for n in &t.nodes {
        assert!(t.of_node(n.id).next().is_some(), "{n:?} has no constraints");
    }
    assert_eq!(t.root, t.nodes.last().unwrap().var);
}

#[tokio::test]
async fn smt2_loads_back_with_every_constraint() {
    let a = traced("SELECT * FROM users WHERE age > 30").await;
    let t = a.trace.as_ref().unwrap();
    let solver = z3::Solver::new();
    solver.from_string(t.to_smt2());
    assert_eq!(solver.get_assertions().len(), t.constraints.len());
}

#[tokio::test]
async fn trace_round_trips_through_json() {
    let a = traced("SELECT DISTINCT age FROM users").await;
    let t = a.trace.unwrap();
    let back: Trace = serde_json::from_str(&serde_json::to_string(&t).unwrap()).unwrap();
    assert_eq!(back, t);
}

/// `sql`, traced, with `users` holding 100 rows and `orders` 300.
async fn traced_sized(sql: &str) -> Analysis {
    let a = traced(sql).await;
    a.with_facts(&common::table_sizes(&[("users", 100), ("orders", 300)])).unwrap()
}

/// Whether `proof`'s core has a constraint that a fact gave.
fn uses_a_fact(t: &Trace, proof: &Proof) -> bool {
    proof.core.iter().any(|&c| t.constraints[c].fact.is_some())
}

#[tokio::test]
async fn filter_bound_is_proven_by_the_filter_and_the_tables_size() {
    let a = traced_sized("SELECT * FROM users WHERE age > 30").await;
    let bounds = a.bounds().unwrap();
    assert_eq!(bounds.upper, Some(100));
    let proofs = a.explain(&bounds).unwrap();
    let t = a.trace.as_ref().unwrap();
    let filter = node_of(t, "Filter");
    let upper = proofs.iter().find(|p| p.name == "upper").unwrap();
    assert_eq!(upper.claim, "X <= 100");
    assert_eq!(upper.status, ProofStatus::Proven);
    assert!(upper.core.iter().any(|&c| t.constraints[c].node == Some(filter)), "{upper:?}");
    assert!(uses_a_fact(t, upper), "{upper:?}");
}

#[tokio::test]
async fn self_join_bound_needs_the_join() {
    let a = traced_sized("SELECT * FROM users a JOIN users b ON a.id = b.id").await;
    let bounds = a.bounds().unwrap();
    assert_eq!(bounds.upper, Some(100));
    let proofs = a.explain(&bounds).unwrap();
    let upper = proofs.iter().find(|p| p.name == "upper").unwrap();
    assert_eq!(upper.status, ProofStatus::Proven);
    let t = a.trace.as_ref().unwrap();
    let join = node_of(t, "Inner Join");
    assert!(upper.core.iter().any(|&c| t.constraints[c].node == Some(join)), "{upper:?}");
}

#[tokio::test]
async fn lower_bound_is_proven_too() {
    let a = traced_sized("SELECT * FROM users u LEFT JOIN orders o ON u.id = o.user_id").await;
    let bounds = a.bounds().unwrap();
    assert_eq!(bounds.lower, 100);
    let proofs = a.explain(&bounds).unwrap();
    let lower = proofs.iter().find(|p| p.name == "lower").unwrap();
    assert_eq!(lower.claim, "X >= 100");
    assert_eq!(lower.status, ProofStatus::Proven);
    assert!(uses_a_fact(a.trace.as_ref().unwrap(), lower), "{lower:?}");
}

#[tokio::test]
async fn unbounded_has_nothing_to_prove() {
    let a = traced("SELECT * FROM users, orders").await;
    let bounds = a.bounds().unwrap();
    assert_eq!(bounds.upper, None);
    assert!(a.explain(&bounds).unwrap().is_empty());
}
