//! The trace of an analysis: every constraint with its node and source line,
//! and minimal sets of constraints that prove each bound.

use cardinal::{Analysis, Options, ProofStatus, Trace, analyze_sql_with};
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
    analyze_sql_with(&shop().await, sql, options).await.unwrap()
}

fn node_of<'a>(t: &'a Trace, kind: &str) -> usize {
    t.nodes.iter().position(|n| n.label.starts_with(kind)).unwrap_or_else(|| panic!("no {kind} in {t:#?}"))
}

#[tokio::test]
async fn untraced_analysis_has_no_trace() {
    let a = analyze_sql_with(&shop().await, "SELECT * FROM users", Options::default()).await.unwrap();
    assert!(a.trace.is_none());
    assert!(a.explain(None).is_err());
}

#[tokio::test]
async fn every_constraint_has_a_source_and_every_node_constraints() {
    let a = traced("SELECT u.age, count(*) FROM users u JOIN orders o ON u.id = o.user_id WHERE u.age > 30 GROUP BY u.age").await;
    let t = a.trace.as_ref().unwrap();
    for c in &t.constraints {
        assert!(c.node.is_none_or(|n| n < t.nodes.len()), "{c:?}");
        assert!(c.source.contains("analyzer.rs:"), "{c:?}");
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

#[tokio::test]
async fn filter_bound_is_proven_by_the_filter() {
    let a = traced("SELECT * FROM users WHERE age > 30").await;
    let bounds = a.bounds().unwrap();
    let proofs = a.explain(Some(&bounds)).unwrap();
    let t = a.trace.as_ref().unwrap();
    let filter = node_of(t, "Filter");
    let verdict = proofs.iter().find(|p| p.name == "verdict").unwrap();
    assert_eq!(verdict.status, ProofStatus::Proven);
    assert!(verdict.core.iter().any(|&c| t.constraints[c].node == Some(filter)), "{verdict:?}");
    let table = proofs.iter().find(|p| p.name == "table:users").unwrap();
    assert_eq!(table.status, ProofStatus::Proven);
    assert!(!table.core.is_empty());
}

#[tokio::test]
async fn self_join_halving_needs_the_key() {
    let a = traced("SELECT * FROM users a JOIN users b ON a.id = b.id").await;
    let bounds = a.bounds().unwrap();
    assert_eq!(bounds.to_string(), "X <= |users|; X <= 1/2·Σ");
    let proofs = a.explain(Some(&bounds)).unwrap();
    let sum = proofs.iter().find(|p| p.name == "sum").unwrap();
    assert_eq!(sum.claim, "X <= 1/2·Σ");
    assert_eq!(sum.status, ProofStatus::Proven);
    let t = a.trace.as_ref().unwrap();
    let join = node_of(t, "Inner Join");
    assert!(sum.core.iter().any(|&c| t.constraints[c].node == Some(join)), "{sum:?}");
}

#[tokio::test]
async fn cross_join_does_not_reduce() {
    let a = traced("SELECT * FROM users, orders").await;
    let proofs = a.explain(None).unwrap();
    assert_eq!(proofs.len(), 1);
    assert_eq!(proofs[0].status, ProofStatus::Refuted);
    assert!(proofs[0].core.is_empty());
}
