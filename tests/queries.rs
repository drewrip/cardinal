//! Test suite of simple to complex queries, each checked against the claim
//! `O_root <= Σ scans`. Tables may be empty. Refuted queries also check the
//! structure of the counterexample.

use std::collections::HashMap;
use std::sync::Arc;

use cardinal::{Analysis, Verdict, analyze_sql};
use datafusion::arrow::datatypes::{DataType, Field, Schema};
use datafusion::datasource::MemTable;
use datafusion::prelude::SessionContext;

fn table(ctx: &SessionContext, name: &str, cols: &[(&str, DataType)]) {
    let schema = Arc::new(Schema::new(
        cols.iter()
            .map(|(c, t)| Field::new(*c, t.clone(), true))
            .collect::<Vec<_>>(),
    ));
    let mem = MemTable::try_new(schema, vec![vec![]]).unwrap();
    ctx.register_table(name, Arc::new(mem)).unwrap();
}

fn setup() -> SessionContext {
    use DataType::*;
    let ctx = SessionContext::new();
    table(
        &ctx,
        "users",
        &[("id", Int64), ("name", Utf8), ("age", Int64)],
    );
    table(
        &ctx,
        "orders",
        &[("id", Int64), ("user_id", Int64), ("amount", Float64)],
    );
    table(&ctx, "products", &[("id", Int64), ("price", Float64)]);
    table(
        &ctx,
        "order_items",
        &[("order_id", Int64), ("product_id", Int64), ("qty", Int64)],
    );
    ctx
}

async fn run(sql: &str) -> Analysis {
    let a = analyze_sql(&setup(), sql).await.unwrap();
    println!("== {sql}\n{}\n{}\n{:?}\n", a.plan, a.smtlib, a.verdict);
    a
}

/// Asserts the claim is Proven.
async fn proven(sql: &str) -> Analysis {
    let a = run(sql).await;
    assert_eq!(a.verdict, Verdict::Proven, "expected Proven for {sql}");
    a
}

/// Asserts the verdict is Refuted and returns the counterexample model.
async fn refuted(sql: &str) -> (Analysis, HashMap<String, i64>) {
    let a = run(sql).await;
    match a.verdict.clone() {
        Verdict::Refuted(m) => {
            // Sanity-check the counterexample actually violates the claim.
            let total: i64 = a.scans.iter().map(|(s, _)| m[s]).sum();
            assert!(m[&a.root] > total, "model does not refute the claim");
            (a, m)
        }
        v => panic!("expected Refuted for {sql}, got {v:?}"),
    }
}

fn has_op(a: &Analysis, kind: &str) -> bool {
    a.smtlib.contains(kind)
}

#[tokio::test]
async fn select_star() {
    let a = proven("SELECT * FROM users").await;
    assert_eq!(a.scans.len(), 1);
    assert_eq!(a.scans.len(), 1);
}

#[tokio::test]
async fn projection() {
    proven("SELECT name, age + 1 FROM users").await;
}

#[tokio::test]
async fn filter() {
    let a = proven("SELECT * FROM users WHERE age > 30").await;
    assert!(has_op(&a, "Filter"));
}

#[tokio::test]
async fn scalar_count() {
    let (a, m) = refuted("SELECT count(*) FROM users").await;
    assert_eq!(m[&a.root], 1);
    // 1 > users forces the table to be empty.
    assert_eq!(m["users"], 0);
}

#[tokio::test]
async fn group_by() {
    let a = proven("SELECT age, count(*) FROM users GROUP BY age").await;
    assert!(has_op(&a, "GroupBy"));
}

#[tokio::test]
async fn group_by_having() {
    let a =
        proven("SELECT user_id, sum(amount) FROM orders GROUP BY user_id HAVING sum(amount) > 100")
            .await;
    assert!(has_op(&a, "GroupBy") && has_op(&a, "Filter"));
}

#[tokio::test]
async fn distinct() {
    proven("SELECT DISTINCT age FROM users").await;
}

#[tokio::test]
async fn order_by_limit() {
    let a = proven("SELECT * FROM users ORDER BY age LIMIT 10").await;
    assert!(a.smtlib.contains(&format!("(<= {} 10)", a.root)));
}

#[tokio::test]
async fn limit_offset() {
    let a = proven("SELECT * FROM users LIMIT 5 OFFSET 20").await;
    assert!(a.smtlib.contains(&format!("(<= {} 5)", a.root)));
}

#[tokio::test]
async fn equijoin_two_tables() {
    let a = proven("SELECT * FROM users u JOIN orders o ON u.id = o.user_id").await;
    assert!(has_op(&a, "InnerEquiJoin"));
    assert_eq!(a.scans.len(), 2);
}

#[tokio::test]
async fn equijoin_three_tables() {
    let a = proven(
        "SELECT * FROM orders o
         JOIN order_items oi ON o.id = oi.order_id
         JOIN products p ON oi.product_id = p.id",
    )
    .await;
    assert_eq!(a.scans.len(), 3);
}

#[tokio::test]
async fn implicit_join_becomes_equijoin() {
    let a = proven("SELECT * FROM users u, orders o WHERE u.id = o.user_id").await;
    assert!(has_op(&a, "InnerEquiJoin"));
}

#[tokio::test]
async fn self_join_counts_each_scan() {
    let a = proven("SELECT * FROM users a JOIN users b ON a.id = b.id").await;
    assert_eq!(a.scans.len(), 2);
    assert!(a.scans.iter().all(|(_, t)| t == "users"));
}

#[tokio::test]
async fn non_equijoin() {
    let (a, _) = refuted("SELECT * FROM users u JOIN orders o ON u.age < o.amount").await;
    assert!(has_op(&a, "InnerThetaJoin"));
}

#[tokio::test]
async fn cross_join() {
    let (a, m) = refuted("SELECT * FROM users CROSS JOIN products").await;
    assert!(has_op(&a, "InnerCrossJoin"));
    assert_eq!(m[&a.root], m["users"] * m["products"]);
}

#[tokio::test]
async fn left_join() {
    let a = proven("SELECT * FROM users u LEFT JOIN orders o ON u.id = o.user_id").await;
    assert!(has_op(&a, "LeftEquiJoin"));
}

#[tokio::test]
async fn full_join() {
    let a = proven("SELECT * FROM users u FULL JOIN orders o ON u.id = o.user_id").await;
    assert!(has_op(&a, "FullEquiJoin"));
}

#[tokio::test]
async fn union_all() {
    let a = proven("SELECT id FROM users UNION ALL SELECT id FROM products").await;
    assert!(has_op(&a, "Union"));
}

#[tokio::test]
async fn union_distinct() {
    let a = proven("SELECT id FROM users UNION SELECT id FROM products").await;
    assert!(has_op(&a, "Union"));
}

#[tokio::test]
async fn intersect() {
    let a = proven("SELECT id FROM users INTERSECT SELECT user_id FROM orders").await;
    assert!(has_op(&a, "LeftSemi"));
}

#[tokio::test]
async fn except() {
    let a = proven("SELECT id FROM users EXCEPT SELECT user_id FROM orders").await;
    assert!(has_op(&a, "LeftAnti"));
}

#[tokio::test]
async fn in_subquery() {
    let a = proven("SELECT * FROM users WHERE id IN (SELECT user_id FROM orders)").await;
    assert!(has_op(&a, "LeftSemi"));
}

#[tokio::test]
async fn not_exists() {
    let a = proven(
        "SELECT * FROM users u WHERE NOT EXISTS (SELECT 1 FROM orders o WHERE o.user_id = u.id)",
    )
    .await;
    assert!(has_op(&a, "LeftAnti"));
}

#[tokio::test]
async fn scalar_subquery() {
    let a = proven("SELECT * FROM orders WHERE amount > (SELECT avg(amount) FROM orders)").await;
    assert_eq!(a.scans.len(), 2);
}

#[tokio::test]
async fn cte() {
    proven(
        "WITH big AS (SELECT * FROM orders WHERE amount > 100)
         SELECT user_id, count(*) FROM big GROUP BY user_id",
    )
    .await;
}

#[tokio::test]
async fn values() {
    let (a, m) = refuted("SELECT * FROM (VALUES (1), (2), (3)) AS t(x)").await;
    assert!(a.scans.is_empty());
    assert_eq!(m[&a.root], 3);
}

#[tokio::test]
async fn window_function() {
    let a = proven("SELECT id, row_number() OVER (ORDER BY age) FROM users").await;
    assert!(has_op(&a, "Window"));
}

#[tokio::test]
async fn tpch_style() {
    let a = proven(
        "SELECT u.name, sum(oi.qty * p.price) AS revenue
         FROM users u
         JOIN orders o ON u.id = o.user_id
         JOIN order_items oi ON o.id = oi.order_id
         JOIN products p ON p.id = oi.product_id
         WHERE o.amount > 10 AND u.age BETWEEN 18 AND 65
         GROUP BY u.name
         ORDER BY revenue DESC
         LIMIT 20",
    )
    .await;
    assert_eq!(a.scans.len(), 4);
}
