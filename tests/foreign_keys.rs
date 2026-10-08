//! Declared foreign keys: a join on exactly one, against every row of the
//! table it references, keeps each referencing row exactly once.

use cardinal::{Analysis, ForeignKey, Options, analyze_sql_with};
use datafusion::prelude::SessionContext;

/// Data satisfying every key of `keys()`.
async fn context() -> SessionContext {
    let ctx = SessionContext::new();
    for sql in [
        "CREATE TABLE customers AS SELECT * FROM (VALUES (1, 'a'), (2, 'a'), (3, 'b'), (4, 'b')) AS t(id, region)",
        "CREATE TABLE orders AS SELECT * FROM (VALUES (1, 1, 5), (2, 1, 20), (3, 2, 7), (4, 3, 30), (5, 3, 1), (6, 4, 12))
         AS t(id, cust, amount)",
        "CREATE TABLE parts AS SELECT * FROM (VALUES (1), (2), (3)) AS t(id)",
        "CREATE TABLE partsupp AS SELECT * FROM (VALUES (1, 1), (1, 2), (2, 1), (3, 2)) AS t(part, supp)",
        "CREATE TABLE items AS SELECT * FROM (VALUES (1, 1, 1), (1, 1, 2), (2, 2, 1), (3, 3, 2), (3, 1, 1), (6, 1, 2))
         AS t(order_id, part, supp)",
    ] {
        ctx.sql(sql).await.unwrap().collect().await.unwrap();
    }
    ctx
}

fn keys() -> Vec<ForeignKey> {
    vec![
        ForeignKey::new("orders", &["cust"], "customers", &["id"]),
        ForeignKey::new("items", &["order_id"], "orders", &["id"]),
        ForeignKey::new("items", &["part", "supp"], "partsupp", &["part", "supp"]),
        ForeignKey::new("partsupp", &["part"], "parts", &["id"]),
    ]
}

/// `sql` analyzed with the keys (or without), checked against the data.
async fn analyze(sql: &str, declared: bool) -> Analysis {
    let ctx = context().await;
    let foreign_keys = if declared { keys() } else { vec![] };
    let options = Options { selectivity: true, foreign_keys, ..Default::default() };
    let a = analyze_sql_with(&ctx, sql, options).await.unwrap();
    let v = a.validate(&ctx).await.unwrap();
    assert_eq!(v.violation, None, "{sql}");
    assert_eq!(v.selectivity.unwrap().violation, None, "{sql}");
    a
}

/// The output's formula and bounds.
async fn formula(sql: &str, declared: bool) -> (String, String) {
    let a = analyze(sql, declared).await;
    let formula = a.selectivity.as_ref().unwrap().output.to_string();
    let bounds = a.bounds().unwrap().to_string();
    println!("{sql}\n  X = {formula}; {bounds}");
    (formula, bounds)
}

#[tokio::test]
async fn join_keeps_every_referencing_row() {
    let sql = "SELECT * FROM orders o JOIN customers c ON o.cust = c.id";
    assert_eq!(formula(sql, true).await, ("|orders|".into(), "X = |orders|".into()));
    // Without the key, each order matches at most one customer only if `id`
    // is unique, which nothing says.
    assert_eq!(formula(sql, false).await.0, "s1·|orders|·|customers|");
}

#[tokio::test]
async fn filters_on_the_referencing_side_keep_it() {
    let sql = "SELECT * FROM orders o JOIN customers c ON o.cust = c.id WHERE o.amount > 10";
    assert_eq!(formula(sql, true).await.0, "s1·|orders|");
}

#[tokio::test]
async fn filters_on_the_referenced_side_do_not() {
    // Not every order's customer is in region a.
    let sql = "SELECT * FROM orders o JOIN customers c ON o.cust = c.id WHERE c.region = 'a'";
    assert_eq!(formula(sql, true).await.0, "s1·s2·|orders|·|customers|");
}

#[tokio::test]
async fn other_conditions_do_not() {
    // The join's matches are filtered again: its selectivity stays.
    let sql = "SELECT * FROM orders o JOIN customers c ON o.cust = c.id AND o.id > c.id";
    assert_eq!(formula(sql, true).await.0, "s1·s2·|orders|·|customers|");
}

#[tokio::test]
async fn composite_keys_need_every_column() {
    let sql = "SELECT * FROM items i JOIN partsupp ps ON i.part = ps.part AND i.supp = ps.supp";
    assert_eq!(formula(sql, true).await.1, "X = |items|");
    // Each item's part has two partsupp rows.
    let sql = "SELECT * FROM items i JOIN partsupp ps ON i.part = ps.part";
    assert_eq!(formula(sql, true).await.0, "s1·|items|·|partsupp|");
    // Columns paired the wrong way round.
    let sql = "SELECT * FROM items i JOIN partsupp ps ON i.part = ps.supp AND i.supp = ps.part";
    assert_eq!(formula(sql, true).await.0, "s1·|items|·|partsupp|");
}

#[tokio::test]
async fn keys_reach_through_joins_and_groups() {
    let sql = "SELECT * FROM items i JOIN orders o ON i.order_id = o.id JOIN customers c ON o.cust = c.id";
    assert_eq!(formula(sql, true).await, ("|items|".into(), "X = |items|".into()));
    let sql = "SELECT * FROM (SELECT cust, count(*) AS n FROM orders GROUP BY cust) g JOIN customers c ON g.cust = c.id";
    assert_eq!(formula(sql, true).await.0, "s1·|orders|");
}

#[tokio::test]
async fn semi_joins_keep_every_row_and_anti_joins_none() {
    let sql = "SELECT * FROM orders WHERE cust IN (SELECT id FROM customers)";
    assert_eq!(formula(sql, true).await, ("|orders|".into(), "X = |orders|".into()));
    let sql = "SELECT * FROM orders o WHERE NOT EXISTS (SELECT 1 FROM customers c WHERE c.id = o.cust)";
    assert_eq!(formula(sql, true).await, ("0".into(), "X <= 0".into()));
}

#[tokio::test]
async fn outer_joins_keep_the_inner_part() {
    // Every order matches its customer once, so the inner join has |orders|
    // rows; which customers have no order is still unknown.
    let sql = "SELECT * FROM customers c LEFT JOIN orders o ON o.cust = c.id";
    assert_eq!(formula(sql, true).await.0, "|orders| + (1 - s2)·|customers|");
    let sql = "SELECT * FROM customers c LEFT JOIN orders o ON o.cust = c.id AND o.amount > 10";
    assert_eq!(formula(sql, true).await.0, "s1·|orders| + (1 - s3)·|customers|");
    // From the referencing side, every row matches: a left join keeps them.
    let sql = "SELECT * FROM orders o FULL JOIN customers c ON o.cust = c.id";
    assert_eq!(formula(sql, true).await.0, "|orders| + (1 - s3)·|customers|");
}
