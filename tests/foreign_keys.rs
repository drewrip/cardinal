//! Declared foreign keys: a join on exactly one, against every row of the
//! table it references, keeps each referencing row exactly once.

mod common;
mod fixtures;

use cardinal::{Analysis, Bounds, ForeignKey, Options, analyze_observed, analyze_sql};
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
    let options = Options { foreign_keys, ..Default::default() };
    let a = analyze_sql(&ctx, sql, options).await.unwrap();
    let v = a.validate(&ctx).await.unwrap();
    assert_eq!(v.violation, None, "{sql}");
    a
}

/// Sizes for the tables, all different (any satisfy the keys), so that a
/// bound shows which table it comes from.
const SIZES: &[(&str, u64)] = &[("customers", 40), ("orders", 60), ("parts", 20), ("partsupp", 30), ("items", 100)];

/// The output's bounds with the tables held to [`SIZES`].
async fn sized(sql: &str, declared: bool) -> Bounds {
    let b = common::sized(&analyze(sql, declared).await, SIZES);
    println!("{sql}\n  {b}");
    b
}

fn range(lo: u64, hi: u64) -> Bounds {
    Bounds { lower: lo, upper: Some(hi) }
}

fn at_most(hi: u64) -> Bounds {
    range(0, hi)
}

fn exactly(n: u64) -> Bounds {
    range(n, n)
}

#[tokio::test]
async fn join_keeps_every_referencing_row() {
    let sql = "SELECT * FROM orders o JOIN customers c ON o.cust = c.id";
    assert_eq!(sized(sql, true).await, exactly(60));
    // Without the key, each order matches at most one customer only if `id`
    // is unique, which nothing says.
    assert_eq!(sized(sql, false).await, at_most(60 * 40));
}

#[tokio::test]
async fn filters_on_the_referencing_side_keep_it() {
    let sql = "SELECT * FROM orders o JOIN customers c ON o.cust = c.id WHERE o.amount > 10";
    assert_eq!(sized(sql, true).await, at_most(60));
}

#[tokio::test]
async fn filters_on_the_referenced_side_do_not() {
    // Not every order's customer is in region a.
    let sql = "SELECT * FROM orders o JOIN customers c ON o.cust = c.id WHERE c.region = 'a'";
    assert_eq!(sized(sql, true).await, at_most(60));
}

#[tokio::test]
async fn other_conditions_do_not() {
    // The join's matches are filtered again.
    let sql = "SELECT * FROM orders o JOIN customers c ON o.cust = c.id AND o.id > c.id";
    assert_eq!(sized(sql, true).await, at_most(60));
}

#[tokio::test]
async fn composite_keys_need_every_column() {
    let sql = "SELECT * FROM items i JOIN partsupp ps ON i.part = ps.part AND i.supp = ps.supp";
    assert_eq!(sized(sql, true).await, exactly(100));
    // Each item's part has two partsupp rows.
    let sql = "SELECT * FROM items i JOIN partsupp ps ON i.part = ps.part";
    assert_eq!(sized(sql, true).await, at_most(100 * 30));
    // Columns paired the wrong way round: not the foreign key, so not every
    // item matches, but `partsupp`'s referenced columns are still unique,
    // so none matches twice.
    let sql = "SELECT * FROM items i JOIN partsupp ps ON i.part = ps.supp AND i.supp = ps.part";
    assert_eq!(sized(sql, true).await, at_most(100));
}

#[tokio::test]
async fn keys_reach_through_joins_and_groups() {
    let sql = "SELECT * FROM items i JOIN orders o ON i.order_id = o.id JOIN customers c ON o.cust = c.id";
    assert_eq!(sized(sql, true).await, exactly(100));
    // One row per customer with an order.
    let sql = "SELECT * FROM (SELECT cust, count(*) AS n FROM orders GROUP BY cust) g JOIN customers c ON g.cust = c.id";
    assert_eq!(sized(sql, true).await, range(1, 40));
}

#[tokio::test]
async fn semi_joins_keep_every_row_and_anti_joins_none() {
    let sql = "SELECT * FROM orders WHERE cust IN (SELECT id FROM customers)";
    assert_eq!(sized(sql, true).await, exactly(60));
    let sql = "SELECT * FROM orders o WHERE NOT EXISTS (SELECT 1 FROM customers c WHERE c.id = o.cust)";
    assert_eq!(sized(sql, true).await, exactly(0));
}

#[tokio::test]
async fn outer_joins_keep_the_inner_part() {
    // Every order matches its customer once, so the inner join has |orders|
    // rows; at least one customer has one, and the rest may have none.
    let sql = "SELECT * FROM customers c LEFT JOIN orders o ON o.cust = c.id";
    assert_eq!(sized(sql, true).await, range(60, 60 + 39));
    // Every customer, and at most every order.
    let sql = "SELECT * FROM customers c LEFT JOIN orders o ON o.cust = c.id AND o.amount > 10";
    assert_eq!(sized(sql, true).await, range(40, 60 + 39));
    // From the referencing side, every row matches: a left join keeps them.
    let sql = "SELECT * FROM orders o FULL JOIN customers c ON o.cust = c.id";
    assert_eq!(sized(sql, true).await, range(60, 60 + 39));
}

#[tokio::test]
async fn widening_casts_keep_the_key() {
    // Each side's key widened to a decimal that holds every BIGINT: still
    // one value per key.
    let sql = "SELECT * FROM orders o JOIN customers c ON CAST(o.cust AS DECIMAL(20, 0)) = CAST(c.id AS DECIMAL(20, 0))";
    assert_eq!(sized(sql, true).await, exactly(60));
    let sql = "SELECT * FROM orders o JOIN customers c ON CAST(o.cust AS DECIMAL(20, 0)) = CAST(c.id AS DECIMAL(20, 0)) WHERE o.amount > 10";
    assert_eq!(sized(sql, true).await, at_most(60));
}

/// A foreign key references a key, so the referenced columns are unique
/// even where their table is filtered: TPC-H q16 as DuckDB planned it, with
/// only the foreign keys declared, joins `partsupp` to the parts of some
/// brands, types and sizes on `p_partkey`, matching each row at most once.
#[tokio::test]
async fn referenced_columns_are_unique() {
    let catalog = fixtures::catalog().await;
    let plan = fixtures::plans("tpch").await.into_iter().find(|p| p.name == "q16").unwrap();
    let analyze = |foreign_keys| {
        let options = Options { foreign_keys, ..Default::default() };
        analyze_observed(&catalog, &plan, options).unwrap()
    };
    let declared = analyze(fixtures::foreign_keys());
    assert!(declared.constraints().contains("InnerKeyJoin"), "{}", declared.plan);
    let undeclared = analyze(vec![]);
    assert!(!undeclared.constraints().contains("InnerKeyJoin"), "{}", undeclared.plan);
}
