//! Simple selectivities: shares of the rows of stored tables alone, seen
//! through views, CTEs and operators that keep their input's rows. Every
//! query is executed, and each simple selectivity's fact, counted over its
//! tables alone, must give the value the execution measured.

mod common;
mod fixtures;

use cardinal::facts::{FactKind, FactSet};
use cardinal::observed::Catalog;
use cardinal::{Analysis, ForeignKey, Options, SimpleKind, SimpleSelectivity, analyze_sql_with};
use datafusion::arrow::array::AsArray;
use datafusion::arrow::compute::cast;
use datafusion::arrow::datatypes::{DataType, Int64Type};
use datafusion::logical_expr::{JoinType, LogicalPlan};
use datafusion::prelude::{SessionContext, col, lit};

async fn context() -> SessionContext {
    let ctx = SessionContext::new();
    for sql in [
        "CREATE TABLE customers (id INT NOT NULL PRIMARY KEY, region VARCHAR)",
        "INSERT INTO customers VALUES (1, 'a'), (2, 'a'), (3, 'b'), (4, 'b')",
        "CREATE TABLE orders AS SELECT * FROM (VALUES (1, 1, 5), (2, 1, 20), (3, 2, 7), (4, 3, 30), (5, 3, 1), (6, 4, 12))
         AS t(id, cust, amount)",
        "CREATE TABLE items AS SELECT * FROM (VALUES (1, 1, 1), (1, 1, 2), (2, 2, 1), (3, 3, 2), (3, 1, 1), (6, 1, 2))
         AS t(order_id, part, supp)",
        "CREATE VIEW big_orders AS SELECT id, cust, amount FROM orders WHERE amount > 10",
        "CREATE VIEW all_orders AS SELECT id AS order_id, cust AS customer, amount FROM orders",
    ] {
        ctx.sql(sql).await.unwrap().collect().await.unwrap();
    }
    ctx
}

fn keys() -> Vec<ForeignKey> {
    vec![
        ForeignKey::new("orders", &["cust"], "customers", &["id"]),
        ForeignKey::new("items", &["order_id"], "orders", &["id"]),
    ]
}

/// The single count `sql` returns.
async fn count(ctx: &SessionContext, sql: &str) -> i64 {
    let batches = ctx.sql(sql).await.unwrap_or_else(|e| panic!("{e}\n{sql}")).collect().await.unwrap();
    let column = cast(batches[0].column(0), &DataType::Int64).unwrap();
    column.as_primitive::<Int64Type>().value(0)
}

/// Each required selectivity of `sql`, classified. Each simple one's fact,
/// counted over the tables alone, must give the value the execution
/// measured for it.
async fn simple(sql: &str) -> Vec<SimpleSelectivity> {
    checked(&context().await, sql, keys()).await
}

/// [`simple`] over `ctx`'s data, with `foreign_keys` declared.
async fn checked(ctx: &SessionContext, sql: &str, foreign_keys: Vec<ForeignKey>) -> Vec<SimpleSelectivity> {
    let options = Options { selectivity: true, foreign_keys, ..Default::default() };
    let a = analyze_sql_with(ctx, sql, options).await.unwrap();
    verified(ctx, &a, sql).await
}

/// The simple selectivities of `plan`, built over `ctx`'s tables, checked as
/// [`simple`] checks a query's.
async fn checked_plan(ctx: &SessionContext, plan: &LogicalPlan) -> Vec<SimpleSelectivity> {
    let options = Options { selectivity: true, foreign_keys: keys(), ..Default::default() };
    let a = cardinal::analyze_plan_with(plan, options);
    verified(ctx, &a, &plan.display_indent().to_string()).await
}

/// `a`'s simple selectivities, each checked against the execution of `sql`.
async fn verified(ctx: &SessionContext, a: &Analysis, sql: &str) -> Vec<SimpleSelectivity> {
    let v = a.validate(ctx).await.unwrap();
    assert_eq!(v.violation, None, "{sql}");
    let measured = v.selectivity.unwrap();
    assert_eq!(measured.violation, None, "{sql}");
    let out = a.simple_selectivities().unwrap();
    println!("{sql}\n  {}", a.selectivity.as_ref().unwrap());
    let catalog = Catalog::from_context(ctx).await.unwrap();
    for s in &out {
        println!("    {s}");
        let (Ok(simple), Some(value)) = (&s.simple, measured.values.get(&s.name)) else { continue };
        let counts = simple.fact.count_sql(&catalog, &FactSet::default()).expect("a table fact has a count");
        let n = count(ctx, &counts.value).await as f64;
        let of = match (&simple.fact, &counts.of) {
            (FactKind::Distinct { .. }, _) => count(ctx, &format!("SELECT count(*) FROM {}", simple.tables[0])).await,
            (_, Some(of)) => count(ctx, of).await,
            (_, None) => panic!("a share counts what it is a share of"),
        } as f64;
        if of > 0.0 {
            assert!((n / of - value).abs() < 1e-9, "{s}: the tables give {n}/{of}, the execution {value}\n{sql}");
        }
    }
    out
}

/// Each selectivity's kind and tables, or `None` if it is not simple.
fn shapes(out: &[SimpleSelectivity]) -> Vec<Option<(SimpleKind, Vec<&str>)>> {
    out.iter()
        .map(|s| s.simple.as_ref().ok().map(|s| (s.kind, s.tables.iter().map(String::as_str).collect())))
        .collect()
}

use SimpleKind::{Distinct, Filter};

#[tokio::test]
async fn views_and_ctes_read_as_their_tables() {
    for sql in [
        "SELECT * FROM orders WHERE amount > 10",
        "SELECT * FROM big_orders",
        "SELECT * FROM all_orders WHERE amount > 10",
        "WITH o AS (SELECT * FROM orders) SELECT * FROM o WHERE o.amount > 10",
    ] {
        let out = simple(sql).await;
        assert_eq!(shapes(&out), [Some((Filter, vec!["orders"]))], "{sql}");
        let simple = out[0].simple.as_ref().unwrap();
        assert_eq!(simple.fact.to_string(), "s(orders.amount > 10 | orders)");
        assert!(simple.proof.is_empty());
    }
}

#[tokio::test]
async fn chains_of_filters_are_simple() {
    let ctx = context().await;
    let orders = ctx.table("orders").await.unwrap();
    let plan = orders.filter(col("amount").gt(lit(10))).unwrap().filter(col("cust").eq(lit(1))).unwrap();
    let out = checked_plan(&ctx, &plan.into_unoptimized_plan()).await;
    assert_eq!(shapes(&out), [Some((Filter, vec!["orders"])), Some((Filter, vec!["orders"]))]);
    let facts: Vec<String> = out.iter().map(|s| s.simple.as_ref().unwrap().fact.to_string()).collect();
    assert_eq!(facts, ["s(orders.amount > 10 | orders)", "s(orders.cust = 1 | orders where orders.amount > 10)"]);

    // A join between the filters, though it keeps each item once.
    let items = ctx.table("items").await.unwrap().filter(col("part").gt(lit(1))).unwrap();
    let orders = ctx.table("orders").await.unwrap().select_columns(&["id"]).unwrap();
    let joined = items.join(orders, JoinType::Inner, &["order_id"], &["id"], None).unwrap();
    let plan = joined.filter(col("supp").eq(lit(1))).unwrap().into_unoptimized_plan();
    let out = checked_plan(&ctx, &plan).await;
    assert_eq!(shapes(&out).last(), Some(&None), "{}", out.last().unwrap());
}

#[tokio::test]
async fn a_filter_rechecking_a_parquet_scan_is_a_share_of_the_table() {
    let ctx = context().await;
    let dir = std::env::temp_dir().join(format!("cardinal-simple-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("orders.parquet");
    let copy = format!("COPY orders TO '{}' STORED AS PARQUET", path.display());
    ctx.sql(&copy).await.unwrap().collect().await.unwrap();
    ctx.register_parquet("orders_file", path.to_str().unwrap(), Default::default()).await.unwrap();
    // The scan takes the filter only to prune, and a filter above checks it.
    let out = checked(&ctx, "SELECT * FROM orders_file WHERE amount > 10", vec![]).await;
    assert_eq!(shapes(&out), [Some((Filter, vec!["orders_file"]))]);
    assert_eq!(out[0].simple.as_ref().unwrap().fact.to_string(), "s(orders_file.amount > 10 | orders_file)");
    std::fs::remove_dir_all(&dir).unwrap();
}

#[tokio::test]
async fn joins_and_semi_joins_are_not_simple() {
    for sql in [
        "SELECT * FROM orders o JOIN items i ON o.id = i.part",
        "SELECT * FROM all_orders o JOIN items i ON o.order_id = i.part",
        "SELECT * FROM orders o1 JOIN orders o2 ON o1.cust = o2.id",
    ] {
        let out = simple(sql).await;
        assert_eq!(shapes(&out), [None], "{sql}");
        assert!(out[0].simple.as_ref().unwrap_err().contains("join condition"), "{}", out[0]);
    }
    let sql = "SELECT * FROM orders o WHERE EXISTS (SELECT 1 FROM items i WHERE i.part = o.id)";
    let out = simple(sql).await;
    assert_eq!(shapes(&out), [None]);
    assert!(out[0].simple.as_ref().unwrap_err().contains("semi join"), "{}", out[0]);
}

#[tokio::test]
async fn shares_of_filtered_rows_are_not_simple() {
    // The join's share is of the big orders' pairs, not of every order's.
    for sql in [
        "SELECT * FROM big_orders o JOIN items i ON o.id = i.part",
        "SELECT * FROM orders o JOIN items i ON o.id = i.part AND o.amount > 10",
    ] {
        let out = simple(sql).await;
        assert_eq!(shapes(&out), [Some((Filter, vec!["orders"])), None], "{sql}");
        assert!(out[1].simple.as_ref().unwrap_err().contains("filtered"), "{}", out[1]);
    }
    let sql = "SELECT * FROM orders WHERE cust IN (SELECT id FROM customers WHERE region = 'a')";
    assert_eq!(shapes(&simple(sql).await), [None]);
}

#[tokio::test]
async fn distinct_counts() {
    for sql in ["SELECT cust, count(*) FROM orders GROUP BY cust", "SELECT DISTINCT customer FROM all_orders"] {
        let out = simple(sql).await;
        assert_eq!(shapes(&out), [Some((Distinct, vec!["orders"]))], "{sql}");
        assert_eq!(out[0].simple.as_ref().unwrap().fact.to_string(), "ndv(orders.cust | orders)");
    }
}

#[tokio::test]
async fn joins_on_foreign_keys_drop_what_nothing_reads() {
    // Each item has one order, and nothing above reads it.
    for (sql, shape) in [
        ("SELECT i.part, count(*) FROM items i JOIN orders o ON i.order_id = o.id GROUP BY i.part", (Distinct, vec!["items"])),
        (
            "SELECT DISTINCT x.supp FROM (SELECT i.* FROM items i JOIN orders o ON i.order_id = o.id) x",
            (Distinct, vec!["items"]),
        ),
    ] {
        let out = simple(sql).await;
        assert_eq!(shapes(&out), [Some(shape)], "{sql}");
        assert_eq!(out[0].simple.as_ref().unwrap().proof.len(), 1, "{}", out[0]);
    }
    // Every order has a customer: the semi join keeps every order.
    let sql = "SELECT cust, count(*) FROM (SELECT * FROM orders WHERE cust IN (SELECT id FROM customers)) o GROUP BY cust";
    let out = simple(sql).await;
    assert_eq!(shapes(&out), [Some((Distinct, vec!["orders"]))]);
    assert!(out[0].simple.as_ref().unwrap().proof[0].contains("keeps every row"), "{}", out[0]);
    // A filter on the order reads it.
    let sql = "SELECT * FROM items i JOIN orders o ON i.order_id = o.id WHERE o.amount > 10";
    assert_eq!(shapes(&simple(sql).await), [Some((Filter, vec!["orders"])), None]);
}

#[tokio::test]
async fn tpch() {
    let ctx = common::tpch_datasets().remove(1).context(true);
    let (mut simple, mut required) = (0, 0);
    for q in 1..=22 {
        let sql = std::fs::read_to_string(format!("{}/tests/tpch/q{q:02}.sql", env!("CARGO_MANIFEST_DIR"))).unwrap();
        let out = checked(&ctx, &sql, fixtures::foreign_keys()).await;
        simple += out.iter().filter(|s| s.simple.is_ok()).count();
        required += out.len();
    }
    println!("{simple} of {required} selectivities are simple");
}

#[tokio::test]
async fn duckdb_plans() {
    let catalog = fixtures::catalog().await;
    let options = || Options { selectivity: true, foreign_keys: fixtures::foreign_keys(), ..Default::default() };
    let (mut simple, mut required) = (0, 0);
    for plan in fixtures::plans("tpch").await {
        let a = cardinal::analyze_observed(&catalog, &plan, options()).unwrap();
        let out = a.simple_selectivities().unwrap();
        println!("{}\n  {}", plan.name, a.selectivity.as_ref().unwrap());
        for s in &out {
            println!("    {s}");
        }
        simple += out.iter().filter(|s| s.simple.is_ok()).count();
        required += out.len();
    }
    println!("{simple} of {required} selectivities are simple");
}

#[tokio::test]
async fn postgres_plans() {
    let catalog = fixtures::catalog().await;
    let options = || Options { selectivity: true, foreign_keys: fixtures::foreign_keys(), ..Default::default() };
    let (mut simple, mut required) = (0, 0);
    for plan in fixtures::pg_plans("tpch").await {
        let a = cardinal::analyze_observed(&catalog, &plan, options()).unwrap();
        let out = a.simple_selectivities().unwrap();
        println!("{}\n  {}", plan.name, a.selectivity.as_ref().unwrap());
        for s in &out {
            println!("    {s}");
        }
        simple += out.iter().filter(|s| s.simple.is_ok()).count();
        required += out.len();
    }
    println!("{simple} of {required} selectivities are simple");
}

#[tokio::test]
async fn a_quoted_date_part_reads_bare() {
    let ctx = context().await;
    let sql = "CREATE TABLE visits AS SELECT * FROM (VALUES (1, DATE '2024-01-05'), (2, DATE '2024-01-20'), (3, DATE '2024-03-02')) AS t(id, day)";
    ctx.sql(sql).await.unwrap().collect().await.unwrap();
    for (sql, part) in [
        ("SELECT extract('month' FROM day) AS m, count(*) FROM visits GROUP BY 1", "month"),
        ("SELECT extract(month FROM day) AS m, count(*) FROM visits GROUP BY 1", "MONTH"),
    ] {
        let out = checked(&ctx, sql, vec![]).await;
        assert_eq!(shapes(&out), [Some((Distinct, vec!["visits"]))], "{sql}");
        assert_eq!(out[0].simple.as_ref().unwrap().fact.to_string(), format!("ndv(date_part('{part}', visits.\"day\") | visits)"));
    }
}
