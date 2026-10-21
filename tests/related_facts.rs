//! Facts about rows related to an operator's, but not its own: a count of
//! the same join over a filtered input is a lower bound on the join, since
//! dropping a filter only adds rows, and a count of wider rows an upper
//! bound. A column's distinct count over a table bounds every GROUP BY on
//! it above that table, through the constraints.
//!
//! Each fact is a count of the data, taken with SQL, so every bound must
//! hold of the query's true row count.

use std::collections::BTreeSet;

use cardinal::facts::{Context, Fact, FactKind, FactSet, Origin, Ratio, Term};
use cardinal::{Analysis, FactMode, Informed, Options, analyze_sql_with};
use datafusion::arrow::array::AsArray;
use datafusion::arrow::datatypes::Int64Type;
use datafusion::common::JoinType;
use datafusion::logical_expr::Expr;
use datafusion::prelude::{SessionContext, col, lit};

async fn context() -> SessionContext {
    let ctx = SessionContext::new();
    for sql in [
        "CREATE TABLE products (id INT NOT NULL PRIMARY KEY, category INT)",
        "INSERT INTO products VALUES (1, 7), (2, 7), (3, 11), (4, 12), (5, 3), (6, 3)",
        "CREATE TABLE sales (product_id INT, store INT)",
        "INSERT INTO sales VALUES (1, 1), (1, 2), (2, 1), (3, 1), (3, 2), (3, 2), (4, 1), (5, 2), (5, 1), (7, 1)",
        "CREATE TABLE reviews (emp_id INT, score INT)",
        "INSERT INTO reviews VALUES (1, 3), (1, NULL), (2, 4), (2, 5), (3, NULL), (4, 1), (4, 2), (4, 3), (5, 5), (6, NULL)",
    ] {
        ctx.sql(sql).await.unwrap().collect().await.unwrap();
    }
    ctx
}

/// The rows `sql` returns.
async fn count(sql: &str) -> u64 {
    let ctx = context().await;
    let batches = ctx.sql(&format!("SELECT count(*) FROM ({sql})")).await.unwrap().collect().await.unwrap();
    batches[0].column(0).as_primitive::<Int64Type>().value(0) as u64
}

async fn analyze(sql: &str) -> Analysis {
    let ctx = context().await;
    let options = Options { selectivity: true, ..Default::default() };
    analyze_sql_with(&ctx, sql, options).await.unwrap()
}

fn terms(exprs: impl IntoIterator<Item = Expr>) -> BTreeSet<Term> {
    exprs.into_iter().map(Term::new).collect()
}

fn t(name: &str) -> Context {
    Context::table(name)
}

fn on() -> BTreeSet<Term> {
    terms([col("products.id").eq(col("sales.product_id"))])
}

/// `products ⋈ sales` on the product.
fn joined() -> Context {
    t("products").cross(&t("sales")).unwrap().filter(&on())
}

fn category(c: i32) -> BTreeSet<Term> {
    terms([col("products.category").eq(lit(c))])
}

/// Facts `|c| = n`, each counted by its SQL.
async fn counted(facts: &[(Context, &str)]) -> FactSet {
    let mut set = FactSet::default();
    for (c, sql) in facts {
        let value = Ratio::int(count(sql).await);
        set.insert(Fact { kind: FactKind::Cardinality(c.canonical()), value, origins: vec![Origin::Counted] });
    }
    set
}

/// Facts `ndv(column | table)`, each counted by SQL.
async fn distinct(set: &mut FactSet, columns: &[(&str, &str)]) {
    for (table, column) in columns {
        let kind = FactKind::Distinct { keys: terms([col(format!("{table}.{column}"))]), over: t(table) };
        let value = Ratio::int(count(&format!("SELECT DISTINCT {column} FROM {table}")).await);
        set.insert(Fact { kind: kind.canonical(), value, origins: vec![Origin::Counted] });
    }
}

/// Facts `|table|` for each of `tables`.
async fn sizes(tables: &[&str]) -> FactSet {
    let facts: Vec<(Context, String)> = tables.iter().map(|n| (t(n), format!("SELECT * FROM {n}"))).collect();
    let facts: Vec<(Context, &str)> = facts.iter().map(|(c, sql)| (c.clone(), sql.as_str())).collect();
    counted(&facts).await
}

/// `sql` informed by `facts`; checks its true row count lies in the range.
async fn informed(sql: &str, facts: &FactSet, mode: FactMode) -> (Informed, (u64, Option<u64>)) {
    let i = analyze(sql).await.with_facts(facts, mode).unwrap();
    let range = i.range().unwrap();
    let rows = count(sql).await;
    println!("{sql}\n  {range:?}, {rows} rows\n  {i}");
    assert!(range.0 <= rows && range.1.is_none_or(|hi| rows <= hi), "{sql}: {rows} outside {range:?}");
    (i, range)
}

const JOIN: &str = "SELECT * FROM sales s JOIN products p ON s.product_id = p.id";
const SEVEN: &str = "SELECT * FROM sales s JOIN products p ON s.product_id = p.id WHERE p.category = 7";
const ELEVEN: &str = "SELECT * FROM sales s JOIN products p ON s.product_id = p.id WHERE p.category IN (11, 12)";

#[tokio::test]
async fn contexts_built_here_are_the_analysis_own() {
    // The join's own count pins it: the contexts below name its rows.
    let facts = counted(&[(joined(), JOIN)]).await;
    let rows = count(JOIN).await;
    assert_eq!(informed(JOIN, &facts, FactMode::Pinned).await.1, (rows, Some(rows)));
}

#[tokio::test]
async fn filtered_joins_bound_the_join_below() {
    let eleven = terms([col("products.category").in_list(vec![lit(11), lit(12)], false)]);
    let facts = counted(&[(joined().filter(&category(7)), SEVEN), (joined().filter(&eleven), ELEVEN)]).await;
    let largest = count(SEVEN).await.max(count(ELEVEN).await);
    let (_, unknown) = informed(JOIN, &FactSet::default(), FactMode::Ratios).await;
    for mode in [FactMode::Ratios, FactMode::Pinned] {
        let (i, range) = informed(JOIN, &facts, mode).await;
        assert_eq!(range.0, largest, "{i}");
        // The upper bound is the same as without the facts.
        assert_eq!(range.1, unknown.1);
    }
}

#[tokio::test]
async fn a_filter_below_the_join_bounds_it_too() {
    let below = t("products").filter(&category(7)).cross(&t("sales")).unwrap().filter(&on());
    let sql = "SELECT * FROM sales s JOIN (SELECT * FROM products WHERE category = 7) p ON s.product_id = p.id";
    let facts = counted(&[(below, sql)]).await;
    assert_eq!(informed(JOIN, &facts, FactMode::Ratios).await.1.0, count(sql).await);
}

#[tokio::test]
async fn semi_joins_bound_below_with_a_narrower_other_side() {
    let semi = |other: Context| Context::join(JoinType::LeftSemi, on(), t("sales"), other);
    let sql = "SELECT * FROM sales WHERE product_id IN (SELECT id FROM products WHERE category = 7)";
    let facts = counted(&[(semi(t("products").filter(&category(7))), sql)]).await;
    let all = "SELECT * FROM sales WHERE product_id IN (SELECT id FROM products)";
    assert_eq!(informed(all, &facts, FactMode::Ratios).await.1.0, count(sql).await);
}

#[tokio::test]
async fn anti_joins_bound_below_only_with_a_narrower_kept_side() {
    let anti = |other: Context| Context::join(JoinType::LeftAnti, on(), t("sales"), other);
    let all = "SELECT * FROM sales WHERE NOT EXISTS (SELECT 1 FROM products p WHERE p.id = sales.product_id)";
    // Excluding only category 7's products keeps more sales than excluding
    // every product: no lower bound on the latter.
    let wider = "SELECT * FROM sales WHERE NOT EXISTS
                 (SELECT 1 FROM products p WHERE p.id = sales.product_id AND p.category = 7)";
    let facts = counted(&[(anti(t("products").filter(&category(7))), wider)]).await;
    // (They are among the sales, which the fact does bound below.)
    let (i, range) = informed(all, &facts, FactMode::Ratios).await;
    assert!(i.floors.iter().all(|(v, _)| v.contains("Scan_sales")), "{i}");
    assert_eq!(range.0, 0);
    // A filter on the sales kept is a narrower context.
    let store = terms([col("sales.store").eq(lit(1))]);
    let narrower = format!("{all} AND store = 1");
    let facts = counted(&[(anti(t("products")).filter(&store), &narrower)]).await;
    assert_eq!(informed(all, &facts, FactMode::Ratios).await.1.0, count(&narrower).await);
}

#[tokio::test]
async fn left_joins_bound_below_with_either_input_narrower() {
    let left = |l: Context, r: Context| Context::join(JoinType::Left, on(), l, r);
    let all = "SELECT * FROM sales s LEFT JOIN products p ON s.product_id = p.id";
    let store = terms([col("sales.store").eq(lit(2))]);
    let fewer_sales = "SELECT * FROM (SELECT * FROM sales WHERE store = 2) s LEFT JOIN products p ON s.product_id = p.id";
    let fewer_products =
        "SELECT * FROM sales s LEFT JOIN (SELECT * FROM products WHERE category = 7) p ON s.product_id = p.id";
    for (c, sql) in [
        (left(t("sales").filter(&store), t("products")), fewer_sales),
        (left(t("sales"), t("products").filter(&category(7))), fewer_products),
        // Its inner join, the rows a filter on the padded side leaves.
        (joined().filter(&category(7)), SEVEN),
    ] {
        let facts = counted(&[(c, sql)]).await;
        assert_eq!(informed(all, &facts, FactMode::Ratios).await.1.0, count(sql).await, "{sql}");
    }
}

#[tokio::test]
async fn limits_and_groups_bound_nothing_yet() {
    let group = Context::Derived {
        op: "group".into(),
        args: terms([col("products.category")]).into_iter().collect(),
        inputs: vec![joined().filter(&category(7))],
    };
    let sql = "SELECT p.category FROM sales s JOIN products p ON s.product_id = p.id WHERE p.category = 7 GROUP BY p.category";
    let facts = counted(&[(group, sql)]).await;
    let all = "SELECT p.category FROM sales s JOIN products p ON s.product_id = p.id GROUP BY p.category";
    assert!(informed(all, &facts, FactMode::Ratios).await.0.floors.is_empty());
}

#[tokio::test]
async fn a_tables_distinct_count_bounds_a_filtered_group_by() {
    // dee's review_agg: only the unfiltered distinct count is known.
    let mut facts = sizes(&["reviews"]).await;
    distinct(&mut facts, &[("reviews", "emp_id")]).await;
    let sql = "SELECT emp_id, count(*) FROM reviews WHERE score IS NOT NULL GROUP BY emp_id";
    let ndv = count("SELECT DISTINCT emp_id FROM reviews").await;
    let (i, range) = informed(sql, &facts, FactMode::Pinned).await;
    assert_eq!(range.1, Some(ndv), "{i}");
    assert!(ndv < count("SELECT * FROM reviews").await);
}

#[tokio::test]
async fn a_dimensions_distinct_count_bounds_a_group_by_over_a_join() {
    let mut facts = sizes(&["sales", "products"]).await;
    distinct(&mut facts, &[("products", "category"), ("sales", "store")]).await;
    let categories = count("SELECT DISTINCT category FROM products").await;
    let stores = count("SELECT DISTINCT store FROM sales").await;
    let sql = "SELECT p.category, count(*) FROM sales s JOIN products p ON s.product_id = p.id GROUP BY p.category";
    assert_eq!(informed(sql, &facts, FactMode::Pinned).await.1.1, Some(categories));
    let sql = "SELECT p.category, s.store, count(*) FROM sales s JOIN products p ON s.product_id = p.id
               GROUP BY p.category, s.store";
    assert_eq!(informed(sql, &facts, FactMode::Pinned).await.1.1, Some(categories * stores));
    // A left join pads with NULL: one more value.
    let sql = "SELECT p.category, count(*) FROM sales s LEFT JOIN products p ON s.product_id = p.id GROUP BY p.category";
    assert_eq!(informed(sql, &facts, FactMode::Pinned).await.1.1, Some(categories + 1));
    // Ratios leave the counts to grow with the tables.
    assert_eq!(informed(sql, &facts, FactMode::Ratios).await.0.pinned_ndv, vec![]);
}

#[tokio::test]
async fn wider_rows_bound_narrower_above() {
    let store = terms([col("sales.store").eq(lit(1))]);
    let wide = "SELECT * FROM sales WHERE store = 1";
    let mut facts = counted(&[(t("sales").filter(&store), wide)]).await;
    let narrow = "SELECT * FROM sales WHERE store = 1 AND product_id > 2";
    assert_eq!(informed(narrow, &facts, FactMode::Pinned).await.1.1, Some(count(wide).await));
    // So does a join's count bound it over a narrower input.
    for f in counted(&[(joined(), JOIN)]).await.iter() {
        facts.insert(f.clone());
    }
    assert_eq!(informed(SEVEN, &facts, FactMode::Pinned).await.1.1, Some(count(JOIN).await));
}
