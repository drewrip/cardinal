//! Declared keys: PRIMARY KEY and UNIQUE constraints reach every path that
//! asks whether columns are unique (joins, GROUP BY, DISTINCT, plans read off
//! another engine), and a key stays one under a widening cast.

use cardinal::observed::Catalog;
use cardinal::{Analysis, ForeignKey, Options, analyze_duckdb, analyze_sql_with};
use datafusion::prelude::SessionContext;

/// Data satisfying every declared key. `codes.code` is UNIQUE and holds
/// several NULLs; `tags.tag` is UNIQUE and NOT NULL. A shipment and a
/// purchase order have no supplier, and every supplier has shipments.
async fn context() -> SessionContext {
    let ctx = SessionContext::new();
    for sql in [
        "CREATE TABLE dims (id INT NOT NULL PRIMARY KEY, category INT)",
        "INSERT INTO dims VALUES (1, 7), (2, 7), (3, 11), (4, 12)",
        "CREATE TABLE stores (store_id INT NOT NULL PRIMARY KEY, region VARCHAR)",
        "INSERT INTO stores VALUES (1, 'a'), (2, 'b')",
        "CREATE TABLE sales (id INT NOT NULL PRIMARY KEY, dim_id INT, store_id INT, big_dim BIGINT, amount INT)",
        "INSERT INTO sales VALUES (1, 1, 1, 1, 5), (2, 1, 2, 1, 20), (3, 2, 1, 2, 7), (4, 3, 1, 3, 30), (5, 4, 2, 4, 1),
         (6, 4, 2, 4, 12), (7, 5, 1, 5, 3)",
        "CREATE TABLE codes (id INT, code INT UNIQUE)",
        "INSERT INTO codes VALUES (1, 10), (2, 20), (3, NULL), (4, NULL)",
        "CREATE TABLE tags (id INT, tag INT NOT NULL UNIQUE)",
        "INSERT INTO tags VALUES (1, 1), (1, 2), (2, 3)",
        "CREATE TABLE suppliers (supplier_id INT NOT NULL PRIMARY KEY, name VARCHAR, category VARCHAR, country VARCHAR)",
        "INSERT INTO suppliers VALUES (1, 'acme', 'tools', 'us'), (2, 'bolt', 'tools', 'de'), (3, NULL, 'food', 'us')",
        "CREATE TABLE shipments (shipment_id INT NOT NULL PRIMARY KEY, supplier_id INT, qty INT)",
        "INSERT INTO shipments VALUES (1, 1, 5), (2, 1, 7), (3, 2, 1), (4, 3, 2), (5, 3, 9), (6, 9, 4), (7, NULL, 1)",
        "CREATE TABLE purchase_orders (po_id INT NOT NULL PRIMARY KEY, supplier_id INT, qty INT)",
        "INSERT INTO purchase_orders VALUES (1, 1, 5), (2, 1, 7), (3, 3, 1), (4, 8, 1)",
        "CREATE TABLE loose (a INT, b INT, c INT, d INT)",
        "INSERT INTO loose VALUES (1, 1, 1, 1), (1, 1, 1, 1), (1, 2, 1, 1)",
        "CREATE VIEW enriched AS SELECT s.id, s.amount, d.category, st.region FROM sales s
         JOIN dims d ON s.dim_id = d.id JOIN stores st ON s.store_id = st.store_id",
    ] {
        ctx.sql(sql).await.unwrap().collect().await.unwrap();
    }
    ctx
}

/// `sql` analyzed with `foreign_keys`, checked against the data.
async fn analyze(sql: &str, foreign_keys: Vec<ForeignKey>) -> Analysis {
    let ctx = context().await;
    let options = Options { selectivity: true, foreign_keys, ..Default::default() };
    let a = analyze_sql_with(&ctx, sql, options).await.unwrap();
    let v = a.validate(&ctx).await.unwrap();
    assert_eq!(v.violation, None, "{sql}");
    assert_eq!(v.selectivity.unwrap().violation, None, "{sql}");
    a
}

/// The output's formula and bounds, with no foreign keys.
async fn formula(sql: &str) -> (String, String) {
    let a = analyze(sql, vec![]).await;
    let formula = a.selectivity.as_ref().unwrap().output.to_string();
    let bounds = a.bounds().unwrap().to_string();
    println!("{sql}\n  X = {formula}; {bounds}");
    (formula, bounds)
}

#[tokio::test]
async fn primary_key_joins_match_once() {
    let sql = "SELECT * FROM sales s JOIN dims d ON s.dim_id = d.id";
    assert_eq!(formula(sql).await.1, "X <= |sales|");
}

#[tokio::test]
async fn primary_key_groups_and_distincts_keep_every_row() {
    assert_eq!(formula("SELECT id, count(*) FROM dims GROUP BY id").await.1, "X = |dims|");
    assert_eq!(formula("SELECT DISTINCT id, category FROM dims").await.1, "X = |dims|");
}

#[tokio::test]
async fn widening_casts_keep_a_key() {
    // `big_dim` is BIGINT, so the INT key is cast up to match it.
    let sql = "SELECT * FROM sales s JOIN dims d ON s.big_dim = d.id";
    assert_eq!(formula(sql).await.1, "X <= |sales|");
    let sql = "SELECT * FROM sales s JOIN dims d ON s.big_dim = CAST(d.id AS BIGINT)";
    assert_eq!(formula(sql).await.1, "X <= |sales|");
}

#[tokio::test]
async fn unique_columns_match_once_but_may_repeat_null() {
    // NULL codes never match, so each sale matches at most one code.
    let sql = "SELECT * FROM sales s JOIN codes c ON s.amount = c.code";
    assert_eq!(formula(sql).await.1, "X <= |sales|");
    // But NULL is one group of several rows. (DataFusion drops a DISTINCT on
    // a UNIQUE column, NULLs and all, so DISTINCT can't show the same.)
    assert_ne!(formula("SELECT code, count(*) FROM codes GROUP BY code").await.1, "X = |codes|");
}

#[tokio::test]
async fn not_null_unique_columns_are_keys() {
    assert_eq!(formula("SELECT tag, count(*) FROM tags GROUP BY tag").await.1, "X = |tags|");
    assert_eq!(formula("SELECT DISTINCT tag FROM tags").await.1, "X = |tags|");
    let sql = "SELECT * FROM sales s JOIN tags t ON s.dim_id = t.tag";
    assert_eq!(formula(sql).await.1, "X <= |sales|");
}

/// dee's shape: a View joins a fact table to two dimensions on their keys,
/// and Tables read it through filters.
#[tokio::test]
async fn views_over_keyed_sources() {
    assert_eq!(formula("SELECT * FROM enriched").await.1, "X <= |sales|");
    assert_eq!(formula("SELECT * FROM enriched WHERE category = 7").await.1, "X <= |sales|");
    // With foreign keys too, every sale is kept. Sale 7's dim_id is 5, which
    // breaks a key from `sales.dim_id`, so only the stores' is declared.
    let keys = vec![ForeignKey::new("sales", &["store_id"], "stores", &["store_id"])];
    let a = analyze("SELECT s.id, st.region FROM sales s JOIN stores st ON s.store_id = st.store_id", keys).await;
    assert_eq!(a.bounds().unwrap().to_string(), "X = |sales|");
}

/// "Group by the id and the id's attributes": the shipments per supplier,
/// with the supplier's name, category and country.
const Q_GROUP: &str = "SELECT sh.supplier_id, upper(s.name) AS name, s.category, s.country, count(*) AS n
    FROM shipments sh JOIN suppliers s ON sh.supplier_id = s.supplier_id
    GROUP BY sh.supplier_id, upper(s.name), s.category, s.country";

/// A declared key determines its table's other columns, and the dependency
/// reaches through the join on it: the GROUP BY's four keys reduce to
/// `supplier_id`, which takes at most `|suppliers|` values.
#[tokio::test]
async fn keys_determine_their_rows_attributes() {
    let bounds = formula(Q_GROUP).await.1;
    assert!(bounds.contains("X <= |suppliers|"), "{bounds}");
}

/// The GROUP BY's output is unique on `supplier_id` alone, the key its other
/// keys depend on, so a LEFT JOIN on it keeps each left row once.
#[tokio::test]
async fn dependent_group_keys_keep_a_key() {
    let sql = format!(
        "WITH perf AS ({Q_GROUP}),
         po AS (SELECT p.supplier_id, upper(s.name) AS name, count(*) AS n
                FROM purchase_orders p JOIN suppliers s ON p.supplier_id = s.supplier_id
                GROUP BY p.supplier_id, upper(s.name))
         SELECT perf.supplier_id, perf.n, po.n AS po_n
         FROM perf LEFT JOIN po ON perf.supplier_id = po.supplier_id"
    );
    let bounds = formula(&sql).await.1;
    assert!(bounds.contains("X <= |suppliers|"), "{bounds}");
}

/// The padded side of a LEFT JOIN is NULL on unmatched rows, so its key
/// determines nothing there: the shipment with no supplier is a group of its
/// own, beyond the suppliers'.
#[tokio::test]
async fn padded_keys_determine_nothing() {
    let sql = "SELECT s.supplier_id, s.name, s.category, s.country, count(*) AS n
        FROM shipments sh LEFT JOIN suppliers s ON sh.supplier_id = s.supplier_id
        GROUP BY s.supplier_id, s.name, s.category, s.country";
    let bounds = formula(sql).await.1;
    assert!(!bounds.contains("X <= |suppliers|"), "{bounds}");
}

/// A volatile group key takes values no column determines.
#[tokio::test]
async fn volatile_keys_are_not_determined() {
    let sql = "SELECT sh.supplier_id, s.name, s.category, random() < 0.5 AS coin, count(*) AS n
        FROM shipments sh JOIN suppliers s ON sh.supplier_id = s.supplier_id
        GROUP BY sh.supplier_id, s.name, s.category, random() < 0.5";
    let bounds = formula(sql).await.1;
    assert!(!bounds.contains("X <= |suppliers|"), "{bounds}");
}

/// Group keys that one input column determines take no more combinations
/// than it has values: `supplier_id`, a key, determines all three.
#[tokio::test]
async fn one_column_determining_the_keys_bounds_the_groups() {
    let sql = "SELECT s.name, s.category, s.country, count(*) AS n
        FROM shipments sh JOIN suppliers s ON sh.supplier_id = s.supplier_id
        GROUP BY s.name, s.category, s.country";
    let bounds = formula(sql).await.1;
    assert!(bounds.contains("X <= |suppliers|"), "{bounds}");
}

/// With no declared key, four group keys are too many to multiply, and the
/// GROUP BY is bounded by its input alone.
#[tokio::test]
async fn groups_without_keys_keep_their_bound() {
    assert_eq!(formula("SELECT a, b, c, d, count(*) FROM loose GROUP BY a, b, c, d").await.1, "X <= |loose|");
}

/// DuckDB's `EXPLAIN (FORMAT JSON)` of
/// `SELECT f.id, d.name FROM facts f JOIN dims d ON f.dim_id = d.id`.
const DUCKDB_KEY_JOIN: &str = r#"[{"name": "HASH_JOIN", "children": [
    {"name": "SEQ_SCAN", "children": [], "extra_info": {"Table": "memory.main.facts", "Type": "Sequential Scan",
     "Projections": ["dim_id", "id"], "Estimated Cardinality": "1000"}},
    {"name": "SEQ_SCAN", "children": [], "extra_info": {"Table": "memory.main.dims", "Type": "Sequential Scan",
     "Projections": ["id", "name"], "Estimated Cardinality": "100"}}],
  "extra_info": {"Join Type": "INNER", "Conditions": "dim_id = id", "Estimated Cardinality": "1010"}}]"#;

/// Plans read off another engine scan the catalog's providers, so they see
/// the keys declared there.
#[tokio::test]
async fn observed_plans_see_declared_keys() {
    let bounds = |keyed: bool| async move {
        let ctx = SessionContext::new();
        let pk = if keyed { " NOT NULL PRIMARY KEY" } else { "" };
        for sql in [
            format!("CREATE TABLE dims (id INT{pk}, name VARCHAR)"),
            "CREATE TABLE facts (id INT, dim_id INT, amount INT)".to_string(),
        ] {
            ctx.sql(&sql).await.unwrap().collect().await.unwrap();
        }
        let catalog = Catalog::from_context(&ctx).await.unwrap();
        let sql = "SELECT f.id, d.name FROM facts f JOIN dims d ON f.dim_id = d.id";
        let options = Options { selectivity: true, ..Default::default() };
        let a = analyze_duckdb(&catalog, DUCKDB_KEY_JOIN, Some(sql), options).unwrap();
        a.bounds().unwrap().to_string()
    };
    assert_eq!(bounds(true).await, "X <= |facts|");
    assert_ne!(bounds(false).await, "X <= |facts|");
}

