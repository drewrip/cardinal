//! Test suite of simple to complex queries, each checked against the claim
//! `O_root <= Σ scans`. Tables may be empty. Refuted queries also check the
//! structure of the counterexample.

use std::sync::Arc;

use cardinal::{Analysis, Counterexample, Verdict, analyze_sql};
use datafusion::arrow::datatypes::{DataType, Field, Schema};
use datafusion::datasource::MemTable;
use datafusion::prelude::SessionContext;

fn table(ctx: &SessionContext, name: &str, cols: &[(&str, DataType)]) {
    keyed_table(ctx, name, cols, &[]);
}

/// Registers an empty table with `key` (column indices) declared as its primary key.
fn keyed_table(ctx: &SessionContext, name: &str, cols: &[(&str, DataType)], key: &[usize]) {
    use datafusion::common::{Constraint, Constraints};
    let schema = Arc::new(Schema::new(
        cols.iter()
            .map(|(c, t)| Field::new(*c, t.clone(), true))
            .collect::<Vec<_>>(),
    ));
    let mut mem = MemTable::try_new(schema, vec![vec![]]).unwrap();
    if !key.is_empty() {
        mem = mem.with_constraints(Constraints::new_unverified(vec![Constraint::PrimaryKey(
            key.to_vec(),
        )]));
    }
    ctx.register_table(name, Arc::new(mem)).unwrap();
}

fn setup() -> SessionContext {
    use DataType::*;
    let ctx = SessionContext::new();
    // `id` is the declared primary key of users, orders and products.
    keyed_table(
        &ctx,
        "users",
        &[("id", Int64), ("name", Utf8), ("age", Int64)],
        &[0],
    );
    keyed_table(
        &ctx,
        "orders",
        &[("id", Int64), ("user_id", Int64), ("amount", Float64)],
        &[0],
    );
    keyed_table(&ctx, "products", &[("id", Int64), ("price", Float64)], &[0]);
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
async fn refuted(sql: &str) -> (Analysis, Counterexample) {
    let a = run(sql).await;
    match a.verdict.clone() {
        Verdict::Refuted(m) => {
            // Sanity-check the counterexample actually violates the claim.
            let total: i64 = a.scans.iter().map(|(s, _)| m.var(s)).sum();
            assert!(m.var(&a.root) > total, "model does not refute the claim");
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
    assert_eq!(m.var(&a.root), 1);
    // 1 > users forces the table to be empty.
    assert_eq!(m.table("users"), 0);
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
    assert!(has_op(&a, "InnerKeyJoin"));
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
    assert!(has_op(&a, "InnerKeyJoin"));
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
    assert_eq!(m.var(&a.root), m.table("users") * m.table("products"));
}

#[tokio::test]
async fn left_join() {
    // Bound is max(l, r) + l: inner matches plus unmatched users, which can
    // exceed l + r when users outnumber orders.
    let (a, m) = refuted("SELECT * FROM users u LEFT JOIN orders o ON u.id = o.user_id").await;
    assert!(has_op(&a, "LeftKeyJoin"));
    assert!(m.var(&a.root) >= m.table("users"));
}

#[tokio::test]
async fn full_join() {
    let (a, m) = refuted("SELECT * FROM users u FULL JOIN orders o ON u.id = o.user_id").await;
    assert!(has_op(&a, "FullKeyJoin"));
    assert!(m.var(&a.root) >= m.table("users") && m.var(&a.root) >= m.table("orders"));
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
    assert_eq!(m.var(&a.root), 3);
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

// --- Regression tests for bugs found in review ------------------------------

#[tokio::test]
async fn qualified_and_bare_names_are_one_table() {
    // Previously `users` and `datafusion.public.users` got separate variables.
    let a = proven("SELECT * FROM users a JOIN datafusion.public.users b ON a.id = b.id").await;
    assert_eq!(a.scans.len(), 2);
    assert!(a.scans.iter().all(|(_, t)| t == "users"));
    assert_eq!(a.smtlib.matches("(declare-fun T").count(), 1);
}

#[tokio::test]
async fn recursive_work_table_is_not_input() {
    // Previously the work table `r` was counted as a base table scan.
    let (a, _) = refuted(
        "WITH RECURSIVE r(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM r WHERE n < 5)
         SELECT * FROM r",
    )
    .await;
    assert!(a.scans.is_empty());
    assert!(has_op(&a, "NonBaseScan_r"));
}

#[tokio::test]
async fn table_function_is_not_input() {
    // Previously generate_series was a "table" whose rows counted as input,
    // which made `SELECT * FROM generate_series(..)` provable.
    let (a, _) = refuted("SELECT * FROM generate_series(1, 5)").await;
    assert!(a.scans.is_empty());
}

#[tokio::test]
async fn table_named_like_an_operator_variable() {
    // Table variables are prefixed so they cannot alias operator variables.
    use datafusion::common::TableReference;
    let ctx = setup();
    let schema = Arc::new(Schema::new(vec![Field::new("x", DataType::Int64, true)]));
    let mem = MemTable::try_new(schema, vec![vec![]]).unwrap();
    ctx.register_table(TableReference::bare("O1_Filter"), Arc::new(mem))
        .unwrap();
    let a = analyze_sql(&ctx, r#"SELECT * FROM "O1_Filter" WHERE x > 1"#)
        .await
        .unwrap();
    assert_eq!(a.verdict, Verdict::Proven);
    assert!(a.smtlib.contains("(declare-fun T0_O1_Filter () Int)"));
    assert!(a.smtlib.contains("(declare-fun O1_Filter () Int)"));
}

#[tokio::test]
async fn pushed_down_scan_filters_and_fetch() {
    // MemTable never accepts pushdowns, so build the scan by hand.
    use datafusion::datasource::provider_as_source;
    use datafusion::logical_expr::{LogicalPlanBuilder, col, lit};
    let schema = Arc::new(Schema::new(vec![Field::new("age", DataType::Int64, true)]));
    let source = provider_as_source(Arc::new(MemTable::try_new(schema, vec![vec![]]).unwrap()));
    let plan = LogicalPlanBuilder::scan_with_filters_fetch(
        "people",
        source,
        None,
        vec![col("age").gt(lit(30))],
        Some(7),
    )
    .unwrap()
    .build()
    .unwrap();
    let a = cardinal::analyze_plan(&plan);
    assert_eq!(a.verdict, Verdict::Proven);
    assert!(has_op(&a, "ScanFilter"));
    // A scan's fetch is a hint (providers may return more rows), so it must not
    // bound the output. Previously this asserted `root <= 7`.
    assert!(!a.smtlib.contains(" 7)"));
    assert_eq!(
        a.scans,
        vec![("O0_Scan_people".to_string(), "people".to_string())]
    );
}

#[tokio::test]
async fn validate_catches_a_false_primary_key() {
    use datafusion::arrow::array::Int64Array;
    use datafusion::arrow::record_batch::RecordBatch;
    use datafusion::common::{Constraint, Constraints};
    // `age` is declared the primary key, but three rows share age 30. The
    // self-join then returns 9 rows, more than the max(3, 3) the key allows.
    let ctx = SessionContext::new();
    let schema = Arc::new(Schema::new(vec![Field::new("age", DataType::Int64, true)]));
    let batch = RecordBatch::try_new(
        schema.clone(),
        vec![Arc::new(Int64Array::from(vec![30, 30, 30]))],
    )
    .unwrap();
    let mem = MemTable::try_new(schema, vec![vec![batch]])
        .unwrap()
        .with_constraints(Constraints::new_unverified(vec![Constraint::PrimaryKey(
            vec![0],
        )]));
    ctx.register_table("people", Arc::new(mem)).unwrap();
    let a = analyze_sql(
        &ctx,
        "SELECT * FROM people a JOIN people b ON a.age = b.age",
    )
    .await
    .unwrap();
    assert_eq!(a.verdict, Verdict::Proven);
    let v = a.validate(&ctx).await.unwrap();
    assert_eq!(v.violation.as_deref(), Some("O4_InnerKeyJoin"));
    assert_eq!(v.rows["O4_InnerKeyJoin"], 9);
}

// --- Join keys: only declared primary keys count as unique ------------------

#[tokio::test]
async fn non_key_equijoin_is_bounded_by_product() {
    // `age` is not a key: the bound is l * r, which exceeds l + r.
    let (a, m) = refuted("SELECT * FROM users a JOIN users b ON a.age = b.age").await;
    assert!(has_op(&a, "InnerEquiJoin"));
    assert!(m.var(&a.root) > 2 * m.table("users"));
}

#[tokio::test]
async fn unique_constraint_is_not_trusted() {
    use datafusion::common::{Constraint, Constraints};
    let ctx = setup();
    let schema = Arc::new(Schema::new(vec![Field::new("email", DataType::Utf8, true)]));
    let mem = MemTable::try_new(schema, vec![vec![]])
        .unwrap()
        .with_constraints(Constraints::new_unverified(vec![Constraint::Unique(vec![
            0,
        ])]));
    ctx.register_table("accounts", Arc::new(mem)).unwrap();
    let a = analyze_sql(
        &ctx,
        "SELECT * FROM accounts a JOIN accounts b ON a.email = b.email",
    )
    .await
    .unwrap();
    assert!(matches!(a.verdict, Verdict::Refuted(_)));
    assert!(has_op(&a, "InnerEquiJoin"));
}

#[tokio::test]
async fn group_by_output_is_not_a_key() {
    let (a, _) = refuted(
        "SELECT * FROM (SELECT user_id FROM orders GROUP BY user_id) g
         JOIN (SELECT user_id FROM orders GROUP BY user_id) h ON g.user_id = h.user_id",
    )
    .await;
    assert!(has_op(&a, "InnerEquiJoin") && !has_op(&a, "KeyJoin"));
}

#[tokio::test]
async fn expression_key_is_not_a_key() {
    let (a, _) = refuted("SELECT * FROM users u JOIN orders o ON u.id + 0 = o.user_id").await;
    assert!(has_op(&a, "InnerEquiJoin"));
}

#[tokio::test]
async fn key_survives_projection_alias_and_filter() {
    let a = proven(
        "SELECT * FROM (SELECT id AS uid FROM users WHERE age > 20) t
         JOIN orders o ON t.uid = o.user_id",
    )
    .await;
    assert!(has_op(&a, "InnerKeyJoin"));
}

#[tokio::test]
async fn key_survives_a_join_on_the_other_sides_key() {
    // Each order matches at most one user, so orders.id stays unique after the
    // first join and keys the second.
    let a = proven(
        "SELECT * FROM orders o JOIN users u ON o.user_id = u.id
         JOIN order_items oi ON o.id = oi.order_id",
    )
    .await;
    assert_eq!(a.smtlib.matches("InnerKeyJoin ()").count(), 2);
    assert!(!has_op(&a, "InnerEquiJoin"));
}

#[tokio::test]
async fn key_lost_after_a_non_key_join() {
    // Joining orders to order_items on a non-key column duplicates orders rows,
    // so orders.id is no longer unique on either side of the final join.
    let (a, _) = refuted(
        "WITH t AS (SELECT o.id AS oid FROM orders o JOIN order_items oi ON o.amount = oi.qty)
         SELECT * FROM t a JOIN t b ON a.oid = b.oid",
    )
    .await;
    assert_eq!(a.smtlib.matches("InnerEquiJoin ()").count(), 3);
    assert!(!has_op(&a, "KeyJoin"));
}

// --- Regression tests for the second review ----------------------------------

/// Registers an Int64 table holding `cols` of data, with optional primary key.
fn data_table(ctx: &SessionContext, name: &str, cols: &[(&str, Vec<i64>)], key: &[usize]) {
    use datafusion::arrow::array::{ArrayRef, Int64Array};
    use datafusion::arrow::record_batch::RecordBatch;
    use datafusion::common::{Constraint, Constraints, TableReference};
    let schema = Arc::new(Schema::new(
        cols.iter()
            .map(|(c, _)| Field::new(*c, DataType::Int64, true))
            .collect::<Vec<_>>(),
    ));
    let arrays: Vec<ArrayRef> = cols
        .iter()
        .map(|(_, v)| Arc::new(Int64Array::from(v.clone())) as ArrayRef)
        .collect();
    let batch = RecordBatch::try_new(schema.clone(), arrays).unwrap();
    let mut mem = MemTable::try_new(schema, vec![vec![batch]]).unwrap();
    if !key.is_empty() {
        mem = mem.with_constraints(Constraints::new_unverified(vec![Constraint::PrimaryKey(
            key.to_vec(),
        )]));
    }
    ctx.register_table(TableReference::bare(name), Arc::new(mem))
        .unwrap();
}

async fn row_count(ctx: &SessionContext, table: &str) -> usize {
    ctx.sql(&format!("SELECT * FROM \"{table}\""))
        .await
        .unwrap()
        .collect()
        .await
        .unwrap()
        .iter()
        .map(|b| b.num_rows())
        .sum()
}

fn operators(a: &Analysis) -> usize {
    a.smtlib.matches("(declare-fun O").count()
}

#[tokio::test]
async fn validate_never_executes_dml() {
    // Previously validating an INSERT inserted the rows.
    let ctx = SessionContext::new();
    data_table(&ctx, "t", &[("x", (0..10).collect())], &[]);
    let a = analyze_sql(&ctx, "INSERT INTO t VALUES (1), (2)")
        .await
        .unwrap();
    a.validate(&ctx).await.unwrap();
    assert_eq!(row_count(&ctx, "t").await, 10);
}

#[tokio::test]
async fn validate_is_consistent_under_random() {
    // Previously each operator was executed separately, so the random filters
    // saw different rows than the union did: 18 of 20 runs reported a violation.
    let ctx = SessionContext::new();
    data_table(&ctx, "t", &[("x", (0..200).collect())], &[]);
    let a = analyze_sql(
        &ctx,
        "SELECT x FROM t WHERE random() < 0.5 UNION ALL SELECT x FROM t WHERE random() < 0.5",
    )
    .await
    .unwrap();
    for _ in 0..20 {
        let v = a.validate(&ctx).await.unwrap();
        assert_eq!(v.violation, None);
        assert_eq!(v.rows.len(), operators(&a));
    }
}

#[tokio::test]
async fn validation_handles_duplicate_column_names() {
    // A self-join outputs `a.x` and `b.x`; materializing it used to fail and
    // fall back to re-running the subtree, which re-rolled random().
    let ctx = SessionContext::new();
    data_table(&ctx, "t", &[("x", (0..30).map(|i| i % 4).collect())], &[]);
    let a = analyze_sql(
        &ctx,
        "SELECT * FROM (SELECT * FROM (SELECT * FROM t WHERE random() < 0.5) a
                        JOIN t b ON a.x = b.x) j WHERE random() < 0.5",
    )
    .await
    .unwrap();
    for _ in 0..10 {
        let v = a.validate(&ctx).await.unwrap();
        assert_eq!(v.violation, None);
        assert_eq!(v.rows.len(), operators(&a));
    }
}

#[tokio::test]
async fn scan_fetch_is_not_a_bound() {
    // generate_series ignores the pushed-down fetch=2 and returns 4 rows, which
    // broke the old `scan <= fetch` constraint.
    let ctx = SessionContext::new();
    let a = analyze_sql(&ctx, "SELECT * FROM generate_series(0, 3) LIMIT 2")
        .await
        .unwrap();
    let v = a.validate(&ctx).await.unwrap();
    assert_eq!(v.violation, None);
    assert_eq!(v.rows[&a.root], 2);
}

#[tokio::test]
async fn odd_table_names_round_trip() {
    // Z3 symbols are sanitized, so constraints survive the SMT-LIB round trip
    // that validation relies on.
    let ctx = SessionContext::new();
    let name = r#"we|ird "x" (tbl)"#;
    data_table(&ctx, name, &[("id", vec![1, 2, 3])], &[0]);
    let a = analyze_sql(
        &ctx,
        r#"SELECT * FROM "we|ird ""x"" (tbl)" a JOIN "we|ird ""x"" (tbl)" b ON a.id = b.id"#,
    )
    .await
    .unwrap();
    assert_eq!(a.verdict, Verdict::Proven);
    assert_eq!(a.scans[0].1, name);
    let v = a.validate(&ctx).await.unwrap();
    assert_eq!(v.violation, None);
    assert_eq!(v.rows.len(), operators(&a));
}

#[tokio::test]
async fn cast_join_key_stays_unique() {
    use datafusion::common::{Constraint, Constraints};
    // An Int32 primary key joined to an Int64 column is compared through a
    // widening cast, which cannot make distinct keys collide.
    let ctx = setup();
    let schema = Arc::new(Schema::new(vec![Field::new("id", DataType::Int32, false)]));
    let mem = MemTable::try_new(schema, vec![vec![]])
        .unwrap()
        .with_constraints(Constraints::new_unverified(vec![Constraint::PrimaryKey(
            vec![0],
        )]));
    ctx.register_table("small", Arc::new(mem)).unwrap();
    let a = analyze_sql(
        &ctx,
        "SELECT * FROM orders o JOIN small s ON o.user_id = s.id",
    )
    .await
    .unwrap();
    assert!(a.plan.contains("CAST"), "{}", a.plan);
    assert!(has_op(&a, "InnerKeyJoin"), "{}", a.smtlib);
    assert_eq!(a.verdict, Verdict::Proven);
}

#[tokio::test]
async fn keyed_join_also_bounded_by_product() {
    // max(l, r) alone is looser than l * r when a side is empty.
    let a = proven("SELECT * FROM users u JOIN orders o ON u.id = o.user_id").await;
    assert!(has_op(&a, "InnerKeyJoin"));
    assert!(
        a.smtlib.contains("(* O1_SubqueryAlias O3_SubqueryAlias)"),
        "{}",
        a.smtlib
    );
}

#[tokio::test]
async fn counterexample_separates_tables_and_vars() {
    // A table named like an operator variable used to overwrite its value.
    let ctx = SessionContext::new();
    data_table(&ctx, "O1_Filter", &[("x", vec![1])], &[]);
    let a = analyze_sql(
        &ctx,
        r#"SELECT count(*) FROM (SELECT * FROM "O1_Filter" WHERE x > 1) t"#,
    )
    .await
    .unwrap();
    let Verdict::Refuted(m) = &a.verdict else {
        panic!("expected Refuted, got {:?}", a.verdict)
    };
    assert!(m.tables.contains_key("O1_Filter"));
    assert!(m.vars.contains_key("O1_Filter"));
    assert_eq!(m.var(&a.root), 1);
}

#[test]
fn futures_are_send() {
    fn assert_send<T: Send>(_: &T) {}
    let ctx = SessionContext::new();
    let analyze = analyze_sql(&ctx, "SELECT 1");
    assert_send(&analyze);
    drop(analyze);
    let a = cardinal::analyze_plan(&datafusion::logical_expr::LogicalPlan::EmptyRelation(
        datafusion::logical_expr::EmptyRelation {
            produce_one_row: true,
            schema: Arc::new(datafusion::common::DFSchema::empty()),
        },
    ));
    let validate = a.validate(&ctx);
    assert_send(&validate);
}
