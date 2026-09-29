//! Bounds relative to the source relations, for queries whose tightest bound is
//! known. Keys are declared on `users.id`, `orders.id` and `products.id`.

mod common;

use std::sync::Arc;

use cardinal::{Bounds, Linear, analyze_sql};
use datafusion::arrow::datatypes::{DataType, Field, Schema};
use datafusion::datasource::MemTable;
use datafusion::prelude::SessionContext;

fn shop() -> SessionContext {
    common::shop_datasets().remove(0).context(true)
}

async fn bounds_in(ctx: &SessionContext, sql: &str) -> Bounds {
    let a = analyze_sql(ctx, sql).await.unwrap();
    let b = a.bounds().unwrap();
    println!("{sql}\n  {b}");
    b
}

async fn bounds(sql: &str) -> Bounds {
    bounds_in(&shop(), sql).await
}

const fn exactly(num: u64, den: u64) -> Linear {
    Linear { num, den, add: 0 }
}

/// The bound relative to `table`, and whether it is exact.
fn table(b: &Bounds, table: &str) -> Option<(Linear, bool)> {
    b.tables
        .iter()
        .find(|t| t.table == table)
        .map(|t| (t.bound, t.exact))
}

#[tokio::test]
async fn self_join_on_key_halves_the_input() {
    let b = bounds("SELECT * FROM users a JOIN users b ON a.id = b.id").await;
    assert_eq!(b.sum, Some(exactly(1, 2)));
    assert_eq!(table(&b, "users"), Some((exactly(1, 1), false)));
    assert_eq!(b.constant, None);
    assert_eq!(b.to_string(), "X <= |users|; X <= 1/2·Σ");
}

#[tokio::test]
async fn three_way_self_join_on_key_thirds_the_input() {
    let b = bounds("SELECT * FROM users a JOIN users b ON a.id = b.id JOIN users c ON b.id = c.id")
        .await;
    assert_eq!(b.sum, Some(exactly(1, 3)));
}

#[tokio::test]
async fn foreign_key_join_is_bounded_by_the_referencing_table() {
    let b = bounds("SELECT * FROM orders o JOIN users u ON o.user_id = u.id").await;
    assert_eq!(table(&b, "orders"), Some((exactly(1, 1), false)));
    // Many orders can share one user, so |users| bounds nothing.
    assert_eq!(table(&b, "users"), None);
}

#[tokio::test]
async fn left_join_to_a_key_keeps_exactly_every_row() {
    let b = bounds("SELECT * FROM orders o LEFT JOIN users u ON o.user_id = u.id").await;
    assert_eq!(table(&b, "orders"), Some((exactly(1, 1), true)));
    assert_eq!(b.to_string(), "X = |orders|");
}

#[tokio::test]
async fn projection_does_not_reduce() {
    let b = bounds("SELECT name, age + 1 FROM users").await;
    assert_eq!(table(&b, "users"), Some((exactly(1, 1), true)));
}

#[tokio::test]
async fn union_all_of_a_table_with_itself() {
    let b = bounds("SELECT id FROM users UNION ALL SELECT id FROM users").await;
    assert_eq!(table(&b, "users"), Some((exactly(2, 1), true)));
}

#[tokio::test]
async fn primary_key_lookup_returns_at_most_one_row() {
    let b = bounds("SELECT * FROM users WHERE id = 5").await;
    assert_eq!(b.constant, Some(1));
    let b = bounds("SELECT * FROM users WHERE id IN (1, 2, 3) AND age > 20").await;
    assert_eq!(b.constant, Some(3));
}

#[tokio::test]
async fn non_key_lookup_is_not_constant() {
    let b = bounds("SELECT * FROM users WHERE age = 5").await;
    assert_eq!(b.constant, None);
    assert_eq!(table(&b, "users"), Some((exactly(1, 1), false)));
}

#[tokio::test]
async fn limit_is_a_constant_bound() {
    let b = bounds("SELECT * FROM users u JOIN orders o ON u.age < o.amount LIMIT 10").await;
    assert_eq!(b.constant, Some(10));
    let b = bounds("SELECT * FROM users ORDER BY age LIMIT 10 OFFSET 5").await;
    assert_eq!(b.constant, Some(10));
}

#[tokio::test]
async fn group_by_boolean_has_at_most_three_groups() {
    let ctx = shop();
    let schema = Arc::new(Schema::new(vec![
        Field::new("id", DataType::Int64, false),
        Field::new("active", DataType::Boolean, true),
    ]));
    ctx.register_table(
        "flags",
        Arc::new(MemTable::try_new(schema, vec![vec![]]).unwrap()),
    )
    .unwrap();
    let b = bounds_in(&ctx, "SELECT active, count(*) FROM flags GROUP BY active").await;
    // true, false, NULL
    assert_eq!(b.constant, Some(3));
}

#[tokio::test]
async fn group_by_a_key_does_not_reduce() {
    let b = bounds("SELECT id, count(*) FROM users GROUP BY id").await;
    assert_eq!(table(&b, "users"), Some((exactly(1, 1), true)));
}

#[tokio::test]
async fn group_by_a_joined_column_is_bounded_by_its_table() {
    // Joins create no new values: at most one group per user.
    let b = bounds(
        "SELECT u.id, count(*) FROM users u JOIN orders o ON o.amount > u.age GROUP BY u.id",
    )
    .await;
    assert_eq!(table(&b, "users"), Some((exactly(1, 1), false)));
}

#[tokio::test]
async fn intersect_is_bounded_by_both_sides() {
    let b = bounds("SELECT id FROM users INTERSECT SELECT user_id FROM orders").await;
    assert_eq!(table(&b, "users"), Some((exactly(1, 1), false)));
    assert_eq!(table(&b, "orders"), Some((exactly(1, 1), false)));
    assert_eq!(b.sum, Some(exactly(1, 2)));
}

#[tokio::test]
async fn ungrouped_aggregate_is_one_row() {
    let b =
        bounds("SELECT count(*), max(age) FROM users u JOIN orders o ON u.id = o.user_id").await;
    assert_eq!(b.constant, Some(1));
    assert_eq!(b.to_string(), "X <= 1");
}

#[tokio::test]
async fn cross_join_is_unbounded() {
    let b = bounds("SELECT * FROM users CROSS JOIN products").await;
    assert_eq!(b, Bounds::default());
    assert_eq!(b.to_string(), "unbounded");
}

#[tokio::test]
async fn sum_bound_when_no_single_table_bounds() {
    // At most |orders| matches plus the unmatched users.
    let b = bounds("SELECT * FROM users u LEFT JOIN orders o ON u.id = o.user_id").await;
    assert!(b.tables.is_empty());
    assert_eq!(b.sum, Some(exactly(1, 1)));
    assert_eq!(b.to_string(), "X <= Σ");
}

#[tokio::test]
async fn tpch_q5_is_bounded_by_the_nation_table() {
    // Six-way join, grouped by n_name: at most one row per nation.
    let ctx = common::tpch_datasets().remove(0).context(true);
    let b = bounds_in(&ctx, include_str!("tpch/q05.sql")).await;
    assert_eq!(table(&b, "nation"), Some((exactly(1, 1), false)));
}

#[test]
fn linear_arithmetic() {
    let half_plus_one = Linear {
        num: 1,
        den: 2,
        add: 1,
    };
    assert!(half_plus_one.holds(6, 10));
    assert!(!half_plus_one.holds(7, 10));
    assert_eq!(half_plus_one.render("Σ"), "1/2·Σ + 1");
    assert_eq!(exactly(3, 1).render("|t|"), "3·|t|");
    assert_eq!(
        Linear {
            num: 0,
            den: 1,
            add: 4
        }
        .render("Σ"),
        "4"
    );
}

#[tokio::test]
async fn product_cap_is_configurable() {
    use cardinal::{Options, analyze_sql_with};
    let ctx = shop();
    let schema = Arc::new(Schema::new(
        ["a", "b", "c", "d"]
            .map(|n| Field::new(n, DataType::Int64, true))
            .to_vec(),
    ));
    ctx.register_table(
        "wide",
        Arc::new(MemTable::try_new(schema, vec![vec![]]).unwrap()),
    )
    .unwrap();
    // Each column is pinned to one value, so there is at most one group, but
    // proving it multiplies four distinct counts.
    let sql = "SELECT a, b, c, d, count(*) FROM wide
               WHERE a = 1 AND b = 2 AND c = 3 AND d = 4 GROUP BY a, b, c, d";
    assert_eq!(Options::default().max_product, 3);
    let b = bounds_in(&ctx, sql).await;
    assert_eq!(b.constant, None);
    assert_eq!(table(&b, "wide"), Some((exactly(1, 1), false)));
    let a = analyze_sql_with(&ctx, sql, Options { max_product: 4 })
        .await
        .unwrap();
    assert_eq!(a.bounds().unwrap().constant, Some(1));
}

#[tokio::test]
async fn contradictory_filter_returns_nothing() {
    let b = bounds("SELECT * FROM users WHERE age > 20 AND age < 10").await;
    assert_eq!(b.constant, Some(0));
    // Also across operators: the join key cannot satisfy both sides' filters.
    let b = bounds(
        "SELECT * FROM (SELECT * FROM users WHERE id < 5) u
         JOIN (SELECT * FROM orders WHERE user_id > 10) o ON u.id = o.user_id",
    )
    .await;
    assert_eq!(b.constant, Some(0));
}

#[tokio::test]
async fn range_on_a_key_is_a_constant_bound() {
    let b = bounds("SELECT * FROM users WHERE id BETWEEN 1 AND 10").await;
    assert_eq!(b.constant, Some(10));
    let b = bounds("SELECT * FROM users WHERE (id IN (1, 2) OR id >= 7 AND id < 9) AND id <> 2").await;
    assert_eq!(b.constant, Some(3));
}

#[tokio::test]
async fn range_on_a_joined_key_bounds_the_other_side_of_an_equality() {
    // o.user_id takes the values of u.id, which is in 1..=5; grouping by it
    // gives at most 5 groups.
    let b = bounds(
        "SELECT o.user_id, count(*) FROM orders o JOIN users u ON o.user_id = u.id
         WHERE u.id BETWEEN 1 AND 5 GROUP BY o.user_id",
    )
    .await;
    assert_eq!(b.constant, Some(5));
}

#[tokio::test]
async fn group_by_case_has_one_group_per_branch() {
    let b = bounds(
        "SELECT CASE WHEN age > 60 THEN 'old' WHEN age < 20 THEN 'young' END, count(*)
         FROM users GROUP BY 1",
    )
    .await;
    // 'old', 'young', NULL
    assert_eq!(b.constant, Some(3));
}

#[tokio::test]
async fn group_by_date_parts() {
    let b = bounds(
        "SELECT date_part('month', make_date(2000, id, 1)), count(*) FROM users GROUP BY 1",
    )
    .await;
    // 12 months and NULL.
    assert_eq!(b.constant, Some(13));
    let b = bounds(
        "SELECT date_part('year', d), count(*)
         FROM (SELECT make_date(1990 + age, 1, 1) AS d FROM users)
         WHERE d >= DATE '1995-06-01' AND d < DATE '1998-01-01' GROUP BY 1",
    )
    .await;
    // 1995, 1996, 1997
    assert_eq!(b.constant, Some(3));
}

#[tokio::test]
async fn tpch_queries_filtered_to_few_groups_are_constant() {
    let ctx = common::tpch_datasets().remove(0).context(true);
    // Two nations each, and two ship years.
    let b = bounds_in(&ctx, include_str!("tpch/q07.sql")).await;
    assert_eq!(b.constant, Some(8));
    // Two order years.
    let b = bounds_in(&ctx, include_str!("tpch/q08.sql")).await;
    assert_eq!(b.constant, Some(2));
    // Seven country codes, from a filter on the grouped expression.
    let b = bounds_in(&ctx, include_str!("tpch/q22.sql")).await;
    assert_eq!(b.constant, Some(7));
}

#[tokio::test]
async fn groups_with_several_rows_are_few() {
    // Each surviving group holds at least two of the table's rows.
    let b = bounds("SELECT name, count(*) FROM users GROUP BY name HAVING count(*) > 1").await;
    assert_eq!(table(&b, "users"), Some((exactly(1, 2), false)));
    let b = bounds(
        "SELECT o.user_id FROM orders o JOIN users u ON o.user_id = u.id
         GROUP BY o.user_id HAVING count(o.id) >= 3 ORDER BY 1",
    )
    .await;
    assert_eq!(table(&b, "orders"), Some((exactly(1, 3), false)));
}

#[tokio::test]
async fn disjoint_filters_of_one_table_partition_it() {
    // No user is both under 18 and at least 18.
    let b = bounds(
        "SELECT id FROM users WHERE age < 18 UNION ALL SELECT id FROM users WHERE age >= 18",
    )
    .await;
    assert_eq!(table(&b, "users"), Some((exactly(1, 1), false)));
    let b = bounds(
        "SELECT name FROM users WHERE age < 18
         UNION ALL SELECT name FROM users WHERE age BETWEEN 18 AND 64
         UNION ALL SELECT name FROM users WHERE age > 64
         UNION ALL SELECT name FROM users WHERE age IS NULL",
    )
    .await;
    assert_eq!(table(&b, "users"), Some((exactly(1, 1), false)));
    // Overlapping filters can hold the same rows twice.
    let b = bounds(
        "SELECT id FROM users WHERE age < 30 UNION ALL SELECT id FROM users WHERE age > 20",
    )
    .await;
    assert_eq!(table(&b, "users"), Some((exactly(2, 1), false)));
}
