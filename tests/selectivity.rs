//! The output cardinality as a formula over table sizes and selectivities.
//! Keys are declared on `users.id`, `orders.id` and `products.id`. Every query
//! is also executed on each shop dataset, and its formulas checked against the
//! real row counts.

mod common;

use std::collections::HashMap;

use cardinal::{Kind, Options, SelectivityReport, analyze_sql, analyze_sql_with};

const ON: Options = common::SELECTIVITY;

/// The report for `sql`, validated on every dataset with unique keys.
async fn report(sql: &str) -> SelectivityReport {
    let mut report = None;
    for d in common::shop_datasets().into_iter().filter(|d| d.unique_keys) {
        let name = d.name.clone();
        let ctx = d.context(true);
        let a = analyze_sql_with(&ctx, sql, ON).await.unwrap();
        let v = a.validate(&ctx).await.unwrap();
        assert_eq!(v.violation, None, "{sql}\n{}", a.plan);
        let check = v.selectivity.expect("selectivity was enabled");
        assert_eq!(check.violation, None, "on {name}: {sql}\n{}", a.plan);
        report = a.selectivity;
    }
    let report = report.unwrap();
    println!("{sql}\n  {report}");
    report
}

/// The formula and the kinds of the selectivities it needs.
async fn formula(sql: &str) -> (String, Vec<Kind>) {
    let r = report(sql).await;
    let kinds = r.required.iter().map(|s| s.kind.clone()).collect();
    (r.output.to_string(), kinds)
}

fn sizes(tables: &[(&str, u64)]) -> HashMap<String, u64> {
    tables.iter().map(|(t, n)| (t.to_string(), *n)).collect()
}

#[tokio::test]
async fn off_by_default() {
    let ctx = common::shop_datasets().remove(0).context(true);
    let a = analyze_sql(&ctx, "SELECT id FROM users WHERE age > 30").await.unwrap();
    assert!(a.selectivity.is_none());
    assert!(a.validate(&ctx).await.unwrap().selectivity.is_none());
}

#[tokio::test]
async fn projection_passes_every_row() {
    let r = report("SELECT id, age + 1 FROM users").await;
    assert_eq!(r.output.to_string(), "|users|");
    assert!(r.is_exact());
    assert!(r.required.is_empty());
}

#[tokio::test]
async fn filter_depends_on_its_predicate() {
    let r = report("SELECT id FROM users WHERE age > 30").await;
    assert_eq!(r.output.to_string(), "s1·|users|");
    assert!(!r.is_exact());
    let [s] = &r.required[..] else { panic!("{r}") };
    let Kind::Filter(p) = &s.kind else { panic!("{s}") };
    assert!(p.to_string().contains("age"), "{p}");
    assert_eq!((s.range.lo, s.range.hi), (0.0, 1.0));
}

#[tokio::test]
async fn group_by_depends_on_its_distinct_keys() {
    let (f, kinds) = formula("SELECT name, count(*) FROM users GROUP BY name").await;
    assert_eq!(f, "s1·|users|");
    let [Kind::Distinct(keys)] = &kinds[..] else { panic!("{kinds:?}") };
    assert_eq!(keys.len(), 1);
    assert!(keys[0].to_string().contains("name"));

    let (f, kinds) = formula("SELECT DISTINCT name, age FROM users").await;
    assert_eq!(f, "s1·|users|");
    assert!(matches!(&kinds[..], [Kind::Distinct(keys)] if keys.len() == 2));
}

#[tokio::test]
async fn group_by_a_key_is_resolved() {
    // Every row is its own group: the selectivity is not needed.
    let r = report("SELECT id, count(*) FROM users GROUP BY id").await;
    assert_eq!(r.output.to_string(), "|users|");
    assert!(r.is_exact());
    assert_eq!(r.resolved.len(), 1);
    assert!(matches!(r.resolved[0].kind, Kind::Distinct(_)));
}

#[tokio::test]
async fn contradictory_filter_is_resolved() {
    let r = report("SELECT id FROM users WHERE age > 50 AND age < 40").await;
    assert_eq!(r.output.to_string(), "0");
    assert!(r.is_exact());
}

#[tokio::test]
async fn ungrouped_aggregate_and_limit_need_nothing() {
    let r = report("SELECT count(*) FROM orders WHERE amount > 10").await;
    assert_eq!(r.output.to_string(), "1");
    let r = report("SELECT id FROM users ORDER BY id LIMIT 5").await;
    assert_eq!(r.output.to_string(), "min(5, |users|)");
    assert!(r.is_exact());
    let r = report("SELECT id FROM users LIMIT 5 OFFSET 2").await;
    assert_eq!(r.output.to_string(), "min(5, max(|users| - 2, 0))");
}

#[tokio::test]
async fn selectivities_compose() {
    // The HAVING filter's selectivity is a share of the groups.
    let (f, kinds) = formula(
        "SELECT name, count(*) FROM users WHERE age > 30 GROUP BY name HAVING count(*) > 1",
    )
    .await;
    assert_eq!(f, "s1·s2·s3·|users|");
    assert!(matches!(
        &kinds[..],
        [Kind::Filter(_), Kind::Distinct(_), Kind::Filter(_)]
    ));
}

#[tokio::test]
async fn semi_join_with_nothing_is_resolved() {
    // A semi join against an empty relation keeps nothing.
    let r = report("SELECT id FROM users WHERE id IN (SELECT user_id FROM orders WHERE 1 = 0)").await;
    assert_eq!(r.output.to_string(), "0");
}

#[tokio::test]
async fn inner_join_is_a_share_of_the_cross_product() {
    let (f, kinds) = formula("SELECT * FROM orders o JOIN users u ON o.user_id = u.id").await;
    assert_eq!(f, "s1·|orders|·|users|");
    assert!(matches!(&kinds[..], [Kind::Join { on, filter: None }] if on.len() == 1));

    let r = report("SELECT * FROM users CROSS JOIN products").await;
    assert_eq!(r.output.to_string(), "|users|·|products|");
    assert!(r.is_exact());
}

#[tokio::test]
async fn semi_and_anti_joins_share_a_definition() {
    let (f, kinds) =
        formula("SELECT id FROM users u WHERE EXISTS (SELECT 1 FROM orders o WHERE o.user_id = u.id)")
            .await;
    assert_eq!(f, "s1·|users|");
    assert!(matches!(&kinds[..], [Kind::Match { left: true, .. }]));

    let (f, kinds) = formula(
        "SELECT id FROM users u WHERE NOT EXISTS (SELECT 1 FROM orders o WHERE o.user_id = u.id)",
    )
    .await;
    assert_eq!(f, "(1 - s1)·|users|");
    assert!(matches!(&kinds[..], [Kind::Match { left: true, .. }]));
}

#[tokio::test]
async fn outer_joins_add_the_unmatched_rows() {
    // Matched pairs, plus the users without an order.
    let (f, kinds) =
        formula("SELECT * FROM users u LEFT JOIN orders o ON o.user_id = u.id").await;
    assert_eq!(f, "s1·|users|·|orders| + (1 - s2)·|users|");
    assert!(matches!(
        &kinds[..],
        [Kind::Join { .. }, Kind::Match { left: true, .. }]
    ));

    let (f, kinds) = formula(
        "SELECT * FROM order_items a FULL JOIN order_items b ON a.order_id = b.product_id",
    )
    .await;
    assert_eq!(
        f,
        "s1·|order_items|·|order_items| + (1 - s2)·|order_items| + (1 - s3)·|order_items|"
    );
    assert_eq!(kinds.len(), 3);
}

#[tokio::test]
async fn left_join_to_a_key_is_resolved() {
    // Each order matches at most one user, so it appears exactly once.
    let r = report("SELECT * FROM orders o LEFT JOIN users u ON o.user_id = u.id").await;
    assert_eq!(r.output.to_string(), "|orders|");
    assert!(r.is_exact());
    assert_eq!(r.resolved.len(), 2);
}

#[tokio::test]
async fn union_adds_its_inputs() {
    let r = report("SELECT id FROM users WHERE age < 30 UNION ALL SELECT id FROM orders").await;
    assert_eq!(r.output.to_string(), "s1·|users| + |orders|");
}

#[tokio::test]
async fn unmodelled_operators_are_unknowns_of_their_own() {
    let r = report("SELECT name, count(*) FROM users GROUP BY ROLLUP (name)").await;
    assert!(!r.is_exact());
    assert!(r.required.is_empty());
    assert!(r.output.to_string().starts_with("|op"), "{r}");
}

#[tokio::test]
async fn evaluate_plugs_values_in() {
    let r = report(
        "SELECT o.id, u.name FROM orders o JOIN users u ON o.user_id = u.id WHERE u.age > 30",
    )
    .await;
    let names: Vec<&str> = r.required.iter().map(|s| s.name.as_str()).collect();
    assert_eq!(names.len(), 2, "{r}");
    let tables = sizes(&[("users", 100), ("orders", 1000)]);

    // No values: only the proven ranges.
    let x = r.evaluate(&tables, &HashMap::new()).unwrap();
    assert_eq!((x.lo, x.hi), (0.0, 100_000.0));
    assert_eq!(x.exact(), None);

    // The filter keeps a quarter of the users, and each order has one user.
    let join = r
        .required
        .iter()
        .find(|s| matches!(s.kind, Kind::Join { .. }))
        .unwrap();
    let filter = r
        .required
        .iter()
        .find(|s| matches!(s.kind, Kind::Filter(_)))
        .unwrap();
    let mut values = HashMap::from([(filter.name.clone(), 0.25)]);
    let x = r.evaluate(&tables, &values).unwrap();
    assert_eq!((x.lo, x.hi), (0.0, 25_000.0));
    values.insert(join.name.clone(), 0.01);
    let x = r.evaluate(&tables, &values).unwrap();
    assert_eq!(x.exact(), Some(250.0));

    // A missing table size is an error.
    assert!(r.evaluate(&sizes(&[("users", 100)]), &values).is_err());
}

#[tokio::test]
async fn measured_selectivities_reproduce_the_output() {
    let sql = "SELECT u.name, count(*) FROM users u LEFT JOIN orders o ON o.user_id = u.id
               WHERE u.age > 20 GROUP BY u.name";
    for d in common::shop_datasets().into_iter().filter(|d| d.unique_keys) {
        let ctx = d.context(true);
        let a = analyze_sql_with(&ctx, sql, ON).await.unwrap();
        let v = a.validate(&ctx).await.unwrap();
        let r = a.selectivity.as_ref().unwrap();
        let check = v.selectivity.as_ref().unwrap();
        let tables: HashMap<String, u64> = a
            .scans
            .iter()
            .map(|(scan, table)| (table.clone(), v.rows[scan]))
            .collect();
        let x = r.evaluate(&tables, &check.values).unwrap();
        // Selectivities over no rows have no measured value; then the
        // formula's range still holds the count.
        assert!(x.contains(v.rows[&a.root] as f64), "{r}\n{x}");
        if check.values.len() == r.required.len() {
            assert_eq!(x.exact().map(f64::round), Some(v.rows[&a.root] as f64), "{r}");
        }
    }
}
