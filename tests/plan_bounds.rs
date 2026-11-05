//! Bounds on every operator's output and on their sum
//! ([`Analysis::plan_bounds`]): what they prove on the shop's tables held to
//! sizes, and that real executions stay within them.

mod common;

use cardinal::{Analysis, Bounds, PlanBounds, analyze_sql};
use datafusion::prelude::SessionContext;

const SIZES: &[(&str, u64)] = &[("users", 100), ("orders", 300), ("products", 50), ("order_items", 1000)];

const QUERIES: &[&str] = &[
    "SELECT * FROM users WHERE id = 5",
    "SELECT * FROM users LIMIT 10",
    "SELECT u.name, o.amount FROM users u JOIN orders o ON u.id = o.user_id WHERE o.amount > 10",
    "SELECT user_id, count(*) FROM orders GROUP BY user_id",
    "SELECT * FROM users WHERE age > 20 UNION ALL SELECT * FROM users WHERE age <= 20",
    "SELECT DISTINCT age FROM users ORDER BY age LIMIT 5",
    "SELECT * FROM orders o LEFT JOIN users u ON o.user_id = u.id",
];

fn shop() -> SessionContext {
    common::shop_datasets().remove(0).context(true)
}

async fn analyze(ctx: &SessionContext, sql: &str) -> Analysis {
    analyze_sql(ctx, sql, Default::default()).await.unwrap()
}

/// `sql`'s plan bounds with the shop's tables held to [`SIZES`].
async fn sized(sql: &str) -> PlanBounds {
    let a = analyze(&shop(), sql).await.with_facts(&common::table_sizes(SIZES)).unwrap();
    let p = a.plan_bounds().unwrap();
    println!("{sql}");
    for (i, n) in p.nodes.iter().enumerate() {
        println!("  {i} {}: {}", n.operator, n.bounds);
    }
    println!("  total: {}", p.total);
    assert_eq!(p.nodes.last().unwrap().bounds, a.bounds().unwrap(), "the root's range is bounds()");
    p
}

fn range(lo: u64, hi: u64) -> Bounds {
    Bounds { lower: lo, upper: Some(hi) }
}

/// The node whose operator starts with `op`, the first if several do.
fn node<'a>(p: &'a PlanBounds, op: &str) -> &'a Bounds {
    &p.nodes.iter().find(|n| n.operator.starts_with(op)).unwrap_or_else(|| panic!("no {op}")).bounds
}

#[tokio::test]
async fn a_key_lookup_reads_the_table_and_keeps_at_most_one_row() {
    let p = sized("SELECT * FROM users WHERE id = 5").await;
    assert_eq!(*node(&p, "TableScan"), range(100, 100));
    assert_eq!(*node(&p, "Filter"), range(0, 1));
    assert_eq!(p.total.lower, 100);
}

#[tokio::test]
async fn a_left_join_to_a_key_keeps_each_row() {
    let p = sized("SELECT * FROM orders o LEFT JOIN users u ON o.user_id = u.id").await;
    assert_eq!(*node(&p, "Left Join"), range(300, 300));
    assert_eq!(p.total, range(1100, 1100));
}

#[tokio::test]
async fn the_total_is_at_least_the_sum_of_lowers_and_at_most_the_sum_of_uppers() {
    for sql in QUERIES {
        let p = sized(sql).await;
        let lower: u64 = p.nodes.iter().map(|n| n.bounds.lower).sum();
        let upper: Option<u64> = p.nodes.iter().map(|n| n.bounds.upper).sum();
        assert!(p.total.lower >= lower, "{sql}: {} < {lower}", p.total);
        if let Some(hi) = upper {
            assert!(p.total.upper.is_some_and(|t| t <= hi), "{sql}: {} > {hi}", p.total);
        }
    }
}

/// Every operator's real row count is in its range, and their sum in the
/// total's, with the tables held to their real sizes.
#[tokio::test]
async fn real_executions_stay_within_every_range() {
    for dataset in common::shop_datasets().into_iter().filter(|d| d.unique_keys) {
        let ctx = dataset.context(true);
        for sql in QUERIES {
            let a = analyze(&ctx, sql).await;
            let v = a.validate(&ctx).await.unwrap();
            assert!(v.violation.is_none(), "{sql}: {:?}", v.violation);
            let sizes: Vec<(&str, u64)> = a.scans.iter().map(|(s, t)| (t.as_str(), v.rows[s])).collect();
            let p = a.with_facts(&common::table_sizes(&sizes)).unwrap().plan_bounds().unwrap();
            let failures = common::check_plan_bounds(&p, &v);
            assert!(failures.is_empty(), "{sql}: {failures:?}");
        }
    }
}
