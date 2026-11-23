//! What an analysis reports of itself: its budgets ([`Limits`]), how it
//! was built ([`Analysis::stats`]), its operators and their bounds one at
//! a time ([`Analysis::node_bounds`]), and which plans it would use
//! ([`Builder::relevant`]).

mod fixtures;

use cardinal::observed::ObservedPlan;
use cardinal::{Analysis, Error, Limits, Options};
use fixtures::{context, foreign_keys, plans, query};

fn options() -> Options {
    Options { foreign_keys: foreign_keys(), ..Default::default() }
}

/// The DuckDB profiles of the `extra` fixtures: every query's but `except`.
async fn profiles(except: &str) -> Vec<ObservedPlan> {
    plans("extra").await.into_iter().filter(|p| p.name != except).collect()
}

#[test]
fn default_limits_are_unchanged() {
    let l = Limits::default();
    assert_eq!((l.search_first, l.search, l.link, l.timeout_ms), (10_000_000, 300_000, 1_000_000, Some(10_000)));
    assert_eq!(Options::default().limits, l);
}

/// With no budget, no check gives up at one, and the bounds still hold.
#[tokio::test]
async fn unbounded_limits_leave_no_check_limited() {
    let ctx = context();
    let name = "join_filtered";
    let plans = profiles(name).await;
    let options = Options { limits: Limits::unbounded(), ..options() };
    let a = Analysis::sql(&ctx, &query("extra", name)).await.unwrap().options(options).with_plans(&plans).build().unwrap();
    let (b, s) = a.bounds_with_stats().unwrap();
    let truth = fixtures::plans("extra").await.into_iter().find(|p| p.name == name).unwrap();
    assert!(b.holds(truth.nodes[truth.root].rows), "{b}");
    let link = a.stats().link_checks;
    assert_eq!((s.checks.limited, s.checks.timed_out, link.limited, link.timed_out), (0, 0, 0, 0), "{s:?} {link:?}");
    assert!(s.checks.checks() > 0 && s.checks.rlimit > 0, "{s:?}");
}

/// The query's operators, and their variables, are the same with and
/// without plans; [`Analysis::node_bounds`] of the root is
/// [`Analysis::bounds`].
#[tokio::test]
async fn operators_are_stable() {
    let ctx = context();
    let name = "join_filtered";
    let plans = profiles(name).await;
    let sql = query("extra", name);
    let alone = Analysis::sql(&ctx, &sql).await.unwrap().options(options()).build().unwrap();
    let with = Analysis::sql(&ctx, &sql).await.unwrap().options(options()).with_plans(&plans).build().unwrap();
    assert_eq!(alone.operators(), with.operators());
    for a in [&alone, &with] {
        let ops = a.operators();
        let root = ops.len() - 1;
        assert_eq!(ops[root].var, a.root);
        assert_eq!(a.node_bounds(root).unwrap().0, a.bounds().unwrap());
        assert!(matches!(a.node_bounds(ops.len()), Err(Error::NoOperator(_))));
        assert_eq!(a.stats().nodes, ops.len());
    }
}

/// The build's counts: plans given and selected, pins, the reduction.
#[tokio::test]
async fn build_stats_count_plans_and_pins() {
    let ctx = context();
    let name = "join_filtered";
    let plans = profiles(name).await;
    let sql = query("extra", name);
    let alone = Analysis::sql(&ctx, &sql).await.unwrap().options(options()).build().unwrap();
    let s = alone.stats();
    assert_eq!((s.plans_given, s.plans_selected, s.plan_nodes, s.pinned, s.floors), (0, 0, 0, 0, 0), "{s:?}");
    assert_eq!(s.assertions, s.assertions_before);
    assert!(s.total >= s.rules + s.link + s.pins, "{s:?}");

    let builder = Analysis::sql(&ctx, &sql).await.unwrap().options(options());
    let relevant = plans.iter().filter(|p| builder.relevant(p)).count();
    let with = builder.with_plans(&plans).build().unwrap();
    let s = with.stats();
    assert_eq!(s.plans_given, plans.len());
    assert_eq!(s.plans_selected, relevant);
    assert!(0 < relevant && relevant < plans.len(), "{relevant} of {}", plans.len());
    assert!(s.plan_nodes > 0 && s.pinned > 0, "{s:?}");
    assert!(s.assertions < s.assertions_before, "{s:?}");
    assert!(s.link_classes > 0 && s.links > 0 && s.link_checks.checks() > 0, "{s:?}");
}

/// A plan [`Builder::relevant`] rejects adds no constraint: the analysis
/// is the one without it.
#[tokio::test]
async fn irrelevant_plans_add_nothing() {
    let ctx = context();
    let name = "join_filtered";
    let plans = profiles(name).await;
    let sql = query("extra", name);
    let builder = Analysis::sql(&ctx, &sql).await.unwrap().options(options());
    let (used, unused): (Vec<&ObservedPlan>, Vec<&ObservedPlan>) = plans.iter().partition(|p| builder.relevant(p));
    assert!(!unused.is_empty());
    let a = builder.clone().with_plans(used.iter().copied()).build().unwrap();
    let b = builder.with_plans(plans.iter()).build().unwrap();
    assert_eq!(a.constraints(), b.constraints());
    assert_eq!(b.stats().plans_selected, used.len());
}
