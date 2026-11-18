//! Reference plans ([`cardinal::Builder::with_plans`]) on the DuckDB
//! fixtures: each query with the other queries' profiles. Compare it with
//! the query alone, one line per query, with
//!
//! ```sh
//! cargo test --release --test reference_plans against_plain -- --ignored --nocapture   # ONLY=q03,q11 for some
//! ```

mod fixtures;

use std::time::Instant;

use cardinal::observed::ObservedPlan;
use cardinal::{Analysis, Options};
use fixtures::{catalog, foreign_keys, plans};

async fn profiles() -> Vec<ObservedPlan> {
    let mut out = vec![];
    for dir in ["extra", "tpch"] {
        out.extend(plans(dir).await);
    }
    out
}

fn options() -> Options {
    Options { foreign_keys: foreign_keys(), ..Default::default() }
}

/// q11 scans no `part`, but groups by `ps_partkey`: the other profiles'
/// scans of `part` pin its size, which caps the groups by the foreign key.
#[tokio::test]
async fn caps_through_a_foreign_key() {
    let catalog = catalog().await;
    let all = profiles().await;
    let q = all.iter().find(|p| p.name == "q11").unwrap();
    let others = all.iter().filter(|p| p.name != q.name);
    let b = Analysis::plan(&catalog, q).options(options()).with_plans(others).build().unwrap().bounds().unwrap();
    assert!(b.holds(q.nodes[q.root].rows), "{b}");
    assert_eq!(b.upper, Some(2000), "{b}");
}

/// The trace, which prints every constraint before the reduction, leaves
/// the reduced constraints as they are without it.
#[tokio::test]
async fn trace_leaves_the_constraints() {
    let catalog = catalog().await;
    let all = profiles().await;
    let q = all.iter().find(|p| p.name == "q11").unwrap();
    let others: Vec<&ObservedPlan> = all.iter().filter(|p| p.name != q.name).collect();
    let build = |trace| {
        let options = Options { trace, ..options() };
        Analysis::plan(&catalog, q).options(options).with_plans(others.iter().copied()).build().unwrap()
    };
    let (plain, traced) = (build(false), build(true));
    assert!(traced.trace.is_some());
    assert_eq!(plain.constraints(), traced.constraints());
}

/// Reference plans given to a query with no catalog to read them against
/// are refused.
#[tokio::test]
async fn plans_need_a_catalog() {
    let all = profiles().await;
    let plan = datafusion::logical_expr::LogicalPlanBuilder::empty(true).build().unwrap();
    let e = Analysis::logical(plan).with_plans(&all).build().unwrap_err();
    assert!(matches!(e, cardinal::Error::NoCatalog), "{e}");
}

/// Each query's bounds, and time, alone and with every other profile.
#[tokio::test]
#[ignore = "slow: minutes; prints a comparison"]
async fn against_plain() {
    let catalog = catalog().await;
    let all = profiles().await;
    let only = std::env::var("ONLY").ok();
    println!("query\ttrue\tplain\tplans\tplain s\tplans s");
    let mut failures = vec![];
    for q in &all {
        if only.as_ref().is_some_and(|o| !o.split(',').any(|n| n == q.name)) {
            continue;
        }
        let truth = q.nodes[q.root].rows;
        let t = Instant::now();
        let plain = Analysis::plan(&catalog, q).options(options()).build().unwrap().bounds().unwrap();
        let t_plain = t.elapsed().as_secs_f64();
        let t = Instant::now();
        let others = all.iter().filter(|p| p.name != q.name);
        let joint = Analysis::plan(&catalog, q).options(options()).with_plans(others).build().unwrap().bounds().unwrap();
        let t_joint = t.elapsed().as_secs_f64();
        println!("{}\t{truth}\t{plain}\t{joint}\t{t_plain:.2}\t{t_joint:.2}", q.name);
        if !joint.holds(truth) {
            failures.push(format!("{}: {joint}, not {truth}", q.name));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}
