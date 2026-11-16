//! Reference plans ([`cardinal::Builder::with_plans`]) on the DuckDB
//! fixtures: each query with the other queries' profiles. Compare it with
//! the query alone, one line per query, with
//!
//! ```sh
//! cargo test --release --test reference_plans against_plain -- --ignored --nocapture   # ONLY=q03,q11 for some
//! ```
//!
//! `DEAD_COLUMNS=1` leaves out dead columns ([`cardinal::postprocess`]).

mod fixtures;

use std::time::Instant;

use cardinal::observed::ObservedPlan;
use cardinal::{Analysis, Options, Postprocess};
use fixtures::{catalog, foreign_keys, plans};

async fn profiles() -> Vec<ObservedPlan> {
    let mut out = vec![];
    for dir in ["extra", "tpch"] {
        out.extend(plans(dir).await);
    }
    out
}

fn options() -> Options {
    let dead_columns = std::env::var("DEAD_COLUMNS").is_ok_and(|v| v == "1");
    Options { foreign_keys: foreign_keys(), postprocess: Postprocess { dead_columns }, ..Default::default() }
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

/// The same cap with dead columns left out: the pins and the
/// `referenced size` claims keep `part`'s size and the group keys live.
#[tokio::test]
async fn caps_with_dead_columns() {
    let catalog = catalog().await;
    let all = profiles().await;
    let q = all.iter().find(|p| p.name == "q11").unwrap();
    let others = all.iter().filter(|p| p.name != q.name);
    let options = Options { postprocess: Postprocess { dead_columns: true }, ..options() };
    let b = Analysis::plan(&catalog, q).options(options).with_plans(others).build().unwrap().bounds().unwrap();
    assert!(b.holds(q.nodes[q.root].rows), "{b}");
    assert_eq!(b.upper, Some(2000), "{b}");
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
