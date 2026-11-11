//! [`cardinal::joint::analyze_joint`] on the DuckDB fixtures: each query
//! with the other queries' profiles. Compare it with
//! [`cardinal::Analysis::with_facts`], one line per query, with
//!
//! ```sh
//! cargo test --release --test joint_facts against_facts -- --ignored --nocapture   # ONLY=q03,q11 for some
//! ```

mod fixtures;

use std::time::Instant;

use cardinal::Options;
use cardinal::facts::FactSet;
use cardinal::observed::ObservedPlan;
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
/// `with_facts` gives no cap.
#[tokio::test]
async fn caps_through_a_foreign_key() {
    let catalog = catalog().await;
    let all = profiles().await;
    let q = all.iter().find(|p| p.name == "q11").unwrap();
    let others: Vec<_> = all.iter().filter(|p| p.name != q.name).cloned().collect();
    let b = cardinal::joint::analyze_joint(&catalog, q, &others, options()).unwrap().bounds().unwrap();
    assert!(b.holds(q.nodes[q.root].rows), "{b}");
    assert_eq!(b.upper, Some(2000), "{b}");
}

/// Each query's bounds, and time, from `with_facts` and from
/// `analyze_joint`, with every other profile.
#[tokio::test]
#[ignore = "slow: minutes; prints a comparison"]
async fn against_facts() {
    let catalog = catalog().await;
    let all = profiles().await;
    let only = std::env::var("ONLY").ok();
    println!("query\ttrue\twith_facts\tjoint\twith_facts s\tjoint s");
    let mut failures = vec![];
    for q in &all {
        if only.as_ref().is_some_and(|o| !o.split(',').any(|n| n == q.name)) {
            continue;
        }
        let others: Vec<_> = all.iter().filter(|p| p.name != q.name).cloned().collect();
        let truth = q.nodes[q.root].rows;
        let mut set = FactSet::default();
        for o in &others {
            set.observe(o);
        }
        let facts = cardinal::Facts::new(set);

        let t = Instant::now();
        let with = cardinal::analyze_observed(&catalog, q, options()).unwrap().with_facts(&facts).unwrap().bounds().unwrap();
        let t_with = t.elapsed().as_secs_f64();
        let t = Instant::now();
        let joint = cardinal::joint::analyze_joint(&catalog, q, &others, options()).unwrap().bounds().unwrap();
        let t_joint = t.elapsed().as_secs_f64();
        println!("{}\t{truth}\t{with}\t{joint}\t{t_with:.2}\t{t_joint:.2}", q.name);
        if !joint.holds(truth) {
            failures.push(format!("{}: {joint}, not {truth}", q.name));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}
