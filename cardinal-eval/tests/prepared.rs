//! The prebaked benchmarks agree with the library: each target's operators
//! are those its operator truth was counted for. Skipped for a benchmark
//! not prebaked.

use cardinal_eval::bench::{Benchmark, default_data};

#[tokio::test]
async fn tpch_operator_truth_matches_operators() {
    if !default_data().join("tpch/manifest.json").exists() {
        return;
    }
    let b = Benchmark::load(&default_data(), "tpch").await.unwrap();
    b.require_prepared().unwrap();
    assert_eq!(b.q_ref.len(), 22);
    for q in &b.q_target {
        let a = b.builder(q).await.unwrap().build().unwrap();
        let truth = &b.operator_truth[q];
        let ops = a.operators();
        assert_eq!(ops.len(), truth.len(), "{q}");
        for (o, t) in ops.iter().zip(truth) {
            assert_eq!((&o.var, &o.operator), (&t.var, &t.operator), "{q}");
        }
        assert_eq!(truth.last().unwrap().rows, Some(b.truth[q]), "{q}");
    }
}

/// DuckDB's profiles pin operators as reference plans, and the bounds
/// they give hold.
#[tokio::test]
async fn tpch_profiles_pin() {
    if !default_data().join("tpch/manifest.json").exists() {
        return;
    }
    let b = Benchmark::load(&default_data(), "tpch").await.unwrap();
    let refs: Vec<_> = ["q01", "q14"].iter().map(|q| b.profile("duckdb", q).unwrap()).collect();
    let a = b.builder("q06").await.unwrap().with_plans(refs).build().unwrap();
    assert!(a.stats().pinned > 0, "{:?}", a.stats());
    let (bounds, _) = a.node_bounds(0).unwrap();
    assert!(bounds.holds(b.operator_truth["q06"][0].rows.unwrap()), "{bounds}");
}
