//! A [`Batch`] analyzes each query as [`cardinal::Builder::build`] does
//! alone, with the batch's options, reference plans and row counts.

mod fixtures;

use cardinal::{Analysis, Options};
use fixtures::{catalog, context, fixtures, foreign_keys, plans, query};

/// A few quick TPC-H queries.
const QUERIES: [&str; 3] = ["q03", "q06", "q12"];

fn options() -> Options {
    Options { foreign_keys: foreign_keys(), ..Default::default() }
}

fn sqls() -> Vec<String> {
    QUERIES.iter().map(|q| query("tpch", q)).collect()
}

/// TPC-H's row counts at the fixtures' scale.
const ROWS: [(&str, u64); 3] = [("lineitem", 60175), ("orders", 15000), ("customer", 1500)];

#[track_caller]
fn assert_same(a: &Analysis, b: &Analysis) {
    assert_eq!(a.root, b.root);
    assert_eq!(a.scans, b.scans);
    assert_eq!(a.plan, b.plan);
    assert_eq!(a.constraints(), b.constraints());
}

#[tokio::test]
async fn sqls_match_sql() {
    let ctx = context();
    let batch = Analysis::sqls(&ctx, sqls()).await.unwrap().options(options());
    assert_eq!(batch.len(), QUERIES.len());
    let analyses = batch.build();
    assert_eq!(analyses.len(), QUERIES.len());
    for (sql, a) in sqls().iter().zip(&analyses) {
        let alone = Analysis::sql(&ctx, sql).await.unwrap().options(options()).build().unwrap();
        assert_same(a.as_ref().unwrap(), &alone);
    }
}

#[tokio::test]
async fn an_invalid_query_fails_alone() {
    let ctx = context();
    let queries = [query("tpch", "q06"), "select * from nowhere".to_string(), query("tpch", "q12")];
    let analyses = Analysis::sqls(&ctx, &queries).await.unwrap().build();
    assert!(analyses[0].is_ok());
    assert!(analyses[1].is_err());
    assert!(analyses[2].is_ok());
}

/// Options, reference plans and row counts reach every query: each is
/// analyzed as it is alone with them, and differs from without.
#[tokio::test]
async fn settings_reach_every_query() {
    let ctx = context();
    let plans = plans("tpch").await;
    let reference = plans.iter().find(|p| p.name == "q03").unwrap();
    let analyses = Analysis::sqls(&ctx, sqls())
        .await
        .unwrap()
        .options(options())
        .with_plans([reference])
        .with_cardinalities(ROWS)
        .build();
    for (sql, a) in sqls().iter().zip(&analyses) {
        let a = a.as_ref().unwrap();
        let plain = Analysis::sql(&ctx, sql).await.unwrap().build().unwrap();
        let alone = Analysis::sql(&ctx, sql).await.unwrap().options(options()).with_plans([reference]).with_cardinalities(ROWS);
        assert_same(a, &alone.build().unwrap());
        assert_ne!(a.constraints(), plain.constraints());
    }
}

#[tokio::test]
async fn batch_of_engine_plans() {
    let catalog = catalog().await;
    let profiles: Vec<(String, String)> = fixtures("tpch").into_iter().filter(|(n, _)| QUERIES.contains(&n.as_str())).collect();
    let duckdb = |(name, json): &(String, String)| Analysis::duckdb(&catalog, json, Some(&query("tpch", name)));
    let analyses = Analysis::batch(profiles.iter().map(duckdb)).options(options()).build();
    assert_eq!(analyses.len(), QUERIES.len());
    for (p, a) in profiles.iter().zip(&analyses) {
        assert_same(a.as_ref().unwrap(), &duckdb(p).unwrap().options(options()).build().unwrap());
    }
}

#[tokio::test]
async fn bounds_all_match_bounds() {
    let ctx = context();
    let analyses: Vec<Analysis> =
        Analysis::sqls(&ctx, sqls()).await.unwrap().with_cardinalities(ROWS).build().into_iter().map(Result::unwrap).collect();
    let bounds = Analysis::bounds_all(&analyses);
    let plans = Analysis::plan_bounds_all(&analyses);
    for ((a, b), p) in analyses.iter().zip(bounds).zip(plans) {
        assert_eq!(b.unwrap(), a.bounds().unwrap());
        assert_eq!(p.unwrap(), a.plan_bounds().unwrap());
    }
}
