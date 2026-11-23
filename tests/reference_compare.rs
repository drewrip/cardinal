//! Bounds on the fixture queries, with reference plans and without, against
//! their true row counts. Each fixture query is analyzed as DataFusion
//! plans it and as the engine did, with its own profile as a reference plan
//! and, with `PLANS=own,others`, with every other profile of its suite
//! (leave-one-out: slow, tens of minutes), and its bounds must hold its
//! true row count. The contenders are `plans`
//! ([`cardinal::Builder::with_plans`]) and `plain`, the query alone.
//!
//! ```sh
//! cargo test --release --test reference_compare -- --nocapture
//! SUITE=duckdb ONLY=q03,q05 CONTENDERS=plans PLANS=others cargo test ...
//! ```
//!
//! Writes one JSON row per (query, planner, plans, contender) to `OUT`, by
//! default `target/reference_compare.json`.

mod fixtures;

use std::collections::BTreeMap;
use std::time::{Duration, Instant};

use cardinal::observed::ObservedPlan;
use cardinal::{Analysis, Bounds, Builder, Options, SearchStats};
use fixtures::{catalog, context, foreign_keys, pg_plans, pg_query, plans, query};
use serde_json::json;

struct Case {
    suite: &'static str,
    name: String,
    /// As DataFusion plans it, if it can.
    datafusion: Option<Builder<'static>>,
    plan: ObservedPlan,
}

impl Case {
    fn rows(&self) -> u64 {
        self.plan.nodes[self.plan.root].rows
    }
}

fn options() -> Options {
    Options { foreign_keys: foreign_keys(), ..Default::default() }
}

fn env_list(key: &str) -> Option<Vec<String>> {
    std::env::var(key).ok().map(|v| v.split(',').map(str::to_string).collect())
}

async fn cases() -> Vec<Case> {
    let ctx = context();
    let suites = env_list("SUITE").unwrap_or(vec!["duckdb".into(), "postgres".into()]);
    let only = env_list("ONLY");
    let mut out = vec![];
    for suite in ["duckdb", "postgres"] {
        if !suites.iter().any(|s| s == suite) {
            continue;
        }
        for dir in ["extra", "tpch"] {
            let profiles = match suite {
                "duckdb" => plans(dir).await,
                _ => pg_plans(dir).await,
            };
            for plan in profiles {
                let sql = match suite {
                    "duckdb" => query(dir, &plan.name),
                    _ => pg_query(&plan.name),
                };
                let datafusion = Analysis::sql(&ctx, &sql).await.ok().map(|q| q.options(options()));
                out.push(Case { suite, name: format!("{dir}/{}", plan.name), datafusion, plan });
            }
        }
    }
    // Every case stays a reference plan; only these are bounded.
    for c in &mut out {
        if only.as_ref().is_some_and(|o| !o.iter().any(|n| c.name.ends_with(&format!("/{n}")))) {
            c.name = format!("-{}", c.name);
        }
    }
    out
}

/// The profiles of `suite`: `c`'s own, or every other.
fn references<'c>(cases: &'c [Case], c: &'c Case, which: &str) -> Vec<&'c ObservedPlan> {
    match which {
        "own" => vec![&c.plan],
        _ => cases.iter().filter(|o| o.suite == c.suite && o.name.trim_start_matches('-') != c.name).map(|o| &o.plan).collect(),
    }
}

/// What one contender gave for one query.
struct Outcome {
    bounds: Bounds,
    stats: SearchStats,
    /// Analyzing the query, with the plans.
    setup: Duration,
    search: Duration,
}

fn run(contender: &str, query: &Builder, plans: &[&ObservedPlan]) -> Result<Outcome, String> {
    let e = |e: cardinal::Error| e.to_string();
    let start = Instant::now();
    let a = match contender {
        "plans" => query.clone().with_plans(plans.iter().copied()).build().map_err(e)?,
        "plain" => query.clone().build().map_err(e)?,
        other => panic!("no contender {other}"),
    };
    let setup = start.elapsed();
    let t = Instant::now();
    let (bounds, stats) = a.bounds_with_stats().map_err(e)?;
    Ok(Outcome { bounds, stats, setup, search: t.elapsed() })
}

fn ms(d: Duration) -> f64 {
    d.as_secs_f64() * 1000.0
}

#[tokio::test]
async fn compare() {
    let cases = cases().await;
    let catalog = catalog().await;
    for suite in ["duckdb", "postgres"] {
        let n = cases.iter().filter(|c| c.suite == suite).count();
        if n > 0 {
            println!("{suite}: {n} plans");
        }
    }
    let contenders = env_list("CONTENDERS").unwrap_or(["plans", "plain"].map(String::from).to_vec());
    let plan_sets = env_list("PLANS").unwrap_or(vec!["own".into()]);
    let mut rows = vec![];
    let mut failures = vec![];
    // Per (contender, plans): unsound, tight, hi/truth ratios, outcomes.
    #[derive(Default)]
    struct Total {
        unsound: usize,
        tight: usize,
        bounded: usize,
        ratios: Vec<f64>,
        n: usize,
        errors: usize,
        stats: SearchStats,
        setup: Duration,
        search: Duration,
    }
    let mut totals: BTreeMap<(String, String), Total> = BTreeMap::new();
    for c in cases.iter().filter(|c| !c.name.starts_with('-')) {
        let truth = c.rows();
        let engine = Analysis::plan(&catalog, &c.plan).options(options());
        for which in &plan_sets {
            let plans = references(&cases, c, which);
            let planned = c.datafusion.iter().map(|q| ("datafusion", q)).chain([("engine", &engine)]);
            for (planner, query) in planned {
                let mut line = vec![];
                for contender in &contenders {
                    let total = totals.entry((contender.clone(), which.clone())).or_default();
                    total.n += 1;
                    let context = format!("{} {} by {planner}, {which} plans, {contender}", c.suite, c.name);
                    let o = match run(contender, query, &plans) {
                        Ok(o) => o,
                        Err(e) => {
                            total.errors += 1;
                            failures.push(format!("{context}: error {e}"));
                            rows.push(json!({"suite": c.suite, "query": c.name, "planner": planner, "plans": which, "contender": contender, "error": e}));
                            continue;
                        }
                    };
                    let b = o.bounds;
                    let unsound = !b.holds(truth);
                    total.unsound += usize::from(unsound);
                    total.tight += usize::from(b.upper == Some(truth));
                    if let Some(hi) = b.upper {
                        total.bounded += 1;
                        total.ratios.push(hi as f64 / truth.max(1) as f64);
                    }
                    total.stats += o.stats;
                    total.setup += o.setup;
                    total.search += o.search;
                    if unsound {
                        failures.push(format!("{context}: {b}, not {truth}"));
                    }
                    line.push(format!("{contender}: {b}"));
                    rows.push(json!({
                        "suite": c.suite, "query": c.name, "planner": planner, "plans": which, "contender": contender,
                        "truth": truth, "lo": b.lower, "hi": b.upper, "unsound": unsound,
                        "sat": o.stats.checks.sat, "unsat": o.stats.checks.unsat, "unknown": o.stats.checks.unknown(),
                        "setup_ms": ms(o.setup), "search_ms": ms(o.search), "solver_ms": ms(o.stats.checks.time),
                    }));
                }
                println!("{:<9} {:<26} {:<10} {:<6} truth {truth:<8} {}", c.suite, c.name, planner, which, line.join("  "));
            }
        }
    }
    println!("\n{:<11} {:<6} {:>4} {:>7} {:>8} {:>7} {:>9} {:>9} {:>6} {:>6} {:>7} {:>9} {:>9}",
        "contender", "plans", "n", "errors", "unsound", "tight", "med hi/t", "p90 hi/t", "sat", "unknw", "unsat", "setup s", "search s");
    for ((contender, which), t) in &mut totals {
        t.ratios.sort_by(f64::total_cmp);
        let q = |p: f64| t.ratios.get(((t.ratios.len() as f64 - 1.0) * p).round() as usize).copied().unwrap_or(f64::NAN);
        println!(
            "{contender:<11} {which:<6} {:>4} {:>7} {:>8} {:>3}/{:<3} {:>9.2} {:>9.2} {:>6} {:>6} {:>7} {:>9.1} {:>9.1}",
            t.n, t.errors, t.unsound, t.tight, t.bounded, q(0.5), q(0.9), t.stats.checks.sat, t.stats.checks.unknown(), t.stats.checks.unsat,
            t.setup.as_secs_f64(), t.search.as_secs_f64(),
        );
    }
    let path = std::env::var("OUT").unwrap_or(concat!(env!("CARGO_MANIFEST_DIR"), "/target/reference_compare.json").into());
    std::fs::write(&path, serde_json::to_string_pretty(&rows).unwrap()).unwrap();
    println!("\nwrote {path}");
    assert!(failures.is_empty(), "{failures:#?}");
}
