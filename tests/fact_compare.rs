//! Bounds on the fixture queries, with facts and without, against their
//! true row counts. Each fixture query is analyzed as DataFusion plans it
//! and as the engine did, with every profile's facts and with every other
//! profile's (leave-one-out), and its bounds must hold its true row count.
//! The contenders are `facts` ([`cardinal::Analysis::with_facts`]) and
//! `plain`, the query alone.
//!
//! ```sh
//! cargo test --release --test fact_compare -- --nocapture
//! SUITE=duckdb ONLY=q03,q05 CONTENDERS=facts FACTS=others cargo test ...
//! ```
//!
//! Writes one JSON row per (query, planner, facts, contender) to `OUT`, by
//! default `target/fact_compare.json`.

mod fixtures;

use std::collections::{BTreeMap, HashMap};
use std::time::{Duration, Instant};

use cardinal::facts::FactSet;
use cardinal::observed::ObservedPlan;
use cardinal::{Analysis, Bounds, Facts, Options, SearchStats};
use fixtures::{catalog, context, foreign_keys, pg_plans, pg_query, plans, query};
use serde_json::json;

struct Case {
    suite: &'static str,
    name: String,
    /// As DataFusion plans it, if it can.
    analysis: Option<Analysis>,
    /// As the engine planned it.
    engine: Analysis,
    plan: ObservedPlan,
    observed: FactSet,
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
    let catalog = catalog().await;
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
                let analysis = cardinal::analyze_sql(&ctx, &sql, options()).await.ok();
                let engine = cardinal::analyze_observed(&catalog, &plan, options()).unwrap();
                let mut observed = FactSet::default();
                observed.observe(&plan);
                observed.observe_translated(&catalog, &plan, &options());
                out.push(Case { suite, name: format!("{dir}/{}", plan.name), analysis, engine, plan, observed });
            }
        }
    }
    // Every case stays a source of facts; only these are bounded.
    for c in &mut out {
        if only.as_ref().is_some_and(|o| !o.iter().any(|n| c.name.ends_with(&format!("/{n}")))) {
            c.name = format!("-{}", c.name);
        }
    }
    out
}

/// The facts of every profile of `suite` but `except`'s, as observed.
fn observed(cases: &[Case], suite: &str, except: Option<&str>) -> FactSet {
    let mut set = FactSet::default();
    for c in cases.iter().filter(|c| c.suite == suite && Some(c.name.as_str()) != except) {
        for f in c.observed.iter() {
            set.insert(f.clone());
        }
        for b in c.observed.bounds() {
            set.insert_bound(b.clone());
        }
        for f in c.observed.floors() {
            set.insert_floor(f.clone());
        }
    }
    set
}

/// What one contender gave for one query.
struct Outcome {
    bounds: Bounds,
    stats: SearchStats,
    /// Putting the facts in.
    setup: Duration,
    search: Duration,
}

fn run(contender: &str, a: &Analysis, facts: &Facts) -> Result<Outcome, String> {
    let e = |e: cardinal::Error| e.to_string();
    let start = Instant::now();
    let a = match contender {
        "facts" => a.with_facts(facts).map_err(e)?,
        "plain" => a.clone(),
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
    for suite in ["duckdb", "postgres"] {
        let n = cases.iter().filter(|c| c.suite == suite).count();
        let facts: usize = cases.iter().filter(|c| c.suite == suite).map(|c| c.observed.len()).sum();
        if n > 0 {
            println!("{suite}: {n} plans, {facts} facts");
        }
    }
    let contenders = env_list("CONTENDERS").unwrap_or(["facts", "plain"].map(String::from).to_vec());
    let fact_sets = env_list("FACTS").unwrap_or(vec!["all".into(), "others".into()]);
    // Every profile's facts serve every query of their suite.
    let all: HashMap<&str, Facts> =
        ["duckdb", "postgres"].into_iter().map(|suite| (suite, Facts::new(observed(&cases, suite, None)))).collect();
    let mut rows = vec![];
    let mut failures = vec![];
    // Per (contender, facts): unsound, tight, hi/truth ratios, outcomes.
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
        for which in &fact_sets {
            let facts = match which.as_str() {
                "others" => &Facts::new(observed(&cases, c.suite, Some(&c.name))),
                _ => &all[c.suite],
            };
            let planned = c.analysis.iter().map(|a| ("datafusion", a)).chain([("engine", &c.engine)]);
            for (planner, a) in planned {
                let mut line = vec![];
                for contender in &contenders {
                    let total = totals.entry((contender.clone(), which.clone())).or_default();
                    total.n += 1;
                    let context = format!("{} {} by {planner}, {which} facts, {contender}", c.suite, c.name);
                    let o = match run(contender, a, facts) {
                        Ok(o) => o,
                        Err(e) => {
                            total.errors += 1;
                            failures.push(format!("{context}: error {e}"));
                            rows.push(json!({"suite": c.suite, "query": c.name, "planner": planner, "facts": which, "contender": contender, "error": e}));
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
                        "suite": c.suite, "query": c.name, "planner": planner, "facts": which, "contender": contender,
                        "truth": truth, "lo": b.lower, "hi": b.upper, "unsound": unsound,
                        "sat": o.stats.sat, "unsat": o.stats.unsat, "unknown": o.stats.unknown,
                        "setup_ms": ms(o.setup), "search_ms": ms(o.search), "solver_ms": ms(o.stats.time),
                    }));
                }
                println!("{:<9} {:<26} {:<10} {:<6} truth {truth:<8} {}", c.suite, c.name, planner, which, line.join("  "));
            }
        }
    }
    println!("\n{:<11} {:<6} {:>4} {:>7} {:>8} {:>7} {:>9} {:>9} {:>6} {:>6} {:>7} {:>9} {:>9}",
        "contender", "facts", "n", "errors", "unsound", "tight", "med hi/t", "p90 hi/t", "sat", "unknw", "unsat", "setup s", "search s");
    for ((contender, which), t) in &mut totals {
        t.ratios.sort_by(f64::total_cmp);
        let q = |p: f64| t.ratios.get(((t.ratios.len() as f64 - 1.0) * p).round() as usize).copied().unwrap_or(f64::NAN);
        println!(
            "{contender:<11} {which:<6} {:>4} {:>7} {:>8} {:>3}/{:<3} {:>9.2} {:>9.2} {:>6} {:>6} {:>7} {:>9.1} {:>9.1}",
            t.n, t.errors, t.unsound, t.tight, t.bounded, q(0.5), q(0.9), t.stats.sat, t.stats.unknown, t.stats.unsat,
            t.setup.as_secs_f64(), t.search.as_secs_f64(),
        );
    }
    let path = std::env::var("OUT").unwrap_or(concat!(env!("CARGO_MANIFEST_DIR"), "/target/fact_compare.json").into());
    std::fs::write(&path, serde_json::to_string_pretty(&rows).unwrap()).unwrap();
    println!("\nwrote {path}");
    assert!(failures.is_empty(), "{failures:#?}");
}
