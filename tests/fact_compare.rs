//! The ways of putting facts in, compared on the same queries: today's
//! (`with_facts`, pinned) and a fact store with axioms (`with_store`).
//! Each fixture query is analyzed as DataFusion plans it and
//! as the engine did, with every profile's facts and with every other
//! profile's (leave-one-out), and each bound is checked against the query's
//! true row count.
//!
//! ```sh
//! cargo test --release --test fact_compare -- --nocapture
//! SUITE=duckdb ONLY=q03,q05 CONTENDERS=a FACTS=others BOUNDS=1 cargo test ...
//! ```
//!
//! Writes one JSON row per (query, planner, facts, contender) to
//! `target/fact_compare.json`.

mod fixtures;

use std::collections::{BTreeMap, HashMap};
use std::time::{Duration, Instant};

use cardinal::facts::{Context, FactKind, FactSet};
use cardinal::observed::ObservedPlan;
use cardinal::{Analysis, Bounds, FactMode, Options, SearchStats, SolverSize};
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
    Options { selectivity: true, foreign_keys: foreign_keys(), ..Default::default() }
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
                let analysis = cardinal::analyze_sql_with(&ctx, &sql, options()).await.ok();
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
    range: (u64, Option<u64>),
    bounds: Option<Bounds>,
    stats: SearchStats,
    rejected: Vec<(String, String)>,
    claims: usize,
    axioms: usize,
    size: SolverSize,
    setup: Duration,
    check: Duration,
    search: Duration,
}

/// Each table's size, from the facts.
fn sizes(facts: &FactSet) -> HashMap<String, u64> {
    let tables = ["customer", "lineitem", "nation", "orders", "part", "partsupp", "region", "supplier"];
    let size = |t: &str| facts.get(&FactKind::Cardinality(Context::table(t)))?.value.as_int();
    tables.iter().filter_map(|t| Some((t.to_string(), size(t)?))).collect()
}

#[allow(clippy::too_many_arguments)]
fn run(
    contender: &str,
    a: &Analysis,
    closed: &FactSet,
    store: &FactSet,
    with_bounds: bool,
) -> Result<Outcome, String> {
    let start = Instant::now();
    let e = |e: cardinal::Error| e.to_string();
    macro_rules! search {
        ($g:expr) => {{
            let t = Instant::now();
            let (range, mut stats) = $g.range_with_stats().map_err(e)?;
            let bounds = if with_bounds {
                let (b, s) = $g.bounds_with_stats().map_err(e)?;
                stats += s;
                Some(b)
            } else {
                None
            };
            (range, bounds, stats, t.elapsed())
        }};
    }
    Ok(match contender {
        "current" => {
            let i = a.with_facts(closed, FactMode::Pinned).map_err(e)?;
            let setup = start.elapsed();
            let (range, bounds, stats, search) = search!(i);
            let claims = i.matched.len() + i.pinned.len() + i.capped.len() + i.pinned_ndv.len() + i.ranges.len() + i.floors.len();
            Outcome {
                range,
                bounds,
                stats,
                rejected: i.rejected.clone(),
                claims,
                axioms: 0,
                size: Default::default(),
                setup,
                check: Duration::ZERO,
                search,
            }
        }
        "a" => {
            let g = a.with_store(store).map_err(e)?;
            let (range, bounds, stats, search) = search!(g);
            Outcome {
                range,
                bounds,
                stats,
                rejected: g.rejected.clone(),
                claims: g.asserted.len(),
                axioms: g.axioms.values().sum(),
                size: g.size,
                setup: g.timings.setup,
                check: g.timings.check,
                search,
            }
        }
        other => panic!("no contender {other}"),
    })
}

/// Why `o` is wrong about a query with `truth` rows, if it is.
fn unsound(o: &Outcome, truth: u64, tables: &HashMap<String, u64>) -> Vec<String> {
    let mut out = vec![];
    let (lo, hi) = o.range;
    if lo > truth || hi.is_some_and(|hi| hi < truth) {
        out.push(format!("{lo} <= X <= {hi:?}, not {truth}"));
    }
    if let Some(b) = &o.bounds {
        if b.constant.is_some_and(|c| c < truth) {
            out.push(format!("constant {:?} < {truth}", b.constant));
        }
        for t in &b.tables {
            if let Some(&n) = tables.get(&t.table)
                && !t.bound.holds(truth, n)
            {
                out.push(format!("{} bound {:?} fails", t.table, t.bound));
            }
        }
    }
    out
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
    let contenders = env_list("CONTENDERS").unwrap_or(["current", "a"].map(String::from).to_vec());
    let fact_sets = env_list("FACTS").unwrap_or(vec!["all".into(), "others".into()]);
    let with_bounds = std::env::var("BOUNDS").is_ok();
    let mut rows = vec![];
    let mut failures = vec![];
    // Per (contender, facts): unsound, rejected, tight, hi/truth ratios, outcomes.
    #[derive(Default)]
    struct Total {
        unsound: usize,
        rejected: usize,
        tight: usize,
        bounded: usize,
        ratios: Vec<f64>,
        n: usize,
        errors: usize,
        stats: SearchStats,
        setup: Duration,
        check: Duration,
        search: Duration,
        size: (usize, usize),
    }
    let mut totals: BTreeMap<(String, String), Total> = BTreeMap::new();
    for c in cases.iter().filter(|c| !c.name.starts_with('-')) {
        let truth = c.rows();
        for which in &fact_sets {
            let except = (which == "others").then_some(c.name.as_str());
            let store = observed(&cases, c.suite, except);
            let mut closed = store.clone();
            closed.close();
            let tables = sizes(&closed);
            let planned = c.analysis.iter().map(|a| ("datafusion", a)).chain([("engine", &c.engine)]);
            for (planner, a) in planned {
                let mut line = vec![];
                for contender in &contenders {
                    let total = totals.entry((contender.clone(), which.clone())).or_default();
                    total.n += 1;
                    let context = format!("{} {} by {planner}, {which} facts, {contender}", c.suite, c.name);
                    let o = match run(contender, a, &closed, &store, with_bounds) {
                        Ok(o) => o,
                        Err(e) => {
                            total.errors += 1;
                            failures.push(format!("{context}: error {e}"));
                            rows.push(json!({"suite": c.suite, "query": c.name, "planner": planner, "facts": which, "contender": contender, "error": e}));
                            continue;
                        }
                    };
                    let wrong = unsound(&o, truth, &tables);
                    total.unsound += usize::from(!wrong.is_empty());
                    total.rejected += o.rejected.len();
                    total.tight += usize::from(o.range.1 == Some(truth));
                    if let Some(hi) = o.range.1 {
                        total.bounded += 1;
                        total.ratios.push(hi as f64 / truth.max(1) as f64);
                    }
                    total.stats += o.stats;
                    total.setup += o.setup;
                    total.check += o.check;
                    total.search += o.search;
                    total.size.0 += o.size.assertions;
                    total.size.1 += o.size.nonlinear;
                    for w in &wrong {
                        failures.push(format!("{context}: {w}"));
                    }
                    line.push(format!("{contender}: {:?}", o.range));
                    rows.push(json!({
                        "suite": c.suite, "query": c.name, "planner": planner, "facts": which, "contender": contender,
                        "truth": truth, "lo": o.range.0, "hi": o.range.1,
                        "bounds": o.bounds.as_ref().map(|b| b.to_string()),
                        "unsound": wrong, "rejected": o.rejected,
                        "claims": o.claims, "axioms": o.axioms,
                        "assertions": o.size.assertions, "vars": o.size.vars, "nonlinear": o.size.nonlinear,
                        "sat": o.stats.sat, "unsat": o.stats.unsat, "unknown": o.stats.unknown,
                        "setup_ms": ms(o.setup), "check_ms": ms(o.check), "search_ms": ms(o.search),
                        "solver_ms": ms(o.stats.time),
                    }));
                }
                println!("{:<9} {:<26} {:<10} {:<6} truth {truth:<8} {}", c.suite, c.name, planner, which, line.join("  "));
            }
        }
    }
    println!("\n{:<11} {:<6} {:>4} {:>7} {:>8} {:>6} {:>7} {:>9} {:>9} {:>6} {:>6} {:>7} {:>9} {:>9} {:>9} {:>10}",
        "contender", "facts", "n", "errors", "unsound", "rejct", "tight", "med hi/t", "p90 hi/t", "sat", "unknw", "unsat", "setup s", "check s", "search s", "asserts");
    for ((contender, which), t) in &mut totals {
        t.ratios.sort_by(f64::total_cmp);
        let q = |p: f64| t.ratios.get(((t.ratios.len() as f64 - 1.0) * p).round() as usize).copied().unwrap_or(f64::NAN);
        println!(
            "{contender:<11} {which:<6} {:>4} {:>7} {:>8} {:>6} {:>3}/{:<3} {:>9.2} {:>9.2} {:>6} {:>6} {:>7} {:>9.1} {:>9.1} {:>9.1} {:>10}",
            t.n, t.errors, t.unsound, t.rejected, t.tight, t.bounded, q(0.5), q(0.9), t.stats.sat, t.stats.unknown, t.stats.unsat,
            t.setup.as_secs_f64(), t.check.as_secs_f64(), t.search.as_secs_f64(), t.size.0,
        );
    }
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/target/fact_compare.json");
    std::fs::write(path, serde_json::to_string_pretty(&rows).unwrap()).unwrap();
    println!("\nwrote {path}");
    assert!(failures.is_empty(), "{failures:#?}");
}
