//! The axiom encoding (`cardinal::uf`) against the fact pipeline, with
//! PostgreSQL's fixtures: each query bounded with every profile's facts, and
//! with only the other queries' (its profiles in every directory left out),
//! as DataFusion plans it and as PostgreSQL planned it.
//!
//! `DIRS` picks the fixture directories (default `tpch,extra`; also
//! `indexed`, `parallel`, `v14`), whose profiles give both the facts and the
//! targets. `ONLY=tpch/q01,extra/limit` (or bare names) bounds only some,
//! `MODES=all,others` picks the fact sets, `NO_MAIN` skips main's pipeline,
//! `FACTS=tpch/q01,...` observes only those profiles.
//!
//! ```sh
//! CARDINAL_UF_TIMEOUT_MS=2000 cargo test --release --test uf_postgres -- --nocapture
//! ```

mod fixtures;

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::time::Instant;

use cardinal::facts::FactSet;
use cardinal::observed::ObservedPlan;
use cardinal::uf::{Bound, Encoder};
use cardinal::{FactMode, Options};
use fixtures::{catalog, context, foreign_keys, pg_plans, pg_query};

struct Case {
    /// `dir/name`.
    name: String,
    /// The query's name, the same in every directory.
    query: String,
    sql: String,
    plan: ObservedPlan,
    observed: FactSet,
}

async fn cases() -> Vec<Case> {
    let dirs = std::env::var("DIRS").unwrap_or("tpch,extra".into());
    let mut out = vec![];
    for dir in dirs.split(',') {
        for mut plan in pg_plans(dir).await {
            let query = plan.name.clone();
            plan.name = format!("{dir}/{query}");
            let mut observed = FactSet::default();
            observed.observe(&plan);
            out.push(Case { name: plan.name.clone(), sql: pg_query(&query), query, plan, observed });
        }
    }
    out
}

/// The facts of every profile but those of query `except`.
fn facts(cases: &[Case], except: Option<&str>) -> FactSet {
    let mut set = FactSet::default();
    for c in cases.iter().filter(|c| Some(c.query.as_str()) != except) {
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
    set.close();
    set
}

fn show(lo: u64, hi: Option<u64>) -> String {
    match hi {
        Some(h) => format!("{lo}..{h}"),
        None => format!("{lo}.."),
    }
}

/// A uf bound, its error or panic as text.
fn guarded(f: impl FnOnce() -> cardinal::Result<Bound>) -> Result<Bound, String> {
    match catch_unwind(AssertUnwindSafe(f)) {
        Ok(Ok(b)) => Ok(b),
        Ok(Err(e)) => Err(format!("error: {e}")),
        Err(p) => Err(format!("panic: {}", p.downcast_ref::<String>().cloned().or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string())).unwrap_or_default())),
    }
}

/// How uf's bound compares with main's, by width, then by lower bound.
fn compare(main: (u64, Option<u64>), uf: (u64, Option<u64>)) -> &'static str {
    let width = |l: u64, h: Option<u64>| h.map(|h| h - l.min(h));
    match (width(main.0, main.1), width(uf.0, uf.1)) {
        (Some(m), Some(u)) if u < m => "TIGHTER",
        (Some(m), Some(u)) if u > m => "looser",
        (None, Some(_)) => "TIGHTER",
        (Some(_), None) => "looser",
        _ if uf.0 > main.0 => "TIGHTER",
        _ if uf.0 < main.0 => "looser",
        _ => "same",
    }
}

#[tokio::test]
async fn compare_postgres() {
    let cases = cases().await;
    let ctx = context();
    let catalog = catalog().await;
    let fks = foreign_keys();
    let mut enc = Encoder::new(&catalog, &fks);
    let facts_from = std::env::var("FACTS").ok();
    for c in &cases {
        if facts_from.as_ref().is_some_and(|o| !o.split(',').any(|q| q == c.name)) {
            continue;
        }
        enc.observe(&c.plan);
    }
    let only = std::env::var("ONLY").ok();
    let modes: Vec<String> = std::env::var("MODES").unwrap_or("all,others".into()).split(',').map(str::to_string).collect();
    let main_too = std::env::var("NO_MAIN").is_err();
    let options = || Options { selectivity: true, foreign_keys: fks.clone(), ..Default::default() };
    let (mut looser, mut tighter, mut same, mut unsound, mut errors, mut wider) = (0, 0, 0, vec![], vec![], vec![]);
    let (mut t_main, mut t_uf) = (0.0, 0.0);
    for c in &cases {
        if only.as_ref().is_some_and(|o| !o.split(',').any(|q| q == c.name || q == c.query)) {
            continue;
        }
        let truth = c.plan.nodes[c.plan.root].rows;
        let state = ctx.state();
        // DataFusion has no `AS MATERIALIZED`.
        let logical = match state.create_logical_plan(&c.sql).await {
            Ok(p) => state.optimize(&p).ok(),
            Err(_) => None,
        };
        for mode in &modes {
            // Every profile of the same query, in any directory.
            let except: Vec<&str> =
                if mode == "others" { cases.iter().filter(|o| o.query == c.query).map(|o| o.name.as_str()).collect() } else { vec![] };
            let rest = facts(&cases, (mode == "others").then_some(c.query.as_str()));
            for planner in ["df", "pg"] {
                let t = Instant::now();
                let (ub, main) = match planner {
                    "df" => {
                        let Some(l) = &logical else { continue };
                        let ub = guarded(|| enc.bound(l, &except));
                        let tu = t.elapsed().as_secs_f64();
                        let main = if main_too {
                            let t = Instant::now();
                            let a = cardinal::analyze_sql_with(&ctx, &c.sql, options()).await.ok();
                            let r = a.and_then(|a| a.with_facts(&rest, FactMode::Pinned).ok()?.range().ok());
                            Some((r, t.elapsed().as_secs_f64()))
                        } else {
                            None
                        };
                        ((ub, tu), main)
                    }
                    _ => {
                        let ub = guarded(|| enc.bound_observed(&c.plan, &except));
                        let tu = t.elapsed().as_secs_f64();
                        let main = main_too.then(|| {
                            let t = Instant::now();
                            let a = cardinal::analyze_observed(&catalog, &c.plan, options()).ok();
                            let r = a.and_then(|a| a.with_facts(&rest, FactMode::Pinned).ok()?.range().ok());
                            (r, t.elapsed().as_secs_f64())
                        });
                        ((ub, tu), main)
                    }
                };
                let ((b, tu), main) = (ub, main);
                t_uf += tu;
                let b = match b {
                    Ok(b) => b,
                    Err(e) => {
                        println!("{:<26} {planner:<4} {mode:<6} truth {truth:<6} uf {e}", c.name);
                        errors.push(format!("{} {planner} {mode}: {e}", c.name));
                        continue;
                    }
                };
                let main_text = match &main {
                    Some((Some((lo, hi)), tm)) => {
                        t_main += tm;
                        let cmp = compare((*lo, *hi), (b.lower, b.upper));
                        match cmp {
                            "TIGHTER" => tighter += 1,
                            "looser" => {
                                looser += 1;
                                wider.push(format!("{} {planner} {mode}: uf {} vs main {} (truth {truth})", c.name, show(b.lower, b.upper), show(*lo, *hi)));
                            }
                            _ => same += 1,
                        }
                        format!("main {} ({tm:.1}s) {cmp}", show(*lo, *hi))
                    }
                    _ => "main -".to_string(),
                };
                if b.lower > truth || b.upper.is_some_and(|u| u < truth) {
                    unsound.push(format!("{} {planner} {mode}: {} not {truth}", c.name, show(b.lower, b.upper)));
                }
                println!(
                    "{:<26} {planner:<4} {mode:<6} truth {truth:<6} uf {:<12} ({tu:.1}s, {} checks, {} needed, {} dropped) {main_text}",
                    c.name,
                    show(b.lower, b.upper),
                    b.checks,
                    b.needed,
                    b.dropped.len(),
                );
                if std::env::var("STATS").is_ok() {
                    println!("    {:?} dropped {:?}", b.stats, b.dropped);
                }
            }
        }
    }
    println!("tighter {tighter}, same {same}, looser {looser}; uf {t_uf:.1}s, main {t_main:.1}s");
    for w in &wider {
        println!("  looser: {w}");
    }
    for e in &errors {
        println!("  failed: {e}");
    }
    for u in &unsound {
        println!("  UNSOUND: {u}");
    }
    assert!(unsound.is_empty() && errors.is_empty(), "{unsound:#?}\n{errors:#?}");
}
