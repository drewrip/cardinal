//! The axiom encoding (`cardinal::uf`) against the fact pipeline: each
//! fixture query bounded with every profile's facts, and with only the
//! other queries', as DataFusion plans it and as DuckDB planned it.
//!
//! ```sh
//! cargo test --release --test uf_compare -- --nocapture       # ONLY=q01,q03 for some
//! ```

mod fixtures;

use std::time::Instant;

use cardinal::facts::FactSet;
use cardinal::observed::ObservedPlan;
use cardinal::uf::Encoder;
use cardinal::{FactMode, Options};
use fixtures::{catalog, context, foreign_keys, plans, query};

struct Case {
    name: String,
    sql: String,
    plan: ObservedPlan,
    observed: FactSet,
}

async fn cases() -> Vec<Case> {
    let only = std::env::var("ONLY").ok();
    let mut out = vec![];
    for dir in ["extra", "tpch"] {
        for plan in plans(dir).await {
            let mut observed = FactSet::default();
            observed.observe(&plan);
            out.push(Case { name: plan.name.clone(), sql: query(dir, &plan.name), plan, observed });
        }
    }
    let _ = only;
    out
}

fn facts(cases: &[Case], except: Option<&str>) -> FactSet {
    let mut set = FactSet::default();
    for c in cases.iter().filter(|c| Some(c.name.as_str()) != except) {
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

#[tokio::test]
async fn compare() {
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
    let all = facts(&cases, None);
    let options = || Options { selectivity: true, foreign_keys: fks.clone(), ..Default::default() };
    let (mut looser, mut tighter, mut same, mut unsound) = (0, 0, 0, vec![]);
    let (mut t_main, mut t_uf) = (0.0, 0.0);
    for c in &cases {
        if only.as_ref().is_some_and(|o| !o.split(',').any(|q| q == c.name)) {
            continue;
        }
        let truth = c.plan.nodes[c.plan.root].rows;
        let state = ctx.state();
        let logical = match state.create_logical_plan(&c.sql).await {
            Ok(p) => state.optimize(&p).ok(),
            Err(_) => None,
        };
        for mode in &modes {
            let except: Vec<&str> = if mode == "others" { vec![c.name.as_str()] } else { vec![] };
            let rest = if mode == "others" { facts(&cases, Some(&c.name)) } else { facts(&cases, None) };
            let _ = &all;
            for planner in ["df", "duck"] {
                let (ub, main) = match planner {
                    "df" => {
                        let Some(l) = &logical else { continue };
                        let t = Instant::now();
                        let ub = enc.bound(l, &except).unwrap();
                        let tu = t.elapsed().as_secs_f64();
                        let main = if main_too {
                            let t = Instant::now();
                            let a = cardinal::analyze_sql_with(&ctx, &c.sql, options()).await.ok();
                            let r = a.map(|a| a.with_facts(&rest, FactMode::Pinned).unwrap().range().unwrap());
                            Some((r, t.elapsed().as_secs_f64()))
                        } else {
                            None
                        };
                        ((ub, tu), main)
                    }
                    _ => {
                        let t = Instant::now();
                        let ub = enc.bound_observed(&c.plan, &except).unwrap();
                        let tu = t.elapsed().as_secs_f64();
                        let main = if main_too {
                            let t = Instant::now();
                            let a = cardinal::analyze_observed(&catalog, &c.plan, options()).ok();
                            let r = a.map(|a| a.with_facts(&rest, FactMode::Pinned).unwrap().range().unwrap());
                            Some((r, t.elapsed().as_secs_f64()))
                        } else {
                            None
                        };
                        ((ub, tu), main)
                    }
                };
                let ((b, tu), main) = (ub, main);
                t_uf += tu;
                let main_text = match &main {
                    Some((Some((lo, hi)), tm)) => {
                        t_main += tm;
                        let width = |l: u64, h: Option<u64>| h.map(|h| h - l.min(h));
                        let (mw, uw) = (width(*lo, *hi), width(b.lower, b.upper));
                        let cmp = match (mw, uw) {
                            (Some(m), Some(u)) if u < m => "TIGHTER",
                            (Some(m), Some(u)) if u > m => "looser",
                            (None, Some(_)) => "TIGHTER",
                            (Some(_), None) => "looser",
                            _ if b.lower > *lo => "TIGHTER",
                            _ if b.lower < *lo => "looser",
                            _ => "same",
                        };
                        match cmp {
                            "TIGHTER" => tighter += 1,
                            "looser" => looser += 1,
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
                    "{:<22} {planner:<4} {mode:<6} truth {truth:<6} uf {:<12} ({tu:.1}s, {} checks, {} dropped) {main_text}",
                    c.name,
                    show(b.lower, b.upper),
                    b.checks,
                    b.dropped.len(),
                );
                if std::env::var("STATS").is_ok() {
                    println!("    {:?} dropped {:?}", b.stats, b.dropped);
                }
            }
        }
    }
    println!("tighter {tighter}, same {same}, looser {looser}; uf {t_uf:.1}s, main {t_main:.1}s");
    assert!(unsound.is_empty(), "{unsound:#?}");
}

#[tokio::test]
async fn describe() {
    let Ok(name) = std::env::var("DESCRIBE") else { return };
    let catalog = catalog().await;
    let fks = foreign_keys();
    let mut enc = Encoder::new(&catalog, &fks);
    for dir in ["extra", "tpch"] {
        for plan in plans(dir).await {
            if plan.name == name {
                println!("{plan}");
                enc.observe(&plan);
            }
        }
    }
    for l in enc.describe(&name) {
        println!("{l}");
    }
    let ctx = context();
    for dir in ["extra", "tpch"] {
        for plan in plans(dir).await {
            if plan.name == name {
                println!("planned: {}", enc.planned_term(&plan));
                let sql = query(dir, &name);
                let state = ctx.state();
                let l = state.optimize(&state.create_logical_plan(&sql).await.unwrap()).unwrap();
                println!("{}", l.display_indent());
                println!("datafusion: {}", enc.target_term(&l));
            }
        }
    }
}
