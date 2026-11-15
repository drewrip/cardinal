//! Parity of the relations between contexts, old path against new. For
//! every DuckDB fixture, analyzed as DataFusion plans it, as DuckDB did,
//! and jointly with the other profiles, it records the contexts, the
//! relations between them, the relevant ones, the axioms, and the claims
//! facts give ([`cardinal::parity`]).
//!
//! ```sh
//! PARITY_WRITE=1 cargo test --release --test egglog_parity   # write the baseline
//! cargo test --release --test egglog_parity                  # diff against it
//! ```
//!
//! The baseline is `target/egglog/baseline.json`; without one, a run is
//! written there. A run fails on a lost context, relation, relevant
//! context, axiom or claim, or a looser bound, and lists the gained ones.
//! Only q11 is analyzed jointly, unless `PARITY_JOINT=all` (an hour).
//! `ONLY=q02,q11` records only those queries, and diffs only them.
//! `PARITY_VERBOSE=1` prints each query's time. `PARITY_BOUNDS=1` also
//! proves every analysis's bounds (minutes).
//! `EGGLOG=1` (or `EGGLOG=fixpoint`) runs the analyses on egglog, with the
//! `egglog` feature.

mod fixtures;

use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use cardinal::facts::FactSet;
use cardinal::parity::{self, Snapshot};
use cardinal::{Analysis, Facts, Options};
use fixtures::{catalog, context, foreign_keys, plans, query};
use serde::{Deserialize, Serialize};

const BASELINE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/target/egglog/baseline.json");
const RUN: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/target/egglog/run.json");

/// One analysis's record.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct Case {
    snapshot: Snapshot,
    /// The claims every fact gives, each once.
    claims: BTreeSet<String>,
    /// `(lower, upper)`, with `PARITY_BOUNDS`.
    bounds: Option<(u64, Option<u64>)>,
    /// Seconds proving them.
    z3: Option<f64>,
}

#[derive(Debug, Default, Serialize, Deserialize)]
struct Record {
    cases: BTreeMap<String, Case>,
}

fn options() -> Options {
    Options { foreign_keys: foreign_keys(), ..Default::default() }
}

/// The record of `a`, the one analysis made since [`parity::start`].
fn case(a: Option<Analysis>, facts: &Facts) -> Option<Case> {
    let mut snapshots = parity::take();
    let t = Instant::now();
    let a = a?;
    assert_eq!(snapshots.len(), 1, "one analysis relates contexts once");
    let snapshot = snapshots.pop().unwrap();
    let with = a.with_facts(facts).unwrap();
    let claims = with.constraints()[a.constraints().len()..].lines().map(str::to_string).collect();
    let (bounds, z3) = match std::env::var("PARITY_BOUNDS").is_ok_and(|v| v == "1") {
        true => {
            let t = Instant::now();
            let b = with.bounds().unwrap();
            (Some((b.lower, b.upper)), Some(t.elapsed().as_secs_f64()))
        }
        false => (None, None),
    };
    if std::env::var("PARITY_VERBOSE").is_ok() {
        eprintln!("  with facts {:.2} s; build {:.2} between {:.2}", t.elapsed().as_secs_f64(), snapshot.timings.build, snapshot.timings.between);
    }
    Some(Case { snapshot, claims, bounds, z3 })
}

async fn record() -> Record {
    let ctx = context();
    let catalog = catalog().await;
    let mut profiles = vec![];
    for dir in ["extra", "tpch"] {
        profiles.extend(plans(dir).await.into_iter().map(|p| (dir, p)));
    }
    let mut set = FactSet::default();
    for (_, p) in &profiles {
        set.observe(p);
    }
    let facts = Facts::new(set);
    let mut out = Record::default();
    let only = std::env::var("ONLY").ok();
    for (dir, plan) in &profiles {
        if only.as_ref().is_some_and(|o| !o.split(',').any(|n| n == plan.name)) {
            continue;
        }
        let t = Instant::now();
        let sql = query(dir, &plan.name);
        // DataFusion has no `AS MATERIALIZED`: some analyses are none.
        parity::start();
        let df = cardinal::analyze_sql(&ctx, &sql, options()).await.ok();
        if let Some(c) = case(df, &facts) {
            out.cases.insert(format!("{dir}/{} datafusion", plan.name), c);
        }
        parity::start();
        let c = case(cardinal::analyze_observed(&catalog, plan, options()).ok(), &facts).unwrap();
        out.cases.insert(format!("{dir}/{} duckdb", plan.name), c);
        // A joint analysis takes up to a minute: by default, only q11's,
        // which `joint_facts` checks.
        if std::env::var("PARITY_JOINT").is_ok_and(|v| v == "all") || plan.name == "q11" {
            let others: Vec<_> = profiles.iter().filter(|(_, p)| p.name != plan.name).map(|(_, p)| p.clone()).collect();
            parity::start();
            let c = case(cardinal::joint::analyze_joint(&catalog, plan, &others, options()).ok(), &facts).unwrap();
            out.cases.insert(format!("{dir}/{} joint", plan.name), c);
        }
        if std::env::var("PARITY_VERBOSE").is_ok() {
            eprintln!("{dir}/{}: {:.2} s", plan.name, t.elapsed().as_secs_f64());
        }
    }
    out
}

/// What `new` lost and gained against `old`, as lines.
fn diff(old: &Record, new: &Record) -> (Vec<String>, Vec<String>) {
    let (mut lost, mut gained) = (vec![], vec![]);
    let only = std::env::var("ONLY").is_ok();
    for (name, o) in &old.cases {
        if only && !new.cases.contains_key(name) {
            continue;
        }
        let Some(n) = new.cases.get(name) else {
            lost.push(format!("{name}: no analysis"));
            continue;
        };
        let (os, ns) = (&o.snapshot, &n.snapshot);
        let mut sets = |what: &str, a: &BTreeSet<String>, b: &BTreeSet<String>| {
            lost.extend(a.difference(b).map(|x| format!("{name}: {what} {x}")));
            gained.extend(b.difference(a).map(|x| format!("{name}: {what} {x}")));
        };
        sets("context", &os.contexts, &ns.contexts);
        sets("relevant", &os.relevant, &ns.relevant);
        let claims = |s: &Snapshot| s.axioms.keys().cloned().collect::<BTreeSet<_>>();
        sets("axiom", &claims(os), &claims(ns));
        sets("claim", &o.claims, &n.claims);
        let pairs = |s: &BTreeSet<(String, String)>| s.iter().map(|(a, b)| format!("{a}  <=  {b}")).collect::<BTreeSet<_>>();
        sets("subset", &pairs(&os.subset), &pairs(&ns.subset));
        sets("fewer", &pairs(&os.fewer), &pairs(&ns.fewer));
        sets("groups among", &pairs(&os.groups_among), &pairs(&ns.groups_among));
        if let (Some((ol, ou)), Some((nl, nu))) = (o.bounds, n.bounds) {
            let looser = nl < ol || matches!((ou, nu), (Some(_), None)) || matches!((ou, nu), (Some(a), Some(b)) if b > a);
            let tighter = nl > ol || matches!((ou, nu), (None, Some(_))) || matches!((ou, nu), (Some(a), Some(b)) if b < a);
            let line = format!("{name}: bounds [{ol}, {ou:?}] now [{nl}, {nu:?}]");
            if looser {
                lost.push(line);
            } else if tighter {
                gained.push(line);
            }
        }
    }
    (lost, gained)
}

/// Seconds per stage, summed over the cases.
fn totals(r: &Record) -> BTreeMap<&'static str, f64> {
    let mut t = BTreeMap::new();
    for c in r.cases.values() {
        let s = &c.snapshot.timings;
        for (k, v) in [("build", s.build), ("between", s.between), ("encode", s.encode), ("saturate", s.saturate), ("extract", s.extract)] {
            *t.entry(k).or_default() += v;
        }
        *t.entry("z3").or_default() += c.z3.unwrap_or(0.0);
    }
    t
}

#[tokio::test]
async fn parity() {
    let t = Instant::now();
    let run = record().await;
    let elapsed = t.elapsed().as_secs_f64();
    std::fs::create_dir_all(std::path::Path::new(BASELINE).parent().unwrap()).unwrap();
    let write = |path: &str, r: &Record| std::fs::write(path, serde_json::to_string_pretty(r).unwrap()).unwrap();
    let size = |r: &Record| {
        let n = |f: fn(&Snapshot) -> usize| r.cases.values().map(|c| f(&c.snapshot)).sum::<usize>();
        format!(
            "{} cases, {} contexts, {} subset, {} fewer, {} groups among, {} relevant, {} axioms",
            r.cases.len(),
            n(|s| s.contexts.len()),
            n(|s| s.subset.len()),
            n(|s| s.fewer.len()),
            n(|s| s.groups_among.len()),
            n(|s| s.relevant.len()),
            n(|s| s.axioms.len())
        )
    };
    println!("run: {}", size(&run));
    println!("run took {elapsed:.2} s; per stage: {:?}", totals(&run));
    write(RUN, &run);
    let fresh = std::env::var("PARITY_WRITE").is_ok_and(|v| v == "1") || !std::path::Path::new(BASELINE).exists();
    if fresh {
        write(BASELINE, &run);
        println!("wrote {BASELINE}");
        return;
    }
    let base: Record = serde_json::from_str(&std::fs::read_to_string(BASELINE).unwrap()).unwrap();
    println!("baseline: {}", size(&base));
    println!("baseline per stage: {:?}", totals(&base));
    let (lost, gained) = diff(&base, &run);
    println!("gained {}:", gained.len());
    for g in &gained {
        println!("  + {g}");
    }
    assert!(lost.is_empty(), "lost {}:\n{}", lost.len(), lost.join("\n"));
}
