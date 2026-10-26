//! The axiom encoding (`cardinal::uf`) against the fact pipeline, with
//! TPC-DS in DuckDB, as `tests/tpcds.rs` runs it: the odd queries' profiles
//! (one thread and four) give the facts, and each even query is bounded as
//! DataFusion plans it and as DuckDB planned it. Mode `others` bounds it
//! with the odd queries' facts only, `all` with its own profiles' too.
//!
//! Needs the `duckdb` CLI with the `tpcds` extension; skipped without.
//! `CARDINAL_TPCDS_DB` names a generated database (by default
//! `tpcds_sf{CARDINAL_TPCDS_SF}.duckdb` under Cargo's test temp directory,
//! made once). Profiles are cached next to it, in `uf_tpcds_profiles`.
//! `ONLY=q02,q04` bounds only some, `MODES=all,others` (default `others`)
//! picks the fact sets, `NO_MAIN` skips main's pipeline.
//!
//! ```sh
//! CARDINAL_UF_TIMEOUT_MS=2000 cargo test --release --test uf_tpcds -- --nocapture
//! ```
//!
//! Building some targets' programs takes far longer than solving them, so
//! for a whole run, bound one query per process under a time limit:
//!
//! ```sh
//! for n in $(seq 2 2 98); do ONLY=$(printf q%02d $n) perl -e 'alarm shift; exec @ARGV' 180 \
//!     target/release/deps/uf_tpcds-<hash> --nocapture; done
//! ```

mod live;

use std::collections::BTreeMap;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Instant;

use cardinal::facts::FactSet;
use cardinal::observed::{Catalog, ObservedPlan};
use cardinal::uf::{Bound, Encoder};
use cardinal::{FactMode, Options};
use datafusion::arrow::datatypes::{DataType, Field, Schema};
use datafusion::datasource::MemTable;
use datafusion::prelude::SessionContext;
use live::{Engine, duckdb_available, run};

/// TPC-DS at the scale factor asked for, made once.
fn database() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("CARDINAL_TPCDS_DB") {
        return Some(PathBuf::from(p));
    }
    let sf = std::env::var("CARDINAL_TPCDS_SF").unwrap_or_else(|_| "1".into());
    let path = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("tpcds_sf{sf}.duckdb"));
    if !path.exists() {
        let tmp = path.with_extension("tmp");
        let _ = std::fs::remove_file(&tmp);
        if let Err(e) = run(&tmp, &format!("INSTALL tpcds; LOAD tpcds; CALL dsdgen(sf = {sf});"), &[]) {
            eprintln!("skipped: cannot generate TPC-DS: {e}");
            return None;
        }
        std::fs::rename(&tmp, &path).unwrap();
    }
    Some(path)
}

fn json(db: &PathBuf, sql: &str) -> serde_json::Value {
    let out = run(db, sql, &["-readonly", "-json"]).unwrap();
    serde_json::from_str(out.trim()).unwrap()
}

/// The 99 queries, by number.
fn queries(db: &PathBuf) -> Vec<(u32, String)> {
    let rows = json(db, "LOAD tpcds; SELECT query_nr, query FROM tpcds_queries() ORDER BY query_nr;");
    rows.as_array()
        .unwrap()
        .iter()
        .map(|r| (r["query_nr"].as_u64().unwrap() as u32, r["query"].as_str().unwrap().to_string()))
        .collect()
}

fn arrow_type(t: &str) -> DataType {
    if let Some(ps) = t.strip_prefix("DECIMAL(").and_then(|r| r.strip_suffix(')')) {
        let (p, s) = ps.split_once(',').unwrap();
        return DataType::Decimal128(p.trim().parse().unwrap(), s.trim().parse().unwrap());
    }
    match t {
        "INTEGER" => DataType::Int32,
        "BIGINT" => DataType::Int64,
        "DOUBLE" => DataType::Float64,
        "VARCHAR" => DataType::Utf8,
        "DATE" => DataType::Date32,
        t => panic!("no Arrow type for DuckDB type {t}"),
    }
}

/// The TPC-DS tables, empty, with DuckDB's schemas.
fn context(db: &PathBuf) -> SessionContext {
    let rows = json(db, "SELECT table_name, column_name, data_type FROM information_schema.columns ORDER BY table_name, ordinal_position;");
    let mut tables: BTreeMap<String, Vec<Field>> = BTreeMap::new();
    for c in rows.as_array().unwrap() {
        let field = Field::new(c["column_name"].as_str().unwrap(), arrow_type(c["data_type"].as_str().unwrap()), true);
        tables.entry(c["table_name"].as_str().unwrap().to_string()).or_default().push(field);
    }
    let ctx = SessionContext::new();
    for (name, fields) in tables {
        let schema = Arc::new(Schema::new(fields));
        ctx.register_table(name.as_str(), Arc::new(MemTable::try_new(schema, vec![vec![]]).unwrap())).unwrap();
    }
    ctx
}

/// DuckDB's profile of query `n` with `variant`'s threads, cached.
fn profile(engine: &Engine, db: &std::path::Path, n: u32, variant: &str, sql: &str) -> Result<String, String> {
    let dir = db.with_file_name("uf_tpcds_profiles");
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    let path = dir.join(format!("q{n:02}_{variant}.json"));
    if let Ok(j) = std::fs::read_to_string(&path) {
        return Ok(j);
    }
    let j = engine.profile(sql, variant)?;
    let _ = std::fs::write(&path, &j);
    Ok(j)
}

struct Case {
    /// `qNN`.
    name: String,
    sql: String,
    /// Its one-thread profile: the target as DuckDB planned it.
    plan: ObservedPlan,
    /// Its profiles' names, as observed.
    own: Vec<String>,
}

fn facts(plans: &[ObservedPlan], except: &[String]) -> FactSet {
    let mut set = FactSet::default();
    for p in plans.iter().filter(|p| !except.contains(&p.name)) {
        set.observe(p);
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
async fn compare_tpcds() {
    if !duckdb_available() {
        eprintln!("skipped: no duckdb CLI");
        return;
    }
    let Some(db) = database() else { return };
    let engine = Engine::DuckDb(db.clone());
    let ctx = context(&db);
    let catalog = Catalog::from_context(&ctx).await.unwrap().with_partial_indexes(Vec::<(String, String)>::new());
    let queries = queries(&db);
    let only = std::env::var("ONLY").ok();
    let wanted = |n: u32| only.as_ref().is_none_or(|o| o.split(',').any(|q| q == format!("q{n:02}")));
    let modes: Vec<String> = std::env::var("MODES").unwrap_or("others".into()).split(',').map(str::to_string).collect();
    let main_too = std::env::var("NO_MAIN").is_err();
    let with_own = modes.iter().any(|m| m == "all");

    // The odd queries' profiles, and the even ones', as targets.
    let mut plans = vec![];
    let mut cases = vec![];
    let mut skipped = vec![];
    for (n, sql) in &queries {
        let odd = n % 2 == 1;
        if !odd && !wanted(*n) {
            continue;
        }
        let mut own = vec![];
        for variant in engine.variants() {
            let name = format!("q{n:02}/{variant}");
            match profile(&engine, &db, *n, &variant, sql).and_then(|j| engine.read(&catalog, &name, &j, sql)) {
                Ok(p) => {
                    if odd || with_own {
                        plans.push(p.clone());
                    }
                    if !odd && variant == "t1" {
                        if p.nodes[p.root].counted {
                            cases.push(Case { name: format!("q{n:02}"), sql: sql.clone(), plan: p, own: vec![] });
                        } else {
                            skipped.push(format!("q{n:02}: its rows were not counted"));
                        }
                    }
                    own.push(name);
                }
                Err(e) if variant == "t1" && !odd => skipped.push(format!("q{n:02}: not profiled: {}", e.lines().next().unwrap_or_default())),
                Err(_) => {}
            }
        }
        if let Some(c) = cases.last_mut().filter(|c| c.name == format!("q{n:02}")) {
            c.own = own;
        }
    }
    let mut enc = Encoder::new(&catalog, &[]);
    for p in &plans {
        enc.observe(p);
    }
    println!("{} plans observed, {} targets", plans.len(), cases.len());

    let options = || Options { selectivity: true, ..Default::default() };
    let (mut looser, mut tighter, mut same, mut unsound, mut errors, mut wider) = (0, 0, 0, vec![], vec![], vec![]);
    let (mut t_main, mut t_uf) = (0.0, 0.0);
    for c in &cases {
        let truth = c.plan.nodes[c.plan.root].rows;
        let state = ctx.state();
        let logical = match state.create_logical_plan(&c.sql).await {
            Ok(p) => state.optimize(&p).ok(),
            Err(_) => None,
        };
        if logical.is_none() {
            skipped.push(format!("{}: DataFusion does not plan it", c.name));
        }
        for mode in &modes {
            let except: Vec<String> = if mode == "others" { c.own.clone() } else { vec![] };
            let except_ref: Vec<&str> = except.iter().map(String::as_str).collect();
            let rest = facts(&plans, &except);
            for planner in ["df", "duck"] {
                let t = Instant::now();
                let (b, main) = match planner {
                    "df" => {
                        let Some(l) = &logical else { continue };
                        let ub = guarded(|| enc.bound(l, &except_ref));
                        let main = if main_too {
                            let t = Instant::now();
                            let a = cardinal::analyze_sql_with(&ctx, &c.sql, options()).await.ok();
                            let r = a.and_then(|a| a.with_facts(&rest, FactMode::Pinned).ok()?.range().ok());
                            Some((r, t.elapsed().as_secs_f64()))
                        } else {
                            None
                        };
                        (ub, main)
                    }
                    _ => {
                        let ub = guarded(|| enc.bound_observed(&c.plan, &except_ref));
                        let main = main_too.then(|| {
                            let t = Instant::now();
                            let a = cardinal::analyze_observed(&catalog, &c.plan, options()).ok();
                            let r = a.and_then(|a| a.with_facts(&rest, FactMode::Pinned).ok()?.range().ok());
                            (r, t.elapsed().as_secs_f64())
                        });
                        (ub, main)
                    }
                };
                let tu = t.elapsed().as_secs_f64() - main.as_ref().map_or(0.0, |m| m.1);
                t_uf += tu;
                let b = match b {
                    Ok(b) => b,
                    Err(e) => {
                        println!("{:<6} {planner:<4} {mode:<6} truth {truth:<8} uf {e}", c.name);
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
                    "{:<6} {planner:<4} {mode:<6} truth {truth:<8} uf {:<14} ({tu:.1}s, {} checks, {} needed, {} dropped) {main_text}",
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
    for s in &skipped {
        println!("  skipped: {s}");
    }
    for u in &unsound {
        println!("  UNSOUND: {u}");
    }
    assert!(unsound.is_empty() && errors.is_empty(), "{unsound:#?}\n{errors:#?}");
}
