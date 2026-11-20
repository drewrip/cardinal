//! TPC-DS's odd queries as reference plans, bounding its even ones.
//!
//! TPC-DS runs in DuckDB (its `tpcds` extension generates the data and the 99
//! queries). Every odd query is profiled, with one thread and with four.
//! Each even query is then analyzed by DataFusion, over empty tables of the
//! same schema, and bounded alone and with the odd queries' profiles as
//! reference plans ([`cardinal::Builder::with_plans`]).
//! Both must hold the query's true row count, read off its own DuckDB
//! profile.
//!
//! The same runs in PostgreSQL, over a copy of the data DuckDB generates
//! (`cardinal_tpcds_sf{N}`, made once through DuckDB's `postgres`
//! extension) and with DuckDB's text of the queries: each profiled as
//! PostgreSQL plans it, with hash joins only, and with merge joins. What it
//! does not run, or not within the time limit, is skipped.
//!
//! Needs the `duckdb` CLI with the `tpcds` extension, and for PostgreSQL a
//! server `psql` connects to; each is skipped without.
//! `CARDINAL_TPCDS_SF` sets the scale factor (default 1), and
//! `CARDINAL_LIVE_TIMEOUT` each call's time limit in seconds, and
//! `ONLY=q04,q06` bounds only those even queries.
//!
//! ```sh
//! cargo test --release --test tpcds -- --nocapture
//! ```

mod live;

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::Arc;

use cardinal::observed::Catalog;
use cardinal::Analysis;
use datafusion::arrow::datatypes::{DataType, Field, Schema};
use datafusion::datasource::MemTable;
use datafusion::prelude::SessionContext;
use live::{Engine, duckdb_available, run};

/// TPC-DS at the scale factor asked for, made once.
fn database() -> Option<PathBuf> {
    static MADE: std::sync::OnceLock<Option<PathBuf>> = std::sync::OnceLock::new();
    MADE.get_or_init(|| {
        let sf = std::env::var("CARDINAL_TPCDS_SF").unwrap_or_else(|_| "1".into());
        let path = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("tpcds_sf{sf}_{}.duckdb", live::duckdb_version()));
        if !path.exists() {
            let tmp = path.with_extension("tmp");
            let _ = std::fs::remove_file(&tmp);
            if let Err(e) = live::make(&tmp, &format!("INSTALL tpcds; LOAD tpcds; CALL dsdgen(sf = {sf});")) {
                eprintln!("skipped: cannot generate TPC-DS: {e}");
                return None;
            }
            std::fs::rename(&tmp, &path).unwrap();
        }
        Some(path)
    })
    .clone()
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

#[tokio::test]
async fn odd_plans_bound_even_queries() {
    if !duckdb_available() {
        eprintln!("skipped: no duckdb CLI");
        return;
    }
    let Some(db) = database() else { return };
    bound(Engine::DuckDb(db.clone()), &db).await;
}

#[tokio::test]
async fn odd_plans_bound_even_queries_in_postgres() {
    if !duckdb_available() || !live::pg::available() {
        eprintln!("skipped: no duckdb CLI or no PostgreSQL");
        return;
    }
    let Some(db) = database() else { return };
    let sf = std::env::var("CARDINAL_TPCDS_SF").unwrap_or_else(|_| "1".into());
    let copy = format!("cardinal_tpcds_sf{}", sf.replace('.', "_"));
    if let Err(e) = live::pg::mirror(&db, &copy, "public", None) {
        eprintln!("skipped: cannot copy TPC-DS into PostgreSQL: {e}");
        return;
    }
    bound(Engine::Postgres(copy), &db).await;
}

/// The odd queries' profiles on `engine`, bounding the even ones. `db` is the DuckDB database, for the schemas and the queries.
async fn bound(engine: Engine, db: &std::path::Path) {
    let db = db.to_path_buf();
    let ctx = context(&db);
    let catalog = Catalog::from_context(&ctx).await.unwrap().with_partial_indexes(engine.partial_indexes());
    let queries = queries(&db);
    let mut failures = vec![];

    // The odd queries' profiles.
    let mut plans = vec![];
    let mut unprofiled = vec![];
    let variants = engine.variants();
    for (n, sql) in queries.iter().filter(|(n, _)| n % 2 == 1) {
        for variant in &variants {
            match engine.profile(sql, variant).and_then(|j| engine.read(&catalog, &format!("q{n:02}/{variant}"), &j, sql)) {
                Ok(p) => plans.push(p),
                Err(e) if *variant == variants[0] => unprofiled.push(format!("q{n:02}: {}", e.lines().next().unwrap_or_default())),
                Err(_) => {}
            }
        }
    }
    println!("{}: odd queries: {} plans", engine.name(), plans.len());
    for u in &unprofiled {
        println!("  not profiled: {u}");
    }

    // Each even query, bounded with them.
    println!();
    println!("{:<5} {:>9}  {:<24} {}", "query", "rows", "alone", "with plans");
    let (mut analyzed, mut tighter, mut exact) = (0, 0, 0);
    let mut skipped = vec![];
    // `ONLY=q04,q06` bounds only those.
    let only = std::env::var("ONLY").ok();
    let wanted = |n: u32| only.as_ref().is_none_or(|o| o.split(',').any(|q| q == format!("q{n:02}")));
    for (n, sql) in queries.iter().filter(|(n, _)| n % 2 == 0 && wanted(*n)) {
        let truth = match engine.profile(sql, &variants[0]).and_then(|j| engine.read(&catalog, &format!("q{n:02}"), &j, sql)) {
            Ok(p) if !p.nodes[p.root].counted => {
                skipped.push(format!("q{n:02}: its rows were not counted"));
                continue;
            }
            Ok(p) => p.nodes[p.root].rows,
            Err(e) => {
                skipped.push(format!("q{n:02}: not profiled: {}", e.lines().next().unwrap_or_default()));
                continue;
            }
        };
        let q = match Analysis::sql(&ctx, sql).await {
            Ok(q) => q,
            Err(e) => {
                skipped.push(format!("q{n:02}: not analyzed: {}", e.to_string().lines().next().unwrap_or_default()));
                continue;
            }
        };
        let plain = q.clone().build().and_then(|a| a.bounds());
        let with = q.with_plans(&plans).build().and_then(|a| a.bounds());
        let (Ok(plain), Ok(with)) = (plain, with) else {
            skipped.push(format!("q{n:02}: no bounds proven"));
            continue;
        };
        analyzed += 1;
        tighter += usize::from(with.upper.is_some_and(|hi| plain.upper.is_none_or(|h| hi < h)));
        exact += usize::from(with.upper == Some(truth) && plain.upper != Some(truth));
        for (which, b) in [("alone", plain), ("with plans", with)] {
            if !b.holds(truth) {
                failures.push(format!("q{n:02} {which}: {b} does not hold {truth}"));
            }
        }
        println!("q{n:02}   {truth:>9}  {:<24} {with}", plain.to_string());
    }
    println!();
    println!(
        "even queries: {analyzed} bounded; upper bound tighter in {tighter}, made the true count by the plans in {exact}"
    );
    for s in &skipped {
        println!("  {s}");
    }
    assert!(failures.is_empty(), "{} failures:\n{}", failures.len(), failures.join("\n"));
}
