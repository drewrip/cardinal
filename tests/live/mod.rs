//! Running queries in a live DuckDB or PostgreSQL through its CLI, for the
//! tests that check facts against the truth.
#![allow(dead_code)]

use std::collections::HashMap;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

use cardinal::facts::{CountDialect, FactKind, FactSet};
use cardinal::observed::{Catalog, ObservedPlan, from_duckdb, from_duckdb_explain, from_postgres, from_postgres_explain};

/// How long one DuckDB call may take, in seconds (`CARDINAL_LIVE_TIMEOUT`,
/// default 20): a generated query may be a cross product of large tables.
fn timeout() -> std::time::Duration {
    let secs = std::env::var("CARDINAL_LIVE_TIMEOUT").ok().and_then(|s| s.parse().ok()).unwrap_or(20);
    std::time::Duration::from_secs(secs)
}
pub const TIMED_OUT: &str = "timed out";

pub fn duckdb_available() -> bool {
    Command::new("duckdb").arg("--version").output().is_ok_and(|o| o.status.success())
}

/// TPC-H at scale factor 0.01, made once.
pub fn database() -> PathBuf {
    static MADE: std::sync::OnceLock<PathBuf> = std::sync::OnceLock::new();
    MADE.get_or_init(|| {
        if let Ok(p) = std::env::var("CARDINAL_TPCH_DB") {
            return p.into();
        }
        let path = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("tpch_sf001.duckdb");
        if !path.exists() {
            let tmp = path.with_extension("tmp");
            let _ = std::fs::remove_file(&tmp);
            run(&tmp, "CALL dbgen(sf = 0.01);", &[]).unwrap();
            std::fs::rename(&tmp, &path).unwrap();
        }
        path
    })
    .clone()
}

/// Runs `sql` on `db` with `args`, returning standard output. A call that
/// takes longer than `CARDINAL_LIVE_TIMEOUT` is killed, and fails with
/// [`TIMED_OUT`].
pub fn run(db: &PathBuf, sql: &str, args: &[&str]) -> Result<String, String> {
    let mut command = Command::new("duckdb");
    command.arg(db).args(args);
    exec(command, sql)
}

/// Runs `command` with `sql` as its input, returning standard output. A
/// call that takes longer than `CARDINAL_LIVE_TIMEOUT` is killed, and fails
/// with [`TIMED_OUT`].
fn exec(command: Command, sql: &str) -> Result<String, String> {
    exec_within(command, sql, timeout())
}

fn exec_within(mut command: Command, sql: &str, timeout: std::time::Duration) -> Result<String, String> {
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| e.to_string())?;
    // Written as it is read, so that a full pipe stalls neither side.
    let mut stdin = child.stdin.take().unwrap();
    let input = sql.as_bytes().to_vec();
    let writer = std::thread::spawn(move || stdin.write_all(&input));
    // Read output as it comes, so a full pipe does not stall the child.
    let mut stdout = child.stdout.take().unwrap();
    let mut stderr = child.stderr.take().unwrap();
    let out_reader = std::thread::spawn(move || {
        let mut b = vec![];
        std::io::Read::read_to_end(&mut stdout, &mut b).map(|_| b)
    });
    let err_reader = std::thread::spawn(move || {
        let mut b = vec![];
        std::io::Read::read_to_end(&mut stderr, &mut b).map(|_| b)
    });
    let start = std::time::Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().map_err(|e| e.to_string())? {
            break status;
        }
        if start.elapsed() > timeout {
            let _ = child.kill();
            let _ = child.wait();
            return Err(TIMED_OUT.into());
        }
        std::thread::sleep(std::time::Duration::from_millis(5));
    };
    let _ = writer.join();
    let stdout = out_reader.join().unwrap().map_err(|e| e.to_string())?;
    let stderr = err_reader.join().unwrap().map_err(|e| e.to_string())?;
    let err = String::from_utf8_lossy(&stderr);
    if !status.success() || err.contains("Error") || err.contains("ERROR:") {
        return Err(format!("{err}{}", String::from_utf8_lossy(&stdout)));
    }
    Ok(String::from_utf8_lossy(&stdout).into_owned())
}

/// The profile of `sql` with `threads` threads, as DuckDB's JSON.
pub fn profile(db: &PathBuf, sql: &str, threads: usize) -> Result<String, String> {
    let sql = sql.trim().trim_end_matches(';');
    let script = format!("PRAGMA disable_print_progress_bar;\nSET threads = {threads};\nEXPLAIN (ANALYZE, FORMAT JSON) {sql};\n");
    let out = run(db, &script, &["-readonly", "-list", "-noheader"])?;
    let start = out.find('{').ok_or_else(|| format!("no profile in {out}"))?;
    Ok(out[start..].to_string())
}

/// The value of each query, by index: its single number.
pub fn values(db: &PathBuf, queries: &[String]) -> Vec<Result<u64, String>> {
    let mut out = vec![];
    for chunk in queries.chunks(150) {
        let base = out.len();
        let union: Vec<String> = chunk.iter().enumerate().map(|(i, q)| format!("SELECT {} AS id, ({q}) AS v", base + i)).collect();
        match run(db, &format!("{};\n", union.join("\nUNION ALL ")), &["-readonly", "-json"]) {
            Ok(json) => {
                let rows: serde_json::Value = serde_json::from_str(json.trim()).unwrap_or_else(|e| panic!("{e}: {json}"));
                let mut got: HashMap<u64, Option<u64>> = HashMap::new();
                for r in rows.as_array().unwrap() {
                    got.insert(r["id"].as_u64().unwrap(), r["v"].as_u64());
                }
                out.extend((0..chunk.len()).map(|i| match got.get(&((base + i) as u64)) {
                    Some(Some(v)) => Ok(*v),
                    Some(None) => Err("not a count".to_string()),
                    None => Err("no row".to_string()),
                }));
            }
            // One query failed or was slow: count each alone, to find which.
            Err(_) => {
                for q in chunk {
                    out.push(run(db, &format!("SELECT ({q}) AS v;\n"), &["-readonly", "-json"]).and_then(|json| {
                        let rows: serde_json::Value = serde_json::from_str(json.trim()).map_err(|e| e.to_string())?;
                        rows[0]["v"].as_u64().ok_or_else(|| format!("no value in {json}"))
                    }));
                }
            }
        }
    }
    out
}

/// PostgreSQL, through `psql`, which connects as its environment says
/// (`PGHOST`, `PGPORT`, `PGUSER`, ...).
pub mod pg {
    use super::*;

    /// The database `scripts/postgres_fixtures.sh` loads TPC-H at scale
    /// factor 0.01 into (`CARDINAL_PG_DB`, default `cardinal_tpch`), if a
    /// server has it.
    pub fn database() -> Option<String> {
        let db = std::env::var("CARDINAL_PG_DB").unwrap_or_else(|_| "cardinal_tpch".into());
        let rows = run(&db, "SELECT count(*) FROM lineitem;").ok()?;
        (rows.trim() == "60175").then_some(db)
    }

    /// Each partial index's name and predicate, as
    /// `Catalog::with_partial_indexes` takes them: a row each, `|` between.
    pub const PARTIAL_INDEXES: &str = "SELECT c.relname, pg_get_expr(i.indpred, i.indrelid) FROM pg_index i \
         JOIN pg_class c ON c.oid = i.indexrelid WHERE i.indpred IS NOT NULL;";

    /// Runs `sql` on `db`, returning its rows, unaligned.
    pub fn run(db: &str, sql: &str) -> Result<String, String> {
        exec(psql(db), sql)
    }

    /// `psql` on `db`: a database, or `database/schema` to read the
    /// schema's relations by their bare names.
    fn psql(db: &str) -> Command {
        let (db, schema) = db.split_once('/').map_or((db, None), |(d, s)| (d, Some(s)));
        let mut command = Command::new("psql");
        command.args(["-X", "-q", "-At", "-v", "ON_ERROR_STOP=1", "-d", db]);
        if let Some(schema) = schema {
            command.env("PGOPTIONS", format!("-c search_path={schema}"));
        }
        command
    }

    /// Whether a server answers.
    pub fn available() -> bool {
        run("postgres", "SELECT 1;").is_ok_and(|out| out.trim() == "1")
    }

    /// Copies the tables of the DuckDB database `duck` into schema `schema`
    /// of the PostgreSQL database `db`, with their primary keys, once: a
    /// copy made before is kept. With `rows`, at most that many rows of
    /// each. DuckDB writes them, through its `postgres` extension, which
    /// connects as `psql` does.
    pub fn mirror(duck: &PathBuf, db: &str, schema: &str, rows: Option<u64>) -> Result<(), String> {
        let long = std::time::Duration::from_secs(3600);
        let exists = run("postgres", &format!("SELECT count(*) FROM pg_database WHERE datname = '{db}';"))?;
        if exists.trim() == "0" {
            run("postgres", &format!("CREATE DATABASE \"{db}\";"))?;
        }
        if run(db, &format!("SELECT count(*) FROM \"{schema}\"._cardinal_mirrored;")).is_ok() {
            return Ok(());
        }
        run(db, &format!("DROP SCHEMA IF EXISTS \"{schema}\" CASCADE; CREATE SCHEMA \"{schema}\";"))?;
        let list = |sql: &str| -> Result<Vec<Vec<String>>, String> {
            // As JSON: the CLI colors what it lists.
            let out = super::run(duck, sql, &["-readonly", "-json"])?;
            let rows: serde_json::Value = serde_json::from_str(out.trim()).unwrap_or(serde_json::Value::Array(vec![]));
            let text = |v: &serde_json::Value| v.as_str().map(str::to_string).unwrap_or_else(|| v.to_string());
            Ok(rows.as_array().into_iter().flatten().filter_map(|r| r.as_object()).map(|r| r.values().map(text).collect()).collect())
        };
        let tables = list("SELECT table_name FROM information_schema.tables WHERE table_schema = 'main' AND table_type = 'BASE TABLE' ORDER BY 1;")?;
        // From a session of its own, the DuckDB database attached to read.
        let mut script = format!(
            "INSTALL postgres; LOAD postgres; ATTACH '{}' AS src (READ_ONLY); ATTACH 'dbname={db}' AS pg (TYPE postgres);\n",
            duck.display()
        );
        for t in tables.iter().filter_map(|t| t.first()) {
            let limit = rows.map(|n| format!(" LIMIT {n}")).unwrap_or_default();
            script.push_str(&format!("CREATE TABLE pg.\"{schema}\".\"{t}\" AS SELECT * FROM src.main.\"{t}\"{limit};\n"));
        }
        exec_within(Command::new("duckdb"), &script, long)?;
        let keys = list(
            "SELECT table_name AS a, array_to_string(list_transform(constraint_column_names, c -> '\"' || c || '\"'), ', ') AS b \
             FROM duckdb_constraints() WHERE schema_name = 'main' AND constraint_type = 'PRIMARY KEY';",
        )?;
        let mut finish = String::new();
        for k in keys.iter().filter(|k| k.len() == 2) {
            finish.push_str(&format!("ALTER TABLE \"{schema}\".\"{}\" ADD PRIMARY KEY ({});\n", k[0], k[1]));
        }
        finish.push_str(&format!("ANALYZE;\nCREATE TABLE \"{schema}\"._cardinal_mirrored ();\n"));
        exec_within(psql(db), &finish, long).map(|_| ())
    }

    /// Planner settings under which a query's plans differ: as PostgreSQL
    /// chooses, with hash joins over sequential scans only, and with merge
    /// joins, each in one process; and in several, which split the rows of
    /// what they share, and report averages.
    pub const SETTINGS: [&str; 4] = [
        "",
        "SET enable_nestloop = off; SET enable_mergejoin = off; SET enable_indexscan = off; SET enable_indexonlyscan = off; SET enable_bitmapscan = off;",
        "SET enable_hashjoin = off; SET enable_nestloop = off;",
        "SET max_parallel_workers_per_gather = 2; SET parallel_setup_cost = 0; SET parallel_tuple_cost = 0; \
         SET min_parallel_table_scan_size = 0; SET min_parallel_index_scan_size = 0;",
    ];

    fn explain(db: &str, options: &str, sql: &str, settings: &str) -> Result<String, String> {
        let sql = sql.trim().trim_end_matches(';');
        // A statement PostgreSQL would run past the time limit ends there,
        // rather than run on after its client is gone.
        let limit = super::timeout().as_millis();
        let script = format!(
            "SET max_parallel_workers_per_gather = 0; SET jit = off; SET statement_timeout = {limit}; {settings}\n\
             EXPLAIN ({options}VERBOSE, COSTS OFF, FORMAT JSON) {sql};\n"
        );
        let out = run(db, &script).map_err(|e| if e.contains("statement timeout") { TIMED_OUT.to_string() } else { e })?;
        let start = out.find('[').ok_or_else(|| format!("no plan in {out}"))?;
        Ok(out[start..].to_string())
    }

    /// The profile of `sql` under `settings`, as PostgreSQL's JSON.
    pub fn profile(db: &str, sql: &str, settings: &str) -> Result<String, String> {
        explain(db, "ANALYZE, TIMING OFF, BUFFERS OFF, SUMMARY OFF, ", sql, settings)
    }

    /// The plan of `sql`, not run.
    pub fn plan(db: &str, sql: &str) -> Result<String, String> {
        explain(db, "", sql, "")
    }

    /// The value of each query, by index: its single number.
    pub fn values(db: &str, queries: &[String]) -> Vec<Result<u64, String>> {
        let one = |out: &str| out.trim().parse::<u64>().map_err(|_| format!("not a count: {out}"));
        let limit = format!("SET statement_timeout = {};\n", super::timeout().as_millis());
        let run = |db: &str, sql: &str| {
            run(db, &format!("{limit}{sql}")).map_err(|e| if e.contains("statement timeout") { TIMED_OUT.to_string() } else { e })
        };
        let mut out = vec![];
        for chunk in queries.chunks(150) {
            let base = out.len();
            let union: Vec<String> = chunk.iter().enumerate().map(|(i, q)| format!("SELECT {} AS id, ({q})::bigint AS v", base + i)).collect();
            match run(db, &format!("{};\n", union.join("\nUNION ALL "))) {
                Ok(rows) => {
                    let got: HashMap<u64, Result<u64, String>> = rows
                        .lines()
                        .filter_map(|l| l.split_once('|'))
                        .filter_map(|(id, v)| Some((id.parse().ok()?, one(v))))
                        .collect();
                    out.extend((0..chunk.len()).map(|i| got.get(&((base + i) as u64)).cloned().unwrap_or(Err("no row".to_string()))));
                }
                // One query failed or was slow: count each alone, to find which.
                Err(_) => out.extend(chunk.iter().map(|q| run(db, &format!("SELECT ({q})::bigint;\n")).and_then(|v| one(&v)))),
            }
        }
        out
    }
}

/// An engine running TPC-H at scale factor 0.01.
#[derive(Debug, Clone)]
pub enum Engine {
    DuckDb(PathBuf),
    Postgres(String),
}

impl Engine {
    /// DuckDB, if its CLI is here.
    pub fn duckdb() -> Option<Engine> {
        duckdb_available().then(|| Engine::DuckDb(database()))
    }

    /// PostgreSQL, if a server has the fixtures' database.
    pub fn postgres() -> Option<Engine> {
        pg::database().map(Engine::Postgres)
    }

    /// The DuckDB database file, or PostgreSQL's `database` or
    /// `database/schema`.
    pub fn target(&self) -> String {
        match self {
            Engine::DuckDb(db) => db.display().to_string(),
            Engine::Postgres(db) => db.clone(),
        }
    }

    /// The rows of `sql`, as JSON objects.
    pub fn json(&self, sql: &str) -> serde_json::Value {
        let sql = sql.trim().trim_end_matches(';');
        let out = match self {
            Engine::DuckDb(db) => run(db, &format!("{sql};"), &["-readonly", "-json"]),
            Engine::Postgres(db) => pg::run(db, &format!("SELECT coalesce(json_agg(t), '[]') FROM ({sql}) t;")),
        };
        serde_json::from_str(out.unwrap_or_default().trim()).unwrap_or(serde_json::Value::Array(vec![]))
    }

    pub fn name(&self) -> &'static str {
        match self {
            Engine::DuckDb(_) => "duckdb",
            Engine::Postgres(_) => "postgres",
        }
    }

    /// The ways to run a query for plans that differ: DuckDB's thread
    /// counts, PostgreSQL's planner settings.
    pub fn variants(&self) -> Vec<String> {
        match self {
            Engine::DuckDb(_) => vec!["t1".into(), "t4".into()],
            Engine::Postgres(_) => (0..pg::SETTINGS.len()).map(|i| format!("s{i}")).collect(),
        }
    }

    /// The profile of `sql`, run as `variant` (one of [`Engine::variants`]).
    pub fn profile(&self, sql: &str, variant: &str) -> Result<String, String> {
        let n: usize = variant[1..].parse().map_err(|_| format!("no variant {variant}"))?;
        match self {
            Engine::DuckDb(db) => profile(db, sql, n),
            Engine::Postgres(db) => pg::profile(db, sql, pg::SETTINGS[n]),
        }
    }

    /// The plan of `sql`, not run.
    pub fn plan(&self, sql: &str) -> Result<String, String> {
        match self {
            Engine::DuckDb(db) => {
                let out = run(db, &format!("EXPLAIN (FORMAT JSON) {};", sql.trim().trim_end_matches(';')), &["-list", "-noheader"])?;
                let start = out.find('[').ok_or_else(|| format!("no plan in {out}"))?;
                Ok(out[start..].to_string())
            }
            Engine::Postgres(db) => pg::plan(db, sql),
        }
    }

    /// A profile of `sql`, read.
    pub fn read(&self, catalog: &Catalog, name: &str, json: &str, sql: &str) -> Result<ObservedPlan, String> {
        match self {
            Engine::DuckDb(_) => from_duckdb(catalog, name, json),
            Engine::Postgres(_) => from_postgres(catalog, name, json, Some(sql)),
        }
        .map_err(|e| e.to_string())
    }

    /// A plan of `sql`, or a profile without its counts, read.
    pub fn read_plan(&self, catalog: &Catalog, name: &str, json: &str, sql: &str) -> Result<ObservedPlan, String> {
        match self {
            Engine::DuckDb(_) => from_duckdb_explain(catalog, name, json, Some(sql)),
            Engine::Postgres(_) => from_postgres_explain(catalog, name, json, Some(sql)),
        }
        .map_err(|e| e.to_string())
    }

    /// The partial indexes of the database with their predicates, which a
    /// catalog must have for PostgreSQL's index scans to be read: DuckDB
    /// has none.
    pub fn partial_indexes(&self) -> Vec<(String, String)> {
        match self {
            Engine::DuckDb(_) => vec![],
            Engine::Postgres(db) => pg::run(db, pg::PARTIAL_INDEXES)
                .unwrap_or_default()
                .lines()
                .filter_map(|l| l.split_once('|'))
                .map(|(i, p)| (i.to_string(), p.to_string()))
                .collect(),
        }
    }

    /// The SQL its counts are written in.
    pub fn dialect(&self) -> CountDialect {
        match self {
            Engine::DuckDb(_) => CountDialect::DuckDb,
            Engine::Postgres(_) => CountDialect::Postgres,
        }
    }

    /// The value of each query, by index: its single number.
    pub fn values(&self, queries: &[String]) -> Vec<Result<u64, String>> {
        match self {
            Engine::DuckDb(db) => values(db, queries),
            Engine::Postgres(db) => pg::values(db, queries),
        }
    }

    /// Counts each fact `facts`' plans have and did not count
    /// ([`FactSet::unobserved`]), and adds it: then what follows. Returns
    /// how many it added, and how many no query here could count.
    pub fn fill(&self, catalog: &Catalog, facts: &mut FactSet) -> (usize, usize) {
        let kinds: Vec<FactKind> = facts.unobserved().cloned().collect();
        let mut queries = vec![];
        let mut asked = vec![];
        for kind in &kinds {
            let Some(c) = kind.count_sql_in(catalog, facts, self.dialect()) else { continue };
            asked.push((kind, queries.len(), c.of.is_some()));
            queries.push(c.value);
            queries.extend(c.of);
        }
        let values = self.values(&queries);
        let mut added = 0;
        for (kind, at, shares) in asked {
            let Ok(value) = values[at].clone() else { continue };
            let of = match shares.then(|| values[at + 1].clone()) {
                Some(Ok(of)) => Some(of),
                Some(Err(_)) => continue,
                None => None,
            };
            if let Some(fact) = kind.counted(value, of) {
                added += facts.insert(fact) as usize;
            }
        }
        facts.close();
        (added, kinds.len() - added)
    }

    /// The rows `sql` returns.
    pub fn count(&self, sql: &str) -> Result<u64, String> {
        self.values(&[format!("select count(*) from ({}) q", sql.trim().trim_end_matches(';'))]).pop().unwrap()
    }
}

/// A small deterministic random source.
pub struct Rng(pub u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)
    }
    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    pub fn below(&mut self, n: usize) -> usize {
        (self.next() % n.max(1) as u64) as usize
    }
    pub fn chance(&mut self, percent: usize) -> bool {
        self.below(100) < percent
    }
    pub fn pick<'a>(&mut self, xs: &[&'a str]) -> &'a str {
        xs[self.below(xs.len())]
    }
}
