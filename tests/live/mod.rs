//! Running queries in a live DuckDB through its CLI, for the tests that
//! check facts against the truth.
#![allow(dead_code)]

use std::collections::HashMap;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

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
}

/// Runs `sql` on `db` with `args`, returning standard output. A call that
/// takes longer than `CARDINAL_LIVE_TIMEOUT` is killed, and fails with
/// [`TIMED_OUT`].
pub fn run(db: &PathBuf, sql: &str, args: &[&str]) -> Result<String, String> {
    let mut child = Command::new("duckdb")
        .arg(db)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| e.to_string())?;
    child.stdin.take().unwrap().write_all(sql.as_bytes()).map_err(|e| e.to_string())?;
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
        if start.elapsed() > timeout() {
            let _ = child.kill();
            let _ = child.wait();
            return Err(TIMED_OUT.into());
        }
        std::thread::sleep(std::time::Duration::from_millis(5));
    };
    let stdout = out_reader.join().unwrap().map_err(|e| e.to_string())?;
    let stderr = err_reader.join().unwrap().map_err(|e| e.to_string())?;
    let err = String::from_utf8_lossy(&stderr);
    if !status.success() || err.contains("Error") {
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
