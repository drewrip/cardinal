//! Raw results: one record per measurement, appended to a run directory's
//! `records.jsonl` as it completes, and `run.json` at the end.
//!
//! A run directory, `results/<eval>/<bench>-<YYYYmmdd-HHMMSS>/`, holds
//! `meta.json` (every switch, the benchmark's manifest, the cardinal
//! revision, the host), `records.jsonl`, and once done `run.json`:
//! `{"meta": ..., "records": [...]}`, records sorted by key. A run resumed
//! (`--resume <dir>`) skips the keys its JSONL already holds.

use std::collections::BTreeSet;
use std::fs::{File, OpenOptions};
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::sync::mpsc::{Sender, channel};
use std::thread::JoinHandle;
use std::time::Duration;

use anyhow::{Context, Result, bail};
use cardinal::{Bounds, BuildStats, CheckStats};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

/// Anything above this is treated as unbounded by the search: the finite
/// stand-in for `qU = ∞` is `CAP / t'`.
pub const CAP: f64 = (1u64 << 30) as f64;

/// The upper Q-error of `upper` against truth `t`: `max(U', t') / min(U',
/// t')`, each at least 1; `None` (∞) without an upper bound.
pub fn q_upper(upper: Option<u64>, t: u64) -> Option<f64> {
    let (u, t) = (upper?.max(1) as f64, t.max(1) as f64);
    Some(u.max(t) / u.min(t))
}

/// The lower Q-error `t' / L'`, `None` (∞) when `L = 0`.
pub fn q_lower(lower: u64, t: u64) -> Option<f64> {
    (lower > 0).then(|| t.max(1) as f64 / lower as f64)
}

/// One measurement: the raw bounds and truth, their metrics, and what it
/// took. Fields an eval does not use are left out of the JSON.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Record {
    pub eval: String,
    pub bench: String,
    pub target: String,
    /// `root`, `core` or `operator`.
    pub target_kind: String,
    pub template: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trial: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub k: Option<usize>,
    /// The operator bounded, by id, its text, and the joins at or below it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub operator: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub operator_text: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub joins: Option<usize>,
    /// The engine whose plans are given, and the setting (`own`, `others`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub engine: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub setting: Option<String>,
    /// The reference plans given, in order, and how many were relevant.
    pub refs: Vec<String>,
    pub relevant: usize,
    pub truth: Option<u64>,
    pub lower: Option<u64>,
    pub upper: Option<u64>,
    pub q_upper: Option<f64>,
    pub q_lower: Option<f64>,
    pub holds: Option<bool>,
    pub exact: Option<bool>,
    /// Shares the result of an earlier record's job.
    pub reused: bool,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub rerun_alone: bool,
    pub time_ms: Times,
    pub build: Option<BuildRecord>,
    pub search: Option<Checks>,
    /// `contended` or `exclusive` (§1.8).
    pub timing: String,
    pub error: Option<String>,
}

impl Record {
    /// What identifies the measurement in a run.
    pub fn key(&self) -> String {
        let o = |v: Option<String>| v.unwrap_or_default();
        [
            self.eval.clone(),
            self.bench.clone(),
            self.target.clone(),
            self.target_kind.clone(),
            o(self.engine.clone()),
            o(self.setting.clone()),
            o(self.trial.map(|t| format!("{t:04}"))),
            o(self.k.map(|k| format!("{k:05}"))),
            o(self.operator.map(|k| format!("{k:05}"))),
        ]
        .join("/")
    }

    /// Sets the bounds and truth, and their metrics.
    pub fn set_bounds(&mut self, b: Bounds, truth: Option<u64>) {
        self.lower = Some(b.lower);
        self.upper = b.upper;
        self.truth = truth;
        if let Some(t) = truth {
            self.q_upper = q_upper(b.upper, t);
            self.q_lower = q_lower(b.lower, t);
            self.holds = Some(b.holds(t));
            self.exact = Some(b.lower == t && b.upper == Some(t));
        }
    }
}

/// Wall times, in milliseconds.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Times {
    pub plan: f64,
    pub build: f64,
    pub rules: f64,
    pub link: f64,
    pub pins: f64,
    pub search: f64,
}

pub fn ms(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

impl Times {
    pub fn of(plan: Duration, build: &BuildStats, search: Duration) -> Times {
        Times { plan: ms(plan), build: ms(build.total), rules: ms(build.rules), link: ms(build.link), pins: ms(build.pins), search: ms(search) }
    }
}

/// [`BuildStats`]' counts.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct BuildRecord {
    pub nodes: usize,
    pub plans_given: usize,
    pub plans_selected: usize,
    pub plan_nodes: usize,
    pub pinned: usize,
    pub floors: usize,
    pub assertions_before: usize,
    pub assertions: usize,
    pub link_classes: usize,
    pub links: usize,
    pub link_checks: Checks,
}

impl From<&BuildStats> for BuildRecord {
    fn from(s: &BuildStats) -> BuildRecord {
        BuildRecord {
            nodes: s.nodes,
            plans_given: s.plans_given,
            plans_selected: s.plans_selected,
            plan_nodes: s.plan_nodes,
            pinned: s.pinned,
            floors: s.floors,
            assertions_before: s.assertions_before,
            assertions: s.assertions,
            link_classes: s.link_classes,
            links: s.links,
            link_checks: s.link_checks.into(),
        }
    }
}

/// [`CheckStats`]' counts, its time in [`Times`].
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Checks {
    pub sat: u32,
    pub unsat: u32,
    pub limited: u32,
    pub timed_out: u32,
    pub incomplete: u32,
    pub rlimit: u64,
}

impl From<CheckStats> for Checks {
    fn from(c: CheckStats) -> Checks {
        Checks { sat: c.sat, unsat: c.unsat, limited: c.limited, timed_out: c.timed_out, incomplete: c.incomplete, rlimit: c.rlimit }
    }
}

/// A run's directory.
pub struct Run {
    pub dir: PathBuf,
    /// The keys already recorded, when resumed.
    pub done: BTreeSet<String>,
}

impl Run {
    /// A new run of `eval` on `bench` under `results`, its `meta.json`
    /// written.
    pub fn create(results: &Path, eval: &str, bench: &str, meta: &Value) -> Result<Run> {
        let stamp = utc_stamp();
        let dir = results.join(eval).join(format!("{bench}-{stamp}"));
        std::fs::create_dir_all(&dir).with_context(|| dir.display().to_string())?;
        std::fs::write(dir.join("meta.json"), serde_json::to_string_pretty(meta)? + "\n")?;
        File::create(dir.join("records.jsonl"))?;
        Ok(Run { dir, done: BTreeSet::new() })
    }

    /// The run at `dir`, to resume: its recorded keys. `meta`'s switches
    /// must be those it was started with.
    pub fn resume(dir: &Path, meta: &Value) -> Result<Run> {
        let old: Value = crate::bench::read_json(&dir.join("meta.json"))?;
        if old["switches"] != meta["switches"] {
            bail!("{} was run with other switches: {} (now {})", dir.display(), old["switches"], meta["switches"]);
        }
        let records = read_records(dir)?;
        // Drop a line cut short, so appends start on a line of their own.
        let path = dir.join("records.jsonl");
        if std::fs::read(&path)?.last().is_some_and(|&c| c != b'\n') {
            let text: String = records.iter().map(|r| serde_json::to_string(r).map(|l| l + "\n")).collect::<serde_json::Result<_>>()?;
            std::fs::write(&path, text)?;
        }
        let done = records.iter().map(Record::key).collect();
        Ok(Run { dir: dir.to_path_buf(), done })
    }

    /// A writer thread appending each record sent to `records.jsonl`, one
    /// line each, flushed as it comes. Drop the sender, then join.
    pub fn writer(&self) -> Result<(Sender<Record>, JoinHandle<Result<()>>)> {
        let mut file = OpenOptions::new().append(true).create(true).open(self.dir.join("records.jsonl"))?;
        let (tx, rx) = channel::<Record>();
        let handle = std::thread::spawn(move || -> Result<()> {
            for r in rx {
                writeln!(file, "{}", serde_json::to_string(&r)?)?;
                file.flush()?;
            }
            Ok(())
        });
        Ok((tx, handle))
    }

    /// Writes `run.json`: `meta.json` with `end` and `extra` added, and
    /// every record, sorted by key. Returns the records.
    pub fn finish(&self, extra: Value) -> Result<Vec<Record>> {
        let mut meta: Value = crate::bench::read_json(&self.dir.join("meta.json"))?;
        meta["end"] = json!(utc_stamp());
        if let (Some(m), Value::Object(e)) = (meta.as_object_mut(), extra) {
            m.extend(e);
        }
        std::fs::write(self.dir.join("meta.json"), serde_json::to_string_pretty(&meta)? + "\n")?;
        let records = latest(read_records(&self.dir)?);
        let run = json!({"meta": meta, "records": records});
        std::fs::write(self.dir.join("run.json"), serde_json::to_string(&run)? + "\n")?;
        Ok(records)
    }
}

/// The last record of each key (a job run again replaces its records),
/// sorted by key.
pub fn latest(records: Vec<Record>) -> Vec<Record> {
    let by_key: std::collections::BTreeMap<String, Record> = records.into_iter().map(|r| (r.key(), r)).collect();
    by_key.into_values().collect()
}

/// The records of run `dir`'s JSONL. A last line cut short (the run was
/// killed while writing it) is skipped.
pub fn read_records(dir: &Path) -> Result<Vec<Record>> {
    let path = dir.join("records.jsonl");
    if !path.exists() {
        return Ok(vec![]);
    }
    let lines: Vec<String> = BufReader::new(File::open(&path)?).lines().collect::<std::io::Result<_>>()?;
    let n = lines.len();
    let mut out = vec![];
    for (i, line) in lines.iter().enumerate().filter(|(_, l)| !l.trim().is_empty()) {
        match serde_json::from_str(line) {
            Ok(r) => out.push(r),
            Err(_) if i + 1 == n => break,
            Err(e) => bail!("{}:{}: {e}", path.display(), i + 1),
        }
    }
    Ok(out)
}

/// The UTC time now, `YYYYmmdd-HHMMSS`.
pub fn utc_stamp() -> String {
    let secs = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0);
    let (days, rem) = (secs / 86_400, secs % 86_400);
    // Civil date from days since 1970-01-01 (Howard Hinnant's algorithm).
    let z = days as i64 + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = yoe + era * 400 + i64::from(m <= 2);
    format!("{y:04}{m:02}{d:02}-{:02}{:02}{:02}", rem / 3600, rem % 3600 / 60, rem % 60)
}

/// The cardinal git revision, and whether the tree is dirty.
pub fn revision() -> Value {
    let git = |args: &[&str]| {
        std::process::Command::new("git")
            .args(args)
            .current_dir(env!("CARGO_MANIFEST_DIR"))
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
    };
    json!({
        "commit": git(&["rev-parse", "HEAD"]),
        "dirty": git(&["status", "--porcelain", "--untracked-files=no"]).map(|s| !s.is_empty()),
    })
}

/// The machine: CPU, cores, memory.
pub fn host() -> Value {
    let cpuinfo = std::fs::read_to_string("/proc/cpuinfo").unwrap_or_default();
    let field = |name: &str| cpuinfo.lines().find(|l| l.starts_with(name)).and_then(|l| l.split(':').nth(1)).map(|v| v.trim().to_string());
    let physical: BTreeSet<(String, String)> = cpuinfo
        .split("\n\n")
        .filter_map(|b| {
            let f = |n: &str| b.lines().find(|l| l.starts_with(n)).and_then(|l| l.split(':').nth(1)).map(|v| v.trim().to_string());
            Some((f("physical id")?, f("core id")?))
        })
        .collect();
    json!({
        "cpu": field("model name"),
        "threads": std::thread::available_parallelism().map(|n| n.get()).ok(),
        "cores": (!physical.is_empty()).then_some(physical.len()),
        "memory_bytes": memory_bytes(),
    })
}

/// Physical cores (not SMT siblings), or every thread if unknown.
pub fn physical_cores() -> usize {
    host()["cores"].as_u64().map(|n| n as usize).unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1))
}

/// The machine's memory, from `/proc/meminfo`.
pub fn memory_bytes() -> Option<u64> {
    let info = std::fs::read_to_string("/proc/meminfo").ok()?;
    let kb: u64 = info.lines().find(|l| l.starts_with("MemTotal:"))?.split_whitespace().nth(1)?.parse().ok()?;
    Some(kb * 1024)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn q_errors() {
        assert_eq!(q_upper(Some(100), 10), Some(10.0));
        assert_eq!(q_upper(Some(0), 0), Some(1.0));
        assert_eq!(q_upper(Some(5), 10), Some(2.0));
        assert_eq!(q_upper(None, 10), None);
        assert_eq!(q_lower(0, 10), None);
        assert_eq!(q_lower(5, 10), Some(2.0));
    }

    #[test]
    fn records_round_trip_and_resume() {
        let dir = std::env::temp_dir().join(format!("cardinal-eval-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let meta = json!({"switches": {"trials": 2}});
        let run = Run::create(&dir, "holdout", "tpch", &meta).unwrap();
        let (tx, h) = run.writer().unwrap();
        for k in [3, 1] {
            let mut r = Record { eval: "holdout".into(), bench: "tpch".into(), target: "q01".into(), k: Some(k), ..Default::default() };
            r.set_bounds(Bounds { lower: 0, upper: Some(20) }, Some(10));
            tx.send(r).unwrap();
        }
        drop(tx);
        h.join().unwrap().unwrap();
        // A line cut short at the end is skipped.
        std::fs::OpenOptions::new().append(true).open(run.dir.join("records.jsonl")).unwrap().write_all(b"{\"eval\":").unwrap();
        let resumed = Run::resume(&run.dir, &meta).unwrap();
        assert_eq!(resumed.done.len(), 2);
        assert!(Run::resume(&run.dir, &json!({"switches": {"trials": 3}})).is_err());
        let records = resumed.finish(json!({})).unwrap();
        assert_eq!(records.iter().map(|r| r.k).collect::<Vec<_>>(), vec![Some(1), Some(3)]);
        assert_eq!(records[0].q_upper, Some(2.0));
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn stamp_is_a_date() {
        let s = utc_stamp();
        assert_eq!(s.len(), 15);
        assert!(s.starts_with("20"));
    }
}
