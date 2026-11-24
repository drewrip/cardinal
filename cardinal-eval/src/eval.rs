//! What every eval shares: its common switches, its run's metadata, the
//! pool its jobs run on, and the checks every run makes.

use std::path::PathBuf;

use anyhow::Result;
use cardinal::Limits;
use clap::{Args, ValueEnum};
use serde_json::{Map, Value, json};

use crate::bench::{Benchmark, default_data};
use crate::jobs::Pool;
use crate::record::{Record, Run, host, memory_bytes, physical_cores, revision, utc_stamp};

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum Timing {
    /// As many jobs at once as `--threads`: times are inflated.
    Contended,
    /// One job at a time, pinned to one core.
    Exclusive,
}

/// The switches every eval takes.
#[derive(Debug, Args)]
pub struct Common {
    #[arg(long)]
    pub bench: String,
    #[arg(long, default_value_os_t = default_data())]
    pub data: PathBuf,
    #[arg(long, default_value_os_t = default_results())]
    pub results: PathBuf,
    #[arg(long, default_value_t = 0)]
    pub seed: u64,
    /// Default: the physical cores.
    #[arg(long)]
    pub threads: Option<usize>,
    /// Give every table's row count.
    #[arg(long)]
    pub cardinalities: bool,
    /// No Z3 budget: `Limits::unbounded`.
    #[arg(long)]
    pub unbounded: bool,
    /// Multiply every Z3 budget, and the wall-clock guard, by this.
    #[arg(long, default_value_t = 1, conflicts_with = "unbounded")]
    pub budget_scale: u32,
    #[arg(long, value_enum, default_value = "contended")]
    pub timing: Timing,
    /// Jobs run again alone after the run, which must agree.
    #[arg(long, default_value_t = 20)]
    pub audit: usize,
    /// Start no job while the process uses more, in GiB. Default: 80 % of
    /// the memory.
    #[arg(long)]
    pub max_memory: Option<f64>,
    /// Continue the run in this directory.
    #[arg(long)]
    pub resume: Option<PathBuf>,
}

pub fn default_results() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("results")
}

impl Common {
    pub fn limits(&self) -> Limits {
        if self.unbounded {
            return Limits::unbounded();
        }
        let d = Limits::default();
        let n = self.budget_scale;
        Limits {
            search_first: d.search_first.saturating_mul(n),
            search: d.search.saturating_mul(n),
            link: d.link.saturating_mul(n),
            timeout_ms: d.timeout_ms.map(|t| t.saturating_mul(n)),
        }
    }

    pub fn threads(&self) -> usize {
        self.threads.unwrap_or_else(physical_cores)
    }

    pub fn pool(&self) -> Pool {
        let max_memory = self.max_memory.map(|g| (g * (1u64 << 30) as f64) as u64).unwrap_or_else(|| memory_bytes().unwrap_or(u64::MAX) / 5 * 4);
        Pool { threads: self.threads(), exclusive: self.timing == Timing::Exclusive, max_memory, audit: self.audit, seed: self.seed }
    }

    /// The run's metadata: `switches` (those that shape its results), and
    /// what every run records.
    pub fn meta(&self, eval: &str, bench: &Benchmark, switches: Value, q_ref: &[String], q_target: &[String]) -> Value {
        let limits = self.limits();
        json!({
            "eval": eval,
            "bench": bench.name,
            "manifest": bench.manifest,
            "revision": revision(),
            "switches": switches,
            "options": {"max_product": bench.options().max_product, "foreign_keys": bench.foreign_keys.len(), "limits": format!("{limits:?}")},
            "seed": self.seed,
            "q_ref": q_ref,
            "q_target": q_target,
            "templates": q_target.iter().map(|q| (q.clone(), bench.queries[q].template.clone())).collect::<std::collections::BTreeMap<_, _>>(),
            "threads": self.threads(),
            "timing": if self.timing == Timing::Exclusive { "exclusive" } else { "contended" },
            "host": host(),
            "start": utc_stamp(),
        })
    }

    /// The run: new, or resumed.
    pub fn run(&self, eval: &str, bench: &str, meta: &Value) -> Result<Run> {
        let run = match &self.resume {
            Some(dir) => Run::resume(dir, meta)?,
            None => Run::create(&self.results, eval, bench, meta)?,
        };
        eprintln!("run: {}", run.dir.display());
        Ok(run)
    }
}

/// The checks every run makes: unsound bounds, errors, records whose
/// checks ran out of budget or time.
pub fn checks(records: &[Record]) -> Map<String, Value> {
    let unsound: Vec<String> = records
        .iter()
        .filter(|r| r.holds == Some(false))
        .map(|r| format!("{}: {:?} <= X <= {:?}, truth {:?}", r.key(), r.lower, r.upper, r.truth))
        .collect();
    for u in &unsound {
        eprintln!("UNSOUND {u}");
    }
    let errors: Vec<String> = records.iter().filter_map(|r| r.error.as_ref().map(|e| format!("{}: {e}", r.key()))).collect();
    let budget = |r: &Record, f: fn(&crate::record::Checks) -> u32| r.build.as_ref().map_or(0, |b| f(&b.link_checks)) + r.search.as_ref().map_or(0, f);
    let limited: Vec<String> = records.iter().filter(|r| budget(r, |c| c.limited) > 0).map(Record::key).collect();
    let timed_out = records.iter().filter(|r| budget(r, |c| c.timed_out) > 0).count();
    let mut m = Map::new();
    m.insert("records".into(), json!(records.len()));
    m.insert("unsound".into(), json!(unsound));
    m.insert("errors".into(), json!(errors));
    m.insert("limited".into(), json!(limited.len()));
    m.insert("limited_records".into(), json!(limited));
    m.insert("timed_out".into(), json!(timed_out));
    m
}

/// Ends `run`: its checks (`checks`, and what `more` adds) into its
/// metadata and `run.json`. Fails if any bound is unsound.
pub fn finish(run: &Run, peak_rss: u64, more: impl FnOnce(&[Record]) -> Map<String, Value>) -> Result<Value> {
    let records = crate::record::latest(crate::record::read_records(&run.dir)?);
    let mut c = checks(&records);
    c.extend(more(&records));
    let c = Value::Object(c);
    run.finish(json!({"peak_rss_bytes": peak_rss, "checks": c}))?;
    let brief: Map<String, Value> = c
        .as_object()
        .unwrap()
        .iter()
        .map(|(k, v)| (k.clone(), v.as_array().map_or(v.clone(), |a| json!(a.len()))))
        .collect();
    eprintln!("checks: {}", Value::Object(brief));
    eprintln!("run: {}", run.dir.display());
    if c["unsound"].as_array().is_some_and(|a| !a.is_empty()) {
        anyhow::bail!("unsound bounds");
    }
    Ok(c)
}
