//! `holdout` (§2, §3): how a query's Q-error falls as more of the rest of
//! the workload's plans are given.
//!
//! For each target `q` and trial `j`, the other references are permuted by
//! the RNG of (seed, bench, q, j), and `q` is bounded with the first `k`
//! of them for each `k` of the grid. Each (target, set of relevant plans
//! given) is one job ([`Builder::relevant`](cardinal::Builder::relevant)):
//! a plan that adds no constraint does not change the analysis, so every
//! record with the same relevant set shares one result. Plans are given in
//! name order, so a job's result does not depend on the trial's order.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use anyhow::{Result, bail};
use cardinal::{Limits, Operator};
use clap::{Args, ValueEnum};
use serde_json::{Value, json};

use crate::bench::{Benchmark, default_data};
use crate::jobs::{Builders, Job, Planned, Pool, What, run_all};
use crate::record::{Record, Run, host, memory_bytes, physical_cores, revision, utc_stamp};
use crate::rng::permuted;

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum, serde::Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Target {
    /// The query's output.
    Root,
    /// The operator under the plan's top chain of Limit, Sort, Projection
    /// and aggregates without GROUP BY.
    Core,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum, serde::Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Grid {
    /// Every k from 0 to n.
    Full,
    /// k in {0, 1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, n}.
    Log,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum Timing {
    /// As many jobs at once as `--threads`: times are inflated.
    Contended,
    /// One job at a time, pinned to one core.
    Exclusive,
}

#[derive(Debug, Args)]
pub struct HoldoutArgs {
    #[arg(long)]
    pub bench: String,
    #[arg(long, default_value_os_t = default_data())]
    pub data: PathBuf,
    #[arg(long, default_value_os_t = default_results())]
    pub results: PathBuf,
    /// Default: core for JOB, root elsewhere.
    #[arg(long, value_enum)]
    pub target: Option<Target>,
    /// Default: 10; 5 with --operators, 3 with --unbounded.
    #[arg(long)]
    pub trials: Option<u32>,
    #[arg(long, default_value_t = 0)]
    pub seed: u64,
    /// Default: full for TPC-H, log elsewhere and with --unbounded.
    #[arg(long, value_enum)]
    pub grid: Option<Grid>,
    /// Only these targets.
    #[arg(long, value_delimiter = ',')]
    pub only: Vec<String>,
    /// No k above this.
    #[arg(long)]
    pub max_k: Option<usize>,
    /// Default: the physical cores.
    #[arg(long)]
    pub threads: Option<usize>,
    /// Give every table's row count, at every k.
    #[arg(long)]
    pub cardinalities: bool,
    /// No Z3 budget: `Limits::unbounded`.
    #[arg(long)]
    pub unbounded: bool,
    /// DSB: the first N instances of each template.
    #[arg(long, default_value_t = 1)]
    pub instances: u32,
    /// Bound every operator, not one target (§3).
    #[arg(long)]
    pub operators: bool,
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

/// The switches that shape a run's results, resolved.
#[derive(Debug, Clone, serde::Serialize)]
struct Switches {
    target: Target,
    trials: u32,
    seed: u64,
    grid: Grid,
    only: Vec<String>,
    max_k: Option<usize>,
    cardinalities: bool,
    unbounded: bool,
    instances: u32,
    operators: bool,
}

impl HoldoutArgs {
    fn switches(&self) -> Switches {
        let trials = self.trials.unwrap_or(if self.unbounded { 3 } else if self.operators { 5 } else { 10 });
        let grid = self.grid.unwrap_or(if self.bench == "tpch" && !self.unbounded { Grid::Full } else { Grid::Log });
        let target = self.target.unwrap_or(if self.bench == "job" { Target::Core } else { Target::Root });
        Switches {
            target,
            trials,
            seed: self.seed,
            grid,
            only: self.only.clone(),
            max_k: self.max_k,
            cardinalities: self.cardinalities,
            unbounded: self.unbounded,
            instances: self.instances,
            operators: self.operators,
        }
    }
}

/// The k of `grid` for `n` references, at most `max_k`.
pub fn ks(grid: Grid, n: usize, max_k: Option<usize>) -> Vec<usize> {
    let all: Vec<usize> = match grid {
        Grid::Full => (0..=n).collect(),
        Grid::Log => [0, 1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96].into_iter().filter(|&k| k < n).chain([n]).collect(),
    };
    all.into_iter().filter(|&k| max_k.is_none_or(|m| k <= m)).collect()
}

/// The operator a `core` target bounds: under the root's chain of Limit,
/// Sort, Projection and aggregates without GROUP BY.
pub fn core(ops: &[Operator]) -> usize {
    let mut id = ops.len() - 1;
    loop {
        let o = &ops[id];
        let passes = ["Limit:", "Sort:", "Projection:", "Aggregate: groupBy=[[]]"].iter().any(|p| o.operator.starts_with(p));
        match o.inputs[..] {
            [input] if passes => id = input,
            _ => return id,
        }
    }
}

/// Whether operator `o` can change a count (§3): a scan, filter, join or
/// aggregate. Others output their input's rows.
pub fn measured(o: &Operator) -> bool {
    let t = &o.operator;
    t.starts_with("TableScan:") || t.starts_with("Filter:") || t.starts_with("Aggregate:") || t.contains(" Join:")
}

/// The joins at or below operator `id`.
pub fn joins(ops: &[Operator], id: usize) -> usize {
    let here = usize::from(ops[id].operator.contains(" Join:"));
    here + ops[id].inputs.iter().map(|&i| joins(ops, i)).sum::<usize>()
}

pub async fn holdout(args: HoldoutArgs) -> Result<()> {
    let bench = Benchmark::load(&args.data, &args.bench).await?;
    bench.require_prepared()?;
    let sw = args.switches();
    if sw.operators && bench.operator_truth.is_empty() {
        bail!("--operators needs operator_truth.json");
    }
    let within = |q: &String| bench.queries[q].instance <= sw.instances;
    let q_ref: Vec<String> = bench.q_ref.iter().filter(|q| within(q)).cloned().collect();
    let targets: Vec<String> = bench.q_target.iter().filter(|q| within(q) && (sw.only.is_empty() || sw.only.contains(q))).cloned().collect();
    if targets.is_empty() {
        bail!("no targets");
    }
    let limits = if sw.unbounded { Limits::unbounded() } else { Limits::default() };
    let threads = args.threads.unwrap_or_else(physical_cores);
    let max_memory = args.max_memory.map(|g| (g * (1u64 << 30) as f64) as u64).unwrap_or_else(|| memory_bytes().unwrap_or(u64::MAX) / 5 * 4);

    let meta = json!({
        "eval": "holdout",
        "bench": bench.name,
        "manifest": bench.manifest,
        "revision": revision(),
        "switches": sw,
        "options": {"max_product": bench.options().max_product, "foreign_keys": bench.foreign_keys.len(), "limits": format!("{limits:?}")},
        "q_ref": q_ref,
        "q_target": targets,
        "templates": targets.iter().map(|q| (q.clone(), bench.queries[q].template.clone())).collect::<BTreeMap<_, _>>(),
        "threads": threads,
        "timing": if args.timing == Timing::Exclusive { "exclusive" } else { "contended" },
        "host": host(),
        "start": utc_stamp(),
    });
    let run = match &args.resume {
        Some(dir) => Run::resume(dir, &meta)?,
        None => Run::create(&args.results, "holdout", &bench.name, &meta)?,
    };
    eprintln!("run: {}", run.dir.display());

    let builders = Builders::new(&bench, &targets).await?;
    let mut planned = plan(&bench, &builders, &sw, &q_ref, &targets, limits)?;
    let pool = Pool { threads, exclusive: args.timing == Timing::Exclusive, max_memory, audit: args.audit, seed: sw.seed };
    let done = run_all(&builders, &mut planned, &run, &pool)?;

    let summary = check(&crate::record::latest(crate::record::read_records(&run.dir)?));
    run.finish(json!({"peak_rss_bytes": done.peak_rss, "checks": summary}))?;
    eprintln!("{}", serde_json::to_string_pretty(&summary)?);
    eprintln!("run: {}", run.dir.display());
    if summary["unsound"].as_array().is_some_and(|a| !a.is_empty()) || summary["same_plans_disagree"].as_array().is_some_and(|a| !a.is_empty()) {
        bail!("unsound bounds, or trials that disagree given the same plans");
    }
    Ok(())
}

/// What one record of a target bounds: the operator (none for the root),
/// its truth, its text, and the joins at or below it.
type Slot = (Option<usize>, Option<u64>, Option<String>, Option<usize>);

/// Every job of the run, with its records.
fn plan(bench: &Benchmark, builders: &Builders, sw: &Switches, q_ref: &[String], targets: &[String], limits: Limits) -> Result<Vec<Planned>> {
    let mut jobs: BTreeMap<(String, Vec<String>), Planned> = BTreeMap::new();
    for t in targets {
        let query = &bench.queries[t];
        let refs: Vec<String> = q_ref.iter().filter(|r| *r != t).cloned().collect();
        let builder = builders.of(t);
        let relevant: BTreeSet<&String> =
            refs.iter().filter(|r| bench.profile("duckdb", r).is_some_and(|p| builder.relevant(p))).collect();
        let n = refs.len();

        // What the target's records bound, and their truth.
        let truth = bench.operator_truth.get(t);
        let (what, slots): (What, Vec<Slot>) = if sw.operators || sw.target == Target::Core {
            let ops = builder.clone().build()?.operators();
            let truth = truth.ok_or_else(|| anyhow::anyhow!("{t}: no operator truth"))?;
            if sw.operators {
                let slots = (0..ops.len())
                    .filter(|&i| measured(&ops[i]) && truth[i].rows.is_some())
                    .map(|i| (Some(i), truth[i].rows, Some(ops[i].operator.clone()), Some(joins(&ops, i))))
                    .collect();
                (What::Plan, slots)
            } else {
                let c = core(&ops);
                let Some(rows) = truth[c].rows else {
                    eprintln!("{t}: core operator {c} has no truth; skipped");
                    continue;
                };
                (What::Node(c), vec![(Some(c), Some(rows), Some(ops[c].operator.clone()), None)])
            }
        } else {
            (What::Root, vec![(None, bench.truth.get(t).copied(), None, None)])
        };
        let kind = if sw.operators { "operator" } else if sw.target == Target::Core { "core" } else { "root" };

        for trial in 1..=sw.trials {
            let order = permuted(&refs, sw.seed, &bench.name, t, trial);
            for k in ks(sw.grid, n, sw.max_k) {
                let given = &order[..k];
                let mut rel: Vec<String> = given.iter().filter(|r| relevant.contains(r)).cloned().collect();
                rel.sort();
                let entry = jobs.entry((t.clone(), rel.clone())).or_insert_with(|| {
                    let cost = 1 + rel.iter().filter_map(|r| bench.profile("duckdb", r)).map(|p| p.nodes.len() as u64).sum::<u64>();
                    Planned {
                        job: Job {
                            target: t.clone(),
                            plans: rel.iter().map(|r| ("duckdb".to_string(), r.clone())).collect(),
                            cardinalities: sw.cardinalities,
                            limits,
                            what: what.clone(),
                            cost,
                        },
                        records: vec![],
                    }
                });
                for (operator, rows, text, joins) in &slots {
                    entry.records.push(Record {
                        eval: "holdout".into(),
                        bench: bench.name.clone(),
                        target: t.clone(),
                        target_kind: kind.into(),
                        template: query.template.clone(),
                        trial: Some(trial),
                        k: Some(k),
                        operator: *operator,
                        operator_text: text.clone(),
                        joins: *joins,
                        refs: given.to_vec(),
                        relevant: rel.len(),
                        truth: *rows,
                        ..Default::default()
                    });
                }
            }
        }
    }
    Ok(jobs.into_values().collect())
}

/// The run's checks: unsound bounds, trials that disagree given the same
/// plans (at k = n, every trial),
/// non-monotone steps, records whose checks ran out of budget, errors.
fn check(records: &[Record]) -> Value {
    let unsound: Vec<String> = records
        .iter()
        .filter(|r| r.holds == Some(false))
        .map(|r| format!("{}: {:?} <= X <= {:?}, truth {:?}", r.key(), r.lower, r.upper, r.truth))
        .collect();
    for u in &unsound {
        eprintln!("UNSOUND {u}");
    }
    let errors: Vec<String> = records.iter().filter_map(|r| r.error.as_ref().map(|e| format!("{}: {e}", r.key()))).collect();
    let limited: Vec<String> = records
        .iter()
        .filter(|r| {
            let b = r.build.as_ref().map_or(0, |b| b.link_checks.limited);
            b + r.search.map_or(0, |s| s.limited) > 0
        })
        .map(Record::key)
        .collect();
    let timed_out = records
        .iter()
        .filter(|r| r.build.as_ref().map_or(0, |b| b.link_checks.timed_out) + r.search.map_or(0, |s| s.timed_out) > 0)
        .count();

    // Per (target, operator, plans given as a set): the bounds, which must
    // be one (at k = n, every trial's).
    let mut same: BTreeMap<(String, Option<usize>, Vec<String>), BTreeSet<(u64, Option<u64>)>> = BTreeMap::new();
    // Per (target, operator, trial): upper bounds by k.
    let mut steps: BTreeMap<(String, Option<usize>, Option<u32>), Vec<(usize, Option<u64>)>> = BTreeMap::new();
    for r in records.iter().filter(|r| r.error.is_none()) {
        let mut refs = r.refs.clone();
        refs.sort();
        same.entry((r.target.clone(), r.operator, refs)).or_default().insert((r.lower.unwrap_or(0), r.upper));
        steps.entry((r.target.clone(), r.operator, r.trial)).or_default().push((r.k.unwrap_or(0), r.upper));
    }
    let disagree: Vec<String> =
        same.iter().filter(|(_, b)| b.len() > 1).map(|((t, o, refs), b)| format!("{t} {o:?} with {} plans: {b:?}", refs.len())).collect();
    let mut non_monotone = vec![];
    for ((t, o, trial), mut s) in steps {
        s.sort();
        for w in s.windows(2) {
            let grew = match (w[0].1, w[1].1) {
                (Some(a), Some(b)) => b > a,
                (Some(_), None) => true,
                _ => false,
            };
            if grew {
                non_monotone.push(format!("{t} {o:?} trial {trial:?}: k {} -> {}: {:?} -> {:?}", w[0].0, w[1].0, w[0].1, w[1].1));
            }
        }
    }
    json!({
        "records": records.len(),
        "unsound": unsound,
        "same_plans_disagree": disagree,
        "non_monotone": non_monotone,
        "limited": limited.len(),
        "limited_records": limited,
        "timed_out": timed_out,
        "errors": errors,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn log_grid_ends_at_n() {
        assert_eq!(ks(Grid::Log, 21, None), vec![0, 1, 2, 3, 4, 6, 8, 12, 16, 21]);
        assert_eq!(ks(Grid::Log, 16, None), vec![0, 1, 2, 3, 4, 6, 8, 12, 16]);
        assert_eq!(ks(Grid::Full, 3, Some(2)), vec![0, 1, 2]);
    }

    #[test]
    fn core_skips_the_top_chain() {
        let op = |t: &str, inputs: Vec<usize>| Operator { var: String::new(), operator: t.into(), inputs };
        let ops = vec![
            op("TableScan: t", vec![]),
            op("Filter: a", vec![0]),
            op("Aggregate: groupBy=[[]], aggr=[[sum(a)]]", vec![1]),
            op("Projection: x", vec![2]),
        ];
        assert_eq!(core(&ops), 1);
        let ops = vec![op("TableScan: t", vec![]), op("Aggregate: groupBy=[[a]], aggr=[[]]", vec![0]), op("Sort: a, fetch=10", vec![1])];
        assert_eq!(core(&ops), 1);
    }
}
