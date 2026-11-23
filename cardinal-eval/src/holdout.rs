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
use anyhow::{Result, bail};
use cardinal::{Limits, Operator};
use clap::{Args, ValueEnum};
use serde_json::{Map, Value, json};

use crate::bench::Benchmark;
use crate::eval::{Common, finish};
use crate::jobs::{Builders, Job, Planned, What, run_all};
use crate::record::Record;
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

#[derive(Debug, Args)]
pub struct HoldoutArgs {
    #[command(flatten)]
    pub common: Common,
    /// Default: core for JOB, root elsewhere.
    #[arg(long, value_enum)]
    pub target: Option<Target>,
    /// Default: 10; 5 with --operators, 3 with --unbounded.
    #[arg(long)]
    pub trials: Option<u32>,
    /// Default: full for TPC-H, log elsewhere and with --unbounded.
    #[arg(long, value_enum)]
    pub grid: Option<Grid>,
    /// Only these targets.
    #[arg(long, value_delimiter = ',')]
    pub only: Vec<String>,
    /// No k above this.
    #[arg(long)]
    pub max_k: Option<usize>,
    /// Add this many plans at each step of the full grid: k in {0, s, 2s,
    /// ..., n}. Fewer steps, so a faster run.
    #[arg(long)]
    pub step: Option<usize>,
    /// The k to bound at, in place of the grid: e.g. `0,8,32,n`, where `n`
    /// is every other query's plan.
    #[arg(long, value_delimiter = ',')]
    pub ks: Vec<String>,
    /// DSB: the first N instances of each template.
    #[arg(long, default_value_t = 1)]
    pub instances: u32,
    /// Bound every operator, not one target (§3).
    #[arg(long)]
    pub operators: bool,
}

/// The switches that shape a run's results, resolved.
#[derive(Debug, Clone, serde::Serialize)]
struct Switches {
    target: Target,
    trials: u32,
    seed: u64,
    grid: Grid,
    step: Option<usize>,
    ks: Vec<String>,
    only: Vec<String>,
    max_k: Option<usize>,
    cardinalities: bool,
    unbounded: bool,
    instances: u32,
    operators: bool,
}

impl HoldoutArgs {
    fn switches(&self) -> Switches {
        let c = &self.common;
        let trials = self.trials.unwrap_or(if c.unbounded { 3 } else if self.operators { 5 } else { 10 });
        let full = (c.bench == "tpch" && !c.unbounded) || self.step.is_some();
        let grid = self.grid.unwrap_or(if full { Grid::Full } else { Grid::Log });
        let target = self.target.unwrap_or(if c.bench == "job" { Target::Core } else { Target::Root });
        Switches {
            target,
            trials,
            seed: c.seed,
            grid,
            step: self.step,
            ks: self.ks.clone(),
            only: self.only.clone(),
            max_k: self.max_k,
            cardinalities: c.cardinalities,
            unbounded: c.unbounded,
            instances: self.instances,
            operators: self.operators,
        }
    }
}

impl Switches {
    /// The k to bound at, for `n` references: `ks` if given, else the
    /// grid's, at most `max_k`.
    fn ks(&self, n: usize) -> Result<Vec<usize>> {
        if self.ks.is_empty() {
            return Ok(ks(self.grid, n, self.step, self.max_k));
        }
        let mut out = BTreeSet::new();
        for k in &self.ks {
            let k = match k.trim() {
                "n" => n,
                k => k.parse::<usize>().map_err(|_| anyhow::anyhow!("--ks: {k} is not a number or n"))?.min(n),
            };
            if self.max_k.is_none_or(|m| k <= m) {
                out.insert(k);
            }
        }
        Ok(out.into_iter().collect())
    }
}

/// The k of `grid` for `n` references, `step` plans apart on the full
/// grid (and n), at most `max_k`.
pub fn ks(grid: Grid, n: usize, step: Option<usize>, max_k: Option<usize>) -> Vec<usize> {
    let all: Vec<usize> = match grid {
        Grid::Full => (0..=n).step_by(step.unwrap_or(1).max(1)).chain([n]).collect::<BTreeSet<_>>().into_iter().collect(),
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
    let c = &args.common;
    let bench = Benchmark::load(&c.data, &c.bench).await?;
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
    let meta = c.meta("holdout", &bench, json!(sw), &q_ref, &targets);
    let run = c.run("holdout", &bench.name, &meta)?;
    let builders = Builders::new(&bench, &targets).await?;
    let mut planned = plan(&bench, &builders, &sw, &q_ref, &targets, c.limits())?;
    let done = run_all(&builders, &mut planned, &run, &c.pool())?;
    let checks = finish(&run, done.peak_rss, check)?;
    if checks["same_plans_disagree"].as_array().is_some_and(|a| !a.is_empty()) {
        bail!("trials disagree given the same plans");
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
            for k in sw.ks(n)? {
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

/// The holdout's own checks: trials that disagree given the same plans
/// (at k = n, every trial), and non-monotone steps.
#[allow(clippy::type_complexity)]
fn check(records: &[Record]) -> Map<String, Value> {
    // Per (target, operator, plans given as a set): the bounds, which must
    // be one.
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
    let mut m = Map::new();
    m.insert("same_plans_disagree".into(), json!(disagree));
    m.insert("non_monotone".into(), json!(non_monotone));
    m
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn log_grid_ends_at_n() {
        assert_eq!(ks(Grid::Log, 21, None, None), vec![0, 1, 2, 3, 4, 6, 8, 12, 16, 21]);
        assert_eq!(ks(Grid::Log, 16, None, None), vec![0, 1, 2, 3, 4, 6, 8, 12, 16]);
        assert_eq!(ks(Grid::Full, 3, None, Some(2)), vec![0, 1, 2]);
        assert_eq!(ks(Grid::Full, 21, Some(5), None), vec![0, 5, 10, 15, 20, 21]);
        assert_eq!(ks(Grid::Full, 20, Some(5), None), vec![0, 5, 10, 15, 20]);
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
