//! Running an eval's jobs (§1.8): each a distinct analysis to build and
//! search, run by a pool of plain threads, longest first, each record of a
//! job written as it completes.
//!
//! Results do not depend on the pool: every build and search runs in a Z3
//! context of its own, checks are limited by work (`rlimit`), and nothing
//! here calls into rayon. After the run, jobs whose checks hit a
//! wall-clock guard are run again alone, and `audit` jobs are run again
//! alone and must give the same bounds and the same `rlimit` counts.

use std::collections::BTreeMap;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc::Sender;
use std::time::{Duration, Instant};

use anyhow::{Result, anyhow, bail};
use cardinal::observed::ObservedPlan;
use cardinal::{Analysis, Bounds, BuildStats, Builder, CheckStats, Limits, Operator};
use rand::seq::IteratorRandom;

use crate::bench::{Benchmark, OperatorTruth};
use crate::record::{BuildRecord, Checks, Record, Run, Times};

/// What a job bounds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum What {
    /// The query's output ([`Analysis::bounds`]).
    Root,
    /// Operator `id` ([`Analysis::node_bounds`]).
    Node(usize),
    /// Every operator ([`Analysis::plan_bounds`]).
    Plan,
}

/// One analysis to build and search.
#[derive(Debug, Clone)]
pub struct Job {
    pub target: String,
    /// The reference plans, by engine and query, in the order given.
    pub plans: Vec<(String, String)>,
    pub cardinalities: bool,
    pub limits: Limits,
    pub what: What,
    /// An estimate of its cost, to start the longest first.
    pub cost: u64,
}

/// A job's result.
#[derive(Debug, Clone)]
pub struct Outcome {
    /// The bounds, one per operator for [`What::Plan`].
    pub bounds: Vec<Bounds>,
    pub build: BuildStats,
    pub search: CheckStats,
    pub search_time: Duration,
}

impl Outcome {
    pub fn limited(&self) -> bool {
        self.build.link_checks.limited + self.search.limited > 0
    }

    pub fn timed_out(&self) -> bool {
        self.build.link_checks.timed_out + self.search.timed_out > 0
    }

    /// What must be the same however the job is run: the bounds, and the
    /// work Z3 did.
    fn fingerprint(&self) -> (Vec<Bounds>, u64, u64) {
        (self.bounds.clone(), self.build.link_checks.rlimit, self.search.rlimit)
    }
}

/// A job, and the records its result fills: each a record of the run with
/// its keys and truth set ([`fill`]).
pub struct Planned {
    pub job: Job,
    pub records: Vec<Record>,
}

/// How jobs are run.
#[derive(Debug, Clone)]
pub struct Pool {
    pub threads: usize,
    /// One job at a time, pinned to one core.
    pub exclusive: bool,
    /// Start no job while the process uses more.
    pub max_memory: u64,
    /// Jobs run again alone after the run.
    pub audit: usize,
    pub seed: u64,
}

/// The targets' builders, made once: each job clones its target's.
pub struct Builders<'b> {
    pub bench: &'b Benchmark,
    pub builders: BTreeMap<String, (Builder<'static>, Duration)>,
}

impl<'b> Builders<'b> {
    pub async fn new(bench: &'b Benchmark, targets: &[String]) -> Result<Builders<'b>> {
        let mut builders = BTreeMap::new();
        for t in targets {
            let start = Instant::now();
            let b = bench.builder(t).await?;
            builders.insert(t.clone(), (b, start.elapsed()));
        }
        Ok(Builders { bench, builders })
    }

    /// Target `t`'s builder, with `options`' limits and no plans.
    pub fn of(&self, t: &str) -> &Builder<'static> {
        &self.builders[t].0
    }

    /// The time it took to parse and optimize target `t`.
    pub fn plan_time(&self, t: &str) -> Duration {
        self.builders[t].1
    }

    /// Runs `job`: builds its analysis and searches it.
    pub fn run(&self, job: &Job) -> Result<(Outcome, Vec<Operator>)> {
        let b = self.bench;
        let plans: Vec<&ObservedPlan> = job
            .plans
            .iter()
            .map(|(e, q)| b.profile(e, q).ok_or_else(|| anyhow!("no {e} profile of {q}")))
            .collect::<Result<_>>()?;
        let mut builder: Builder<'_> = self.of(&job.target).clone();
        builder = builder.options(cardinal::Options { limits: job.limits, ..b.options() }).with_plans(plans);
        if job.cardinalities {
            builder = builder.with_cardinalities(b.cardinalities.iter().map(|(t, n)| (t.clone(), *n)));
        }
        let a: Analysis = builder.build()?;
        let ops = a.operators();
        if let Some(truth) = b.operator_truth.get(&job.target) {
            check_operators(&job.target, &ops, truth)?;
        }
        let start = Instant::now();
        let (bounds, search) = match job.what {
            What::Root => {
                let (x, s) = a.bounds_with_stats()?;
                (vec![x], s)
            }
            What::Node(id) => {
                let (x, s) = a.node_bounds(id)?;
                (vec![x], s)
            }
            What::Plan => {
                let (p, s) = a.plan_bounds_with_stats()?;
                (p.nodes.into_iter().map(|n| n.bounds).collect(), s)
            }
        };
        let outcome = Outcome { bounds, build: a.stats().clone(), search: search.checks, search_time: start.elapsed() };
        Ok((outcome, ops))
    }
}

/// Fails unless `ops` are the operators `truth` was counted for.
fn check_operators(target: &str, ops: &[Operator], truth: &[OperatorTruth]) -> Result<()> {
    let same = ops.len() == truth.len() && ops.iter().zip(truth).all(|(o, t)| o.var == t.var && o.operator == t.operator);
    if !same {
        bail!("{target}: its operators are not those of operator_truth.json");
    }
    Ok(())
}

/// Fills `r`, a record of a job, from its outcome (or error).
pub fn fill(r: &mut Record, result: &Result<Outcome, String>, plan_time: Duration, exclusive: bool) {
    r.timing = if exclusive { "exclusive" } else { "contended" }.to_string();
    match result {
        Err(e) => r.error = Some(e.clone()),
        Ok(o) => {
            let b = match r.operator {
                Some(id) if o.bounds.len() > 1 => o.bounds.get(id).copied(),
                _ => o.bounds.first().copied(),
            };
            match b {
                Some(b) => r.set_bounds(b, r.truth),
                None => r.error = Some(format!("no bounds for operator {:?}", r.operator)),
            }
            r.time_ms = Times::of(plan_time, &o.build, o.search_time);
            r.build = Some(BuildRecord::from(&o.build));
            r.search = Some(Checks::from(o.search));
        }
    }
}

/// What a pool's run did.
pub struct Done {
    /// Each job's outcome, by its index in the jobs run.
    pub outcomes: BTreeMap<usize, Result<Outcome, String>>,
    pub peak_rss: u64,
}

/// Runs each job of `planned` whose records are not all in `run` yet,
/// longest first, writing every record as its job completes: the first
/// to be written measured, the rest `reused`. Then reruns alone the jobs
/// whose checks timed out, and audits.
pub fn run_all(builders: &Builders, planned: &mut [Planned], run: &Run, pool: &Pool) -> Result<Done> {
    for p in planned.iter_mut() {
        p.records.retain(|r| !run.done.contains(&r.key()));
    }
    let mut order: Vec<usize> = (0..planned.len()).filter(|&i| !planned[i].records.is_empty()).collect();
    order.sort_by_key(|&i| std::cmp::Reverse(planned[i].job.cost));
    let total = order.len();
    eprintln!("{total} jobs to run, {} records", order.iter().map(|&i| planned[i].records.len()).sum::<usize>());

    let (tx, writer) = run.writer()?;
    let outcomes = Mutex::new(BTreeMap::new());
    let next = AtomicUsize::new(0);
    let running = AtomicUsize::new(0);
    let finished = AtomicUsize::new(0);
    let started = Instant::now();
    let threads = if pool.exclusive { 1 } else { pool.threads.max(1) };
    let planned_ref = &*planned;
    std::thread::scope(|s| -> Result<()> {
        let mut handles = vec![];
        for w in 0..threads {
            let tx = tx.clone();
            let (order, outcomes, next, running, finished) = (&order, &outcomes, &next, &running, &finished);
            let h = std::thread::Builder::new().name(format!("eval-{w}")).stack_size(64 << 20).spawn_scoped(s, move || {
                if pool.exclusive {
                    pin_to_last_core();
                }
                loop {
                    let n = next.fetch_add(1, Ordering::SeqCst);
                    let Some(&i) = order.get(n) else { return };
                    // Memory: wait while others run and the process is over.
                    while running.load(Ordering::SeqCst) > 0 && rss() > pool.max_memory {
                        std::thread::sleep(Duration::from_millis(200));
                    }
                    running.fetch_add(1, Ordering::SeqCst);
                    let p = &planned_ref[i];
                    let result = builders.run(&p.job).map(|(o, _)| o).map_err(|e| format!("{e:#}"));
                    running.fetch_sub(1, Ordering::SeqCst);
                    send(&tx, p, &result, builders, pool.exclusive, false);
                    let done = finished.fetch_add(1, Ordering::SeqCst) + 1;
                    progress(done, total, started, &p.job);
                    outcomes.lock().unwrap().insert(i, result);
                }
            })?;
            handles.push(h);
        }
        for h in handles {
            h.join().map_err(|_| anyhow!("a worker panicked"))?;
        }
        Ok(())
    })?;
    let mut outcomes = outcomes.into_inner().unwrap();

    // Wall-clock guards that fired under contention: again, alone.
    let timed_out: Vec<usize> = outcomes.iter().filter(|(_, r)| r.as_ref().is_ok_and(Outcome::timed_out)).map(|(&i, _)| i).collect();
    if !pool.exclusive && !timed_out.is_empty() {
        eprintln!("{} jobs timed out: running them again alone", timed_out.len());
        for i in timed_out {
            let p = &planned[i];
            let result = builders.run(&p.job).map(|(o, _)| o).map_err(|e| format!("{e:#}"));
            send(&tx, p, &result, builders, false, true);
            outcomes.insert(i, result);
        }
    }
    drop(tx);
    writer.join().map_err(|_| anyhow!("the writer panicked"))??;

    audit(builders, planned, &outcomes, pool)?;
    Ok(Done { outcomes, peak_rss: peak_rss() })
}

/// Writes each record of `p`, filled from `result`.
fn send(tx: &Sender<Record>, p: &Planned, result: &Result<Outcome, String>, builders: &Builders, exclusive: bool, rerun: bool) {
    let plan_time = builders.plan_time(&p.job.target);
    let mut measured = std::collections::BTreeSet::new();
    for r in &p.records {
        let mut r = r.clone();
        fill(&mut r, result, plan_time, exclusive);
        // The first record of each operator is measured; the rest reuse it.
        r.reused = !measured.insert(r.operator);
        r.rerun_alone = rerun;
        let _ = tx.send(r);
    }
}

/// Runs `pool.audit` of the jobs again, one at a time, and fails unless
/// each gives the same bounds and `rlimit` counts.
fn audit(builders: &Builders, planned: &[Planned], outcomes: &BTreeMap<usize, Result<Outcome, String>>, pool: &Pool) -> Result<()> {
    let mut rng = crate::rng::rng(pool.seed, "audit", "", 0);
    let ok: Vec<usize> = outcomes.iter().filter(|(_, r)| r.is_ok()).map(|(&i, _)| i).collect();
    let picked = ok.iter().copied().choose_multiple(&mut rng, pool.audit.min(ok.len()));
    if picked.is_empty() {
        return Ok(());
    }
    eprintln!("auditing {} jobs alone", picked.len());
    let mut failures = vec![];
    for i in picked {
        let job = &planned[i].job;
        let Ok(before) = &outcomes[&i] else { continue };
        let again = builders.run(job)?.0;
        if before.fingerprint() != again.fingerprint() {
            failures.push(format!("{} with {} plans: {:?} then {:?}", job.target, job.plans.len(), before.fingerprint(), again.fingerprint()));
        }
    }
    if !failures.is_empty() {
        for f in &failures {
            eprintln!("AUDIT: {f}");
        }
        bail!("{} audited jobs differ when run alone", failures.len());
    }
    eprintln!("audit passed");
    Ok(())
}

fn progress(done: usize, total: usize, started: Instant, job: &Job) {
    let every = (total / 100).max(1);
    if done.is_multiple_of(every) || done == total {
        let el = started.elapsed().as_secs_f64();
        let eta = el / done as f64 * (total - done) as f64;
        eprintln!("[{done}/{total}] {:.0} s, ~{:.0} s left ({} with {} plans)", el, eta, job.target, job.plans.len());
    }
}

/// The process's resident memory, from `/proc/self/statm`.
pub fn rss() -> u64 {
    let statm = std::fs::read_to_string("/proc/self/statm").unwrap_or_default();
    let pages: u64 = statm.split_whitespace().nth(1).and_then(|p| p.parse().ok()).unwrap_or(0);
    pages * 4096
}

/// The process's peak resident memory, from `/proc/self/status`.
pub fn peak_rss() -> u64 {
    let status = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    status
        .lines()
        .find(|l| l.starts_with("VmHWM:"))
        .and_then(|l| l.split_whitespace().nth(1))
        .and_then(|kb| kb.parse::<u64>().ok())
        .map_or(0, |kb| kb * 1024)
}

/// Pins the calling thread to the machine's last core.
fn pin_to_last_core() {
    let n = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    // SAFETY: a zeroed cpu_set_t is a valid empty set; the call only reads it.
    unsafe {
        let mut set: libc::cpu_set_t = std::mem::zeroed();
        libc::CPU_SET(n - 1, &mut set);
        libc::sched_setaffinity(0, std::mem::size_of::<libc::cpu_set_t>(), &set);
    }
}
