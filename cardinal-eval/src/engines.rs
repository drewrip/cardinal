//! `engines` (§5): the same queries over the same data, bounded with the
//! plans of each engine. The bounded query is always DataFusion's, so only
//! the plans differ. Per query and engine: `own`, its own plan only;
//! `others`, every other query's plan from that engine (leave-one-out).
//! One job per (query, engine, setting).

use anyhow::{Result, bail};
use clap::Args;
use serde_json::{Map, json};

use crate::bench::{Benchmark, root_rows};
use crate::eval::{Common, finish};
use crate::jobs::{Builders, Job, Planned, What, run_all};
use crate::record::Record;

#[derive(Debug, Args)]
pub struct EnginesArgs {
    #[command(flatten)]
    pub common: Common,
    /// The engines whose plans are given. Default: every engine with
    /// profiles.
    #[arg(long, value_delimiter = ',')]
    pub engines: Vec<String>,
    /// Only these queries.
    #[arg(long, value_delimiter = ',')]
    pub only: Vec<String>,
}

pub async fn engines(args: EnginesArgs) -> Result<()> {
    let c = &args.common;
    let bench = Benchmark::load(&c.data, &c.bench).await?;
    bench.require_prepared()?;
    let engines: Vec<String> = match args.engines.is_empty() {
        true => bench.profiles.keys().cloned().collect(),
        false => args.engines.clone(),
    };
    for e in &engines {
        if !bench.profiles.contains_key(e) {
            bail!("no {e} profiles in {}", bench.dir.display());
        }
    }
    let targets: Vec<String> = bench.q_target.iter().filter(|q| args.only.is_empty() || args.only.contains(q)).cloned().collect();
    // An engine's profile counts its root as DuckDB's does, over the same
    // data: else it is no reference.
    let mut mismatched = vec![];
    let usable = |e: &str, q: &str| -> bool {
        let Some(p) = bench.profile(e, q) else { return false };
        bench.q_ref.iter().any(|r| r == q) && root_rows(p).is_some_and(|n| Some(n) == bench.truth.get(q).copied())
    };
    for e in &engines {
        for (q, p) in &bench.profiles[e] {
            if root_rows(p).is_some_and(|n| Some(n) != bench.truth.get(q).copied()) {
                mismatched.push(format!("{e} {q}: {:?} rows, truth {:?}", root_rows(p), bench.truth.get(q)));
            }
        }
    }
    for m in &mismatched {
        eprintln!("ROOT MISMATCH {m}");
    }

    let switches = json!({"cardinalities": c.cardinalities, "unbounded": c.unbounded, "engines": engines, "only": args.only});
    let meta = c.meta("engines", &bench, switches, &bench.q_ref, &targets);
    let run = c.run("engines", &bench.name, &meta)?;
    let builders = Builders::new(&bench, &targets).await?;
    let mut planned = vec![];
    for q in &targets {
        let builder = builders.of(q);
        for e in &engines {
            let others: Vec<String> = bench.profiles[e].keys().filter(|r| *r != q && usable(e, r)).cloned().collect();
            let own: Vec<String> = if usable(e, q) { vec![q.clone()] } else { vec![] };
            for (setting, refs) in [("own", own), ("others", others)] {
                if refs.is_empty() {
                    continue;
                }
                let relevant = refs.iter().filter(|r| builder.relevant(bench.profile(e, r).unwrap())).count();
                let cost = refs.iter().map(|r| bench.profile(e, r).unwrap().nodes.len() as u64).sum::<u64>();
                planned.push(Planned {
                    job: Job {
                        target: q.clone(),
                        plans: refs.iter().map(|r| (e.clone(), r.clone())).collect(),
                        cardinalities: c.cardinalities,
                        limits: c.limits(),
                        what: What::Root,
                        cost,
                    },
                    records: vec![Record {
                        eval: "engines".into(),
                        bench: bench.name.clone(),
                        target: q.clone(),
                        target_kind: "root".into(),
                        template: bench.queries[q].template.clone(),
                        engine: Some(e.clone()),
                        setting: Some(setting.into()),
                        refs,
                        relevant,
                        truth: bench.truth.get(q).copied(),
                        ..Default::default()
                    }],
                });
            }
        }
    }
    let done = run_all(&builders, &mut planned, &run, &c.pool())?;
    finish(&run, done.peak_rss, |records| {
        let mut m = Map::new();
        m.insert("root_mismatches".into(), json!(mismatched));
        // Operators pinned, per engine and setting: plan shape, not the
        // engine, can leave a plan pinning little.
        let mut pinned: std::collections::BTreeMap<String, usize> = Default::default();
        for r in records {
            if let (Some(e), Some(s), Some(b)) = (&r.engine, &r.setting, &r.build) {
                *pinned.entry(format!("{e}/{s}")).or_default() += b.pinned;
            }
        }
        m.insert("pinned".into(), json!(pinned));
        m
    })?;
    Ok(())
}
