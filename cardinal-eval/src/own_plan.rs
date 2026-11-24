//! `own-plan` (§4): each query bounded with its own profile. The plan
//! counted every row, so the ideal is `qU = 1` everywhere: anything else is
//! information in the plan cardinal does not use. One job per query.

use anyhow::{Result, bail};
use clap::Args;
use serde_json::{Map, json};

use crate::bench::Benchmark;
use crate::eval::{Common, finish};
use crate::jobs::{Builders, Job, Planned, What, run_all};
use crate::record::Record;

#[derive(Debug, Args)]
pub struct OwnPlanArgs {
    #[command(flatten)]
    pub common: Common,
    /// Only these queries.
    #[arg(long, value_delimiter = ',')]
    pub only: Vec<String>,
    /// The engine whose profiles are given.
    #[arg(long, default_value = "duckdb")]
    pub engine: String,
}

pub async fn own_plan(args: OwnPlanArgs) -> Result<()> {
    let c = &args.common;
    let bench = Benchmark::load(&c.data, &c.bench).await?;
    bench.require_prepared()?;
    let targets: Vec<String> = bench
        .q_target
        .iter()
        .filter(|q| args.only.is_empty() || args.only.contains(q))
        .filter(|q| bench.profile(&args.engine, q).is_some())
        .cloned()
        .collect();
    if targets.is_empty() {
        bail!("no targets with a {} profile", args.engine);
    }
    let switches = json!({"cardinalities": c.cardinalities, "unbounded": c.unbounded, "budget_scale": c.budget_scale, "engine": args.engine, "only": args.only});
    let meta = c.meta("own-plan", &bench, switches, &bench.q_ref, &targets);
    let run = c.run("own-plan", &bench.name, &meta)?;
    let builders = Builders::new(&bench, &targets).await?;
    let mut planned: Vec<Planned> = targets
        .iter()
        .map(|q| {
            let plan = bench.profile(&args.engine, q).expect("filtered above");
            Planned {
                job: Job {
                    target: q.clone(),
                    plans: vec![(args.engine.clone(), q.clone())],
                    cardinalities: c.cardinalities,
                    limits: c.limits(),
                    what: What::Root,
                    cost: plan.nodes.len() as u64,
                },
                records: vec![Record {
                    eval: "own-plan".into(),
                    bench: bench.name.clone(),
                    target: q.clone(),
                    target_kind: "root".into(),
                    template: bench.queries[q].template.clone(),
                    engine: Some(args.engine.clone()),
                    refs: vec![q.clone()],
                    relevant: 1,
                    truth: bench.truth.get(q).copied(),
                    ..Default::default()
                }],
            }
        })
        .collect();
    let done = run_all(&builders, &mut planned, &run, &c.pool())?;
    finish(&run, done.peak_rss, |records| {
        let mut m = Map::new();
        let exact = records.iter().filter(|r| r.exact == Some(true)).count();
        m.insert("exact".into(), json!(exact));
        m
    })?;
    Ok(())
}
