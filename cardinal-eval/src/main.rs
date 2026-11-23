//! `cardinal-eval <eval> --bench <name> [opts]`.

use std::path::PathBuf;

use anyhow::Result;
use cardinal_eval::bench::{Benchmark, default_data};
use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(about = "Accuracy evaluations of cardinal's bounds")]
struct Cli {
    #[command(subcommand)]
    eval: Eval,
}

#[derive(Subcommand)]
enum Eval {
    /// How a query's Q-error falls as more of the workload's plans are given.
    Holdout(cardinal_eval::holdout::HoldoutArgs),
    /// Summarize a prebaked benchmark: its queries, profiles and query sets.
    Info {
        #[arg(long)]
        bench: String,
        #[arg(long, default_value_os_t = default_data())]
        data: PathBuf,
    },
}

#[tokio::main]
async fn main() -> Result<()> {
    match Cli::parse().eval {
        Eval::Info { bench, data } => info(&Benchmark::load(&data, &bench).await?),
        Eval::Holdout(args) => cardinal_eval::holdout::holdout(args).await,
    }
}

fn info(b: &Benchmark) -> Result<()> {
    println!("{} at {}", b.name, b.dir.display());
    println!("  queries: {}, foreign keys: {}, tables counted: {}", b.queries.len(), b.foreign_keys.len(), b.cardinalities.len());
    for (engine, ps) in &b.profiles {
        let errors = b.profile_errors.get(engine).map_or(0, |e| e.len());
        println!("  profiles {engine}: {} read, {errors} not", ps.len());
    }
    println!("  q_ref: {}, q_target: {}, truth: {}, operator truth: {}", b.q_ref.len(), b.q_target.len(), b.truth.len(), b.operator_truth.len());
    if let Some(ex) = b.manifest["exclusions"].as_object() {
        for (q, why) in ex {
            println!("  excluded {q}: {}", why.as_str().unwrap_or_default());
        }
    }
    b.require_prepared()
}
