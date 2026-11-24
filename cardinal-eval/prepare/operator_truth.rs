//! `operator-truth --bench <name>`: the truth of a prebaked benchmark, and
//! which of its queries the evals use.
//!
//! - `truth.json`: each query's output rows, its DuckDB profile's root
//!   count.
//! - `operator_truth.json`: each operator's rows, by operator id: the
//!   query's analysis with no plans, validated ([`Analysis::validate`])
//!   over the Parquet copies, which runs the analyzed plan operator by
//!   operator. Operators it leaves uncounted are `null`.
//! - `manifest.json` gains `q_ref` (queries with a profile that reads and
//!   counted its root), `q_target` (those of `q_ref` DataFusion analyzes,
//!   whose root count DataFusion agrees with), and the reason each other
//!   query is excluded.
//!
//! Each query's counts are kept under `raw/operator_truth/` as they come,
//! so a run stopped part way resumes; delete them to count again.
//!
//! The Parquet tables are wrapped to look like the schema's empty tables
//! (the same schema and keys, no filter pushed into the scan), so each
//! query's analysis, and its operator ids, are those the evals make. Each
//! is checked to be.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use anyhow::{Context, Result, anyhow, bail};
use async_trait::async_trait;
use cardinal::Analysis;
use cardinal_eval::bench::{Benchmark, OperatorTruth, context, default_data, read_json_or_default, root_rows};
use clap::Parser;
use datafusion::arrow::datatypes::SchemaRef;
use datafusion::catalog::{Session, TableProvider};
use datafusion::common::Constraints;
use datafusion::datasource::file_format::parquet::ParquetFormat;
use datafusion::datasource::listing::{ListingOptions, ListingTable, ListingTableConfig, ListingTableUrl};
use datafusion::logical_expr::{Expr, TableType};
use datafusion::physical_plan::ExecutionPlan;
use datafusion::prelude::SessionContext;
use serde_json::{Value, json};

#[derive(Parser)]
struct Cli {
    /// The benchmark, a directory of `--data`.
    #[arg(long)]
    bench: String,
    #[arg(long, default_value_os_t = default_data())]
    data: PathBuf,
    /// Only these queries' operator truth, merged into what is there.
    #[arg(long, value_delimiter = ',')]
    only: Vec<String>,
    /// Queries validated at once: each holds every operator's output in
    /// memory.
    #[arg(long, default_value_t = 4)]
    jobs: usize,
    /// Skip validation: only `truth.json` and the query sets, every
    /// analyzable query a target.
    #[arg(long)]
    no_operators: bool,
    /// Seconds one query's validation may take: a query slower has no
    /// operator truth, and is no target.
    #[arg(long, default_value_t = 900)]
    timeout: u64,
    /// GiB the process may use: past it, the queries being validated stop,
    /// have no operator truth, and are no targets. Default: 60 % of the
    /// memory.
    #[arg(long)]
    max_memory: Option<f64>,
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let rt = tokio::runtime::Runtime::new()?;
    let bench = rt.block_on(Benchmark::load(&cli.data, &cli.bench))?;
    let mut exclusions: BTreeMap<String, String> = BTreeMap::new();

    // References: a profile that reads, and counted its root.
    let duckdb = bench.profiles.get("duckdb").cloned().unwrap_or_default();
    let errors = bench.profile_errors.get("duckdb").cloned().unwrap_or_default();
    let failures: BTreeMap<String, String> = serde_json::from_value(bench.manifest["profile_failures"].clone()).unwrap_or_default();
    let mut q_ref = vec![];
    let mut truth = BTreeMap::new();
    for q in bench.queries.keys() {
        let why = match (duckdb.get(q), errors.get(q), failures.get(q)) {
            (Some(p), _, _) => match root_rows(p) {
                Some(rows) => {
                    truth.insert(q.clone(), rows);
                    q_ref.push(q.clone());
                    continue;
                }
                None => "profile did not count its root".to_string(),
            },
            (None, Some(e), _) => format!("profile does not read: {e}"),
            (None, None, Some(e)) => format!("DuckDB could not profile it: {e}"),
            (None, None, None) => "no profile".to_string(),
        };
        exclusions.insert(q.clone(), format!("no reference: {why}"));
    }
    write(&bench, "truth.json", &json!(truth))?;

    // Targets: references DataFusion analyzes.
    let mut analyzable = vec![];
    for q in &q_ref {
        let built = rt.block_on(bench.builder(q)).and_then(|b| b.build().map_err(Into::into));
        match built {
            Ok(_) => analyzable.push(q.clone()),
            Err(e) => {
                exclusions.insert(q.clone(), format!("no target: DataFusion cannot analyze it: {e}"));
            }
        }
    }

    let mut q_target = analyzable.clone();
    let mut violations = BTreeMap::new();
    if !cli.no_operators {
        let todo: Vec<String> = analyzable.iter().filter(|q| cli.only.is_empty() || cli.only.contains(q)).cloned().collect();
        let mut stored: BTreeMap<String, Vec<OperatorTruth>> = match cli.only.is_empty() {
            true => BTreeMap::new(),
            false => read_json_or_default(&bench.dir.join("operator_truth.json"))?,
        };
        let limit = cli
            .max_memory
            .map(|g| (g * (1u64 << 30) as f64) as u64)
            .unwrap_or_else(|| cardinal_eval::record::memory_bytes().unwrap_or(u64::MAX) / 10 * 6);
        let results = validate_all(&bench, &todo, cli.jobs, cli.timeout, limit)?;
        for (q, result) in results {
            match result {
                Ok(t) => {
                    let root = t.ops.last().and_then(|o| o.rows);
                    if let Some(v) = t.violation {
                        eprintln!("{q}: VIOLATION {v}");
                        violations.insert(q.clone(), v);
                    }
                    if root != truth.get(&q).copied() {
                        exclusions.insert(q.clone(), format!("no target: DataFusion counts {root:?} rows, DuckDB {:?}", truth.get(&q)));
                    }
                    stored.insert(q, t.ops);
                }
                Err(e) => {
                    exclusions.insert(q.clone(), format!("no target: no operator truth: {e:#}"));
                }
            }
        }
        write(&bench, "operator_truth.json", &json!(stored))?;
        // A target needs its operators' truth, its root counted as DuckDB
        // counted it (those of --only and those stored before alike).
        for q in &analyzable {
            let root = stored.get(q).and_then(|ops| ops.last()).and_then(|o| o.rows);
            if !exclusions.contains_key(q) && root != truth.get(q).copied() {
                let why = match stored.get(q) {
                    None => "no target: no operator truth".to_string(),
                    Some(_) => format!("no target: DataFusion counts {root:?} rows, DuckDB {:?}", truth.get(q)),
                };
                exclusions.insert(q.clone(), why);
            }
        }
        q_target.retain(|q| !exclusions.contains_key(q));
    }

    let mut manifest = bench.manifest.clone();
    manifest["q_ref"] = json!(q_ref);
    manifest["q_target"] = json!(q_target);
    manifest["exclusions"] = json!(exclusions);
    manifest["validation_violations"] = json!(violations);
    write(&bench, "manifest.json", &manifest)?;
    eprintln!("{}: {} queries, {} references, {} targets", bench.name, bench.queries.len(), q_ref.len(), q_target.len());
    for (q, why) in &exclusions {
        eprintln!("  {q}: {why}");
    }
    if !violations.is_empty() {
        bail!("{} queries violate their constraints on real data", violations.len());
    }
    Ok(())
}

fn write(bench: &Benchmark, file: &str, v: &Value) -> Result<()> {
    std::fs::write(bench.dir.join(file), serde_json::to_string_pretty(v)? + "\n")?;
    Ok(())
}

/// One query's operators' rows, and any violation validation found.
#[derive(serde::Serialize, serde::Deserialize)]
struct Truth {
    ops: Vec<OperatorTruth>,
    violation: Option<String>,
}

/// [`validate`] of each of `queries`, `jobs` at once, each worker on a
/// thread of its own with its own Parquet context.
fn validate_all(bench: &Benchmark, queries: &[String], jobs: usize, timeout: u64, max_memory: u64) -> Result<Vec<(String, Result<Truth>)>> {
    let queue = Mutex::new(queries.iter().rev().cloned().collect::<Vec<_>>());
    let cache = bench.dir.join("raw").join("operator_truth");
    let cache = &cache;
    let out = Mutex::new(vec![]);
    std::thread::scope(|s| -> Result<()> {
        let mut handles = vec![];
        for _ in 0..jobs.max(1).min(queries.len().max(1)) {
            handles.push(std::thread::Builder::new().stack_size(64 << 20).spawn_scoped(s, || -> Result<()> {
                let rt = tokio::runtime::Builder::new_current_thread().enable_all().build()?;
                let ctx = rt.block_on(parquet_context(bench))?;
                loop {
                    let Some(q) = queue.lock().unwrap().pop() else { return Ok(()) };
                    // Each query's truth is kept as it is counted, so a run
                    // stopped part way resumes.
                    let cached = cache.join(format!("{q}.json"));
                    if let Ok(t) = std::fs::read_to_string(&cached).map_err(anyhow::Error::from).and_then(|s| Ok(serde_json::from_str::<Truth>(&s)?)) {
                        out.lock().unwrap().push((q, Ok(t)));
                        continue;
                    }
                    let start = std::time::Instant::now();
                    let limit = std::time::Duration::from_secs(timeout);
                    let r = rt.block_on(async {
                        tokio::select! {
                            r = tokio::time::timeout(limit, validate(bench, &ctx, &q)) =>
                                r.unwrap_or_else(|_| Err(anyhow!("timed out after {timeout} s"))),
                            _ = over_memory(max_memory) =>
                                Err(anyhow!("stopped: the process used over {} GiB", max_memory >> 30)),
                        }
                    });
                    eprintln!("{q}: {:.1} s{}", start.elapsed().as_secs_f64(), r.as_ref().err().map(|e| format!(": {e:#}")).unwrap_or_default());
                    // Give freed memory back, so the guard reads what is in use.
                    // SAFETY: malloc_trim only releases free heap memory.
                    unsafe { libc::malloc_trim(0) };
                    if let Ok(t) = &r {
                        std::fs::create_dir_all(cached.parent().unwrap())?;
                        std::fs::write(&cached, serde_json::to_string(t)?)?;
                    }
                    out.lock().unwrap().push((q, r));
                }
            })?);
        }
        for h in handles {
            h.join().map_err(|_| anyhow!("a worker panicked"))??;
        }
        Ok(())
    })?;
    let mut out = out.into_inner().unwrap();
    out.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(out)
}

/// Returns once the process uses more than `limit` bytes.
async fn over_memory(limit: u64) {
    while cardinal_eval::jobs::rss() <= limit {
        tokio::time::sleep(std::time::Duration::from_millis(200)).await;
    }
}

/// Query `q` analyzed over `ctx`'s Parquet tables and validated: each
/// operator's rows.
async fn validate(bench: &Benchmark, ctx: &SessionContext, q: &str) -> Result<Truth> {
    let sql = &bench.queries[q].sql;
    let a = Analysis::sql(ctx, sql).await?.options(bench.options()).build()?;
    let empty = bench.builder(q).await?.build()?;
    if a.operators() != empty.operators() {
        bail!("its operators over Parquet are not those over the schema's tables");
    }
    let v = a.validate(ctx).await?;
    let ops = a
        .operators()
        .into_iter()
        .map(|o| OperatorTruth { rows: v.rows.get(&o.var).copied(), var: o.var, operator: o.operator })
        .collect();
    Ok(Truth { ops, violation: v.violation })
}

/// The schema's tables over the Parquet copies, each as the schema's
/// table is to the analysis ([`AsDeclared`]).
async fn parquet_context(bench: &Benchmark) -> Result<SessionContext> {
    let declared = context(&bench.schema).await?;
    let ctx = SessionContext::new();
    let names = declared.catalog("datafusion").and_then(|c| c.schema("public")).map(|s| s.table_names()).unwrap_or_default();
    for name in names {
        let table = declared.table_provider(name.as_str()).await?;
        let path = bench.dir.join("parquet").join(format!("{name}.parquet"));
        if !path.exists() {
            bail!("no {}: run prepare/{}.sh", path.display(), bench.name);
        }
        let url = ListingTableUrl::parse(path.to_str().context("a UTF-8 path")?)?;
        let options = ListingOptions::new(Arc::new(ParquetFormat::default())).with_file_extension(".parquet");
        let config = ListingTableConfig::new(url).with_listing_options(options).with_schema(table.schema());
        let inner = Arc::new(ListingTable::try_new(config)?);
        let wrapped = AsDeclared { inner, schema: table.schema(), constraints: table.constraints().cloned() };
        ctx.register_table(name.as_str(), Arc::new(wrapped))?;
    }
    Ok(ctx)
}

/// A table read from `inner`, shown with a declared table's schema and
/// keys and, like it, taking no filters into its scan.
#[derive(Debug)]
struct AsDeclared {
    inner: Arc<dyn TableProvider>,
    schema: SchemaRef,
    constraints: Option<Constraints>,
}

#[async_trait]
impl TableProvider for AsDeclared {
    fn schema(&self) -> SchemaRef {
        self.schema.clone()
    }

    fn constraints(&self) -> Option<&Constraints> {
        self.constraints.as_ref()
    }

    fn table_type(&self) -> TableType {
        TableType::Base
    }

    async fn scan(
        &self,
        state: &dyn Session,
        projection: Option<&Vec<usize>>,
        filters: &[Expr],
        limit: Option<usize>,
    ) -> datafusion::error::Result<Arc<dyn ExecutionPlan>> {
        self.inner.scan(state, projection, filters, limit).await
    }
}
