//! A benchmark: a prebaked directory `data/<bench>/`, loaded.
//!
//! | file                         | contents                                          |
//! |------------------------------|---------------------------------------------------|
//! | `schema.sql`                 | `CREATE TABLE`s with primary keys                 |
//! | `foreign_keys.json`          | foreign keys that hold on the data                |
//! | `queries/<q>.sql`            | the text run                                      |
//! | `queries.json`               | optional: each query's template, set and instance |
//! | `profiles/<engine>/<q>.json` | `EXPLAIN ANALYZE` profiles                        |
//! | `truth.json`                 | each query's output rows                          |
//! | `operator_truth.json`        | each operator's rows, by operator id              |
//! | `cardinalities.json`         | every table's row count                           |
//! | `manifest.json`              | provenance, `q_ref`, `q_target` and exclusions    |

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::{Context, Result, anyhow, bail};
use cardinal::observed::{Catalog, ObservedPlan, from_duckdb, from_postgres, from_snowflake};
use cardinal::{Analysis, Builder, ForeignKey, Options};
use datafusion::prelude::SessionContext;
use serde::{Deserialize, Serialize};
use serde_json::Value;

/// Where prebaked benchmarks live by default.
pub fn default_data() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("data")
}

/// One query of a benchmark.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Query {
    /// Its path under `queries/`, without `.sql`.
    pub name: String,
    pub sql: String,
    /// What it was instantiated from: itself, but for DSB's and JOB's.
    pub template: String,
    /// DSB's query set (SPJ, aggregate, multi-block).
    pub set: Option<String>,
    /// DSB's instance of its template, from 1.
    pub instance: u32,
}

/// What `queries.json` may say of a query.
#[derive(Debug, Clone, Default, Deserialize)]
struct QueryMeta {
    template: Option<String>,
    set: Option<String>,
    instance: Option<u32>,
}

/// One operator's true rows, as `operator_truth.json` stores them.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OperatorTruth {
    pub var: String,
    pub operator: String,
    /// `None` where validation left it uncounted.
    pub rows: Option<u64>,
}

/// A loaded benchmark. Profiles are read once, and every analysis is made
/// against one context of empty tables with the schema's keys.
pub struct Benchmark {
    pub name: String,
    pub dir: PathBuf,
    pub schema: String,
    pub foreign_keys: Vec<ForeignKey>,
    /// Every query, by name.
    pub queries: BTreeMap<String, Query>,
    /// Each engine's profiles that read, by query.
    pub profiles: BTreeMap<String, BTreeMap<String, ObservedPlan>>,
    /// Each engine's profiles that did not read, and why.
    pub profile_errors: BTreeMap<String, BTreeMap<String, String>>,
    pub truth: BTreeMap<String, u64>,
    pub operator_truth: BTreeMap<String, Vec<OperatorTruth>>,
    pub cardinalities: BTreeMap<String, u64>,
    pub manifest: Value,
    /// The queries whose plans may be references, and those that may be
    /// targets (a subset): from the manifest, once `operator-truth` ran.
    pub q_ref: Vec<String>,
    pub q_target: Vec<String>,
    pub ctx: SessionContext,
    pub catalog: Arc<Catalog>,
}

impl Benchmark {
    /// `data/<name>`, read.
    pub async fn load(data: &Path, name: &str) -> Result<Benchmark> {
        let dir = data.join(name);
        if !dir.is_dir() {
            bail!("no benchmark at {}: run prepare/{name}.sh", dir.display());
        }
        let schema = read(&dir.join("schema.sql"))?;
        let ctx = context(&schema).await?;
        let catalog = Arc::new(Catalog::from_context(&ctx).await?);
        let foreign_keys = read_json::<Vec<ForeignKeyJson>>(&dir.join("foreign_keys.json"))?.into_iter().map(Into::into).collect();
        let meta: BTreeMap<String, QueryMeta> = read_json_or_default(&dir.join("queries.json"))?;
        let mut queries = BTreeMap::new();
        for (name, path) in files(&dir.join("queries"), "sql")? {
            let m = meta.get(&name).cloned().unwrap_or_default();
            let sql = read(&path)?;
            let q = Query { template: m.template.unwrap_or_else(|| name.clone()), set: m.set, instance: m.instance.unwrap_or(1), sql, name: name.clone() };
            queries.insert(name, q);
        }
        let (mut profiles, mut profile_errors) = (BTreeMap::new(), BTreeMap::new());
        let engines = dir.join("profiles");
        if engines.is_dir() {
            for entry in std::fs::read_dir(&engines)? {
                let engine = entry?.file_name().to_string_lossy().into_owned();
                let (ok, err) = read_profiles(&catalog, &engines.join(&engine), &engine, &queries)?;
                profiles.insert(engine.clone(), ok);
                profile_errors.insert(engine, err);
            }
        }
        let manifest: Value = read_json_or_default(&dir.join("manifest.json"))?;
        let list = |k: &str| -> Vec<String> {
            manifest[k].as_array().map(|a| a.iter().filter_map(|v| v.as_str().map(String::from)).collect()).unwrap_or_default()
        };
        let (q_ref, q_target) = (list("q_ref"), list("q_target"));
        Ok(Benchmark {
            name: name.to_string(),
            schema,
            foreign_keys,
            queries,
            profiles,
            profile_errors,
            truth: read_json_or_default(&dir.join("truth.json"))?,
            operator_truth: read_json_or_default(&dir.join("operator_truth.json"))?,
            cardinalities: read_json_or_default(&dir.join("cardinalities.json"))?,
            manifest,
            q_ref,
            q_target,
            ctx,
            catalog,
            dir,
        })
    }

    /// Fails unless `operator-truth` has run: the truth and the query sets
    /// are what every eval reads.
    pub fn require_prepared(&self) -> Result<()> {
        if self.q_target.is_empty() || self.truth.is_empty() {
            bail!("{}: no q_target or truth; run operator-truth --bench {}", self.name, self.name);
        }
        Ok(())
    }

    /// The analysis options every eval uses: the benchmark's foreign keys.
    pub fn options(&self) -> Options {
        Options { foreign_keys: self.foreign_keys.clone(), ..Default::default() }
    }

    /// Query `q` as DataFusion plans it, against the benchmark's tables.
    pub async fn builder(&self, q: &str) -> Result<Builder<'static>> {
        let query = self.queries.get(q).ok_or_else(|| anyhow!("{}: no query {q}", self.name))?;
        Ok(Analysis::sql(&self.ctx, &query.sql).await?.options(self.options()))
    }

    /// Engine `engine`'s profile of `q`.
    pub fn profile(&self, engine: &str, q: &str) -> Option<&ObservedPlan> {
        self.profiles.get(engine)?.get(q)
    }
}

/// A context with the tables of `ddl`, empty: `CREATE TABLE`s, with their
/// primary keys.
pub async fn context(ddl: &str) -> Result<SessionContext> {
    let ctx = SessionContext::new();
    for statement in strip_comments(ddl).split(';').map(str::trim).filter(|s| !s.is_empty()) {
        ctx.sql(statement).await.with_context(|| statement.to_string())?;
    }
    Ok(ctx)
}

fn strip_comments(sql: &str) -> String {
    sql.lines().filter(|l| !l.trim_start().starts_with("--")).collect::<Vec<_>>().join("\n")
}

/// A profile's true root rows, if it ran and counted its root.
pub fn root_rows(p: &ObservedPlan) -> Option<u64> {
    let root = &p.nodes[p.root];
    (p.counted && root.counted).then_some(root.rows)
}

#[derive(Deserialize)]
struct ForeignKeyJson {
    table: String,
    columns: Vec<String>,
    references: String,
    referenced: Vec<String>,
}

impl From<ForeignKeyJson> for ForeignKey {
    fn from(f: ForeignKeyJson) -> ForeignKey {
        ForeignKey { table: f.table, columns: f.columns, references: f.references, referenced: f.referenced }
    }
}

/// The profiles under `dir` of `engine`, by query, read against `catalog`
/// with their query's text; and those that did not read, with why.
#[allow(clippy::type_complexity)]
fn read_profiles(
    catalog: &Catalog,
    dir: &Path,
    engine: &str,
    queries: &BTreeMap<String, Query>,
) -> Result<(BTreeMap<String, ObservedPlan>, BTreeMap<String, String>)> {
    let read_as = match engine {
        "duckdb" => from_duckdb,
        "postgres" => from_postgres,
        "snowflake" => from_snowflake,
        e => bail!("unknown engine {e}"),
    };
    let (mut ok, mut err) = (BTreeMap::new(), BTreeMap::new());
    for (name, path) in files(dir, "json")? {
        let sql = queries.get(&name).map(|q| q.sql.as_str());
        match read_as(catalog, &name, &read(&path)?, sql) {
            Ok(p) => {
                ok.insert(name, p);
            }
            Err(e) => {
                err.insert(name, e.to_string());
            }
        }
    }
    Ok((ok, err))
}

/// Every file with extension `ext` under `dir`, recursively, by its path
/// relative to `dir` without the extension, in name order.
pub fn files(dir: &Path, ext: &str) -> Result<BTreeMap<String, PathBuf>> {
    let mut out = BTreeMap::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        for entry in std::fs::read_dir(&d).with_context(|| d.display().to_string())? {
            let path = entry?.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|e| e == ext) {
                let rel = path.strip_prefix(dir)?.with_extension("");
                out.insert(rel.to_string_lossy().replace('\\', "/"), path);
            }
        }
    }
    Ok(out)
}

pub fn read(path: &Path) -> Result<String> {
    std::fs::read_to_string(path).with_context(|| path.display().to_string())
}

pub fn read_json<T: serde::de::DeserializeOwned>(path: &Path) -> Result<T> {
    serde_json::from_str(&read(path)?).with_context(|| path.display().to_string())
}

/// `path` read, or the default if there is no such file.
pub fn read_json_or_default<T: serde::de::DeserializeOwned + Default>(path: &Path) -> Result<T> {
    if path.exists() { read_json(path) } else { Ok(T::default()) }
}
