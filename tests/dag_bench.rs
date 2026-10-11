//! Facts from the TABLE models of dbt DAGs, bounding the VIEW models of the
//! same DAGs.
//!
//! Each project of a [dag-bench](https://github.com/) checkout (`projects/*`,
//! with a compiled `target/manifest.json` and a built DuckDB warehouse) is a
//! DAG of models over source tables, each materialized as a TABLE or a VIEW.
//! Every TABLE model's query runs, profiled, in the warehouse (read only, so
//! nothing is rebuilt), with one thread and with four; every fact and bound
//! read off the profiles is checked against its true count. Each VIEW model's
//! query is then analyzed by DataFusion, over empty tables of the same schema
//! with the DAG's views defined as views (so that a view reads, as DuckDB's
//! plans do, its definition over the stored tables), and bounded without
//! facts, with the TABLE models' facts as selectivities only (`Ratios`), and
//! with their row counts and bounds too (`Pinned`). Each must hold the view's
//! true row count, and no fact may be rejected.
//!
//! `CARDINAL_DAG_BENCH` is the checkout (default `~/dag-bench`),
//! `CARDINAL_DAG_ONLY` a substring of the projects to run, and
//! `CARDINAL_DAG_SHOW` (any value) prints every fact and bound, and
//! `CARDINAL_DAG_FORMULAS` each view's selectivity formula, and the formula
//! with the facts put in. Needs the `duckdb`
//! CLI; skipped without it or the checkout. `CARDINAL_LIVE_TIMEOUT` sets each
//! DuckDB call's time limit in seconds.
//!
//! ```sh
//! CARDINAL_LIVE_TIMEOUT=120 cargo test --release --test dag_bench -- --nocapture
//! ```

mod live;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use cardinal::facts::{Fact, FactKind, FactSet, Ratio};
use cardinal::observed::{Catalog, from_duckdb};
use cardinal::{FactMode, Options};
use datafusion::arrow::datatypes::{DataType, Field, Schema, TimeUnit};
use datafusion::datasource::MemTable;
use datafusion::logical_expr::{ColumnarValue, ScalarFunctionArgs, ScalarUDF, ScalarUDFImpl, Signature, Volatility};
use datafusion::prelude::{SessionConfig, SessionContext};
use live::{TIMED_OUT, duckdb_available, profile, run, values};
use serde_json::Value;

/// A model of the DAG.
struct Model {
    name: String,
    table: bool,
    sql: String,
    depends: Vec<String>,
}

/// A project: its database, sources, and models in dependency order.
struct Dag {
    name: String,
    db: PathBuf,
    database: String,
    models: Vec<Model>,
}

fn dags(root: &Path) -> Vec<Dag> {
    let mut out = vec![];
    let mut dirs: Vec<PathBuf> = std::fs::read_dir(root.join("projects")).into_iter().flatten().flatten().map(|e| e.path()).collect();
    dirs.sort();
    for dir in dirs {
        let Ok(text) = std::fs::read_to_string(dir.join("target/manifest.json")) else { continue };
        let m: Value = serde_json::from_str(&text).unwrap();
        let mut models: HashMap<String, Model> = HashMap::new();
        let mut database = None;
        for (id, n) in m["nodes"].as_object().unwrap() {
            if n["resource_type"] != "model" {
                continue;
            }
            database.get_or_insert_with(|| n["database"].as_str().unwrap_or_default().to_string());
            let depends = n["depends_on"]["nodes"].as_array().unwrap().iter().filter_map(|d| d.as_str().map(String::from)).collect();
            models.insert(
                id.clone(),
                Model {
                    name: n["alias"].as_str().or(n["name"].as_str()).unwrap().to_string(),
                    table: n["config"]["materialized"] == "table",
                    sql: n["compiled_code"].as_str().unwrap_or_default().to_string(),
                    depends,
                },
            );
        }
        let Some(database) = database else { continue };
        // Dependency order.
        let mut order = vec![];
        let mut done = BTreeSet::new();
        fn visit(id: &str, models: &HashMap<String, Model>, done: &mut BTreeSet<String>, order: &mut Vec<String>) {
            if !done.insert(id.to_string()) {
                return;
            }
            if let Some(m) = models.get(id) {
                for d in &m.depends {
                    visit(d, models, done, order);
                }
                order.push(id.to_string());
            }
        }
        let mut ids: Vec<&String> = models.keys().collect();
        ids.sort();
        for id in ids {
            visit(id, &models, &mut done, &mut order);
        }
        let models: Vec<Model> = order.into_iter().map(|id| models.remove(&id).unwrap()).collect();
        // The built warehouse: whichever copy has the most of the models.
        let names: BTreeSet<String> = models.iter().map(|m| m.name.clone()).collect();
        let candidates = [dir.join(format!("{database}.duckdb")), dir.join("data").join(format!("{database}.duckdb"))];
        let best = candidates
            .into_iter()
            .filter(|c| c.exists())
            .map(|c| (relations(&c).intersection(&names).count(), c))
            .max_by_key(|(n, _)| *n);
        let Some((_, db)) = best else { continue };
        out.push(Dag { name: dir.file_name().unwrap().to_string_lossy().into_owned(), db, database, models });
    }
    out
}

fn json(db: &PathBuf, sql: &str) -> Value {
    let out = run(db, sql, &["-readonly", "-json"]).unwrap_or_default();
    serde_json::from_str(out.trim()).unwrap_or(Value::Array(vec![]))
}

/// The relations (tables and views) of `db`'s main schema.
fn relations(db: &PathBuf) -> BTreeSet<String> {
    json(db, "SELECT table_name FROM information_schema.tables WHERE table_schema = 'main';")
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|r| r["table_name"].as_str().map(String::from))
        .collect()
}

fn arrow_type(t: &str) -> DataType {
    if let Some(ps) = t.strip_prefix("DECIMAL(").and_then(|r| r.strip_suffix(')')) {
        let (p, s) = ps.split_once(',').unwrap();
        return DataType::Decimal128(p.trim().parse().unwrap(), s.trim().parse().unwrap());
    }
    match t {
        "BOOLEAN" => DataType::Boolean,
        "TINYINT" => DataType::Int8,
        "SMALLINT" => DataType::Int16,
        "INTEGER" => DataType::Int32,
        "BIGINT" => DataType::Int64,
        "HUGEINT" => DataType::Decimal128(38, 0),
        "UTINYINT" => DataType::UInt8,
        "USMALLINT" => DataType::UInt16,
        "UINTEGER" => DataType::UInt32,
        "UBIGINT" => DataType::UInt64,
        "FLOAT" => DataType::Float32,
        "DOUBLE" => DataType::Float64,
        "DATE" => DataType::Date32,
        "TIMESTAMP" => DataType::Timestamp(TimeUnit::Microsecond, None),
        "TIMESTAMP WITH TIME ZONE" => DataType::Timestamp(TimeUnit::Microsecond, Some("UTC".into())),
        "TIME" => DataType::Time64(TimeUnit::Microsecond),
        "INTERVAL" => DataType::Interval(datafusion::arrow::datatypes::IntervalUnit::MonthDayNano),
        _ => DataType::Utf8,
    }
}

/// DuckDB's `date_diff(part, start, end)`, the whole parts between two
/// times, for DataFusion to plan queries that call it. Never evaluated: the
/// tables are empty.
#[derive(Debug, PartialEq, Eq, Hash)]
struct DateDiff {
    signature: Signature,
}

impl ScalarUDFImpl for DateDiff {
    fn name(&self) -> &str {
        "date_diff"
    }
    fn signature(&self) -> &Signature {
        &self.signature
    }
    fn return_type(&self, _: &[DataType]) -> datafusion::error::Result<DataType> {
        Ok(DataType::Int64)
    }
    fn invoke_with_args(&self, _: ScalarFunctionArgs) -> datafusion::error::Result<ColumnarValue> {
        datafusion::common::not_impl_err!("date_diff is only planned")
    }
}

/// DataFusion over `dag`'s schema: its stored tables empty, its views
/// defined as views, under the warehouse's catalog and schema. The views
/// DataFusion cannot define are left out, by name.
async fn context(dag: &Dag) -> (SessionContext, Vec<String>) {
    let config = SessionConfig::new().with_default_catalog_and_schema(dag.database.as_str(), "main");
    let ctx = SessionContext::new_with_config(config);
    ctx.register_udf(ScalarUDF::from(DateDiff { signature: Signature::any(3, Volatility::Immutable) }));
    let rows = json(
        &dag.db,
        "SELECT c.table_name, c.column_name, c.data_type FROM information_schema.columns c \
         JOIN information_schema.tables t USING (table_schema, table_name) \
         WHERE c.table_schema = 'main' AND t.table_type = 'BASE TABLE' ORDER BY c.table_name, c.ordinal_position;",
    );
    let mut tables: BTreeMap<String, Vec<Field>> = BTreeMap::new();
    for c in rows.as_array().unwrap() {
        let field = Field::new(c["column_name"].as_str().unwrap(), arrow_type(c["data_type"].as_str().unwrap()), true);
        tables.entry(c["table_name"].as_str().unwrap().to_string()).or_default().push(field);
    }
    for (name, fields) in tables {
        let schema = Arc::new(Schema::new(fields));
        ctx.register_table(name.as_str(), Arc::new(MemTable::try_new(schema, vec![vec![]]).unwrap())).unwrap();
    }
    let mut undefined = vec![];
    for m in dag.models.iter().filter(|m| !m.table) {
        let sql = format!("CREATE VIEW \"{}\" AS {}", m.name, m.sql);
        if let Err(e) = async { ctx.sql(&sql).await?.collect().await }.await {
            undefined.push(format!("{}: {}", m.name, e.to_string().lines().next().unwrap_or_default()));
        }
    }
    (ctx, undefined)
}

fn agrees(kind: &FactKind, value: Ratio, n: u64, of: Option<u64>) -> bool {
    match (kind, of) {
        (FactKind::Unique { .. }, Some(of)) => n == of,
        (_, Some(of)) => Ratio::new(n, of) == Some(value),
        (_, None) => value.as_int() == Some(n),
    }
}

/// Every fact and bound of `facts` against its count: the failures, and how
/// many were counted true, could not be counted, and timed out.
fn check(db: &PathBuf, catalog: &Catalog, facts: &FactSet) -> (Vec<String>, usize, usize, usize) {
    let mut checks: Vec<(&Fact, bool, usize, Option<usize>)> = vec![];
    let mut sql: Vec<String> = vec![];
    let mut index: HashMap<String, usize> = HashMap::new();
    let mut at = |q: String, sql: &mut Vec<String>| {
        *index.entry(q.clone()).or_insert_with(|| {
            sql.push(q);
            sql.len() - 1
        })
    };
    let mut uncountable = 0;
    for (f, bound) in facts.iter().map(|f| (f, false)).chain(facts.bounds().map(|f| (f, true))) {
        match f.kind.count_sql(catalog, facts) {
            Some(c) => {
                let v = at(c.value, &mut sql);
                let of = c.of.map(|q| at(q, &mut sql));
                checks.push((f, bound, v, of));
            }
            None => uncountable += 1,
        }
    }
    let counted = values(db, &sql);
    let (mut failures, mut ok, mut slow) = (vec![], 0, 0);
    for (f, bound, v, of) in checks {
        let (n, of) = match (&counted[v], of.map(|o| &counted[o])) {
            (Ok(n), None) => (*n, None),
            (Ok(n), Some(Ok(o))) => (*n, Some(*o)),
            (Err(e), _) | (_, Some(Err(e))) if e == TIMED_OUT => {
                slow += 1;
                continue;
            }
            (Err(e), _) | (_, Some(Err(e))) => {
                failures.push(format!("{}: does not count: {}", f.kind, e.lines().next().unwrap_or_default()));
                continue;
            }
        };
        let right = match bound {
            true => f.value.as_int().is_some_and(|b| b >= n),
            false => agrees(&f.kind, f.value, n, of),
        };
        if right {
            ok += 1;
        } else {
            let sign = if bound { "<=" } else { "=" };
            failures.push(format!("{} {sign} {} but is {n}{}", f.kind, f.value, of.map(|o| format!("/{o}")).unwrap_or_default()));
        }
    }
    (failures, ok, uncountable, slow)
}

fn range(r: (u64, Option<u64>)) -> String {
    match r.1 {
        Some(hi) => format!("{}..={hi}", r.0),
        None => format!("{}..", r.0),
    }
}

fn holds(r: (u64, Option<u64>), truth: u64) -> bool {
    r.0 <= truth && r.1.is_none_or(|hi| truth <= hi)
}

/// What an unmatched selectivity needed, by kind.
fn miss(why: &str) -> &'static str {
    let Some(fact) = why.strip_prefix("no fact for ") else {
        return if why.starts_with("unresolved") { "terms that did not resolve" } else { "other" };
    };
    let over = fact.rsplit_once(" | ").map(|(_, o)| o).unwrap_or(fact);
    let joined = over.contains(" × ") || over.contains("join");
    match (fact.split('(').next().unwrap_or(""), joined) {
        ("s", false) => "a filter's share of one table",
        ("s", true) => "a share over joined rows",
        ("m", _) => "a semi or anti join's match share",
        ("ndv", false) => "distinct values of one table",
        ("ndv", true) => "distinct values over joined rows",
        _ => "a row count",
    }
}

#[derive(Default)]
struct Summary {
    tables: usize,
    profiled: usize,
    facts: usize,
    bounds: usize,
    counted: usize,
    views: usize,
    bounded: usize,
    required: usize,
    matched: usize,
    capped: usize,
    tighter: usize,
    exact: usize,
}

#[tokio::test]
async fn table_facts_bound_views() {
    let root = std::env::var("CARDINAL_DAG_BENCH")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from(std::env::var("HOME").unwrap_or_default()).join("dag-bench"));
    if !duckdb_available() || !root.join("projects").exists() {
        eprintln!("skipped: no duckdb CLI or no dag-bench at {}", root.display());
        return;
    }
    let only = std::env::var("CARDINAL_DAG_ONLY").ok();
    let mut failures = vec![];
    let mut summaries: Vec<(String, Summary)> = vec![];
    for dag in dags(&root).into_iter().filter(|d| only.as_ref().is_none_or(|o| d.name.contains(o.as_str()))) {
        let mut s = Summary { tables: dag.models.iter().filter(|m| m.table).count(), views: dag.models.iter().filter(|m| !m.table).count(), ..Default::default() };
        if s.views == 0 {
            println!("==== {}: {} TABLE models and no VIEW models: nothing to match\n", dag.name, s.tables);
            summaries.push((dag.name.clone(), s));
            continue;
        }
        let (ctx, undefined) = context(&dag).await;
        let catalog = Catalog::from_context(&ctx).await.unwrap();
        println!("==== {} ({}): {} TABLE and {} VIEW models", dag.name, dag.db.display(), s.tables, s.views);

        // The TABLE models' facts.
        let mut facts = FactSet::default();
        for m in dag.models.iter().filter(|m| m.table) {
            let mut ok = false;
            for threads in [1, 4] {
                let label = format!("{}/{}/t{threads}", dag.name, m.name);
                match profile(&dag.db, &m.sql, threads).and_then(|j| from_duckdb(&catalog, &label, &j).map_err(|e| e.to_string())) {
                    Ok(p) => {
                        facts.observe(&p);
                        ok = true;
                    }
                    Err(e) if threads == 1 => println!("  table {} not profiled: {}", m.name, e.lines().next().unwrap_or_default()),
                    Err(_) => {}
                }
            }
            s.profiled += usize::from(ok);
        }
        facts.close();
        for c in &facts.conflicts {
            failures.push(format!("{}: conflict: {} = {} vs {}", dag.name, c.kind, c.values.0, c.values.1));
        }
        if std::env::var("CARDINAL_DAG_SHOW").is_ok() {
            let from = |f: &Fact| {
                let mut q: Vec<String> = f
                    .origins
                    .iter()
                    .map(|o| match o {
                        cardinal::facts::Origin::Observed { query, .. } => query.split('/').nth(1).unwrap_or(query).to_string(),
                        cardinal::facts::Origin::Derived { rule } => format!("derived ({rule})"),
                    })
                    .collect();
                q.sort();
                q.dedup();
                q.join(", ")
            };
            for f in facts.iter() {
                println!("  fact  {f}    [{}]", from(f));
            }
            for b in facts.bounds() {
                println!("  bound {} <= {}    [{}]", b.kind, b.value, from(b));
            }
        }
        let (wrong, counted, uncountable, slow) = check(&dag.db, &catalog, &facts);
        failures.extend(wrong.into_iter().map(|w| format!("{}: {w}", dag.name)));
        (s.facts, s.bounds, s.counted) = (facts.len(), facts.bounds().count(), counted);
        println!(
            "  {} of {} tables profiled: {} facts and {} bounds; {counted} counted true, {uncountable} not countable, {slow} too slow to count",
            s.profiled,
            s.tables,
            s.facts,
            s.bounds
        );

        // Each VIEW model, bounded with them.
        println!("  {:<34} {:>10} {:>8} {:>6}  {:<16} {:<16} {:<16}", "view", "rows", "matched", "capped", "no facts", "ratios", "pinned");
        let mut misses: BTreeMap<&str, usize> = BTreeMap::new();
        let mut skipped = vec![];
        for m in dag.models.iter().filter(|m| !m.table) {
            let truth = match profile(&dag.db, &m.sql, 1).and_then(|j| from_duckdb(&catalog, &m.name, &j).map_err(|e| e.to_string())) {
                Ok(p) => p.nodes[p.root].rows,
                Err(e) => {
                    skipped.push(format!("{}: not profiled: {}", m.name, e.lines().next().unwrap_or_default()));
                    continue;
                }
            };
            let options = Options { selectivity: true, ..Default::default() };
            let a = match cardinal::analyze_sql_with(&ctx, &m.sql, options).await {
                Ok(a) if a.selectivity.is_some() => a,
                Ok(_) => {
                    skipped.push(format!("{}: no selectivity formula", m.name));
                    continue;
                }
                Err(e) => {
                    skipped.push(format!("{}: not analyzed: {}", m.name, e.to_string().lines().next().unwrap_or_default()));
                    continue;
                }
            };
            let (Ok(none), Ok(ratios), Ok(pinned)) = (
                a.with_facts(&FactSet::default(), FactMode::Pinned),
                a.with_facts(&facts, FactMode::Ratios),
                a.with_facts(&facts, FactMode::Pinned),
            ) else {
                skipped.push(format!("{}: facts not applied", m.name));
                continue;
            };
            let (Ok(r0), Ok(r1), Ok(r2)) = (none.range(), ratios.range(), pinned.range()) else {
                skipped.push(format!("{}: no range proven", m.name));
                continue;
            };
            if std::env::var("CARDINAL_DAG_FORMULAS").is_ok() {
                println!("  ---- {} ({truth} rows)", m.name);
                for line in a.selectivity.as_ref().unwrap().to_string().lines() {
                    println!("    {line}");
                }
                println!("    ratios: X = {}", ratios.output);
                println!("    pinned: X = {}", pinned.output);
            }
            s.bounded += 1;
            let required = &a.selectivity.as_ref().unwrap().required;
            let got = required.iter().filter(|r| ratios.matched.iter().any(|x| x.name == r.name)).count();
            s.required += required.len();
            s.matched += got;
            s.capped += pinned.capped.len();
            s.tighter += usize::from(r2.1.is_some_and(|hi| r0.1.is_none_or(|h0| hi < h0)));
            s.exact += usize::from(r2.1 == Some(truth) && r0.1 != Some(truth));
            for (_, why) in &ratios.unmatched {
                *misses.entry(miss(why)).or_default() += 1;
            }
            for (mode, i) in [("ratios", &ratios), ("pinned", &pinned)] {
                if !i.rejected.is_empty() {
                    failures.push(format!("{}/{} {mode}: rejected {:?}", dag.name, m.name, i.rejected));
                }
            }
            for (mode, r) in [("no facts", r0), ("ratios", r1), ("pinned", r2)] {
                if !holds(r, truth) {
                    failures.push(format!("{}/{} {mode}: {} does not hold {truth}", dag.name, m.name, range(r)));
                }
            }
            println!(
                "  {:<34} {truth:>10} {:>8} {:>6}  {:<16} {:<16} {:<16}",
                m.name,
                format!("{got}/{}", required.len()),
                pinned.capped.len(),
                range(r0),
                range(r1),
                range(r2)
            );
        }
        for u in &undefined {
            println!("  view not defined in DataFusion: {u}");
        }
        for k in &skipped {
            println!("  skipped {k}");
        }
        if !misses.is_empty() {
            let mut misses: Vec<(&str, usize)> = misses.into_iter().collect();
            misses.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
            let text: Vec<String> = misses.iter().map(|(w, n)| format!("{n} {w}")).collect();
            println!("  unmatched: {}", text.join("; "));
        }
        println!();
        summaries.push((dag.name.clone(), s));
    }

    println!("{:<15} {:>6} {:>6} {:>12} {:>7} {:>7} {:>9} {:>7} {:>8} {:>6}", "dag", "tables", "views", "facts/bounds", "checked", "bounded", "matched", "capped", "tighter", "exact");
    for (name, s) in &summaries {
        println!(
            "{name:<15} {:>6} {:>6} {:>12} {:>7} {:>7} {:>9} {:>7} {:>8} {:>6}",
            format!("{}/{}", s.profiled, s.tables),
            s.views,
            format!("{}/{}", s.facts, s.bounds),
            s.counted,
            s.bounded,
            format!("{}/{}", s.matched, s.required),
            s.capped,
            s.tighter,
            s.exact
        );
    }
    assert!(failures.is_empty(), "{} failures:\n{}", failures.len(), failures.join("\n"));
}
