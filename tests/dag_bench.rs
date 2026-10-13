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
//! with the facts put in. `CARDINAL_DAG_PLANNER` is how views are planned:
//! `datafusion` (the default), `duckdb` (DuckDB's `EXPLAIN (FORMAT JSON)` of
//! the view's query, analyzed as DuckDB planned it), or `both`. Every
//! model's query is read with the VIEW models it reads inlined.
//! `CARDINAL_DAG_DUMP` is a JSON file to write each project's models, facts
//! and results to (`{dag}` in it is the project). Needs the `duckdb`
//! CLI; skipped without it or the checkout. `CARDINAL_LIVE_TIMEOUT` sets each
//! DuckDB call's time limit in seconds.
//!
//! With `CARDINAL_DAG_ENGINE=postgres`, PostgreSQL is the engine: for a
//! checkout compiled and built with dbt's `postgres` target, whose manifest
//! names each project's database and schema. `psql` connects to that
//! database as its environment says (`PGHOST`, `PGUSER`, ...); the models run
//! and are planned there (`CARDINAL_DAG_PLANNER=engine`, for PostgreSQL's
//! plan of each view), each TABLE model profiled as PostgreSQL plans it,
//! with hash joins only, and with merge joins. Where the schema is not built
//! and `CARDINAL_DAG_MIRROR` is set, the tables of the project's DuckDB
//! warehouse (`data/warehouse.duckdb`) are copied into it first: with
//! `CARDINAL_DAG_MIRROR_ROWS`, at most that many rows of each, for a
//! warehouse PostgreSQL is quick over.
//!
//! ```sh
//! CARDINAL_LIVE_TIMEOUT=120 cargo test --release --test dag_bench -- --nocapture
//! ```

mod live;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use cardinal::facts::{Fact, FactKind, FactSet, Ratio};
use cardinal::observed::Catalog;
use cardinal::{FactMode, ForeignKey, Options};
use datafusion::arrow::datatypes::{DataType, Field, Schema, TimeUnit};
use datafusion::common::{Constraint, Constraints};
use datafusion::datasource::MemTable;
use datafusion::logical_expr::{ColumnarValue, ScalarFunctionArgs, ScalarUDF, ScalarUDFImpl, Signature, Volatility};
use datafusion::prelude::{SessionConfig, SessionContext};
use live::{Engine, TIMED_OUT, duckdb_available};
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
    /// Where its models run: the built warehouse.
    engine: Engine,
    database: String,
    /// The schema its relations are in.
    schema: String,
    models: Vec<Model>,
    /// dbt `relationships` tests, `(column, field)` of a model referencing
    /// another, each model as the source tables it reads.
    relationships: Vec<(Vec<String>, String, Vec<String>, String)>,
}

/// The projects under `root` whose name contains `only`, if given.
fn dags(root: &Path, postgres: bool, only: Option<&str>) -> Vec<Dag> {
    let mut out = vec![];
    let mut dirs: Vec<PathBuf> = std::fs::read_dir(root.join("projects")).into_iter().flatten().flatten().map(|e| e.path()).collect();
    dirs.retain(|d| only.is_none_or(|o| d.file_name().is_some_and(|n| n.to_string_lossy().contains(o))));
    dirs.sort();
    for dir in dirs {
        let Ok(text) = std::fs::read_to_string(dir.join("target/manifest.json")) else { continue };
        let m: Value = serde_json::from_str(&text).unwrap();
        let mut models: HashMap<String, Model> = HashMap::new();
        let mut database = None;
        let mut schema = None;
        for (id, n) in m["nodes"].as_object().unwrap() {
            if n["resource_type"] != "model" {
                continue;
            }
            database.get_or_insert_with(|| n["database"].as_str().unwrap_or_default().to_string());
            schema.get_or_insert_with(|| n["schema"].as_str().unwrap_or("main").to_string());
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
        // The source tables each model reads directly.
        let sources: HashMap<String, Vec<String>> = models
            .values()
            .map(|md| {
                let tables = md
                    .depends
                    .iter()
                    .filter_map(|d| m["sources"][d.as_str()]["identifier"].as_str().or(m["sources"][d.as_str()]["name"].as_str()))
                    .map(String::from)
                    .collect();
                (md.name.clone(), tables)
            })
            .collect();
        let mut relationships = vec![];
        for n in m["nodes"].as_object().unwrap().values() {
            let t = &n["test_metadata"];
            if n["resource_type"] != "test" || t["name"] != "relationships" {
                continue;
            }
            let from = n["attached_node"].as_str().and_then(|a| models.get(a)).map(|md| md.name.clone());
            let to = t["kwargs"]["to"].as_str().and_then(|r| r.strip_prefix("ref('")).and_then(|r| r.strip_suffix("')"));
            let (Some(from), Some(to), Some(column), Some(field)) = (from, to, n["column_name"].as_str(), t["kwargs"]["field"].as_str()) else {
                continue;
            };
            let tables = |model: &str| sources.get(model).cloned().unwrap_or_default();
            relationships.push((tables(&from), column.to_string(), tables(to), field.to_string()));
        }
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
        let name = dir.file_name().unwrap().to_string_lossy().into_owned();
        let names: BTreeSet<String> = models.iter().map(|m| m.name.clone()).collect();
        if postgres {
            // The schema dbt built; or, asked for, a copy of the DuckDB
            // warehouse's tables.
            let schema = schema.unwrap_or_else(|| "public".into());
            let engine = Engine::Postgres(format!("{database}/{schema}"));
            let warehouse = dir.join("data/warehouse.duckdb");
            let copy = relations(&engine, &schema).is_empty() && std::env::var("CARDINAL_DAG_MIRROR").is_ok() && warehouse.exists();
            let rows = std::env::var("CARDINAL_DAG_MIRROR_ROWS").ok().and_then(|n| n.parse().ok());
            if copy && let Err(e) = live::pg::mirror(&warehouse, &database, &schema, rows) {
                eprintln!("{name}: not copied into PostgreSQL: {e}");
            }
            if relations(&engine, &schema).is_empty() {
                eprintln!("{name}: no relations in PostgreSQL's {database}.{schema}");
                continue;
            }
            out.push(Dag { name, engine, database, schema, models, relationships });
            continue;
        }
        // The built warehouse: whichever copy has the most of the models.
        let candidates = [dir.join(format!("{database}.duckdb")), dir.join("data").join(format!("{database}.duckdb"))];
        let best = candidates
            .into_iter()
            .filter(|c| c.exists())
            .map(|c| (relations(&Engine::DuckDb(c.clone()), "main").intersection(&names).count(), c))
            .max_by_key(|(n, _)| *n);
        let Some((_, db)) = best else { continue };
        out.push(Dag { name, engine: Engine::DuckDb(db), database, schema: "main".into(), models, relationships });
    }
    out
}

/// The relations (tables and views) of `schema`.
fn relations(engine: &Engine, schema: &str) -> BTreeSet<String> {
    engine
        .json(&format!("SELECT table_name FROM information_schema.tables WHERE table_schema = '{schema}'"))
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
    // PostgreSQL's names, as DuckDB's.
    let upper = t.to_uppercase();
    let t = match upper.as_str() {
        "CHARACTER VARYING" | "TEXT" | "CHARACTER" => "VARCHAR",
        "DOUBLE PRECISION" => "DOUBLE",
        "REAL" => "FLOAT",
        "TIMESTAMP WITHOUT TIME ZONE" => "TIMESTAMP",
        "TIME WITHOUT TIME ZONE" => "TIME",
        t => t,
    };
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

/// DataFusion over `dag`'s schema: its stored tables empty, with the
/// warehouse's primary keys, its views defined as views, under the
/// warehouse's catalog and schema. The views DataFusion cannot define are
/// left out, by name. Also the foreign keys the data satisfies: the dbt
/// `relationships` tests, between the source tables their models read, that
/// hold on the stored rows against a primary key.
async fn context(dag: &Dag) -> (SessionContext, Vec<String>, Vec<ForeignKey>) {
    let (engine, schema) = (&dag.engine, dag.schema.as_str());
    let postgres = matches!(engine, Engine::Postgres(_));
    let config = SessionConfig::new().with_default_catalog_and_schema(dag.database.as_str(), schema);
    let ctx = SessionContext::new_with_config(config);
    ctx.register_udf(ScalarUDF::from(DateDiff { signature: Signature::any(3, Volatility::Immutable) }));
    // A `numeric` column's type, with the precision and scale PostgreSQL
    // lists beside it.
    let data_type = match postgres {
        true => "CASE WHEN c.data_type = 'numeric' AND c.numeric_precision IS NOT NULL \
                 THEN 'DECIMAL(' || c.numeric_precision || ',' || c.numeric_scale || ')' ELSE c.data_type END",
        false => "c.data_type",
    };
    let rows = engine.json(&format!(
        "SELECT c.table_name, c.column_name, {data_type} AS data_type FROM information_schema.columns c \
         JOIN information_schema.tables t USING (table_schema, table_name) \
         WHERE c.table_schema = '{schema}' AND t.table_type = 'BASE TABLE' AND c.table_name NOT LIKE '\\_cardinal%' ESCAPE '\\' \
         ORDER BY c.table_name, c.ordinal_position"
    ));
    let mut tables: BTreeMap<String, Vec<Field>> = BTreeMap::new();
    for c in rows.as_array().unwrap() {
        let field = Field::new(c["column_name"].as_str().unwrap(), arrow_type(c["data_type"].as_str().unwrap()), true);
        tables.entry(c["table_name"].as_str().unwrap().to_string()).or_default().push(field);
    }
    let mut primary: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let keys = engine.json(&match postgres {
        true => format!(
            "SELECT t.relname AS table_name, json_agg(a.attname ORDER BY k.ord) AS constraint_column_names \
             FROM pg_constraint c JOIN pg_class t ON t.oid = c.conrelid JOIN pg_namespace n ON n.oid = t.relnamespace \
             CROSS JOIN LATERAL unnest(c.conkey) WITH ORDINALITY AS k(attnum, ord) \
             JOIN pg_attribute a ON a.attrelid = t.oid AND a.attnum = k.attnum \
             WHERE c.contype = 'p' AND n.nspname = '{schema}' GROUP BY t.relname"
        ),
        false => "SELECT table_name, constraint_column_names FROM duckdb_constraints() \
                  WHERE schema_name = 'main' AND constraint_type = 'PRIMARY KEY'"
            .to_string(),
    });
    for k in keys.as_array().unwrap() {
        let cols = k["constraint_column_names"].as_array().unwrap().iter().filter_map(|c| c.as_str().map(String::from)).collect();
        primary.insert(k["table_name"].as_str().unwrap().to_string(), cols);
    }
    for (name, fields) in &tables {
        let schema = Arc::new(Schema::new(fields.clone()));
        let mut table = MemTable::try_new(schema.clone(), vec![vec![]]).unwrap();
        if let Some(pk) = primary.get(name) {
            let ix = pk.iter().map(|c| schema.index_of(c).unwrap()).collect();
            table = table.with_constraints(Constraints::new_unverified(vec![Constraint::PrimaryKey(ix)]));
        }
        ctx.register_table(name.as_str(), Arc::new(table)).unwrap();
    }
    let mut undefined = vec![];
    for m in dag.models.iter().filter(|m| !m.table) {
        let sql = format!("CREATE VIEW \"{}\" AS {}", m.name, m.sql);
        if let Err(e) = async { ctx.sql(&sql).await?.collect().await }.await {
            undefined.push(format!("{}: {}", m.name, e.to_string().lines().next().unwrap_or_default()));
        }
    }
    let has = |t: &str, c: &str| tables.get(t).is_some_and(|fs| fs.iter().any(|f| f.name() == c));
    let mut foreign = vec![];
    for (froms, column, tos, field) in &dag.relationships {
        for from in froms.iter().filter(|t| has(t, column)) {
            for to in tos.iter().filter(|t| primary.get(*t).is_some_and(|pk| pk == &vec![field.clone()])) {
                let fk = ForeignKey::new(from, &[column], to, &[field]);
                if (from == to && column == field) || foreign.contains(&fk) {
                    continue;
                }
                // Never NULL, and always matched.
                let orphans = format!(
                    "SELECT count(*) AS n FROM \"{from}\" f WHERE f.\"{column}\" IS NULL \
                     OR NOT EXISTS (SELECT 1 FROM \"{to}\" t WHERE t.\"{field}\" = f.\"{column}\")"
                );
                if engine.json(&orphans)[0]["n"].as_u64() == Some(0) {
                    foreign.push(fk);
                }
            }
        }
    }
    (ctx, undefined, foreign)
}

/// What `kind` is, if it is simple to estimate from the stored tables: the
/// share of one table's rows a filter keeps (`filter`), of a join of two
/// tables (`join`), of one table's rows with a partner in another (`semi
/// join`), or a distinct count over one table (`ndv`). Each table may be
/// filtered on its own columns.
fn simple(kind: &FactKind) -> Option<&'static str> {
    use cardinal::facts::{Context, Term};
    let reads = |t: &Term| t.expr.column_refs().iter().filter_map(|c| c.relation.as_ref().map(|r| r.table().to_string())).collect::<BTreeSet<_>>();
    let table = |c: &Context| matches!(c, Context::Spj { tables, atoms, exists, .. } if tables.len() == 1 && atoms.is_empty() && exists.is_empty());
    match kind {
        FactKind::Selectivity { pred, over: Context::Spj { tables, atoms, preds, exists } }
            if tables.len() == 2 && atoms.is_empty() && exists.is_empty() && preds.iter().all(|p| reads(p).len() <= 1) =>
        {
            pred.iter().any(|p| reads(p).len() == 2).then_some("join")
        }
        FactKind::Selectivity { pred, over } if table(over) && pred.iter().all(|p| reads(p).len() <= 1) => Some("filter"),
        FactKind::Match { kept, other, .. } if table(kept) && table(other) => Some("semi join"),
        FactKind::Distinct { over, .. } if table(over) => Some("ndv"),
        _ => None,
    }
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
fn check(engine: &Engine, catalog: &Catalog, facts: &FactSet) -> (Vec<String>, usize, usize, usize) {
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
        match f.kind.count_sql_in(catalog, facts, engine.dialect()) {
            Some(c) => {
                let v = at(c.value, &mut sql);
                let of = c.of.map(|q| at(q, &mut sql));
                checks.push((f, bound, v, of));
            }
            None => uncountable += 1,
        }
    }
    let counted = engine.values(&sql);
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

/// `sql` with every VIEW model it reads replaced by its definition, itself
/// inlined, as a derived table under the name it was read by: the query an
/// engine plans. `None` if it does not parse.
fn inline(sql: &str, views: &HashMap<String, String>) -> Option<String> {
    use datafusion::sql::sqlparser::ast::{Ident, Query, Statement, TableAlias, TableFactor, VisitMut, VisitorMut};
    use datafusion::sql::sqlparser::dialect::DuckDbDialect;
    use datafusion::sql::sqlparser::parser::Parser;
    use std::ops::ControlFlow;

    fn query(sql: &str, views: &HashMap<String, String>, depth: usize) -> Option<Query> {
        let mut statements = Parser::parse_sql(&DuckDbDialect {}, sql).ok()?;
        let Some(Statement::Query(q)) = statements.pop() else { return None };
        let mut q = *q;
        struct Inline<'v> {
            views: &'v HashMap<String, String>,
            depth: usize,
            failed: bool,
        }
        impl VisitorMut for Inline<'_> {
            type Break = ();
            fn pre_visit_table_factor(&mut self, f: &mut TableFactor) -> ControlFlow<()> {
                let TableFactor::Table { name, alias, args: None, .. } = f else { return ControlFlow::Continue(()) };
                let Some(view) = name.0.last().map(|p| p.to_string().trim_matches('"').to_lowercase()) else {
                    return ControlFlow::Continue(());
                };
                let Some(definition) = self.views.get(&view) else { return ControlFlow::Continue(()) };
                // Views do not read themselves, but bound the recursion.
                match (self.depth < 32).then(|| query(definition, self.views, self.depth + 1)).flatten() {
                    Some(sub) => {
                        let alias = alias.clone().unwrap_or(TableAlias { explicit: true, name: Ident::new(view), columns: vec![], at: None });
                        *f = TableFactor::Derived { lateral: false, subquery: Box::new(sub), alias: Some(alias), sample: None };
                    }
                    None => self.failed = true,
                }
                ControlFlow::Continue(())
            }
        }
        let mut v = Inline { views, depth, failed: false };
        let _ = q.visit(&mut v);
        (!v.failed).then_some(q)
    }
    query(sql.trim().trim_end_matches(';'), views, 0).map(|q| q.to_string())
}

/// Writes `dag`'s models and dependencies, its TABLE models' facts and
/// bounds (with the models each was read from), and each view's results, by
/// planner, as JSON to `path` (`{dag}` in it is the project's name).
fn dump(
    path: &str,
    dag: &Dag,
    facts: &FactSet,
    table_rows: &HashMap<String, u64>,
    views: &BTreeMap<String, serde_json::Map<String, Value>>,
) {
    use serde_json::json;
    let name_of = |id: &str| id.rsplit('.').next().unwrap_or(id).to_string();
    let origins = |f: &Fact| -> (Vec<String>, Vec<String>) {
        let (mut models, mut rules) = (vec![], vec![]);
        for o in &f.origins {
            match o {
                cardinal::facts::Origin::Observed { query, rule, .. } => {
                    models.push(query.split('/').nth(1).unwrap_or(query).to_string());
                    rules.push(rule.to_string());
                }
                cardinal::facts::Origin::Derived { rule } => rules.push(format!("derived: {rule}")),
                cardinal::facts::Origin::Counted => rules.push("counted".to_string()),
            }
        }
        for v in [&mut models, &mut rules] {
            v.sort();
            v.dedup();
        }
        (models, rules)
    };
    let fact = |f: &Fact, bound: bool| {
        let (models, rules) = origins(f);
        json!({ "kind": f.kind.to_string(), "value": f.value.to_string(), "bound": bound, "from": models, "rules": rules })
    };
    let models: Vec<Value> = dag
        .models
        .iter()
        .map(|m| {
            json!({
                "name": m.name,
                "table": m.table,
                "depends": m.depends.iter().map(|d| json!({ "name": name_of(d), "source": d.starts_with("source.") })).collect::<Vec<_>>(),
                "rows": if m.table { table_rows.get(&m.name).copied().map(Value::from) } else { views.get(&m.name).and_then(|v| v.get("rows").cloned()) },
                "results": views.get(&m.name),
            })
        })
        .collect();
    let all: Vec<Value> = facts.iter().map(|f| fact(f, false)).chain(facts.bounds().map(|f| fact(f, true))).collect();
    let out = json!({ "dag": dag.name, "models": models, "facts": all });
    let path = path.replace("{dag}", &dag.name);
    std::fs::write(&path, serde_json::to_string_pretty(&out).unwrap()).unwrap();
    println!("  wrote {path}");
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

#[derive(Default, Clone)]
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
    let postgres = std::env::var("CARDINAL_DAG_ENGINE").is_ok_and(|e| e == "postgres");
    let available = if postgres { live::pg::available() } else { duckdb_available() };
    if !available || !root.join("projects").exists() {
        eprintln!("skipped: no {} or no dag-bench at {}", if postgres { "PostgreSQL" } else { "duckdb CLI" }, root.display());
        return;
    }
    let only = std::env::var("CARDINAL_DAG_ONLY").ok();
    // `engine`: as the warehouse's engine planned it.
    let planners: Vec<&str> = match std::env::var("CARDINAL_DAG_PLANNER").as_deref() {
        Ok("duckdb" | "postgres" | "engine") => vec!["engine"],
        Ok("both") => vec!["datafusion", "engine"],
        _ => vec!["datafusion"],
    };
    let mut failures = vec![];
    let mut summaries: Vec<(String, Summary)> = vec![];
    for dag in dags(&root, postgres, only.as_deref()) {
        let mut s = Summary { tables: dag.models.iter().filter(|m| m.table).count(), views: dag.models.iter().filter(|m| !m.table).count(), ..Default::default() };
        if s.views == 0 {
            println!("==== {}: {} TABLE models and no VIEW models: nothing to match\n", dag.name, s.tables);
            summaries.push((dag.name.clone(), s));
            continue;
        }
        let (ctx, undefined, foreign_keys) = context(&dag).await;
        let catalog = Catalog::from_context(&ctx).await.unwrap().with_partial_indexes(dag.engine.partial_indexes());
        println!("==== {} ({} {}): {} TABLE and {} VIEW models", dag.name, dag.engine.name(), dag.engine.target(), s.tables, s.views);
        for fk in &foreign_keys {
            println!("  foreign key {}({}) -> {}({})", fk.table, fk.columns.join(", "), fk.references, fk.referenced.join(", "));
        }

        // Every query read with the VIEW models it reads inlined, as DuckDB
        // plans it: so its text, which the profile carries, says what the
        // plan reads.
        let views: HashMap<String, String> =
            dag.models.iter().filter(|m| !m.table).map(|m| (m.name.to_lowercase(), m.sql.clone())).collect();
        let inlined = |m: &Model| inline(&m.sql, &views).unwrap_or_else(|| m.sql.clone());

        // The TABLE models' facts.
        let mut facts = FactSet::default();
        let mut table_rows: HashMap<String, u64> = HashMap::new();
        for m in dag.models.iter().filter(|m| m.table) {
            let mut ok = false;
            let variants = dag.engine.variants();
            for variant in &variants {
                let label = format!("{}/{}/{variant}", dag.name, m.name);
                let sql = inlined(m);
                match dag.engine.profile(&sql, variant).and_then(|j| dag.engine.read(&catalog, &label, &j, &sql)) {
                    Ok(p) => {
                        if p.nodes[p.root].counted {
                            table_rows.insert(m.name.clone(), p.nodes[p.root].rows);
                        }
                        facts.observe(&p);
                        ok = true;
                    }
                    Err(e) if *variant == variants[0] => println!("  table {} not profiled: {}", m.name, e.lines().next().unwrap_or_default()),
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
                        cardinal::facts::Origin::Counted => "counted".to_string(),
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
        let (wrong, counted, uncountable, slow) = check(&dag.engine, &catalog, &facts);
        failures.extend(wrong.into_iter().map(|w| format!("{}: {w}", dag.name)));
        (s.facts, s.bounds, s.counted) = (facts.len(), facts.bounds().count(), counted);
        println!(
            "  {} of {} tables profiled: {} facts and {} bounds; {counted} counted true, {uncountable} not countable, {slow} too slow to count",
            s.profiled,
            s.tables,
            s.facts,
            s.bounds
        );

        // Each VIEW model, bounded with them, as each planner plans it.
        let base = s.clone();
        let mut dumped: BTreeMap<String, serde_json::Map<String, Value>> = BTreeMap::new();
        for &planner in &planners {
            let mut s = base.clone();
            let mut misses: BTreeMap<&str, usize> = BTreeMap::new();
            let mut skipped = vec![];
            println!("  planned by {planner}:");
            println!("  {:<34} {:>10} {:>8} {:>6}  {:<16} {:<16} {:<16}", "view", "rows", "matched", "capped", "no facts", "ratios", "pinned");
            for m in dag.models.iter().filter(|m| !m.table) {
                // PostgreSQL may have only the tables: the views inlined.
                let run = if postgres { inlined(m) } else { m.sql.clone() };
                let first = &dag.engine.variants()[0];
                let truth = match dag.engine.profile(&run, first).and_then(|j| dag.engine.read(&catalog, &m.name, &j, &run)) {
                    Ok(p) if !p.nodes[p.root].counted => {
                        skipped.push(format!("{}: its rows were not counted", m.name));
                        continue;
                    }
                    Ok(p) => p.nodes[p.root].rows,
                    Err(e) => {
                        skipped.push(format!("{}: not profiled: {}", m.name, e.lines().next().unwrap_or_default()));
                        continue;
                    }
                };
                let options = Options { selectivity: true, foreign_keys: foreign_keys.clone(), ..Default::default() };
                let analyzed = match planner {
                    // The view's query with the views it reads inlined, as
                    // the engine plans it: so its text says what the plan reads.
                    "engine" => Some(inlined(m))
                        .ok_or_else(|| "does not inline".to_string())
                        .and_then(|sql| {
                            let j = dag.engine.plan(&sql)?;
                            let plan = dag.engine.read_plan(&catalog, &m.name, &j, &sql)?;
                            cardinal::analyze_observed(&catalog, &plan, options).map_err(|e| e.to_string())
                        }),
                    _ => cardinal::analyze_sql_with(&ctx, &m.sql, options).await.map_err(|e| e.to_string()),
                };
                let a = match analyzed {
                    Ok(a) if a.selectivity.is_some() => a,
                    Ok(_) => {
                        skipped.push(format!("{}: no selectivity formula", m.name));
                        continue;
                    }
                    Err(e) => {
                        skipped.push(format!("{}: not analyzed: {}", m.name, e.lines().next().unwrap_or_default()));
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
                    for line in a.plan.lines() {
                        println!("    | {line}");
                    }
                    println!("    ratios: X = {}", ratios.output);
                    for (sel, why) in &ratios.unmatched {
                        println!("      {sel}: {why}");
                    }
                    println!("    pinned: X = {}", pinned.output);
                    println!("      pinned sizes {:?}; capped {:?}; unchecked {:?}; rejected {:?}", pinned.pinned, pinned.capped, pinned.unchecked, pinned.rejected);
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
                        failures.push(format!("{}/{} {planner} {mode}: rejected {:?}", dag.name, m.name, i.rejected));
                    }
                }
                for (mode, r) in [("no facts", r0), ("ratios", r1), ("pinned", r2)] {
                    if !holds(r, truth) {
                        failures.push(format!("{}/{} {planner} {mode}: {} does not hold {truth}", dag.name, m.name, range(r)));
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
                let hi = |r: (u64, Option<u64>)| serde_json::json!({ "lo": r.0, "hi": r.1 });
                let entry = dumped.entry(m.name.clone()).or_default();
                entry.insert("rows".into(), truth.into());
                entry.insert(
                    planner.into(),
                    serde_json::json!({
                        "none": hi(r0),
                        "ratios": hi(r1),
                        "pinned": hi(r2),
                        "required": required.len(),
                        "matched": ratios.matched.iter().map(|x| serde_json::json!({ "sel": x.name, "value": x.value.to_string(), "facts": x.facts })).collect::<Vec<_>>(),
                        "pinned_sizes": pinned.pinned.len(),
                        "unmatched": ratios.unmatched.iter().map(|(n, why)| serde_json::json!({ "sel": n, "why": why })).collect::<Vec<_>>(),
                        "output": a.selectivity.as_ref().unwrap().output.to_string(),
                        "terms": a.selectivity_facts().iter().map(|(n, k)| {
                            let value = ratios.matched.iter().find(|x| x.name == *n).map(|x| x.value.to_string());
                            match k {
                                Ok(k) => serde_json::json!({ "sel": n, "fact": k.to_string(), "simple": simple(k), "value": value }),
                                Err(why) => serde_json::json!({ "sel": n, "fact": Value::Null, "why": why, "simple": Value::Null, "value": value }),
                            }
                        }).collect::<Vec<_>>(),
                    }),
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
            summaries.push((format!("{}/{planner}", dag.name), s));
        }
        if let Ok(path) = std::env::var("CARDINAL_DAG_DUMP") {
            dump(&path, &dag, &facts, &table_rows, &dumped);
        }
    }

    println!("{:<22} {:>6} {:>6} {:>12} {:>7} {:>7} {:>9} {:>7} {:>8} {:>6}", "dag", "tables", "views", "facts/bounds", "checked", "bounded", "matched", "capped", "tighter", "exact");
    for (name, s) in &summaries {
        println!(
            "{name:<22} {:>6} {:>6} {:>12} {:>7} {:>7} {:>9} {:>7} {:>8} {:>6}",
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
