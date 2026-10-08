//! The DuckDB fixtures under `tests/duckdb`: profiles of TPC-H at scale
//! factor 0.01 and of hand-written queries, and the tables they ran over.
#![allow(dead_code)]

use std::sync::Arc;

use cardinal::observed::{Catalog, ObservedPlan, from_duckdb};
use datafusion::arrow::datatypes::{DataType, Field, Schema};
use datafusion::datasource::MemTable;
use datafusion::prelude::SessionContext;
use serde_json::Value;

pub const DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/duckdb");

pub fn json(path: &str) -> Value {
    serde_json::from_str(&std::fs::read_to_string(format!("{DIR}/{path}")).unwrap()).unwrap()
}

/// DuckDB's type names as Arrow types.
fn arrow_type(t: &str) -> DataType {
    if let Some(ps) = t.strip_prefix("DECIMAL(").and_then(|r| r.strip_suffix(')')) {
        let (p, s) = ps.split_once(',').unwrap();
        return DataType::Decimal128(p.trim().parse().unwrap(), s.trim().parse().unwrap());
    }
    match t {
        "INTEGER" => DataType::Int32,
        "BIGINT" => DataType::Int64,
        "DOUBLE" => DataType::Float64,
        "VARCHAR" => DataType::Utf8,
        "DATE" => DataType::Date32,
        t => panic!("no Arrow type for DuckDB type {t}"),
    }
}

/// The TPC-H tables, empty, with DuckDB's schemas.
pub fn context() -> SessionContext {
    let mut tables: Vec<(String, Vec<Field>)> = vec![];
    for c in json("catalog.json").as_array().unwrap() {
        let table = c["table_name"].as_str().unwrap();
        let field = Field::new(c["column_name"].as_str().unwrap(), arrow_type(c["data_type"].as_str().unwrap()), true);
        match tables.last_mut() {
            Some((t, fields)) if t == table => fields.push(field),
            _ => tables.push((table.to_string(), vec![field])),
        }
    }
    let ctx = SessionContext::new();
    for (name, fields) in tables {
        let schema = Arc::new(Schema::new(fields));
        ctx.register_table(name.as_str(), Arc::new(MemTable::try_new(schema, vec![vec![]]).unwrap())).unwrap();
    }
    ctx
}

pub async fn catalog() -> Catalog {
    Catalog::from_context(&context()).await.unwrap()
}

/// Every fixture under `dir`, by name, in name order.
pub fn fixtures(dir: &str) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = std::fs::read_dir(format!("{DIR}/{dir}"))
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "json"))
        .map(|p| (p.file_stem().unwrap().to_string_lossy().into_owned(), std::fs::read_to_string(&p).unwrap()))
        .collect();
    out.sort();
    out
}

pub async fn plans(dir: &str) -> Vec<ObservedPlan> {
    let catalog = catalog().await;
    fixtures(dir).iter().map(|(name, json)| from_duckdb(&catalog, name, json).unwrap()).collect()
}

/// The query each profile of `dir` ran, by name: TPC-H's from `tests/tpch`,
/// the others' next to their profiles.
pub fn query(dir: &str, name: &str) -> String {
    let path = match dir {
        "tpch" => format!("{}/tests/tpch/{name}.sql", env!("CARGO_MANIFEST_DIR")),
        dir => format!("{DIR}/{dir}/{name}.sql"),
    };
    std::fs::read_to_string(path).unwrap()
}

/// TPC-H's foreign keys, all of which its data satisfies.
pub fn foreign_keys() -> Vec<cardinal::ForeignKey> {
    use cardinal::ForeignKey as Fk;
    vec![
        Fk::new("lineitem", &["l_orderkey"], "orders", &["o_orderkey"]),
        Fk::new("lineitem", &["l_partkey"], "part", &["p_partkey"]),
        Fk::new("lineitem", &["l_suppkey"], "supplier", &["s_suppkey"]),
        Fk::new("lineitem", &["l_partkey", "l_suppkey"], "partsupp", &["ps_partkey", "ps_suppkey"]),
        Fk::new("orders", &["o_custkey"], "customer", &["c_custkey"]),
        Fk::new("customer", &["c_nationkey"], "nation", &["n_nationkey"]),
        Fk::new("supplier", &["s_nationkey"], "nation", &["n_nationkey"]),
        Fk::new("partsupp", &["ps_partkey"], "part", &["p_partkey"]),
        Fk::new("partsupp", &["ps_suppkey"], "supplier", &["s_suppkey"]),
        Fk::new("nation", &["n_regionkey"], "region", &["r_regionkey"]),
    ]
}
