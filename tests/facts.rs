//! Facts read off DuckDB `EXPLAIN ANALYZE` profiles of TPC-H at scale factor
//! 0.01, checked against true counts. Regenerate the fixtures with
//! `scripts/duckdb_fixtures.sh`; print every fact with
//! `cargo test --test facts print_facts -- --nocapture`.

use std::collections::HashMap;
use std::sync::Arc;

use cardinal::facts::{FactSet, State, derive_facts, states};
use cardinal::observed::{Catalog, ObservedPlan, from_duckdb};
use datafusion::arrow::datatypes::{DataType, Field, Schema};
use datafusion::datasource::MemTable;
use datafusion::prelude::SessionContext;
use serde_json::{Value, json};

const DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/duckdb");

fn json(path: &str) -> Value {
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
async fn catalog() -> Catalog {
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
    Catalog::from_context(&ctx).await.unwrap()
}

/// Every fixture under `dir`, by name, in name order.
fn fixtures(dir: &str) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = std::fs::read_dir(format!("{DIR}/{dir}"))
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "json"))
        .map(|p| (p.file_stem().unwrap().to_string_lossy().into_owned(), std::fs::read_to_string(&p).unwrap()))
        .collect();
    out.sort();
    out
}

async fn plans(dir: &str) -> Vec<ObservedPlan> {
    let catalog = catalog().await;
    fixtures(dir).iter().map(|(name, json)| from_duckdb(&catalog, name, json).unwrap()).collect()
}

async fn plan(name: &str) -> ObservedPlan {
    let catalog = catalog().await;
    from_duckdb(&catalog, name, &std::fs::read_to_string(format!("{DIR}/extra/{name}.json")).unwrap()).unwrap()
}

/// True counts, by the names in `expected.sql`.
fn expected() -> HashMap<String, u64> {
    json("expected.json")
        .as_array()
        .unwrap()
        .iter()
        .map(|r| (r["fact"].as_str().unwrap().to_string(), r["value"].as_u64().unwrap()))
        .collect()
}

/// The value of the fact printed as `text`, as a float.
fn value(facts: &FactSet, text: &str) -> f64 {
    match facts.find(text) {
        Some(f) => f.value.as_f64(),
        None => panic!("no fact {text} among:\n{facts}"),
    }
}

fn ratio(n: u64, d: u64) -> f64 {
    n as f64 / d as f64
}

#[tokio::test]
async fn print_facts() {
    let mut all = vec![];
    for dir in ["extra", "tpch"] {
        for p in plans(dir).await {
            println!("==== {}\n{p}", p.name);
            for (i, s) in states(&p).iter().enumerate() {
                match s {
                    State::Clean(c) => println!("  #{i}: {c}"),
                    State::Pending(c, pending) => println!("  #{i}: {c} (pending {})", pending.len()),
                    State::Tainted(t) => println!("  #{i}: tainted: {t}"),
                }
            }
            println!("{}", derive_facts(std::slice::from_ref(&p)));
            all.push(p);
        }
    }
    let facts = derive_facts(&all);
    println!("==== all {} plans: {} facts\n{facts}", all.len(), facts.len());
}

#[tokio::test]
async fn every_fixture_converts() {
    for dir in ["extra", "tpch"] {
        for p in plans(dir).await {
            assert!(!p.nodes.is_empty(), "{}", p.name);
        }
    }
}

/// The same context seen in different plans must have one value: the main
/// check that the contexts name the rows they claim to.
#[tokio::test]
async fn no_conflicts() {
    let mut all = plans("extra").await;
    all.extend(plans("tpch").await);
    let facts = derive_facts(&all);
    assert!(facts.conflicts.is_empty(), "{:#?}", facts.conflicts);
    assert!(facts.len() > 100, "{facts}");
}

/// Every fact of a hand-written query, against true counts.
#[tokio::test]
async fn extra_facts_are_true() {
    let e = expected();
    let mut all = vec![];
    for p in plans("extra").await {
        all.push(p);
    }
    let facts = derive_facts(&all);
    assert!(facts.conflicts.is_empty(), "{:#?}", facts.conflicts);
    let li = e["lineitem"];
    let q10 = e["lineitem|l_quantity<10"];
    assert_eq!(value(&facts, "|lineitem|"), li as f64);
    assert_eq!(value(&facts, "|lineitem where lineitem.l_quantity < 10.0|"), q10 as f64);
    assert_eq!(value(&facts, "s(lineitem.l_quantity < 10.0 | lineitem)"), ratio(q10, li));
    assert_eq!(
        value(&facts, "ndv(lineitem.l_suppkey | lineitem)"),
        e["ndv(l_suppkey|lineitem)"] as f64
    );
    assert_eq!(
        value(&facts, "ndv(lineitem.l_suppkey | lineitem where lineitem.l_quantity < 10.0)"),
        e["ndv(l_suppkey|lineitem,l_quantity<10)"] as f64
    );
    assert_eq!(
        value(&facts, "ndv(customer.c_mktsegment, customer.c_nationkey | customer)"),
        e["ndv(c_nationkey,c_mktsegment|customer)"] as f64
    );

    // The same predicate over a join's input is a different fact.
    let (f, o) = (e["orders|o_orderstatus=F"], e["orders"]);
    let joined = e["lineitem⋈orders|F,l_quantity<10"];
    let join = "lineitem × orders where lineitem.l_orderkey = orders.o_orderkey \
                and lineitem.l_quantity < 10.0 and orders.o_orderstatus = 'F'";
    assert_eq!(value(&facts, &format!("|{join}|")), joined as f64);
    // From one plan's join and filtered orders, and another's filtered
    // lineitem: the join selectivity over both filtered inputs.
    assert_eq!(
        value(
            &facts,
            "s(lineitem.l_orderkey = orders.o_orderkey | lineitem × orders \
             where lineitem.l_quantity < 10.0 and orders.o_orderstatus = 'F')"
        ),
        joined as f64 / (q10 * f) as f64
    );
    // |orders| comes from yet another plan; the semi join's probe side was
    // pruned by a runtime filter, so its own count of orders says nothing.
    assert_eq!(value(&facts, "|orders|"), o as f64);
    assert_eq!(
        value(
            &facts,
            "m(customer.c_custkey = orders.o_custkey | orders ⋉ customer \
             where customer.c_custkey <= 1499 and customer.c_mktsegment = 'BUILDING')"
        ),
        ratio(e["orders semi customer BUILDING"], o)
    );
    println!("{facts}");
}

/// A DuckDB profile node.
fn node(op: &str, rows: u64, info: Value, children: Vec<Value>) -> Value {
    json!({"operator_type": op, "operator_cardinality": rows, "extra_info": info, "children": children})
}

/// A filter above projections measures the same rows as one directly on the
/// scan: projections pass the distribution through, and a computed column,
/// referred to by name or position, reads as its expression.
#[tokio::test]
async fn projections_pass_through() {
    let catalog = catalog().await;
    let scan = || {
        let info = json!({"Table": "tpch.main.lineitem", "Projections": ["l_quantity", "l_extendedprice"]});
        node("TABLE_SCAN", 60175, info, vec![])
    };
    let computed = node("PROJECTION", 60175, json!({"Projections": ["l_quantity", "(l_extendedprice * 2)"]}), vec![scan()]);
    let renamed = node("PROJECTION", 60175, json!({"Projections": ["#1", "l_quantity"]}), vec![computed]);
    let over = node("FILTER", 6959, json!({"Expression": "(#0 > 10000.00)"}), vec![renamed]);
    let direct = node("FILTER", 6959, json!({"Expression": "((l_extendedprice * 2) > 10000.00)"}), vec![scan()]);
    let key = "s(lineitem.l_extendedprice * 2 > 10000.0 | lineitem)";
    for (name, plan) in [("over", over), ("direct", direct)] {
        let facts = derive_facts(&[from_duckdb(&catalog, name, &plan.to_string()).unwrap()]);
        assert_eq!(value(&facts, key), ratio(6959, 60175), "{name}");
    }
}

/// Rows a scan may not have finished producing give no facts; the join
/// above a runtime-filtered scan does.
#[tokio::test]
async fn taint() {
    let e = expected();
    let limit = derive_facts(&[plan("limit").await]);
    assert!(limit.is_empty(), "{limit}");

    let p = plan("join_filtered").await;
    let s = states(&p);
    let scan = p.nodes.iter().position(|n| n.engine_op == "TABLE_SCAN" && n.op.to_string() == "Scan orders").unwrap();
    assert!(matches!(s[scan], State::Pending(..)), "{:?}", s[scan]);
    let facts = derive_facts(&[p]);
    assert!(facts.find("|orders|").is_none(), "{facts}");
    let joined = facts
        .iter()
        .find(|f| f.kind.to_string().starts_with("|customer × orders"))
        .unwrap_or_else(|| panic!("no join cardinality in\n{facts}"));
    assert_eq!(joined.value.as_int(), Some(e["orders⋈customer|BUILDING"]));
}

/// Plans whose operators do not resolve give no facts above them.
#[tokio::test]
async fn unresolved() {
    // DuckDB plans a correlated EXISTS as a delim join, which has no model.
    let facts = derive_facts(&[plan("semi_join").await]);
    assert!(facts.iter().all(|f| !f.kind.to_string().starts_with("m(")), "{facts}");
    // This anti join's condition names the build side's column for both
    // sides, so its probe side does not resolve.
    let p = plan("anti_exists").await;
    let join = p.nodes.iter().position(|n| n.engine_op == "HASH_JOIN").unwrap();
    assert!(matches!(states(&p)[join], State::Tainted(_)));
}
