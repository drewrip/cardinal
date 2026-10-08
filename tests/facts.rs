//! Facts read off DuckDB `EXPLAIN ANALYZE` profiles of TPC-H at scale factor
//! 0.01, checked against true counts. Regenerate the fixtures with
//! `scripts/duckdb_fixtures.sh`; print every fact with
//! `cargo test --test facts print_facts -- --nocapture`.

mod fixtures;

use std::collections::{BTreeMap, HashMap};

use cardinal::facts::{FactSet, State, derive_facts, states};
use cardinal::observed::{ObservedPlan, from_duckdb};
use fixtures::{DIR, catalog, json, plans};
use serde_json::{Value, json};

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
    let mut taints = BTreeMap::<String, usize>::new();
    for dir in ["extra", "tpch"] {
        for p in plans(dir).await {
            println!("==== {}\n{p}", p.name);
            for (i, s) in states(&p).iter().enumerate() {
                match s {
                    State::Clean(c) => println!("  #{i}: {}", c.canonical()),
                    State::Pending(c, pending) => println!("  #{i}: {} (pending {})", c.canonical(), pending.len()),
                    State::Tainted(t) => {
                        println!("  #{i}: tainted: {t}");
                        *taints.entry(t.to_string()).or_default() += 1;
                    }
                }
            }
            println!("{}", derive_facts(std::slice::from_ref(&p)));
            all.push(p);
        }
    }
    let facts = derive_facts(&all);
    println!("==== all {} plans: {} facts\n{facts}", all.len(), facts.len());
    println!("==== tainted operators, by reason");
    for (t, n) in taints {
        println!("{n:4} {t}");
    }
}

/// Every plan's facts together.
async fn all_facts() -> FactSet {
    let mut all = plans("extra").await;
    all.extend(plans("tpch").await);
    derive_facts(&all)
}

/// Writes a query counting each fact that counts rows of base tables, for
/// `scripts/duckdb_fixtures.sh` to run into `fact_checks.json`.
#[tokio::test]
async fn dump_fact_queries() {
    let facts = all_facts().await;
    let rows: Vec<String> = facts
        .iter()
        .filter_map(|f| {
            let sql = f.kind.count_sql()?;
            Some(format!("SELECT '{}' AS fact, ({sql}) AS value", f.kind.to_string().replace('\'', "''")))
        })
        .collect();
    std::fs::write(format!("{DIR}/fact_checks.sql"), rows.join("\nUNION ALL ") + ";\n").unwrap();
}

/// Every fact that counts rows of base tables, against DuckDB's count.
#[tokio::test]
async fn facts_match_duckdb() {
    let counted: HashMap<String, u64> = json("fact_checks.json")
        .as_array()
        .unwrap()
        .iter()
        .map(|r| (r["fact"].as_str().unwrap().to_string(), r["value"].as_u64().unwrap()))
        .collect();
    let facts = all_facts().await;
    let mut checked = 0;
    for f in facts.iter().filter(|f| f.kind.count_sql().is_some()) {
        let Some(&n) = counted.get(&f.kind.to_string()) else {
            panic!("{} is not in fact_checks.json: run scripts/duckdb_fixtures.sh", f.kind)
        };
        assert_eq!(f.value.as_int(), Some(n), "{} from {:?}", f.kind, f.origins);
        checked += 1;
    }
    assert!(checked > 50, "only {checked} facts checked");
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
    assert_eq!(value(&facts, "|lineitem where lineitem.l_quantity < 10.00|"), q10 as f64);
    assert_eq!(value(&facts, "s(lineitem.l_quantity < 10.00 | lineitem)"), ratio(q10, li));
    assert_eq!(
        value(&facts, "ndv(lineitem.l_suppkey | lineitem)"),
        e["ndv(l_suppkey|lineitem)"] as f64
    );
    assert_eq!(
        value(&facts, "ndv(lineitem.l_suppkey | lineitem where lineitem.l_quantity < 10.00)"),
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
                and lineitem.l_quantity < 10.00 and orders.o_orderstatus = 'F'";
    assert_eq!(value(&facts, &format!("|{join}|")), joined as f64);
    // From one plan's join and filtered orders, and another's filtered
    // lineitem: the join selectivity over both filtered inputs.
    assert_eq!(
        value(
            &facts,
            "s(lineitem.l_orderkey = orders.o_orderkey | lineitem × orders \
             where lineitem.l_quantity < 10.00 and orders.o_orderstatus = 'F')"
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
    let key = "s(lineitem.l_extendedprice * 2 > 10000.00 | lineitem)";
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

/// The fact printed as text starting with `prefix`.
fn starting<'f>(facts: &'f FactSet, prefix: &str) -> &'f cardinal::facts::Fact {
    let mut found = facts.iter().filter(|f| f.kind.to_string().starts_with(prefix));
    match (found.next(), found.next()) {
        (Some(f), None) => f,
        (None, _) => panic!("no fact starting {prefix} among:\n{facts}"),
        (Some(a), Some(b)) => panic!("several facts starting {prefix}: {a}, {b}"),
    }
}

/// Correlated subqueries (delim joins) and IN / NOT IN (mark joins).
#[tokio::test]
async fn subqueries() {
    let e = expected();
    let mut all = vec![];
    for name in ["semi_join", "not_exists", "in_subquery", "not_in", "scan_filter", "group_base"] {
        all.push(plan(name).await);
    }
    let facts = derive_facts(&all);
    assert!(facts.conflicts.is_empty(), "{:#?}", facts.conflicts);
    // EXISTS and NOT EXISTS over the same subquery share one match share.
    let exists = starting(&facts, "m((\"orders@1\".o_orderkey IS NOT DISTINCT FROM \"orders@2\".o_orderkey) | orders@1 ⋉");
    assert_eq!(exists.value.as_f64(), ratio(e["orders semi lineitem>49"], e["orders"]));
    assert_eq!(exists.origins.len(), 2, "{:?}", exists.origins);
    // A semi join's probe side is pruned by its runtime filter; |part| is
    // from the NOT IN plan, which scans all of it.
    let semi = starting(&facts, "m(\"part\".p_partkey = partsupp.ps_partkey | part ⋉ partsupp");
    assert_eq!(semi.value.as_f64(), ratio(e["part semi partsupp<100"], 2000));
    let not_in = starting(&facts, "|LeftMark join, unmarked");
    assert_eq!(not_in.value.as_int(), Some(e["part not in partsupp<100"]));
}

/// Plans whose operators do not resolve give no facts above them.
#[tokio::test]
async fn unresolved() {
    // This anti join's condition names the build side's column for both
    // sides, so its probe side does not resolve.
    let p = plan("anti_exists").await;
    let join = p.nodes.iter().position(|n| n.engine_op == "HASH_JOIN").unwrap();
    assert!(matches!(states(&p)[join], State::Tainted(_)));
}

/// A condition the query does not vouch for is not read, even where its
/// names resolve: here `o_custkey = c_custkey` printed for a query
/// comparing `o_orderkey` and `c_custkey`.
#[tokio::test]
async fn misnamed_condition() {
    let catalog = catalog().await;
    let scan = |table: &str, cols: Vec<&str>, rows| {
        node("TABLE_SCAN", rows, json!({"Table": format!("tpch.main.{table}"), "Projections": cols}), vec![])
    };
    let join = |sql: &str| {
        let mut j = node(
            "HASH_JOIN",
            100,
            json!({"Join Type": "INNER", "Conditions": "o_custkey = c_custkey"}),
            vec![scan("orders", vec!["o_custkey", "o_orderkey"], 15000), scan("customer", vec!["c_custkey"], 1500)],
        );
        j["query_name"] = json!(sql);
        j.to_string()
    };
    let vouched = from_duckdb(&catalog, "ok", &join("select * from orders, customer where o_custkey = c_custkey")).unwrap();
    assert!(matches!(states(&vouched)[2], State::Clean(_)));
    let wrong = from_duckdb(&catalog, "wrong", &join("select * from orders, customer where o_orderkey = c_custkey")).unwrap();
    assert!(matches!(states(&wrong)[2], State::Tainted(_)), "{:?}", states(&wrong)[2]);
}

/// Self-joins, CTEs, aggregate values, and aliases.
#[tokio::test]
async fn other_shapes() {
    let e = expected();
    let one = |name: &'static str| async move { derive_facts(&[plan(name).await]) };

    let f = one("self_join").await;
    let join = starting(&f, "|lineitem@1 × lineitem@2 where");
    assert_eq!(join.value.as_int(), Some(e["self join"]));

    let f = one("cte").await;
    assert!(f.iter().any(|f| f.kind.to_string().starts_with("ndv(orders.o_custkey | orders)")), "{f}");

    let f = one("having").await;
    assert_eq!(value(&f, "ndv(lineitem.l_orderkey | lineitem)"), e["ndv(l_orderkey|lineitem)"] as f64);
    let having = starting(&f, "s(\"value\".\"sum(lineitem.l_quantity) of group[lineitem.l_orderkey](lineitem)\" > 200.0");
    assert_eq!(having.value.as_f64(), ratio(e["having sum>200"], e["ndv(l_orderkey|lineitem)"]));

    let f = one("scalar_subquery").await;
    let price = f.iter().find(|f| f.kind.to_string().starts_with("|σ")).unwrap_or_else(|| panic!("{f}"));
    assert_eq!(price.value.as_int(), Some(e["price>avg"]));

    let f = one("alias").await;
    let years = starting(&f, "ndv(date_part(");
    assert_eq!(years.value.as_int(), Some(e["ndv(year|orders,price>100000)"]));
}
