//! Facts read off DuckDB `EXPLAIN ANALYZE` profiles of TPC-H at scale factor
//! 0.01, checked against true counts. Regenerate the fixtures with
//! `scripts/duckdb_fixtures.sh`; print every fact with
//! `cargo test --test facts print_facts -- --nocapture`.

mod fixtures;

use std::collections::{BTreeMap, HashMap};

use cardinal::facts::{Fact, FactKind, FactSet, Origin, Ratio, State, derive_facts, states};
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

/// The bound printed as `text` (without its value), as an integer, and
/// that no fact gives it exactly.
fn bound(facts: &FactSet, text: &str) -> u64 {
    assert!(facts.find(text).is_none(), "{text} is exact among:\n{facts}");
    match facts.bounds().find(|b| b.kind.to_string() == text) {
        Some(b) => b.value.as_int().unwrap(),
        None => panic!("no bound {text} among:\n{facts}"),
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

/// Each fact (`=`) and bound (`<=`) as written in `fact_checks.json`.
fn label(f: &Fact, bound: bool) -> String {
    format!("{} {}", if bound { "<=" } else { "=" }, f.kind)
}

/// Writes a query counting what each fact and bound counts, for
/// `scripts/duckdb_fixtures.sh` to run into `fact_checks.json`.
#[tokio::test]
async fn dump_fact_queries() {
    let facts = all_facts().await;
    let catalog = catalog().await;
    let all = facts.iter().map(|f| (f, false)).chain(facts.bounds().map(|f| (f, true)));
    let rows: Vec<String> = all
        .filter_map(|(f, bound)| {
            let c = f.kind.count_sql(&catalog, &facts)?;
            let of = c.of.map(|q| format!("({q})")).unwrap_or("NULL".into());
            Some(format!("SELECT '{}' AS fact, ({}) AS value, {of} AS of", label(f, bound).replace('\'', "''"), c.value))
        })
        .collect();
    std::fs::write(format!("{DIR}/fact_checks.sql"), rows.join("\nUNION ALL ") + ";\n").unwrap();
}

/// Every fact and bound, against DuckDB's count of what it counts: a fact
/// equal to it, a bound at least it.
#[tokio::test]
async fn facts_match_duckdb() {
    let counted: HashMap<String, (u64, Option<u64>)> = json("fact_checks.json")
        .as_array()
        .unwrap()
        .iter()
        .map(|r| (r["fact"].as_str().unwrap().to_string(), (r["value"].as_u64().unwrap(), r["of"].as_u64())))
        .collect();
    let facts = all_facts().await;
    let catalog = catalog().await;
    let mut checked = 0;
    let all = facts.iter().map(|f| (f, false)).chain(facts.bounds().map(|f| (f, true)));
    for (f, bound) in all.filter(|(f, _)| f.kind.count_sql(&catalog, &facts).is_some()) {
        let Some(&(n, of)) = counted.get(&label(f, bound)) else {
            panic!("{} is not in fact_checks.json: run scripts/duckdb_fixtures.sh", label(f, bound))
        };
        let ok = match (bound, &f.kind, of) {
            (true, _, _) => f.value.as_int().is_some_and(|b| b >= n),
            (false, FactKind::Unique { .. }, Some(of)) => n == of,
            (false, _, Some(of)) => Ratio::new(n, of) == Some(f.value),
            (false, _, None) => f.value.as_int() == Some(n),
        };
        assert!(ok, "{} is {n}{}, from {:?}", label(f, bound), of.map(|o| format!("/{o}")).unwrap_or_default(), f.origins);
        checked += 1;
    }
    assert!(checked > 100, "only {checked} facts and bounds checked");
}

#[tokio::test]
async fn every_fixture_converts() {
    for dir in ["extra", "tpch"] {
        for p in plans(dir).await {
            assert!(!p.nodes.is_empty(), "{}", p.name);
        }
    }
}

/// The same context seen in different plans must have one value, and no
/// bound may be below it: the main check that the contexts name the rows
/// they claim to.
#[tokio::test]
async fn no_conflicts() {
    let mut all = plans("extra").await;
    all.extend(plans("tpch").await);
    let facts = derive_facts(&all);
    assert!(facts.conflicts.is_empty(), "{:#?}", facts.conflicts);
    assert!(facts.len() + facts.bounds().count() > 100, "{facts}");
}

/// The facts of hand-written queries, against true counts. A filter pushed
/// into a scan gives only a bound on its rows, and on what keeps them all
/// above; the rows of unfiltered scans, and what is computed from them
/// alone, are exact.
#[tokio::test]
async fn extra_facts_are_true() {
    let e = expected();
    let mut all = vec![];
    for p in plans("extra").await {
        all.push(p);
    }
    let facts = derive_facts(&all);
    assert!(facts.conflicts.is_empty(), "{:#?}", facts.conflicts);
    assert_eq!(value(&facts, "|lineitem|"), e["lineitem"] as f64);
    assert_eq!(value(&facts, "|orders|"), e["orders"] as f64);
    assert_eq!(value(&facts, "ndv(customer.c_mktsegment, customer.c_nationkey | customer)"), e["ndv(c_nationkey,c_mktsegment|customer)"] as f64);

    // The filter in the scan bounds its rows; no share of them is known.
    assert_eq!(bound(&facts, "|lineitem where lineitem.l_quantity < 10.00|"), e["lineitem|l_quantity<10"]);
    assert!(facts.iter().all(|f| !f.kind.to_string().starts_with("s(lineitem.l_quantity < 10.00")), "{facts}");

    // A join and a semi join keep all the rows of a superset input.
    let join = "|customer × orders where customer.c_custkey <= 1499 and customer.c_custkey = orders.o_custkey \
                and customer.c_mktsegment = 'BUILDING'|";
    assert_eq!(bound(&facts, join), e["orders⋈customer|BUILDING"]);
    let semi = "|orders where exists[customer.c_custkey = orders.o_custkey](customer \
                where customer.c_custkey <= 1499 and customer.c_mktsegment = 'BUILDING')|";
    assert_eq!(bound(&facts, semi), e["orders semi customer BUILDING"]);
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

/// Rows a scan may not have finished producing give no facts or bounds;
/// the join above a runtime-filtered scan does, bounded by its other side's
/// pushed filter.
#[tokio::test]
async fn taint() {
    let e = expected();
    let limit = derive_facts(&[plan("limit").await]);
    assert!(limit.is_empty() && limit.bounds().next().is_none(), "{limit}");

    let p = plan("join_filtered").await;
    let s = states(&p);
    let scan = p.nodes.iter().position(|n| n.engine_op == "TABLE_SCAN" && n.op.to_string() == "Scan orders").unwrap();
    assert!(matches!(s[scan], State::Pending(..)), "{:?}", s[scan]);
    let facts = derive_facts(&[p]);
    assert!(facts.find("|orders|").is_none(), "{facts}");
    let joined = facts
        .bounds()
        .find(|f| f.kind.to_string().starts_with("|customer × orders"))
        .unwrap_or_else(|| panic!("no join bound in\n{facts}"));
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

/// Correlated subqueries (delim joins) and IN / NOT IN (mark joins). A
/// semi join keeps every row with a partner among a superset of its other
/// side's rows, so a filter pushed into that side bounds it; an anti join
/// or NOT IN keeps fewer, so gives nothing.
#[tokio::test]
async fn subqueries() {
    let e = expected();
    let mut all = vec![];
    for name in ["semi_join", "not_exists", "in_subquery", "not_in", "scan_filter", "group_base"] {
        all.push(plan(name).await);
    }
    let facts = derive_facts(&all);
    assert!(facts.conflicts.is_empty(), "{:#?}", facts.conflicts);
    // EXISTS decorrelated to read as the semi join a query would write.
    let exists = "|orders where exists[lineitem.l_orderkey = orders.o_orderkey](lineitem where lineitem.l_quantity > 49.00)|";
    assert_eq!(bound(&facts, exists), e["orders semi lineitem>49"]);
    let anti = |f: &Fact| f.kind.to_string().contains("not exists[") || f.kind.to_string().contains("not in[");
    assert!(!facts.iter().chain(facts.bounds()).any(anti), "{facts}");
    assert!(!facts.iter().any(|f| matches!(f.kind, FactKind::Match { .. })), "{facts}");
}

/// Outer joins and filters on grouping keys, read the same however a plan
/// placed them.
#[tokio::test]
async fn outer_joins_and_groups() {
    let e = expected();
    let mut all = vec![];
    for name in ["left_preserved", "full_one_side", "left_rejected", "left_chain", "group_key_filter"] {
        all.push(plan(name).await);
    }
    let facts = derive_facts(&all);
    assert!(facts.conflicts.is_empty(), "{:#?}", facts.conflicts);
    let observed = |f: &Fact, q: &str| f.origins.iter().any(|o| matches!(o, Origin::Observed { query, .. } if query == q));

    // A full join filtered on one side's columns is the left join preserving
    // it, and a filter on the preserved side reads above the join, as does
    // the condition's term on the other side below it. Exact from the plan
    // that filtered above the join; the one that pushed the filters into
    // its scans says nothing of the join, whose padded side may be a
    // superset.
    let left = starting(
        &facts,
        "|Left join[customer.c_custkey = orders.o_custkey](customer, orders where orders.o_totalprice > 300000.00) \
         where customer.c_acctbal > 5000.00|",
    );
    assert_eq!(left.value.as_int(), Some(e["customer⟕orders>300000|acctbal>5000"]));
    assert!(observed(left, "full_one_side") && !observed(left, "left_preserved"), "{:?}", left.origins);
    assert!(!facts.bounds().any(|b| b.kind.to_string().contains("Left join")), "{facts}");

    // A filter rejecting the NULLs of the other side leaves the inner join.
    let inner = "|customer × orders where customer.c_custkey <= 1499 and customer.c_custkey = orders.o_custkey \
                 and orders.o_totalprice > 300000.00|";
    assert_eq!(bound(&facts, inner), e["customer⋈orders|price>300000"]);

    // HAVING on a grouping key filters the rows grouped.
    let groups = "ndv(lineitem.l_suppkey | lineitem where lineitem.l_suppkey < 50)";
    assert_eq!(bound(&facts, groups), e["ndv(l_suppkey|lineitem,l_suppkey<50)"]);
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
    let join = f.bounds().find(|b| b.kind.to_string().starts_with("|lineitem@1 × lineitem@2 where")).unwrap_or_else(|| panic!("{f}"));
    assert_eq!(join.value.as_int(), Some(e["self join"]));

    let f = one("cte").await;
    assert!(f.iter().any(|f| f.kind.to_string().starts_with("ndv(orders.o_custkey | orders)")), "{f}");

    let f = one("having").await;
    assert_eq!(value(&f, "ndv(lineitem.l_orderkey | lineitem)"), e["ndv(l_orderkey|lineitem)"] as f64);
    let having = starting(&f, "s(\"value\".\"sum(lineitem.l_quantity) of group[lineitem.l_orderkey](lineitem)\" > 200.0");
    assert_eq!(having.value.as_f64(), ratio(e["having sum>200"], e["ndv(l_orderkey|lineitem)"]));

    let f = one("scalar_subquery").await;
    let price = starting(&f, "|lineitem@1 × aggregate(");
    assert_eq!(price.value.as_int(), Some(e["price>avg"]));

    let f = one("alias").await;
    let years = f.bounds().find(|b| b.kind.to_string().starts_with("ndv(date_part(")).unwrap_or_else(|| panic!("{f}"));
    assert_eq!(years.value.as_int(), Some(e["ndv(year|orders,price>100000)"]));
}
