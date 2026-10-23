//! Facts read off DuckDB `EXPLAIN ANALYZE` profiles of TPC-H at scale factor
//! 0.01, checked against true counts. Regenerate the fixtures with
//! `scripts/duckdb_fixtures.sh`; print every fact with
//! `cargo test --test facts print_facts -- --nocapture`.

mod fixtures;

use std::collections::{BTreeMap, HashMap};

use cardinal::facts::{Fact, FactKind, FactSet, Origin, Ratio, State, derive_facts, states};
use cardinal::observed::{ObservedPlan, from_duckdb};
use fixtures::{DIR, catalog, json, pg_plans, plans};
use serde_json::{Value, json};

async fn plan(name: &str) -> ObservedPlan {
    let catalog = catalog().await;
    from_duckdb(&catalog, name, &std::fs::read_to_string(format!("{DIR}/extra/{name}.json")).unwrap(), None).unwrap()
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

/// The facts of hand-written queries, against true counts. A required
/// filter pushed into a scan is applied exactly: its rows, and what is
/// computed from them, are exact.
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

    assert_eq!(value(&facts, "|lineitem where lineitem.l_quantity < 10.00|"), e["lineitem|l_quantity<10"] as f64);

    // A join and a semi join over a scan with a pushed filter.
    let join = "|customer × orders where customer.c_custkey <= 1499 and customer.c_custkey = orders.o_custkey \
                and customer.c_mktsegment = 'BUILDING'|";
    assert_eq!(value(&facts, join), e["orders⋈customer|BUILDING"] as f64);
    let semi = "|orders where exists[customer.c_custkey = orders.o_custkey](customer \
                where customer.c_custkey <= 1499 and customer.c_mktsegment = 'BUILDING')|";
    assert_eq!(value(&facts, semi), e["orders semi customer BUILDING"] as f64);
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
        let facts = derive_facts(&[from_duckdb(&catalog, name, &plan.to_string(), None).unwrap()]);
        assert_eq!(value(&facts, key), ratio(6959, 60175), "{name}");
    }
}

/// Rows a scan may not have finished producing give no facts or bounds;
/// the join above a runtime-filtered scan does.
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
    let joined = "|customer × orders where customer.c_custkey = orders.o_custkey and customer.c_mktsegment = 'BUILDING'|";
    assert_eq!(value(&facts, joined), e["orders⋈customer|BUILDING"] as f64);
}

/// A floor printed as `text` (without its value), as an integer.
fn floor(facts: &FactSet, text: &str) -> Option<u64> {
    facts.floors().find(|f| f.kind.to_string() == text).and_then(|f| f.value.as_int())
}

/// A runtime filter only drops rows without a partner, so a scan it pruned
/// has at most its table's rows, and so does an inner join over it: each
/// gives a floor. The padded side of an outer join gains rows when pruned:
/// above it, the rows are no longer among the context's.
#[tokio::test]
async fn pruned_rows_give_floors() {
    let p = plan("join_filtered").await;
    let facts = derive_facts(&[p]);
    assert_eq!(floor(&facts, "|orders|"), Some(14860), "{facts}");

    let catalog = catalog().await;
    let scan = |table: &str, cols: Value, rows, dynamic: Option<&str>| {
        let mut info = json!({"Table": format!("tpch.main.{table}"), "Projections": cols});
        if let Some(d) = dynamic {
            info["Dynamic Filters"] = json!(d);
        }
        node("TABLE_SCAN", rows, info, vec![])
    };
    let pruned = scan("partsupp", json!(["ps_suppkey", "ps_partkey", "ps_availqty"]), 900, Some("optional: ps_partkey>=1 AND optional: ps_partkey<=100"));
    let left = node(
        "HASH_JOIN",
        950,
        json!({"Join Type": "LEFT", "Conditions": "s_suppkey = ps_suppkey"}),
        vec![scan("supplier", json!(["s_suppkey"]), 100, None), pruned],
    );
    let unmatched = node("FILTER", 50, json!({"Expression": "(ps_availqty IS NULL)"}), vec![left]);
    let top = node(
        "HASH_JOIN",
        10,
        json!({"Join Type": "INNER", "Conditions": "ps_partkey = p_partkey"}),
        vec![unmatched, scan("part", json!(["p_partkey"]), 100, None)],
    );
    let facts = derive_facts(&[from_duckdb(&catalog, "padded", &top.to_string(), None).unwrap()]);
    assert_eq!(floor(&facts, "|partsupp|"), Some(900), "{facts}");
    assert!(!facts.floors().any(|f| f.kind.to_string().contains("Left join")), "{facts}");
}

/// A runtime filter drops no row with a partner, so a scan it pruned holds
/// every row of its table satisfying it: the rows bound that many. A bloom
/// filter beside it gives no bound: DuckDB 1.5.0 pushes it before it is
/// filled. Its join's build side has at least as many distinct keys as an
/// IN list has values, and at most one more (NULL).
#[tokio::test]
async fn runtime_filters_give_upper_bounds() {
    let catalog = catalog().await;
    let scan = |table: &str, cols: Value, rows, dynamic: Option<&str>| {
        let mut info = json!({"Table": format!("tpch.main.{table}"), "Projections": cols});
        if let Some(d) = dynamic {
            info["Dynamic Filters"] = json!(d);
        }
        node("TABLE_SCAN", rows, info, vec![])
    };
    let joined = |dynamic: &str| {
        let probe = scan("customer", json!(["c_custkey", "c_nationkey"]), 300, Some(dynamic));
        let join = node(
            "HASH_JOIN",
            290,
            json!({"Join Type": "INNER", "Conditions": "c_nationkey = n_nationkey"}),
            vec![probe, scan("nation", json!(["n_nationkey"]), 5, None)],
        );
        derive_facts(&[from_duckdb(&catalog, "dynamic", &join.to_string(), None).unwrap()])
    };

    let range = joined("optional: c_nationkey>=8 AND optional: c_nationkey<=21");
    assert_eq!(bound(&range, "|customer where customer.c_nationkey <= 21 and customer.c_nationkey >= 8|"), 300);
    assert_eq!(floor(&range, "|customer|"), Some(300));
    assert_eq!(bound(&range, "ndv(nation.n_nationkey | nation)"), 15);

    let listed = joined("optional: c_nationkey IN (8, 9, 12, 18, 21) AND optional: c_nationkey>=8 AND optional: c_nationkey<=21");
    let ndv = "ndv(nation.n_nationkey | nation)";
    assert_eq!(bound(&listed, ndv), 6, "{listed}");
    assert_eq!(floor(&listed, ndv), Some(5), "{listed}");
    assert!(listed.bounds().any(|b| b.kind.to_string().contains("customer.c_nationkey = 12") && b.value == Ratio::int(300)), "{listed}");

    let single = joined("c_nationkey=7");
    assert_eq!(bound(&single, "|customer where customer.c_nationkey = 7|"), 300);
    assert_eq!(bound(&single, ndv), 2);

    let bloom = joined("optional: c_nationkey>=8 AND optional: c_nationkey<=21 AND optional: c_nationkey IN BF(n_nationkey)");
    assert!(!bloom.bounds().any(|b| b.kind.to_string().contains("customer")), "{bloom}");
    assert_eq!(floor(&bloom, "|customer|"), Some(300));
}

/// A required filter pushed into a scan gives a fact on its table. An
/// optional one gives only a bound, until a filter above checks it: then
/// the filter's rows give the fact on the table it was pushed into.
#[tokio::test]
async fn pushed_filters() {
    let catalog = catalog().await;
    let scan = |filters: Value, rows| {
        let info = json!({"Table": "tpch.main.lineitem", "Projections": ["l_shipmode"], "Filters": filters});
        node("TABLE_SCAN", rows, info, vec![])
    };
    let read = |plan: Value| derive_facts(&[from_duckdb(&catalog, "pushed", &plan.to_string(), None).unwrap()]);

    let facts = read(scan(json!(["l_quantity<10.00"]), 10816));
    assert_eq!(value(&facts, "|lineitem where lineitem.l_quantity < 10.00|"), 10816.0);

    let optional = || scan(json!(["optional: l_shipmode IN ('AIR', 'AIR REG')", "l_shipinstruct='DELIVER IN PERSON'"]), 15023);
    let both = "|lineitem where lineitem.l_shipinstruct = 'DELIVER IN PERSON' and \
                (lineitem.l_shipmode = 'AIR REG' OR lineitem.l_shipmode = 'AIR')|";
    assert_eq!(bound(&read(optional()), both), 15023);
    let checked = node("FILTER", 2033, json!({"Expression": "((l_shipmode = 'AIR') OR (l_shipmode = 'AIR REG'))"}), vec![optional()]);
    assert_eq!(value(&read(checked), both), 2033.0);
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
    // EXISTS decorrelated to read as the semi join a query would write.
    let exists = "|orders where exists[lineitem.l_orderkey = orders.o_orderkey](lineitem where lineitem.l_quantity > 49.00)|";
    assert_eq!(value(&facts, exists), e["orders semi lineitem>49"] as f64);
    let anti = "|orders where not exists[lineitem.l_orderkey = orders.o_orderkey](lineitem where lineitem.l_quantity > 49.00)|";
    assert_eq!(value(&facts, anti), e["orders anti lineitem>49"] as f64);
    let not_in = "|part where not in[\"part\".p_partkey = partsupp.ps_partkey](partsupp where partsupp.ps_availqty < 100)|";
    assert_eq!(value(&facts, not_in), e["part not in partsupp<100"] as f64);
    // The share of the kept side with a partner.
    let semi = "m(lineitem.l_orderkey = orders.o_orderkey | orders ⋉ lineitem where lineitem.l_quantity > 49.00)";
    assert_eq!(value(&facts, semi), ratio(e["orders semi lineitem>49"], e["orders"]));
    let semi_in = "m(\"part\".p_partkey = partsupp.ps_partkey | part ⋉ partsupp where partsupp.ps_availqty < 100)";
    assert_eq!(value(&facts, semi_in), ratio(e["part semi partsupp<100"], 2000));
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
    // that filtered above the join, and from the one that pushed the
    // filters into its scans.
    let left = starting(
        &facts,
        "|Left join[customer.c_custkey = orders.o_custkey](customer, orders where orders.o_totalprice > 300000.00) \
         where customer.c_acctbal > 5000.00|",
    );
    assert_eq!(left.value.as_int(), Some(e["customer⟕orders>300000|acctbal>5000"]));
    assert!(observed(left, "full_one_side") && observed(left, "left_preserved"), "{:?}", left.origins);
    assert!(!facts.bounds().any(|b| b.kind.to_string().contains("Left join")), "{facts}");

    // A filter rejecting the NULLs of the other side leaves the inner join.
    let inner = "|customer × orders where customer.c_custkey <= 1499 and customer.c_custkey = orders.o_custkey \
                 and orders.o_totalprice > 300000.00|";
    assert_eq!(value(&facts, inner), e["customer⋈orders|price>300000"] as f64);

    // HAVING on a grouping key filters the rows grouped.
    let groups = "ndv(lineitem.l_suppkey | lineitem where lineitem.l_suppkey < 50)";
    assert_eq!(value(&facts, groups), e["ndv(l_suppkey|lineitem,l_suppkey<50)"] as f64);
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
    let vouched = from_duckdb(&catalog, "ok", &join("select * from orders, customer where o_custkey = c_custkey"), None).unwrap();
    assert!(matches!(states(&vouched)[2], State::Clean(_)));
    let wrong = from_duckdb(&catalog, "wrong", &join("select * from orders, customer where o_orderkey = c_custkey"), None).unwrap();
    assert!(matches!(states(&wrong)[2], State::Tainted(_)), "{:?}", states(&wrong)[2]);
}

/// A query passed in vouches in place of the profile's own text: here a
/// `CREATE TABLE AS` over a view, which does not compare what it joins.
#[tokio::test]
async fn query_passed_in() {
    let catalog = catalog().await;
    let scan = |table: &str, cols: Vec<&str>, rows| {
        node("TABLE_SCAN", rows, json!({"Table": format!("tpch.main.{table}"), "Projections": cols}), vec![])
    };
    let mut j = node(
        "HASH_JOIN",
        100,
        json!({"Join Type": "INNER", "Conditions": "o_custkey = c_custkey"}),
        vec![scan("orders", vec!["o_custkey"], 15000), scan("customer", vec!["c_custkey"], 1500)],
    );
    j["query_name"] = json!("CREATE TABLE t AS SELECT * FROM v");
    let json = j.to_string();
    let own = from_duckdb(&catalog, "own", &json, None).unwrap();
    assert!(matches!(states(&own)[2], State::Tainted(_)), "{:?}", states(&own)[2]);
    let sql = "select * from orders join customer on o_custkey = c_custkey";
    let passed = from_duckdb(&catalog, "passed", &json, Some(sql)).unwrap();
    assert!(matches!(states(&passed)[2], State::Clean(_)), "{:?}", states(&passed)[2]);
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
    let price = starting(&f, "|lineitem@1 × aggregate(");
    assert_eq!(price.value.as_int(), Some(e["price>avg"]));

    let f = one("alias").await;
    let years = starting(&f, "ndv(date_part(");
    assert_eq!(years.value.as_int(), Some(e["ndv(year|orders,price>100000)"]));
}

/// Facts written as JSON read back as they were: each by the same kind,
/// with its value and origins, and so the same JSON again.
#[tokio::test]
async fn round_trip() {
    let mut all = vec![];
    for dir in ["extra", "tpch"] {
        all.extend(plans(dir).await);
    }
    for dir in ["extra", "tpch", "indexed", "parallel", "v14"] {
        all.extend(pg_plans(dir).await);
    }
    for p in &all {
        let set = derive_facts(std::slice::from_ref(p));
        let text = serde_json::to_string(&set).unwrap();
        let read: FactSet = serde_json::from_str(&text).unwrap();
        assert_eq!(serde_json::to_string(&read).unwrap(), text, "{}", p.name);
        assert_eq!(read.to_string(), set.to_string(), "{}", p.name);
        for f in set.iter() {
            let r = read.get(&f.kind).unwrap_or_else(|| panic!("{}: no {f}", p.name));
            assert_eq!((r.value, &r.origins), (f.value, &f.origins), "{}: {f}", p.name);
        }
        for b in set.bounds() {
            assert_eq!(read.bound(&b.kind).map(|r| r.value), Some(b.value), "{}: {}", p.name, b.kind);
        }
        for f in set.floors() {
            assert_eq!(read.floor(&f.kind).map(|r| r.value), Some(f.value), "{}: {}", p.name, f.kind);
        }
        for v in set.values() {
            assert_eq!(read.value(&v.name), Some(v), "{}: {}", p.name, v.name);
        }
        assert!(read.unobserved().eq(set.unobserved()), "{}", p.name);
    }
}

#[test]
fn ratio_reads_reduced() {
    let r: Ratio = serde_json::from_value(json!({"num": 4, "den": 6})).unwrap();
    assert_eq!((r.num(), r.den()), (2, 3));
    assert!(serde_json::from_value::<Ratio>(json!({"num": 1, "den": 0})).is_err());
}

/// A column passed on under its own name, as an unparsed query does at
/// every level, leaves the alias naming what the level below defines.
#[tokio::test]
async fn aliases_passed_on() {
    let catalog = catalog().await;
    let sql = "select q.twice as twice from (select l_quantity * 2 as twice from lineitem) q";
    let q = cardinal::observed::QueryText::parse(&catalog, sql).unwrap();
    assert_eq!(q.alias("twice"), Some("l_quantity * 2"));
    // A real rename still names two expressions, and so neither.
    let sql = "select q.other as twice from (select l_quantity * 2 as twice, l_tax as other from lineitem) q";
    let q = cardinal::observed::QueryText::parse(&catalog, sql).unwrap();
    assert_eq!(q.alias("twice"), None);
}

/// An alias over a table the query reads more than once names its
/// expression where each definition reads the one instance in its own
/// `SELECT`, as each level of an unparsed query does; not where one
/// `SELECT` reads both.
#[tokio::test]
async fn aliases_over_one_instance() {
    let catalog = catalog().await;
    let sql = "select x.d, y.d from (select l1.l_quantity * 2 as d, l1.l_orderkey as k from lineitem l1) x \
               join (select l2.l_quantity * 2 as d, l2.l_orderkey as k from lineitem l2) y on x.k = y.k";
    let q = cardinal::observed::QueryText::parse(&catalog, sql).unwrap();
    assert_eq!(q.alias("d"), Some("l_quantity * 2"));
    let sql = "select l1.l_quantity * 2 as d from lineitem l1, lineitem l2 where l1.l_orderkey = l2.l_orderkey";
    let q = cardinal::observed::QueryText::parse(&catalog, sql).unwrap();
    assert_eq!(q.alias("d"), None);
}

/// A projection renaming a compressed column keeps it bijective, so a
/// grouping on it reads.
#[tokio::test]
async fn renamed_compressed_key() {
    let catalog = catalog().await;
    let scan = node("TABLE_SCAN", 15000, json!({"Table": "tpch.main.orders", "Projections": ["o_orderpriority"]}), vec![]);
    let compressed = node("PROJECTION", 15000, json!({"Projections": ["__internal_compress_string_uhugeint(#0)"]}), vec![scan]);
    let renamed = node("PROJECTION", 15000, json!({"Projections": ["priority"]}), vec![compressed]);
    let group = node("HASH_GROUP_BY", 5, json!({"Groups": ["#0"], "Aggregates": ["count_star()"]}), vec![renamed]);
    let sql = "select \"o_orderpriority\" as priority, count(*) from orders group by 1";
    let p = from_duckdb(&catalog, "renamed", &group.to_string(), Some(sql)).unwrap();
    let at = p.nodes.iter().position(|n| n.engine_op == "HASH_GROUP_BY").unwrap();
    assert!(matches!(states(&p)[at], State::Clean(_)), "{:?}", states(&p)[at]);
    let facts = derive_facts(&[p]);
    assert_eq!(starting(&facts, "ndv(orders.o_orderpriority | orders)").value.as_int(), Some(5));
}
