//! DuckDB `EXPLAIN ANALYZE` profiles of TPC-H at scale factor 0.01, read
//! and used as reference plans ([`cardinal::Builder::with_plans`]): which
//! operators' counts are pinned, and that the pins agree with the
//! constraints and the truth. Regenerate the fixtures with
//! `scripts/duckdb_fixtures.sh`.

mod fixtures;

use cardinal::facts::{Ratio, State, states};
use cardinal::observed::{ObservedPlan, from_duckdb};
use cardinal::{Analysis, Options};
use fixtures::{DIR, catalog, foreign_keys, plans};
use serde_json::{Value, json};

async fn plan(name: &str) -> ObservedPlan {
    let catalog = catalog().await;
    from_duckdb(&catalog, name, &std::fs::read_to_string(format!("{DIR}/extra/{name}.json")).unwrap(), None).unwrap()
}

/// Each pin `query` with `references` gets, as `(operator, claim)`: e.g.
/// `("limit#3 TABLE_SCAN", "observed floor >= 100")`.
async fn pins(query: &ObservedPlan, references: &[&ObservedPlan]) -> Vec<(String, String)> {
    let catalog = catalog().await;
    let options = Options { trace: true, foreign_keys: foreign_keys(), ..Default::default() };
    let a = Analysis::plan(&catalog, query).options(options).with_plans(references.iter().copied()).build().unwrap();
    let t = a.trace.unwrap();
    t.constraints
        .iter()
        .filter_map(|c| c.fact.as_ref())
        .filter(|f| f.source.starts_with("observed"))
        .map(|f| (f.facts[0].text.trim_matches('|').to_string(), format!("{} {}", f.source, f.value)))
        .collect()
}

#[tokio::test]
async fn every_fixture_converts() {
    for dir in ["extra", "tpch"] {
        for p in plans(dir).await {
            assert!(!p.nodes.is_empty(), "{}", p.name);
        }
    }
}

/// A DuckDB profile node.
fn node(op: &str, rows: u64, info: Value, children: Vec<Value>) -> Value {
    json!({"operator_type": op, "operator_cardinality": rows, "extra_info": info, "children": children})
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

fn pin(op: &str, claim: &str) -> (String, String) {
    (op.to_string(), claim.to_string())
}

/// Each fixture with its own profile as a reference plan: every operator
/// it counted is pinned, and the bounds hold the true count, most exactly. A pin naming
/// other rows than the engine counted contradicts the constraints, and the
/// bounds then hold nothing in particular.
#[tokio::test]
async fn own_profile_pins_the_truth() {
    let catalog = catalog().await;
    let options = Options { foreign_keys: foreign_keys(), ..Default::default() };
    let (mut failures, mut exact, mut all) = (vec![], 0, 0);
    for dir in ["extra", "tpch"] {
        for p in plans(dir).await {
            let b = Analysis::plan(&catalog, &p).options(options.clone()).with_plans([&p]).build().unwrap().bounds().unwrap();
            let truth = p.nodes[p.root].rows;
            all += 1;
            exact += usize::from(b.lower == truth && b.upper == Some(truth));
            if !b.holds(truth) {
                failures.push(format!("{dir}/{}: {b}, not {truth}", p.name));
            }
        }
    }
    // Not every root's rows have a context to equal the query's by (a
    // `LIMIT`'s), nor is every bound proven tight.
    println!("{exact} of {all} exact");
    assert!(failures.is_empty(), "{failures:#?}");
    assert!(exact * 4 >= all * 3, "only {exact} of {all} exact");
}

/// What may not have run to completion is not pinned: the scan below a
/// `LIMIT` stopped early.
#[tokio::test]
async fn what_stops_early_is_not_pinned() {
    let p = plan("limit").await;
    let pins = pins(&p, &[&p]).await;
    assert!(!pins.iter().any(|(op, _)| op.starts_with("limit#0 ")), "{pins:?}");
    assert!(pins.contains(&pin("limit#1 STREAMING_LIMIT", "observed rows = 5")), "{pins:?}");
}

/// A runtime filter only drops rows without a partner: the scan it pruned
/// had at least its count, and the join above it exactly its own.
#[tokio::test]
async fn pruned_rows_are_a_floor() {
    let p = plan("join_filtered").await;
    let pins = pins(&p, &[&p]).await;
    assert!(pins.contains(&pin("join_filtered#0 TABLE_SCAN", "observed floor >= 14860")), "{pins:?}");
    assert!(pins.contains(&pin("join_filtered#3 HASH_JOIN", "observed rows = 3706")), "{pins:?}");
}

/// Of a reference plan, only what scans the query's tables, or those they
/// reference, is analyzed: `lineitem` references `orders`, not back.
#[tokio::test]
async fn plans_over_other_tables_are_left_out() {
    let (orders, lineitem) = (plan("join_filtered").await, plan("limit").await);
    let pins = pins(&orders, &[&lineitem]).await;
    assert!(pins.is_empty(), "{pins:?}");
    let pins = self::pins(&lineitem, &[&orders]).await;
    assert!(pins.contains(&pin("join_filtered#3 HASH_JOIN", "observed rows = 3706")), "{pins:?}");
}
