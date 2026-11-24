//! Snowflake operator stats (`GET_QUERY_OPERATOR_STATS`) of TPC-H at scale
//! factor 0.01, read and used as reference plans
//! ([`cardinal::Builder::with_plans`]): which operators are counted, and
//! that their pins agree with the constraints and the truth. Regenerate the
//! fixtures with `scripts/snowflake_fixtures.sh`; `sf1/` holds a few at scale
//! factor 1, from `cardinal-eval/prepare/engines_tpch.sh`.

mod fixtures;

use cardinal::observed::{ObservedPlan, Op, from_snowflake, from_snowflake_explain, from_snowflake_plan};
use datafusion::common::JoinType;
use snowflake_explain::{QueryPlan, rows_from_json};
use cardinal::{Analysis, Options};
use fixtures::{SF_DIR, catalog, foreign_keys, sf_plans, sf_query};

async fn plan(dir: &str, name: &str) -> ObservedPlan {
    let json = std::fs::read_to_string(format!("{SF_DIR}/{dir}/{name}.json")).unwrap();
    from_snowflake(&catalog().await, name, &json, Some(&sf_query(name))).unwrap()
}

#[tokio::test]
async fn every_fixture_converts() {
    for dir in ["tpch", "extra"] {
        for p in sf_plans(dir).await {
            assert!(!p.nodes.is_empty(), "{}", p.name);
            assert!(p.nodes[p.root].counted, "{dir}/{}: its output is not counted\n{p}", p.name);
        }
    }
}

/// Each fixture with its own profile as a reference plan: every operator
/// it counted is pinned, and the bounds hold the true count. A pin naming
/// other rows than the engine counted contradicts the constraints, and the
/// bounds then hold nothing in particular.
#[tokio::test]
async fn own_profile_pins_the_truth() {
    let catalog = catalog().await;
    let options = Options { foreign_keys: foreign_keys(), ..Default::default() };
    let (mut failures, mut exact, mut all, mut loose) = (vec![], 0, 0, vec![]);
    for dir in ["tpch", "extra"] {
        for p in sf_plans(dir).await {
            let b = Analysis::plan(&catalog, &p).options(options.clone()).with_plans([&p]).build().unwrap().bounds().unwrap();
            let truth = p.nodes[p.root].rows;
            all += 1;
            if b.lower == truth && b.upper == Some(truth) {
                exact += 1;
            } else {
                loose.push(format!("{dir}/{}: {b}, truth {truth}", p.name));
            }
            if !b.holds(truth) {
                failures.push(format!("{dir}/{}: {b}, not {truth}", p.name));
            }
        }
    }
    println!("{exact} of {all} exact; not:\n{}", loose.join("\n"));
    assert!(failures.is_empty(), "{failures:#?}");
    assert!(exact * 4 >= all * 3, "only {exact} of {all} exact");
}

/// The operators of `plan` that Snowflake names `engine_op`.
fn operators<'p>(plan: &'p ObservedPlan, engine_op: &str) -> Vec<(usize, &'p cardinal::observed::ONode)> {
    plan.nodes.iter().enumerate().filter(|(_, n)| n.engine_op == engine_op).collect()
}

/// Operator stats rows, a `QueryPlan` made of them (as a value, or JSON),
/// and `EXPLAIN USING JSON` all read; an estimated plan counts nothing.
#[tokio::test]
async fn inputs() {
    let catalog = catalog().await;
    let rows = std::fs::read_to_string(format!("{SF_DIR}/tpch/q03.json")).unwrap();
    let sql = sf_query("q03");
    let from_rows = from_snowflake(&catalog, "q03", &rows, Some(&sql)).unwrap();
    let plan = QueryPlan::from_rows(rows_from_json(&rows).unwrap()).unwrap();
    let from_json = from_snowflake(&catalog, "q03", &serde_json::to_string(&plan).unwrap(), Some(&sql)).unwrap();
    let from_value = from_snowflake_plan(&catalog, "q03", &plan, Some(&sql), true).unwrap();
    assert_eq!(from_rows.to_string(), from_json.to_string());
    assert_eq!(from_rows.to_string(), from_value.to_string());
    let explain = std::fs::read_to_string(format!("{SF_DIR}/explain/q03.json")).unwrap();
    assert!(from_snowflake(&catalog, "q03", &explain, Some(&sql)).is_err());
    for (name, json) in fixtures::sf_fixtures("explain") {
        let p = from_snowflake_explain(&catalog, &name, &json, Some(&sf_query(&name))).unwrap();
        assert!(!p.counted && p.nodes.iter().all(|n| !n.counted && n.rows == 0), "{name}");
    }
}

/// A join's first input is its build side, and the one its type names: a
/// `LEFT OUTER` join keeping it reads as a right join of the probe side to
/// it. Which side a semi or anti join keeps is told by the bloom filter on
/// the other, or the counts, or the columns read above.
#[tokio::test]
async fn join_sides() {
    let kind = |p: &ObservedPlan| -> Vec<JoinType> {
        p.nodes.iter().filter_map(|n| match &n.op {
            Op::Join { kind, .. } => Some(*kind),
            _ => None,
        }).collect()
    };
    // customer LEFT JOIN orders: customer, the build side, kept.
    assert_eq!(kind(&plan("tpch", "q13").await), [JoinType::Right]);
    // NOT EXISTS keeps the build side, which the bloom filter is not on.
    assert_eq!(kind(&plan("extra", "anti_exists").await), [JoinType::RightAnti]);
    // NOT IN keeps the probe side, null-aware: a filter on a mark join.
    let p = plan("extra", "not_in").await;
    assert_eq!(kind(&p), [JoinType::LeftMark], "{p}");
    assert!(p.nodes.iter().any(|n| matches!(n.op, Op::MarkFilter { negated: true })), "{p}");
    // EXISTS under count(*), with as many rows on each side as out: not told.
    let p = plan("extra", "semi_join").await;
    assert!(kind(&p).is_empty() && operators(&p, "Join").iter().all(|(_, n)| matches!(n.op, Op::Other)), "{p}");
}

/// A scan under a `JoinFilter` may be pruned by the build side of any join
/// above on its columns: TPC-H q08's customers, by the join to orders the
/// filter names, and by the join to the nations of the region.
#[tokio::test]
async fn bloom_filters() {
    let p = plan("tpch", "q08").await;
    let [(_, customer)] = p.nodes.iter().enumerate().filter(|(_, n)| matches!(&n.op, Op::Scan { table, .. } if table == "customer")).collect::<Vec<_>>()[..] else { panic!("{p}") };
    let Op::Scan { instance, runtime_filters, .. } = &customer.op else { unreachable!() };
    let mut columns: Vec<String> = runtime_filters.iter().map(|r| r.column.clone().unwrap()).collect();
    columns.sort();
    assert_eq!(columns, [format!("{instance}.c_custkey"), format!("{instance}.c_nationkey")]);
    // A scan under no JoinFilter is not pruned.
    let nation = operators(&p, "TableScan").into_iter().filter(|(_, n)| matches!(&n.op, Op::Scan { table, .. } if table == "nation")).collect::<Vec<_>>();
    assert!(nation.iter().any(|(_, n)| matches!(&n.op, Op::Scan { runtime_filters, .. } if runtime_filters.is_empty())), "{p}");
}

/// Snowflake prunes what cannot be in a top-n's rows (TPC-H q18's groups by
/// `o_totalprice`): nothing below one is counted, but its own count is.
#[tokio::test]
async fn top_k_pruning() {
    let p = plan("tpch", "q18").await;
    let [(top, n)] = operators(&p, "SortWithLimit")[..] else { panic!("{p}") };
    assert!(n.counted && top == p.root);
    assert!(p.nodes.iter().enumerate().all(|(i, n)| i == top || !n.counted), "{p}");
    let catalog = catalog().await;
    let options = Options { foreign_keys: foreign_keys(), ..Default::default() };
    let b = Analysis::plan(&catalog, &p).options(options).with_plans([&p]).build().unwrap().bounds().unwrap();
    assert!(b.lower == 100 && b.upper == Some(100), "{b}");
}

/// Snowflake prints IN lists `x IN 'a' IN 'b'`, and its own functions.
#[tokio::test]
async fn expressions() {
    let p = plan("tpch", "q19").await;
    let filters: Vec<String> = p.nodes.iter().filter_map(|n| match &n.op {
        Op::Filter { predicate } => Some(predicate.iter().map(|p| p.expr.as_ref().map_or("?".to_string(), |e| e.to_string())).collect::<Vec<_>>().join(" AND ")),
        _ => None,
    }).collect();
    // A short list, simplified to equalities.
    assert!(filters.iter().any(|f| f.contains("l_shipmode = Utf8(\"AIR\") OR lineitem#2.l_shipmode = Utf8(\"AIR REG\")")), "{filters:#?}");
    assert!(filters.iter().any(|f| f.contains("p_container IN ([Utf8(\"SM CASE\"), ")), "{filters:#?}");
    let p = plan("tpch", "q01").await;
    let [(_, scan)] = operators(&p, "TableScan")[..] else { panic!("{p}") };
    let Op::Scan { filters, .. } = &scan.op else { unreachable!() };
    assert_eq!(filters.iter().map(|f| f.expr.as_ref().unwrap().to_string()).collect::<Vec<_>>(), [format!("{}.l_shipdate <= Date32(\"1998-09-02\")", p.nodes.iter().find_map(|n| match &n.op { Op::Scan { instance, .. } => Some(instance.clone()), _ => None }).unwrap())]);
}


/// At scale factor 1, Snowflake aggregates in phases on several workers:
/// below the aggregate that completes them, q04's aggregate outputs a group
/// per worker (40 rows for 5 priorities), and q12's eager aggregate below
/// its join passes rows through (30,988 rows for 29,999 groups). Each is
/// read as its input, what lies between is not counted, and the bounds hold
/// the truth.
#[tokio::test]
async fn partial_aggregates() {
    let catalog = catalog().await;
    let options = Options { foreign_keys: foreign_keys(), ..Default::default() };
    for (name, aggregates) in [("q04", 1), ("q12", 1), ("q19", 1)] {
        let p = plan("sf1", name).await;
        assert_eq!(operators(&p, "Aggregate").len(), aggregates, "{p}");
        assert!(p.nodes[p.root].counted, "{p}");
        let b = Analysis::plan(&catalog, &p).options(options.clone()).with_plans([&p]).build().unwrap().bounds().unwrap();
        let truth = p.nodes[p.root].rows;
        assert!(b.holds(truth) && b.lower == truth, "{name}: {b}, truth {truth}");
    }
}
