//! Reference plans put in place: each fixture query analyzed as DataFusion
//! plans it, and as DuckDB planned it (read from its profile), with
//! DuckDB's profiles of the same queries as reference plans
//! ([`cardinal::Builder::with_plans`]). Print the bounds before and after,
//! with
//!
//! ```sh
//! cargo test --release --test reference_bounds print_bounds -- --ignored --nocapture   # ONLY=q01,q03 for some
//! ```
//!
//! A query with every other query's plan takes seconds to analyze, so the
//! tests over every query with every other's plans are ignored by default
//! (tens of minutes, in parallel); the others use the query's own plan.
//! `tests/duckdb/t3` holds more shapes, bounded only with their own plan.

mod fixtures;

use cardinal::observed::{Catalog, ObservedPlan};
use cardinal::{Analysis, Bounds, Options};
use datafusion::prelude::SessionContext;
use fixtures::{DIR, catalog, context, foreign_keys, plans, query};

/// A fixture query, and its profile.
struct Case {
    name: String,
    sql: String,
    plan: ObservedPlan,
}

impl Case {
    /// The query's true row count.
    fn rows(&self) -> u64 {
        self.plan.nodes[self.plan.root].rows
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Planner {
    DataFusion,
    DuckDb,
}

const PLANNERS: [Planner; 2] = [Planner::DataFusion, Planner::DuckDb];

/// Every fixture, and what they are analyzed against.
struct Fixtures {
    cases: Vec<Case>,
    ctx: SessionContext,
    catalog: Catalog,
}

async fn fixtures() -> Fixtures {
    let mut cases = vec![];
    for dir in ["extra", "tpch"] {
        for plan in plans(dir).await {
            cases.push(Case { name: plan.name.clone(), sql: query(dir, &plan.name), plan });
        }
    }
    Fixtures { cases, ctx: context(), catalog: catalog().await }
}

fn options() -> Options {
    Options { foreign_keys: foreign_keys(), ..Default::default() }
}

impl Fixtures {
    fn case(&self, name: &str) -> &Case {
        self.cases.iter().find(|c| c.name == name).unwrap()
    }

    /// Every profile, or with `except`, every other one.
    fn profiles(&self, except: Option<&str>) -> Vec<&ObservedPlan> {
        self.cases.iter().filter(|c| Some(c.name.as_str()) != except).map(|c| &c.plan).collect()
    }

    /// `c` as `planner` plans it, with `references`; `None` where
    /// DataFusion cannot plan it (it has no `AS MATERIALIZED`).
    async fn analyze(&self, c: &Case, planner: Planner, references: &[&ObservedPlan]) -> Option<Analysis> {
        let query = match planner {
            Planner::DataFusion => Analysis::sql(&self.ctx, &c.sql).await.ok()?,
            Planner::DuckDb => Analysis::plan(&self.catalog, &c.plan),
        };
        Some(query.options(options()).with_plans(references.iter().copied()).build().unwrap())
    }

    async fn bounds(&self, c: &Case, planner: Planner, references: &[&ObservedPlan]) -> Option<Bounds> {
        Some(self.analyze(c, planner, references).await?.bounds().unwrap())
    }
}

/// Each fixture's bounds with its own plan, `[lower, upper]`, as DataFusion
/// plans it (`None` where it cannot) and as DuckDB did. Link relates the
/// query's operators to the plan's, so most are exact. Update a bound that
/// tightens; none may loosen.
#[allow(clippy::type_complexity)]
const OWN: &[(&str, Option<(u64, Option<u64>)>, (u64, Option<u64>))] = &[
    ("alias", Some((7, Some(7))), (7, Some(7))),
    ("anti_exists", Some((1, Some(1))), (1, Some(1))),
    ("cte", None, (1, Some(1))),
    ("distinct", Some((125, Some(125))), (125, Some(125))),
    ("full_one_side", Some((0, Some(16499))), (715, Some(715))),
    ("group_base", Some((100, Some(100))), (100, Some(100))),
    ("group_key_filter", Some((25, Some(25))), (25, Some(25))),
    ("group_over_filter", Some((100, Some(100))), (100, Some(100))),
    ("having", Some((838, Some(838))), (838, Some(838))),
    ("in_subquery", Some((1, Some(1))), (1, Some(1))),
    ("join_filtered", Some((5, None)), (5, Some(5))),
    ("left_chain", Some((322, Some(322))), (322, Some(322))),
    ("left_preserved", Some((715, Some(715))), (715, Some(715))),
    ("left_rejected", Some((532, None)), (532, Some(532))),
    ("limit", Some((5, Some(5))), (0, Some(5))),
    ("not_exists", Some((1, Some(1))), (1, Some(1))),
    ("not_in", Some((1, Some(1))), (1, Some(1))),
    ("project_filter", Some((0, None)), (0, Some(10816))),
    ("same_pred_two_inputs", Some((1, Some(1))), (1, Some(1))),
    ("scalar_subquery", Some((1, Some(1))), (1, Some(1))),
    ("scan_filter", Some((10816, Some(10816))), (10816, Some(10816))),
    ("self_join", Some((1, Some(1))), (1, Some(1))),
    ("semi_in", Some((1, Some(1))), (1, Some(1))),
    ("semi_join", Some((1, Some(1))), (1, Some(1))),
    ("q01", Some((4, Some(4))), (4, Some(4))),
    ("q02", Some((0, Some(5))), (4, Some(4))),
    ("q03", Some((10, Some(10))), (10, Some(10))),
    ("q04", Some((0, Some(582))), (5, Some(5))),
    ("q05", Some((5, None)), (5, Some(5))),
    ("q06", Some((1, Some(1))), (1, Some(1))),
    ("q07", Some((4, Some(8))), (4, Some(4))),
    ("q08", Some((2, Some(2))), (2, Some(2))),
    ("q09", Some((173, Some(173))), (173, Some(173))),
    ("q10", Some((20, Some(20))), (20, Some(20))),
    ("q11", Some((0, Some(374))), (359, Some(359))),
    ("q12", Some((2, Some(2))), (2, Some(2))),
    ("q13", Some((1, Some(1500))), (1, Some(1500))),
    ("q14", Some((1, Some(1))), (1, Some(1))),
    ("q15", Some((0, Some(100))), (0, Some(100))),
    ("q16", Some((296, Some(296))), (296, Some(296))),
    ("q17", Some((1, Some(1))), (1, Some(1))),
    ("q18", Some((0, Some(100))), (100, Some(100))),
    ("q19", Some((1, Some(1))), (1, Some(1))),
    ("q20", Some((0, Some(3))), (0, Some(3))),
    ("q21", Some((0, Some(1))), (0, Some(1))),
    ("q22", Some((0, Some(7))), (7, Some(7))),
    ("e04_group_small", Some((4, Some(4))), (4, Some(4))),
    ("e06_limit", Some((0, Some(25))), (0, Some(25))),
    ("h06_nested_agg", Some((1, Some(1000))), (1, Some(1000))),
    ("h07_cte_twice", Some((0, Some(15000))), (0, Some(15000))),
    ("h10_full_join", Some((464, Some(464))), (464, Some(464))),
    ("h11_q18_like", Some((0, Some(60175))), (67, Some(67))),
    ("m03_exists", Some((0, Some(15000))), (13773, Some(13773))),
    ("m05_in_sub", Some((83, Some(83))), (83, Some(83))),
    ("m06_left_join", Some((3597, Some(3597))), (3597, Some(3597))),
    ("m07_distinct", Some((403, Some(403))), (403, Some(403))),
    ("m08_having", Some((217, Some(217))), (217, Some(217))),
];

/// The `tests/duckdb/t3` fixtures, read with their queries' text.
async fn t3() -> Vec<Case> {
    let catalog = catalog().await;
    fixtures::fixtures("t3")
        .into_iter()
        .map(|(name, json)| {
            let sql = query("t3", &name);
            let plan = cardinal::observed::from_duckdb(&catalog, &name, &json, Some(&sql)).unwrap();
            Case { name, sql, plan }
        })
        .collect()
}

/// With its own plan, each fixture's bounds are those of [`OWN`].
#[tokio::test]
async fn own_plan_bounds() {
    let mut f = fixtures().await;
    f.cases.extend(t3().await);
    assert_eq!(f.cases.len(), OWN.len(), "a fixture in {DIR} without its bounds in OWN");
    let bounds = |b: Option<Bounds>| b.map(|b| (b.lower, b.upper));
    let mut differ = vec![];
    for (name, df, duck) in OWN {
        let c = f.case(name);
        let got = (bounds(f.bounds(c, Planner::DataFusion, &[&c.plan]).await), bounds(f.bounds(c, Planner::DuckDb, &[&c.plan]).await));
        if got != (*df, Some(*duck)) {
            differ.push(format!("{name}: {got:?}, not {:?}", (df, duck)));
        }
    }
    assert!(differ.is_empty(), "{differ:#?}");
}

#[tokio::test]
#[ignore = "slow: tens of minutes; prints the bounds"]
async fn print_bounds() {
    let f = fixtures().await;
    let only = std::env::var("ONLY").ok();
    for c in &f.cases {
        if only.as_ref().is_some_and(|o| !o.split(',').any(|q| q == c.name)) {
            continue;
        }
        println!("==== {}: {} rows", c.name, c.rows());
        for p in PLANNERS {
            let Some(before) = f.bounds(c, p, &[]).await else { continue };
            println!("{p:?}:");
            println!("before: {before}");
            println!("with the others' plans: {}", f.bounds(c, p, &f.profiles(Some(&c.name))).await.unwrap());
        }
    }
}

/// With its own plan, the bounds hold each query's true row count, as
/// DataFusion plans it too.
#[tokio::test]
async fn bounds_hold_with_its_own_plan() {
    let f = fixtures().await;
    let mut failures = vec![];
    for c in &f.cases {
        let truth = c.rows();
        let Some(b) = f.bounds(c, Planner::DataFusion, &[&c.plan]).await else { continue };
        if !b.holds(truth) {
            failures.push(format!("{}, planned by DataFusion, with its plan: {b}, not {truth}", c.name));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// With the plans of other queries on the data the query ran on, the
/// bounds hold its true row count.
#[tokio::test]
#[ignore = "slow: tens of minutes"]
async fn bounds_hold() {
    let f = fixtures().await;
    let mut failures = vec![];
    for c in &f.cases {
        let truth = c.rows();
        for p in PLANNERS {
            let Some(b) = f.bounds(c, p, &f.profiles(Some(&c.name))).await else { continue };
            if !b.holds(truth) {
                failures.push(format!("{}, planned by {p:?}, with the others' plans: {b}, not {truth}", c.name));
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// How many outputs the bounds with the other queries' plans cap at their
/// true count. Raise the floors as matching improves.
#[tokio::test]
#[ignore = "slow: tens of minutes"]
async fn tight_rates() {
    let f = fixtures().await;
    // Per planner: DataFusion's, then DuckDB's.
    const TIGHT: [usize; 2] = [25, 25];
    // Per planner, over the queries DataFusion plans.
    let (mut tight, mut shared) = ([0; 2], 0);
    for c in &f.cases {
        if Analysis::sql(&f.ctx, &c.sql).await.is_err() {
            continue;
        }
        shared += 1;
        for p in PLANNERS {
            let hi = f.bounds(c, p, &f.profiles(Some(&c.name))).await.unwrap().upper;
            tight[p as usize] += usize::from(hi == Some(c.rows()));
        }
    }
    for p in PLANNERS {
        let k = p as usize;
        println!("{p:?}: {} of {shared} outputs capped at their count", tight[k]);
        assert!(tight[k] >= TIGHT[k], "{p:?}: {} outputs capped at their true count", tight[k]);
    }
}

/// A required filter pushed into a scan is applied exactly; an optional one
/// is left out, and what it pruned is pinned only from below. DuckDB's plan
/// meets DataFusion's operators through pushed-down filters, a projection's
/// alias, and a join's inputs, and caps the output at its true count.
#[tokio::test]
async fn pushed_filters_bound() {
    let f = fixtures().await;
    // `select * from lineitem where l_quantity < 10`.
    // The GROUP BY reads `yr`, an alias of `extract(year from o_orderdate)`;
    // DuckDB prints `p_name LIKE '%green%'` as `contains(p_name, 'green')`;
    // and its `date - interval` is a timestamp, DataFusion's a date.
    for name in ["scan_filter", "alias", "q09", "q01", "q03"] {
        let c = f.case(name);
        let b = f.bounds(c, Planner::DataFusion, &[&c.plan]).await.unwrap();
        assert_eq!(b.upper, Some(c.rows()), "{name}: {b}");
    }
}

/// DuckDB's plain `EXPLAIN` plan of each TPC-H query reads as the plan its
/// profile ran: analyzed, it gives the same constraints. As a reference
/// plan, it counted nothing, and adds nothing.
#[tokio::test]
async fn explain_plans() {
    let f = fixtures().await;
    let mut differ = vec![];
    for (name, json) in fixtures::fixtures("explain") {
        let sql = query("tpch", &name);
        let plan = cardinal::observed::from_duckdb_explain(&f.catalog, &name, &json, Some(&sql)).unwrap();
        assert!(!plan.counted);
        let explained = Analysis::plan(&f.catalog, &plan).options(options()).build().unwrap();
        let profiled = Analysis::plan(&f.catalog, &f.case(&name).plan).options(options()).build().unwrap();
        if explained.constraints() != profiled.constraints() {
            differ.push(format!("{name}:\n{}\nvs its profile's\n{}", explained.plan, profiled.plan));
        }
        let referenced = Analysis::plan(&f.catalog, &plan).options(options()).with_plans([&plan]).build().unwrap();
        assert_eq!(referenced.constraints(), explained.constraints(), "{name}");
    }
    assert!(differ.is_empty(), "{}", differ.join("\n\n"));
}

/// DuckDB does not print a limit's count; the query's `LIMIT` clause gives it.
#[tokio::test]
async fn limits_from_query_text() {
    let f = fixtures().await;
    let a = f.analyze(f.case("limit"), Planner::DuckDb, &[]).await.unwrap();
    assert_eq!(a.bounds().unwrap().upper, Some(5), "{}", a.plan);
}

/// Above a self-join, DuckDB prints both instances' columns by one name
/// (TPC-H q07's `n_name`s): the query's aliases tell them apart, by what
/// each is joined to, and its plan caps the output at its true count.
#[tokio::test]
async fn self_join_names() {
    let f = fixtures().await;
    let c = f.case("q07");
    let b = f.bounds(c, Planner::DuckDb, &[]).await.unwrap();
    assert_eq!(b.upper, Some(8), "{b}");
    let b = f.bounds(c, Planner::DuckDb, &[&c.plan]).await.unwrap();
    assert_eq!(b.upper, Some(c.rows()), "{b}");
}
