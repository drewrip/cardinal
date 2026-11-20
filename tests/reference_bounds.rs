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

mod fixtures;

use cardinal::observed::{Catalog, ObservedPlan};
use cardinal::{Analysis, Bounds, Options};
use datafusion::prelude::SessionContext;
use fixtures::{catalog, context, foreign_keys, plans, query};

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
