//! Facts put in place: each fixture query analyzed as DataFusion plans it,
//! and as DuckDB planned it (read from its profile), with facts read off
//! DuckDB's profiles of the same queries. Print the bounds before and
//! after, with
//!
//! ```sh
//! cargo test --test fact_bounds print_bounds -- --nocapture   # ONLY=q01,q03 for some
//! ```

mod fixtures;

use cardinal::facts::{FactSet, derive_facts};
use cardinal::observed::ObservedPlan;
use cardinal::{Analysis, Facts, Options};
use fixtures::{catalog, context, foreign_keys, plans, query};

/// A fixture query, analyzed by each planner.
struct Case {
    name: String,
    /// As DataFusion plans it, if it can.
    analysis: Option<Analysis>,
    /// As DuckDB planned it.
    duck: Analysis,
    plan: ObservedPlan,
    /// The facts its profile shows, before closure.
    observed: FactSet,
}

impl Case {
    /// The query's true row count.
    fn rows(&self) -> u64 {
        self.plan.nodes[self.plan.root].rows
    }

    /// Its analyses, by planner.
    fn planned(&self) -> impl Iterator<Item = (Planner, &Analysis)> {
        let df = self.analysis.as_ref().map(|a| (Planner::DataFusion, a));
        df.into_iter().chain([(Planner::DuckDb, &self.duck)])
    }

    fn by(&self, p: Planner) -> Option<&Analysis> {
        self.planned().find(|(q, _)| *q == p).map(|(_, a)| a)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Planner {
    DataFusion,
    DuckDb,
}

const PLANNERS: [Planner; 2] = [Planner::DataFusion, Planner::DuckDb];

async fn cases() -> Vec<Case> {
    let ctx = context();
    let catalog = catalog().await;
    let options = || Options { foreign_keys: foreign_keys(), ..Default::default() };
    let mut out = vec![];
    for dir in ["extra", "tpch"] {
        for plan in plans(dir).await {
            let sql = query(dir, &plan.name);
            // DataFusion has no `AS MATERIALIZED`.
            let analysis = cardinal::analyze_sql(&ctx, &sql, options()).await.ok();
            let duck = cardinal::analyze_observed(&catalog, &plan, options()).unwrap();
            let mut observed = FactSet::default();
            observed.observe(&plan);
            out.push(Case { name: plan.name.clone(), analysis, duck, plan, observed });
        }
    }
    out
}

/// The facts of every profile, or with `except`, of every other one.
/// Observing a plan is slow, so each is observed once.
fn facts(cases: &[Case], except: Option<&str>) -> Facts {
    let mut set = FactSet::default();
    for c in cases.iter().filter(|c| Some(c.name.as_str()) != except) {
        for f in c.observed.iter() {
            set.insert(f.clone());
        }
        for b in c.observed.bounds() {
            set.insert_bound(b.clone());
        }
        for f in c.observed.floors() {
            set.insert_floor(f.clone());
        }
    }
    Facts::new(set)
}

#[tokio::test]
async fn print_bounds() {
    let cases = cases().await;
    let all = facts(&cases, None);
    let only = std::env::var("ONLY").ok();
    for c in &cases {
        if only.as_ref().is_some_and(|o| !o.split(',').any(|q| q == c.name)) {
            continue;
        }
        println!("==== {}: {} rows", c.name, c.rows());
        for (p, a) in c.planned() {
            println!("{p:?}:");
            println!("before: {}", a.bounds().unwrap());
            println!("with facts: {}", a.with_facts(&all).unwrap().bounds().unwrap());
        }
    }
}

/// With facts of the data the query ran on, the bounds hold its true row
/// count.
#[tokio::test]
async fn bounds_hold() {
    let cases = cases().await;
    let all = facts(&cases, None);
    let mut failures = vec![];
    for c in &cases {
        let truth = c.rows();
        let rest = facts(&cases, Some(&c.name));
        for ((p, a), (which, facts)) in c.planned().flat_map(|pa| [(pa, ("all", &all)), (pa, ("others", &rest))]) {
            let b = a.with_facts(facts).unwrap().bounds().unwrap();
            if !b.holds(truth) {
                failures.push(format!("{}, planned by {p:?}, with {which} facts: {b}, not {truth}", c.name));
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// How many outputs the bounds with every fact cap at their true count.
/// Raise the floors as matching improves.
#[tokio::test]
async fn tight_rates() {
    let cases = cases().await;
    let all = facts(&cases, None);
    // Per planner: DataFusion's, then DuckDB's.
    const TIGHT: [usize; 2] = [30, 35];
    // Per planner, over the queries DataFusion plans.
    let mut tight = [0; 2];
    let shared: Vec<&Case> = cases.iter().filter(|c| c.analysis.is_some()).collect();
    for c in &shared {
        for (p, a) in c.planned() {
            let hi = a.with_facts(&all).unwrap().bounds().unwrap().upper;
            tight[p as usize] += usize::from(hi == Some(c.rows()));
        }
    }
    for p in PLANNERS {
        let k = p as usize;
        println!("{p:?}: {} of {} outputs capped at their count", tight[k], shared.len());
        assert!(tight[k] >= TIGHT[k], "{p:?}: {} outputs capped at their true count", tight[k]);
    }
}

/// A required filter pushed into a scan is applied exactly, and gives a
/// fact. An optional one gives only an upper bound on the rows it and what
/// keeps them above name, until a filter above checks it: pinned, facts and
/// bounds meet the query's operators through pushed-down filters, a
/// projection's alias, and a join's inputs, and cap the output at its true
/// count.
#[tokio::test]
async fn pushed_filters_bound() {
    let cases = cases().await;
    let all = facts(&cases, None);
    let case = |name: &str| {
        let c = cases.iter().find(|c| c.name == name).unwrap();
        (c.by(Planner::DataFusion).unwrap(), c.rows())
    };

    // `select * from lineitem where l_quantity < 10`.
    // The GROUP BY reads `yr`, an alias of `extract(year from o_orderdate)`;
    // DuckDB prints `p_name LIKE '%green%'` as `contains(p_name, 'green')`;
    // and its `date - interval` is a timestamp, DataFusion's a date.
    for name in ["scan_filter", "alias", "q09", "q01", "q03"] {
        let (a, rows) = case(name);
        let b = a.with_facts(&all).unwrap().bounds().unwrap();
        assert_eq!(b.upper, Some(rows), "{name}: {b}");
    }
}

/// DuckDB's plain `EXPLAIN` plan of each TPC-H query reads as the plan its
/// profile ran, with no facts: analyzed, it gives the same constraints.
#[tokio::test]
async fn explain_plans() {
    let catalog = catalog().await;
    let profiles = plans("tpch").await;
    let options = || Options { foreign_keys: foreign_keys(), ..Default::default() };
    let mut differ = vec![];
    for (name, json) in fixtures::fixtures("explain") {
        let sql = query("tpch", &name);
        let plan = cardinal::observed::from_duckdb_explain(&catalog, &name, &json, Some(&sql)).unwrap();
        assert!(!plan.counted);
        assert!(derive_facts(std::slice::from_ref(&plan)).iter().next().is_none(), "{name} gives facts");
        let explained = cardinal::analyze_observed(&catalog, &plan, options()).unwrap();
        let profile = profiles.iter().find(|p| p.name == name).unwrap();
        let profiled = cardinal::analyze_observed(&catalog, profile, options()).unwrap();
        if explained.constraints() != profiled.constraints() {
            differ.push(format!("{name}:\n{}\nvs its profile's\n{}", explained.plan, profiled.plan));
        }
    }
    assert!(differ.is_empty(), "{}", differ.join("\n\n"));
}

/// DuckDB does not print a limit's count; the query's `LIMIT` clause gives it.
#[tokio::test]
async fn limits_from_query_text() {
    let cases = cases().await;
    let c = cases.iter().find(|c| c.name == "limit").unwrap();
    let a = c.by(Planner::DuckDb).unwrap();
    assert_eq!(a.bounds().unwrap().upper, Some(5), "{}", a.plan);
}

/// Above a self-join, DuckDB prints both instances' columns by one name
/// (TPC-H q07's `n_name`s): the query's aliases tell them apart, by what
/// each is joined to, and cap the output at its true count.
#[tokio::test]
async fn self_join_names() {
    let cases = cases().await;
    let all = facts(&cases, None);
    let c = cases.iter().find(|c| c.name == "q07").unwrap();
    let a = c.by(Planner::DuckDb).unwrap();
    assert_eq!(a.bounds().unwrap().upper, Some(8), "{}", a.plan);
    let b = a.with_facts(&all).unwrap().bounds().unwrap();
    assert_eq!(b.upper, Some(c.rows()), "{b}");
}
