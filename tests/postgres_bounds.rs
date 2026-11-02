//! Facts put in place, with PostgreSQL as the engine: each fixture query
//! analyzed as DataFusion plans it, and as PostgreSQL planned it (read from
//! its profile), with facts read off PostgreSQL's profiles of the same
//! queries. Print how many outputs the facts cap at their count with
//!
//! ```sh
//! cargo test --test postgres_bounds tight_rates -- --nocapture
//! ```

mod fixtures;

use cardinal::facts::{FactSet, derive_facts};
use cardinal::observed::{ObservedPlan, from_postgres_explain};
use cardinal::{Analysis, Facts, Options};
use fixtures::{catalog, context, foreign_keys, pg_fixtures, pg_plans, pg_query};

/// A fixture query, analyzed by each planner.
struct Case {
    name: String,
    /// As DataFusion plans it, if it can.
    analysis: Option<Analysis>,
    /// As PostgreSQL planned it.
    postgres: Analysis,
    plan: ObservedPlan,
    /// The facts its profile shows, before closure.
    observed: FactSet,
}

impl Case {
    /// The query's true row count.
    fn rows(&self) -> u64 {
        let root = &self.plan.nodes[self.plan.root];
        assert!(root.counted, "{}'s output was not counted", self.name);
        root.rows
    }

    /// Its analyses, by planner.
    fn planned(&self) -> impl Iterator<Item = (Planner, &Analysis)> {
        let df = self.analysis.as_ref().map(|a| (Planner::DataFusion, a));
        df.into_iter().chain([(Planner::Postgres, &self.postgres)])
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Planner {
    DataFusion,
    Postgres,
}

const PLANNERS: [Planner; 2] = [Planner::DataFusion, Planner::Postgres];

fn options() -> Options {
    Options { foreign_keys: foreign_keys(), ..Default::default() }
}

/// The queries of `dirs`, each as its profile there.
async fn cases(dirs: &[&str]) -> Vec<Case> {
    let ctx = context();
    let catalog = catalog().await;
    let mut out = vec![];
    for dir in dirs {
        for plan in pg_plans(dir).await {
            let sql = pg_query(&plan.name);
            // DataFusion has no `AS MATERIALIZED`.
            let analysis = cardinal::analyze_sql(&ctx, &sql, options()).await.ok();
            let postgres = cardinal::analyze_observed(&catalog, &plan, options()).unwrap();
            let mut observed = FactSet::default();
            observed.observe(&plan);
            out.push(Case { name: format!("{dir}/{}", plan.name), analysis, postgres, plan, observed });
        }
    }
    out
}

/// The facts of every profile, or with `except`, of every other one.
fn facts(cases: &[Case], except: Option<&str>) -> Facts {
    let mut set = FactSet::default();
    for c in cases.iter().filter(|c| Some(c.name.as_str()) != except) {
        for f in c.observed.iter() {
            set.insert(f.clone());
        }
        for b in c.observed.bounds() {
            set.insert_bound(b.clone());
        }
    }
    Facts::new(set)
}

/// With facts of the data the query ran on, the bounds hold its true row
/// count. So for the plans PostgreSQL chose without indexes, for those
/// it chose with them (index scans, nested loops and merge joins), and for
/// version 14's.
#[tokio::test]
async fn bounds_hold() {
    let cases = cases(&["extra", "tpch", "indexed", "parallel", "v14"]).await;
    let all = facts(&cases, None);
    assert!(all.set().conflicts.is_empty(), "{:#?}", all.set().conflicts);
    let mut failures = vec![];
    for c in &cases {
        let truth = c.rows();
        let rest = facts(&cases, Some(&c.name));
        for ((p, a), (which, facts)) in c.planned().flat_map(|pa| [(pa, ("all", &all)), (pa, ("others", &rest))]) {
            // Without facts, too: the plan as read bounds its own output.
            let b = a.bounds().unwrap();
            if !b.holds(truth) {
                failures.push(format!("{}, planned by {p:?}: {b}, not {truth}", c.name));
            }
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
    let cases = cases(&["extra", "tpch"]).await;
    let all = facts(&cases, None);
    // Per planner: DataFusion's, then PostgreSQL's.
    const TIGHT: [usize; 2] = [36, 39];
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

/// PostgreSQL's plain `EXPLAIN` plan of each TPC-H query reads as the plan
/// its profile ran, with no facts: analyzed, it gives the same constraints.
#[tokio::test]
async fn explain_plans() {
    let catalog = catalog().await;
    let profiles = pg_plans("tpch").await;
    let mut differ = vec![];
    for (name, json) in pg_fixtures("explain") {
        let sql = pg_query(&name);
        let plan = from_postgres_explain(&catalog, &name, &json, Some(&sql)).unwrap();
        assert!(!plan.counted);
        assert!(derive_facts(std::slice::from_ref(&plan)).iter().next().is_none(), "{name} gives facts");
        let explained = cardinal::analyze_observed(&catalog, &plan, options()).unwrap();
        // A profile reads the same with its counts ignored.
        let (_, profile_json) = pg_fixtures("tpch").into_iter().find(|(n, _)| *n == name).unwrap();
        let uncounted = from_postgres_explain(&catalog, &name, &profile_json, Some(&sql)).unwrap();
        assert_eq!(plan.to_string(), uncounted.to_string(), "{name}");
        let profile = profiles.iter().find(|p| p.name == name).unwrap();
        let profiled = cardinal::analyze_observed(&catalog, profile, options()).unwrap();
        if explained.constraints() != profiled.constraints() {
            differ.push(format!("{name}:\n{}\nvs its profile's\n{}", explained.plan, profiled.plan));
        }
        // `analyze_postgres` is the two steps in one.
        let direct = cardinal::analyze_postgres(&catalog, &json, Some(&sql), options()).unwrap();
        assert_eq!(direct.constraints(), explained.constraints(), "{name}");
    }
    assert!(differ.is_empty(), "{}", differ.join("\n\n"));
}

/// PostgreSQL does not print a limit's count; the query's `LIMIT` clause
/// gives it.
#[tokio::test]
async fn limits_from_query_text() {
    let cases = cases(&["extra"]).await;
    let c = cases.iter().find(|c| c.name == "extra/limit").unwrap();
    assert_eq!(c.postgres.bounds().unwrap().upper, Some(5), "{}", c.postgres.plan);
}

/// PostgreSQL prints every column with its relation's alias, so TPC-H q07's
/// two `nation`s read apart with no help: two nations each and two years
/// bound the output, and the facts cap it at its true count.
#[tokio::test]
async fn self_join_names() {
    let cases = cases(&["extra", "tpch"]).await;
    let all = facts(&cases, None);
    let c = cases.iter().find(|c| c.name == "tpch/q07").unwrap();
    assert_eq!(c.postgres.bounds().unwrap().upper, Some(8), "{}", c.postgres.plan);
    let b = c.postgres.with_facts(&all).unwrap().bounds().unwrap();
    assert_eq!(b.upper, Some(c.rows()), "{b}");
}
