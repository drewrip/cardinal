//! Reference plans put in place, with PostgreSQL as the engine: each
//! fixture query analyzed as DataFusion plans it, and as PostgreSQL planned
//! it (read from its profile), with PostgreSQL's profiles of the same
//! queries as reference plans ([`cardinal::Builder::with_plans`]). Print
//! how many outputs the other queries' plans cap at their count with
//!
//! ```sh
//! cargo test --release --test postgres_bounds tight_rates -- --ignored --nocapture
//! ```
//!
//! The tests over every query with every other's plans are slow (tens of
//! minutes), and ignored by default; the others use the query's own plan.

mod fixtures;

use cardinal::observed::{Catalog, ObservedPlan, from_postgres_explain};
use cardinal::{Analysis, Bounds, Options};
use datafusion::prelude::SessionContext;
use fixtures::{catalog, context, foreign_keys, pg_fixtures, pg_plans, pg_query};

/// A fixture query, and its profile.
struct Case {
    name: String,
    sql: String,
    plan: ObservedPlan,
}

impl Case {
    /// The query's true row count.
    fn rows(&self) -> u64 {
        let root = &self.plan.nodes[self.plan.root];
        assert!(root.counted, "{}'s output was not counted", self.name);
        root.rows
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

/// The queries of some directories, and what they are analyzed against.
struct Fixtures {
    cases: Vec<Case>,
    ctx: SessionContext,
    catalog: Catalog,
}

/// The queries of `dirs`, each as its profile there.
async fn fixtures(dirs: &[&str]) -> Fixtures {
    let mut cases = vec![];
    for dir in dirs {
        for plan in pg_plans(dir).await {
            cases.push(Case { name: format!("{dir}/{}", plan.name), sql: pg_query(&plan.name), plan });
        }
    }
    Fixtures { cases, ctx: context(), catalog: catalog().await }
}

impl Fixtures {
    fn case(&self, name: &str) -> &Case {
        self.cases.iter().find(|c| c.name == name).unwrap()
    }

    /// Every other profile than `c`'s.
    fn others(&self, c: &Case) -> Vec<&ObservedPlan> {
        self.cases.iter().filter(|o| o.name != c.name).map(|o| &o.plan).collect()
    }

    /// `c` as `planner` plans it, with `references`; `None` where
    /// DataFusion cannot plan it (it has no `AS MATERIALIZED`).
    async fn bounds(&self, c: &Case, planner: Planner, references: &[&ObservedPlan]) -> Option<Bounds> {
        let query = match planner {
            Planner::DataFusion => Analysis::sql(&self.ctx, &c.sql).await.ok()?,
            Planner::Postgres => Analysis::plan(&self.catalog, &c.plan),
        };
        Some(query.options(options()).with_plans(references.iter().copied()).build().unwrap().bounds().unwrap())
    }
}

/// Without reference plans, and with the query's own, the bounds hold its
/// true row count. So for the plans PostgreSQL chose without indexes, for
/// those it chose with them (index scans, nested loops and merge joins),
/// and for version 14's.
#[tokio::test]
async fn bounds_hold() {
    let f = fixtures(&["extra", "tpch", "indexed", "parallel", "v14"]).await;
    let mut failures = vec![];
    for c in &f.cases {
        let truth = c.rows();
        for p in PLANNERS {
            for (which, references) in [("no", vec![]), ("its own", vec![&c.plan])] {
                let Some(b) = f.bounds(c, p, &references).await else { continue };
                if !b.holds(truth) {
                    failures.push(format!("{}, planned by {p:?}, with {which} plan: {b}, not {truth}", c.name));
                }
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// With the plans of other queries on the data the query ran on, the
/// bounds hold its true row count.
#[tokio::test]
#[ignore = "slow: tens of minutes"]
async fn bounds_hold_with_the_others_plans() {
    let f = fixtures(&["extra", "tpch", "indexed", "parallel", "v14"]).await;
    let mut failures = vec![];
    for c in &f.cases {
        let truth = c.rows();
        for p in PLANNERS {
            let Some(b) = f.bounds(c, p, &f.others(c)).await else { continue };
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
    let f = fixtures(&["extra", "tpch"]).await;
    // Per planner: DataFusion's, then PostgreSQL's.
    const TIGHT: [usize; 2] = [0, 0];
    let (mut tight, mut shared) = ([0; 2], 0);
    for c in &f.cases {
        if Analysis::sql(&f.ctx, &c.sql).await.is_err() {
            continue;
        }
        shared += 1;
        for p in PLANNERS {
            let hi = f.bounds(c, p, &f.others(c)).await.unwrap().upper;
            tight[p as usize] += usize::from(hi == Some(c.rows()));
        }
    }
    for p in PLANNERS {
        let k = p as usize;
        println!("{p:?}: {} of {shared} outputs capped at their count", tight[k]);
        assert!(tight[k] >= TIGHT[k], "{p:?}: {} outputs capped at their true count", tight[k]);
    }
}

/// PostgreSQL's plain `EXPLAIN` plan of each TPC-H query reads as the plan
/// its profile ran: analyzed, it gives the same constraints. As a reference
/// plan, it counted nothing, and adds nothing.
#[tokio::test]
async fn explain_plans() {
    let f = fixtures(&["tpch"]).await;
    let mut differ = vec![];
    for (name, json) in pg_fixtures("explain") {
        let sql = pg_query(&name);
        let plan = from_postgres_explain(&f.catalog, &name, &json, Some(&sql)).unwrap();
        assert!(!plan.counted);
        let explained = Analysis::plan(&f.catalog, &plan).options(options()).build().unwrap();
        let referenced = Analysis::plan(&f.catalog, &plan).options(options()).with_plans([&plan]).build().unwrap();
        assert_eq!(referenced.constraints(), explained.constraints(), "{name}");
        // A profile reads the same with its counts ignored.
        let (_, profile_json) = pg_fixtures("tpch").into_iter().find(|(n, _)| *n == name).unwrap();
        let uncounted = from_postgres_explain(&f.catalog, &name, &profile_json, Some(&sql)).unwrap();
        assert_eq!(plan.to_string(), uncounted.to_string(), "{name}");
        let profile = &f.case(&format!("tpch/{name}")).plan;
        let profiled = Analysis::plan(&f.catalog, profile).options(options()).build().unwrap();
        if explained.constraints() != profiled.constraints() {
            differ.push(format!("{name}:\n{}\nvs its profile's\n{}", explained.plan, profiled.plan));
        }
        // `Analysis::postgres` is the two steps in one.
        let direct = Analysis::postgres(&f.catalog, &json, Some(&sql)).unwrap().options(options()).build().unwrap();
        assert_eq!(direct.constraints(), explained.constraints(), "{name}");
    }
    assert!(differ.is_empty(), "{}", differ.join("\n\n"));
}

/// PostgreSQL does not print a limit's count; the query's `LIMIT` clause
/// gives it.
#[tokio::test]
async fn limits_from_query_text() {
    let f = fixtures(&["extra"]).await;
    let b = f.bounds(f.case("extra/limit"), Planner::Postgres, &[]).await.unwrap();
    assert_eq!(b.upper, Some(5), "{b}");
}

/// PostgreSQL prints every column with its relation's alias, so TPC-H q07's
/// two `nation`s read apart with no help: two nations each and two years
/// bound the output, and its plan caps it at its true count.
#[tokio::test]
async fn self_join_names() {
    let f = fixtures(&["tpch"]).await;
    let c = f.case("tpch/q07");
    assert_eq!(f.bounds(c, Planner::Postgres, &[]).await.unwrap().upper, Some(8));
    let b = f.bounds(c, Planner::Postgres, &[&c.plan]).await.unwrap();
    assert_eq!(b.upper, Some(c.rows()), "{b}");
}
