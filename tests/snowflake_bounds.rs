//! Reference plans put in place, with Snowflake as the engine: each fixture
//! query analyzed as DataFusion plans it, and as Snowflake planned it (read
//! from its operator stats), with Snowflake's profiles of the same queries
//! as reference plans ([`cardinal::Builder::with_plans`]). Print how tight
//! the bounds are with
//!
//! ```sh
//! cargo test --release --test snowflake_bounds tight_rates -- --ignored --nocapture
//! ```

mod fixtures;

use cardinal::observed::{Catalog, ObservedPlan, from_snowflake_explain};
use cardinal::{Analysis, Bounds, Options};
use datafusion::prelude::SessionContext;
use fixtures::{catalog, context, foreign_keys, sf_fixtures, sf_plans, sf_query};

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
    Snowflake,
}

const PLANNERS: [Planner; 2] = [Planner::DataFusion, Planner::Snowflake];

fn options() -> Options {
    Options { foreign_keys: foreign_keys(), ..Default::default() }
}

struct Fixtures {
    cases: Vec<Case>,
    ctx: SessionContext,
    catalog: Catalog,
}

async fn fixtures() -> Fixtures {
    let mut cases = vec![];
    for dir in ["tpch", "extra"] {
        for plan in sf_plans(dir).await {
            cases.push(Case { name: format!("{dir}/{}", plan.name), sql: sf_query(&plan.name), plan });
        }
    }
    Fixtures { cases, ctx: context(), catalog: catalog().await }
}

impl Fixtures {
    fn others(&self, c: &Case) -> Vec<&ObservedPlan> {
        self.cases.iter().filter(|o| o.name != c.name).map(|o| &o.plan).collect()
    }

    /// `c` as `planner` plans it, with `references`; `None` where
    /// DataFusion cannot plan it.
    async fn bounds(&self, c: &Case, planner: Planner, references: &[&ObservedPlan]) -> Option<Bounds> {
        let query = match planner {
            Planner::DataFusion => Analysis::sql(&self.ctx, &c.sql).await.ok()?,
            Planner::Snowflake => Analysis::plan(&self.catalog, &c.plan),
        };
        Some(query.options(options()).with_plans(references.iter().copied()).build().unwrap().bounds().unwrap())
    }
}

/// Without reference plans, and with the query's own, the bounds hold its
/// true row count.
#[tokio::test]
async fn bounds_hold() {
    let f = fixtures().await;
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

/// With the plans of the other queries, the bounds hold the true row count.
#[tokio::test]
#[ignore = "slow"]
async fn bounds_hold_with_the_others_plans() {
    let f = fixtures().await;
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

/// How tight the bounds are: with no plans, with the others' plans, and
/// with the query's own, by planner.
#[tokio::test]
#[ignore = "slow"]
async fn tight_rates() {
    let f = fixtures().await;
    for p in PLANNERS {
        let (mut n, mut capped, mut exact, mut own_exact, mut none_capped) = (0, 0, 0, 0, 0);
        for c in &f.cases {
            let truth = c.rows();
            let Some(none) = f.bounds(c, p, &[]).await else { continue };
            let others = f.bounds(c, p, &f.others(c)).await.unwrap();
            let own = f.bounds(c, p, &[&c.plan]).await.unwrap();
            n += 1;
            none_capped += usize::from(none.upper == Some(truth));
            capped += usize::from(others.upper == Some(truth));
            exact += usize::from(others.lower == truth && others.upper == Some(truth));
            own_exact += usize::from(own.lower == truth && own.upper == Some(truth));
            println!("{p:?} {}: truth {truth}; none {none}; others {others}; own {own}", c.name);
        }
        println!("{p:?}: {n} queries; capped at the truth with no plans {none_capped}, with the others' {capped} (exact {exact}); exact with its own {own_exact}");
    }
}

/// Snowflake's `EXPLAIN USING JSON` plan of each TPC-H query reads as a plan
/// that counted nothing: as a reference plan, it adds nothing, and
/// `Analysis::snowflake` is the two steps in one. Analyzed, it gives the
/// constraints of the plan its profile ran.
#[tokio::test]
async fn explain_plans() {
    let f = fixtures().await;
    let mut differ = vec![];
    for (name, json) in sf_fixtures("explain") {
        let sql = sf_query(&name);
        let plan = from_snowflake_explain(&f.catalog, &name, &json, Some(&sql)).unwrap();
        assert!(!plan.counted);
        let explained = Analysis::plan(&f.catalog, &plan).options(options()).build().unwrap();
        let referenced = Analysis::plan(&f.catalog, &plan).options(options()).with_plans([&plan]).build().unwrap();
        assert_eq!(referenced.constraints(), explained.constraints(), "{name}");
        let direct = Analysis::snowflake(&f.catalog, &json, Some(&sql)).unwrap().options(options()).build().unwrap();
        assert_eq!(direct.constraints(), explained.constraints(), "{name}");
        let profile = &f.cases.iter().find(|c| c.name == format!("tpch/{name}")).unwrap().plan;
        let profiled = Analysis::plan(&f.catalog, profile).options(options()).build().unwrap();
        if explained.constraints() != profiled.constraints() {
            differ.push(name);
        }
    }
    assert!(differ.is_empty(), "EXPLAIN reads otherwise than the profile: {differ:?}");
}
