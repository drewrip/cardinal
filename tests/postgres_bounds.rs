//! Facts put in place of selectivities, with PostgreSQL as the engine: each
//! fixture query analyzed as DataFusion plans it, and as PostgreSQL planned
//! it (read from its profile), with facts read off PostgreSQL's profiles of
//! the same queries. Print how many selectivities find a fact with
//!
//! ```sh
//! cargo test --test postgres_bounds match_rates -- --nocapture
//! ```

mod fixtures;

use std::collections::HashMap;

use cardinal::facts::{Context, FactKind, FactSet, derive_facts};
use cardinal::observed::{ObservedPlan, from_postgres_explain};
use cardinal::{Analysis, FactMode, Informed, Options};
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
    Options { selectivity: true, foreign_keys: foreign_keys(), ..Default::default() }
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
            let analysis = cardinal::analyze_sql_with(&ctx, &sql, options()).await.ok();
            let postgres = cardinal::analyze_observed(&catalog, &plan, options()).unwrap();
            let mut observed = FactSet::default();
            observed.observe(&plan);
            out.push(Case { name: format!("{dir}/{}", plan.name), analysis, postgres, plan, observed });
        }
    }
    out
}

/// The facts of every profile, or with `except`, of every other one.
fn facts(cases: &[Case], except: Option<&str>) -> FactSet {
    let mut set = FactSet::default();
    for c in cases.iter().filter(|c| Some(c.name.as_str()) != except) {
        for f in c.observed.iter() {
            set.insert(f.clone());
        }
        for b in c.observed.bounds() {
            set.insert_bound(b.clone());
        }
    }
    set.close();
    set
}

/// Each table's size, from the facts.
fn sizes(facts: &FactSet) -> HashMap<String, u64> {
    let tables = ["customer", "lineitem", "nation", "orders", "part", "partsupp", "region", "supplier"];
    let size = |t: &str| facts.get(&FactKind::Cardinality(Context::table(t)))?.value.as_int();
    tables.iter().filter_map(|t| Some((t.to_string(), size(t)?))).collect()
}

/// How many of the selectivities the output needs have a value.
fn matched(a: &Analysis, i: &Informed) -> usize {
    let required = &a.selectivity.as_ref().unwrap().required;
    required.iter().filter(|s| !i.unmatched.iter().any(|(u, _)| *u == s.name)).count()
}

/// With facts of the data the query ran on, each bound holds its true row
/// count, and no fact is rejected: a rejection is a fact matched to the
/// wrong rows. So for the plans PostgreSQL chose without indexes, for those
/// it chose with them (index scans, nested loops and merge joins), and for
/// version 14's.
#[tokio::test]
async fn bounds_hold() {
    let cases = cases(&["extra", "tpch", "indexed", "parallel", "v14"]).await;
    let all = facts(&cases, None);
    assert!(all.conflicts.is_empty(), "{:#?}", all.conflicts);
    let mut failures = vec![];
    for c in &cases {
        let truth = c.rows();
        let rest = facts(&cases, Some(&c.name));
        for ((p, a), (which, facts)) in c.planned().flat_map(|pa| [(pa, ("all", &all)), (pa, ("others", &rest))]) {
            // Without facts, too: the plan as read bounds its own output.
            let b = a.bounds().unwrap();
            if b.constant.is_some_and(|n| n < truth) {
                failures.push(format!("{}, planned by {p:?}: X <= {:?}, not {truth}", c.name, b.constant));
            }
            for mode in [FactMode::Ratios, FactMode::Pinned] {
                let i = a.with_facts(facts, mode).unwrap();
                let context = format!("{}, planned by {p:?}, {mode:?} with {which} facts", c.name);
                if !i.rejected.is_empty() {
                    failures.push(format!("{context}: rejected {:?}", i.rejected));
                }
                if let Ok(r) = i.evaluate(&sizes(facts))
                    && !r.contains(truth as f64)
                {
                    failures.push(format!("{context}: {} gives {r}, not {truth}", i.output));
                }
                if mode == FactMode::Pinned {
                    let (lo, hi) = i.range().unwrap();
                    if lo > truth || hi.is_some_and(|hi| hi < truth) {
                        failures.push(format!("{context}: {lo} <= X <= {hi:?}, not {truth}"));
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// How many selectivities find a fact, and how many outputs the bounds cap
/// at their true count. Raise the floors as matching improves.
#[tokio::test]
async fn match_rates() {
    let cases = cases(&["extra", "tpch"]).await;
    let all = facts(&cases, None);
    // Per planner: DataFusion's, then PostgreSQL's.
    const EVERY: [usize; 2] = [60, 95];
    const OTHERS: [usize; 2] = [10, 10];
    const TIGHT: [usize; 2] = [36, 39];
    let (mut every, mut others, mut tight) = ([0; 2], [0; 2], [0; 2]);
    let shared: Vec<&Case> = cases.iter().filter(|c| c.analysis.is_some()).collect();
    for c in &shared {
        let rest = facts(&cases, Some(&c.name));
        for (p, a) in c.planned() {
            let k = p as usize;
            every[k] += matched(a, &a.with_facts(&all, FactMode::Ratios).unwrap());
            others[k] += matched(a, &a.with_facts(&rest, FactMode::Ratios).unwrap());
            let (_, hi) = a.with_facts(&all, FactMode::Pinned).unwrap().range().unwrap();
            tight[k] += usize::from(hi == Some(c.rows()));
        }
    }
    for p in PLANNERS {
        let k = p as usize;
        println!(
            "{p:?}: {} matched with every fact, {} with others', {} of {} outputs capped at their count",
            every[k], others[k], tight[k], shared.len(),
        );
    }
    for p in PLANNERS {
        let k = p as usize;
        assert!(every[k] >= EVERY[k], "{p:?}: {} selectivities matched with every fact", every[k]);
        assert!(others[k] >= OTHERS[k], "{p:?}: {} selectivities matched with other queries' facts", others[k]);
        assert!(tight[k] >= TIGHT[k], "{p:?}: {} outputs capped at their true count", tight[k]);
    }
}

/// PostgreSQL's plain `EXPLAIN` plan of each TPC-H query reads as the plan
/// its profile ran, with no facts: analyzed, it asks for the same
/// selectivities.
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
        let report = |a: &Analysis| a.selectivity.as_ref().unwrap().to_string();
        if report(&explained) != report(&profiled) {
            differ.push(format!("{name}:\n{}\nvs its profile's\n{}", report(&explained), report(&profiled)));
        }
        // `analyze_postgres` is the two steps in one.
        let direct = cardinal::analyze_postgres(&catalog, &json, Some(&sql), options()).unwrap();
        assert_eq!(report(&direct), report(&explained), "{name}");
    }
    assert!(differ.is_empty(), "{}", differ.join("\n\n"));
}

/// PostgreSQL does not print a limit's count; the query's `LIMIT` clause
/// gives it.
#[tokio::test]
async fn limits_from_query_text() {
    let cases = cases(&["extra"]).await;
    let c = cases.iter().find(|c| c.name == "extra/limit").unwrap();
    assert_eq!(c.postgres.bounds().unwrap().constant, Some(5), "{}", c.postgres.plan);
}

/// PostgreSQL prints every column with its relation's alias, so TPC-H q07's
/// two `nation`s read apart with no help: two nations each and two years
/// bound the output, and the facts cap it at its true count.
#[tokio::test]
async fn self_join_names() {
    let cases = cases(&["extra", "tpch"]).await;
    let all = facts(&cases, None);
    let c = cases.iter().find(|c| c.name == "tpch/q07").unwrap();
    assert_eq!(c.postgres.bounds().unwrap().constant, Some(8), "{}", c.postgres.plan);
    let i = c.postgres.with_facts(&all, FactMode::Pinned).unwrap();
    assert!(i.rejected.is_empty(), "{i}");
    assert_eq!(i.range().unwrap().1, Some(c.rows()), "{i}");
}
