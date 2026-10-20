//! Facts put in place of selectivities: each fixture query analyzed as
//! DataFusion plans it, and as DuckDB planned it (read from its profile),
//! with facts read off DuckDB's profiles of the same queries. Print how many
//! selectivities find a fact, and the bounds before and after, with
//!
//! ```sh
//! cargo test --test fact_bounds print_matches -- --nocapture
//! cargo test --test fact_bounds print_bounds -- --nocapture   # ONLY=q01,q03 for some
//! ```

mod fixtures;

use std::collections::HashMap;

use cardinal::facts::{Context, FactKind, FactSet, derive_facts};
use cardinal::observed::ObservedPlan;
use cardinal::{Analysis, FactMode, Informed, Options};
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
    let options = || Options { selectivity: true, foreign_keys: foreign_keys(), ..Default::default() };
    let mut out = vec![];
    for dir in ["extra", "tpch"] {
        for plan in plans(dir).await {
            let sql = query(dir, &plan.name);
            // DataFusion has no `AS MATERIALIZED`.
            let analysis = cardinal::analyze_sql_with(&ctx, &sql, options()).await.ok();
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

/// How many of the selectivities the output needs have a value. One the
/// output mentions twice (an outer join's) is unmatched twice.
fn matched(a: &Analysis, i: &Informed) -> usize {
    let required = &a.selectivity.as_ref().unwrap().required;
    required.iter().filter(|s| !i.unmatched.iter().any(|(u, _)| *u == s.name)).count()
}

#[tokio::test]
async fn print_matches() {
    let cases = cases().await;
    let all = facts(&cases, None);
    // Per planner: required, and matched from own, others', every profile.
    let mut totals = [[0usize; 4]; 2];
    // Over the queries both plan.
    let mut shared = [[0usize; 4]; 2];
    for c in &cases {
        let rest = facts(&cases, Some(&c.name));
        let mine_facts = derive_facts(std::slice::from_ref(&c.plan));
        println!("==== {}: {} rows", c.name, c.rows());
        for (p, a) in c.planned() {
            let report = a.selectivity.as_ref().unwrap();
            let mine = a.with_facts(&mine_facts, FactMode::Ratios).unwrap();
            let others = a.with_facts(&rest, FactMode::Ratios).unwrap();
            let both = a.with_facts(&all, FactMode::Ratios).unwrap();
            let n = [report.required.len(), matched(a, &mine), matched(a, &others), matched(a, &both)];
            println!(
                "{p:?}: of {}, {} from its own profile, {} from the others, {} from all",
                n[0], n[1], n[2], n[3],
            );
            println!("{report}\nown: {mine}\nothers: {others}\nall: {both}");
            let k = p as usize;
            for j in 0..4 {
                totals[k][j] += n[j];
                if c.analysis.is_some() {
                    shared[k][j] += n[j];
                }
            }
        }
    }
    for p in PLANNERS {
        let [t, s] = [totals[p as usize], shared[p as usize]];
        println!("==== {p:?}: of {}, {} from their own profiles, {} from the others', {} from all", t[0], t[1], t[2], t[3]);
        println!("     on queries both plan: of {}, {} own, {} others', {} all", s[0], s[1], s[2], s[3]);
    }
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
            let ratios = a.with_facts(&all, FactMode::Ratios).unwrap();
            let pinned = a.with_facts(&all, FactMode::Pinned).unwrap();
            let (lo, hi) = pinned.range().unwrap();
            println!("{p:?}:");
            println!("before: {}", a.bounds().unwrap());
            println!("ratios: {ratios}\n  {}", ratios.bounds().unwrap());
            println!("pinned: {lo} <= X <= {hi:?}; {}", pinned.bounds().unwrap());
        }
    }
}

/// With facts of the data the query ran on, each bound holds its true row
/// count, and no fact is rejected: a rejection is a fact matched to the
/// wrong rows.
#[tokio::test]
async fn bounds_hold() {
    let cases = cases().await;
    let all = facts(&cases, None);
    let mut failures = vec![];
    for c in &cases {
        let truth = c.rows();
        let rest = facts(&cases, Some(&c.name));
        for ((p, a), (which, facts)) in c.planned().flat_map(|pa| [(pa, ("all", &all)), (pa, ("others", &rest))]) {
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
    let cases = cases().await;
    let all = facts(&cases, None);
    // Per planner: DataFusion's, then DuckDB's.
    const EVERY: [usize; 2] = [6, 8];
    const OTHERS: [usize; 2] = [1, 1];
    const TIGHT: [usize; 2] = [30, 35];
    // Per planner, over the queries DataFusion plans.
    let (mut every, mut others, mut tight) = ([0; 2], [0; 2], [0; 2]);
    let shared: Vec<&Case> = cases.iter().filter(|c| c.analysis.is_some()).collect();
    for c in &shared {
        let rest = facts(&cases, Some(&c.name));
        for (p, a) in c.planned() {
            let k = p as usize;
            every[k] += matched(a, &a.with_facts(&all, FactMode::Ratios).unwrap());
            others[k] += matched(a, &a.with_facts(&rest, FactMode::Ratios).unwrap());
            // Bounds that cap the output at its true count.
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

    // `select * from lineitem where l_quantity < 10`: the share is known.
    let (a, rows) = case("scan_filter");
    let i = a.with_facts(&all, FactMode::Ratios).unwrap();
    assert!(!i.matched.is_empty(), "{i}");
    let i = a.with_facts(&all, FactMode::Pinned).unwrap();
    assert_eq!(i.range().unwrap().1, Some(rows));

    // The GROUP BY reads `yr`, an alias of `extract(year from o_orderdate)`;
    // DuckDB prints `p_name LIKE '%green%'` as `contains(p_name, 'green')`;
    // and its `date - interval` is a timestamp, DataFusion's a date.
    for name in ["alias", "q09", "q01", "q03"] {
        let (a, rows) = case(name);
        let i = a.with_facts(&all, FactMode::Pinned).unwrap();
        assert!(i.rejected.is_empty(), "{name}: {i}");
        assert_eq!(i.range().unwrap().1, Some(rows), "{name}: {i}");
    }
}

/// DuckDB's plain `EXPLAIN` plan of each TPC-H query reads as the plan its
/// profile ran, with no facts: analyzed, it asks for the same selectivities.
#[tokio::test]
async fn explain_plans() {
    let catalog = catalog().await;
    let profiles = plans("tpch").await;
    let options = || Options { selectivity: true, foreign_keys: foreign_keys(), ..Default::default() };
    let mut differ = vec![];
    for (name, json) in fixtures::fixtures("explain") {
        let sql = query("tpch", &name);
        let plan = cardinal::observed::from_duckdb_explain(&catalog, &name, &json, Some(&sql)).unwrap();
        assert!(!plan.counted);
        assert!(derive_facts(std::slice::from_ref(&plan)).iter().next().is_none(), "{name} gives facts");
        let explained = cardinal::analyze_observed(&catalog, &plan, options()).unwrap();
        let profile = profiles.iter().find(|p| p.name == name).unwrap();
        let profiled = cardinal::analyze_observed(&catalog, profile, options()).unwrap();
        let report = |a: &Analysis| a.selectivity.as_ref().unwrap().to_string();
        if report(&explained) != report(&profiled) {
            differ.push(format!("{name}:\n{}\nvs its profile's\n{}", report(&explained), report(&profiled)));
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
    assert_eq!(a.bounds().unwrap().constant, Some(5), "{}", a.plan);
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
    assert_eq!(a.bounds().unwrap().constant, Some(8), "{}", a.plan);
    let i = a.with_facts(&all, FactMode::Pinned).unwrap();
    assert!(i.rejected.is_empty(), "{i}");
    assert_eq!(i.range().unwrap().1, Some(c.rows()), "{i}");
}
