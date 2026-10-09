//! Facts put in place of selectivities: each fixture query analyzed by
//! DataFusion, with facts read off DuckDB's profiles of the same queries.
//! Print how many selectivities find a fact, and the bounds before and after,
//! with
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
use fixtures::{context, foreign_keys, plans, query};

/// A fixture DataFusion can plan.
struct Case {
    name: String,
    analysis: Analysis,
    plan: ObservedPlan,
    /// The facts its profile shows, before closure.
    observed: FactSet,
}

impl Case {
    /// The query's true row count.
    fn rows(&self) -> u64 {
        self.plan.nodes[self.plan.root].rows
    }
}

async fn cases() -> Vec<Case> {
    let ctx = context();
    let mut out = vec![];
    for dir in ["extra", "tpch"] {
        for plan in plans(dir).await {
            let sql = query(dir, &plan.name);
            let options = Options { selectivity: true, foreign_keys: foreign_keys(), ..Default::default() };
            // DataFusion has no `AS MATERIALIZED`.
            if let Ok(analysis) = cardinal::analyze_sql_with(&ctx, &sql, options).await {
                let mut observed = FactSet::default();
                observed.observe(&plan);
                out.push(Case { name: plan.name.clone(), analysis, plan, observed });
            }
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
    let (mut required, mut own, mut others, mut every) = (0, 0, 0, 0);
    for Case { name, analysis: a, plan, .. } in &cases {
        let report = a.selectivity.as_ref().unwrap();
        let mine = a.with_facts(&derive_facts(std::slice::from_ref(plan)), FactMode::Ratios).unwrap();
        let rest = a.with_facts(&facts(&cases, Some(name)), FactMode::Ratios).unwrap();
        let both = a.with_facts(&all, FactMode::Ratios).unwrap();
        let n = report.required.len();
        required += n;
        own += matched(a, &mine);
        others += matched(a, &rest);
        every += matched(a, &both);
        println!(
            "==== {name}: of {n}, {} from its own profile, {} from the others, {} from all; {} rows",
            matched(a, &mine),
            matched(a, &rest),
            matched(a, &both),
            plan.nodes[plan.root].rows,
        );
        println!("{report}\nown: {mine}\nothers: {rest}\nall: {both}");
    }
    println!("==== of {required}, {own} from their own profiles, {others} from the others', {every} from all");
}

#[tokio::test]
async fn print_bounds() {
    let cases = cases().await;
    let all = facts(&cases, None);
    let only = std::env::var("ONLY").ok();
    for Case { name, analysis: a, plan, .. } in &cases {
        if only.as_ref().is_some_and(|o| !o.split(',').any(|q| q == name)) {
            continue;
        }
        let ratios = a.with_facts(&all, FactMode::Ratios).unwrap();
        let pinned = a.with_facts(&all, FactMode::Pinned).unwrap();
        let (lo, hi) = pinned.range().unwrap();
        println!("==== {name}: {} rows", plan.nodes[plan.root].rows);
        println!("before: {}", a.bounds().unwrap());
        println!("ratios: {ratios}\n  {}", ratios.bounds().unwrap());
        println!("pinned: {lo} <= X <= {hi:?}; {}", pinned.bounds().unwrap());
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
    for c @ Case { name, analysis: a, .. } in &cases {
        let truth = c.rows();
        for (which, facts) in [("all", all.clone()), ("others", facts(&cases, Some(name)))] {
            for mode in [FactMode::Ratios, FactMode::Pinned] {
                let i = a.with_facts(&facts, mode).unwrap();
                let context = format!("{name}, {mode:?} with {which} facts");
                if !i.rejected.is_empty() {
                    failures.push(format!("{context}: rejected {:?}", i.rejected));
                }
                if let Ok(r) = i.evaluate(&sizes(&facts))
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
    const EVERY: usize = 6;
    const OTHERS: usize = 1;
    const TIGHT: usize = 30;
    let (mut every, mut others, mut tight) = (0, 0, 0);
    for c @ Case { name, analysis: a, .. } in &cases {
        every += matched(a, &a.with_facts(&all, FactMode::Ratios).unwrap());
        others += matched(a, &a.with_facts(&facts(&cases, Some(name)), FactMode::Ratios).unwrap());
        // Bounds that cap the output at its true count.
        let (_, hi) = a.with_facts(&all, FactMode::Pinned).unwrap().range().unwrap();
        tight += usize::from(hi == Some(c.rows()));
    }
    println!("{every} matched with every fact, {others} with others', {tight} of {} outputs capped at their count", cases.len());
    assert!(every >= EVERY, "{every} selectivities matched with every fact");
    assert!(others >= OTHERS, "{others} selectivities matched with other queries' facts");
    assert!(tight >= TIGHT, "{tight} outputs capped at their true count");
}

/// A filter pushed into a scan gives no exact fact, only an upper bound on
/// the rows it and what keeps them above name: pinned, those bounds meet
/// the query's operators through pushed-down filters, a projection's alias,
/// and a join's inputs, and cap the output at its true count.
#[tokio::test]
async fn pushed_filters_bound() {
    let cases = cases().await;
    let all = facts(&cases, None);
    let case = |name: &str| {
        let c = cases.iter().find(|c| c.name == name).unwrap();
        (&c.analysis, c.rows())
    };

    // `select * from lineitem where l_quantity < 10`: the share is unknown,
    // and the scan's rows are at most what it returned.
    let (a, rows) = case("scan_filter");
    let i = a.with_facts(&all, FactMode::Ratios).unwrap();
    assert!(i.matched.is_empty(), "{i}");
    let i = a.with_facts(&all, FactMode::Pinned).unwrap();
    assert!(i.capped.iter().any(|(_, n)| *n == rows), "{:?}", i.capped);
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
