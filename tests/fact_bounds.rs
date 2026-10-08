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
    a.selectivity.as_ref().unwrap().required.len() - i.unmatched.len()
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

/// How many selectivities find a fact. Raise the floors as matching improves.
#[tokio::test]
async fn match_rates() {
    let cases = cases().await;
    let all = facts(&cases, None);
    let (mut every, mut others) = (0, 0);
    for Case { name, analysis: a, .. } in &cases {
        every += matched(a, &a.with_facts(&all, FactMode::Ratios).unwrap());
        others += matched(a, &a.with_facts(&facts(&cases, Some(name)), FactMode::Ratios).unwrap());
    }
    assert!(every >= 38, "{every} selectivities matched with every fact");
    assert!(others >= 7, "{others} selectivities matched with other queries' facts");
}

/// Facts from other plans meet the query's operators, through pushed-down
/// filters, a projection's alias, and a join's inputs.
#[tokio::test]
async fn values_are_exact() {
    let cases = cases().await;
    let all = facts(&cases, None);
    let case = |name: &str| {
        let c = cases.iter().find(|c| c.name == name).unwrap();
        (&c.analysis, c.rows())
    };
    let value = |i: &Informed, s: &str| i.matched.iter().find(|m| m.name == s).map(|m| m.value.to_string());

    // `select * from lineitem where l_quantity < 10`: its filter is pushed
    // into the scan, measured from another plan's sizes.
    let (a, _) = case("scan_filter");
    let i = a.with_facts(&facts(&cases, Some("scan_filter")), FactMode::Ratios).unwrap();
    assert_eq!(value(&i, "s1").as_deref(), Some("10816/60175 ≈ 0.1797"), "{i}");
    assert_eq!(i.output.to_string(), "10816/60175·|lineitem|");

    // The GROUP BY reads `yr`, an alias of `extract(year from o_orderdate)`.
    let (a, _) = case("alias");
    let i = a.with_facts(&all, FactMode::Ratios).unwrap();
    assert!(i.unmatched.is_empty(), "{i}");

    // Every share of a filtered join, through its inputs' contexts.
    let (a, rows) = case("join_filtered");
    let i = a.with_facts(&all, FactMode::Ratios).unwrap();
    assert!(i.unmatched.is_empty(), "{i}");
    let exact = i.evaluate(&sizes(&all)).unwrap();
    assert_eq!(exact.exact(), Some(rows as f64), "{i}");

    // DuckDB prints `p_name LIKE '%green%'` as `contains(p_name, 'green')`.
    let (a, _) = case("q09");
    let i = a.with_facts(&all, FactMode::Ratios).unwrap();
    assert_eq!(value(&i, "s1").as_deref(), Some("107/2000 ≈ 0.0535"), "{i}");

    // DuckDB's `date - interval` is a timestamp, DataFusion's a date.
    let (a, rows) = case("q01");
    let i = a.with_facts(&all, FactMode::Pinned).unwrap();
    assert!(i.unmatched.is_empty(), "{i}");
    assert_eq!(i.range().unwrap(), (rows, Some(rows)));
}
