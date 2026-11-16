//! PostgreSQL `EXPLAIN (ANALYZE, VERBOSE)` profiles of TPC-H at scale
//! factor 0.01, read and used as reference plans
//! ([`cardinal::Builder::with_plans`]): which operators are counted, and
//! that their pins agree with the constraints and the truth. Regenerate the
//! fixtures with `scripts/postgres_fixtures.sh`.

mod fixtures;

use cardinal::observed::{ONode, ObservedPlan, Op, from_postgres, from_postgres_explain};
use cardinal::{Analysis, Options};
use fixtures::{PG_DIR, catalog, foreign_keys, pg_plans, pg_query};
use serde_json::Value;

async fn plan(dir: &str, name: &str) -> ObservedPlan {
    let json = std::fs::read_to_string(format!("{PG_DIR}/{dir}/{name}.json")).unwrap();
    from_postgres(&catalog().await, name, &json, Some(&pg_query(name))).unwrap()
}

/// The operators of `plan` that are `engine_op`s of kind `op`.
fn operators<'p>(plan: &'p ObservedPlan, engine_op: &str, op: fn(&Op) -> bool) -> Vec<&'p ONode> {
    plan.nodes.iter().filter(|n| n.engine_op == engine_op && op(&n.op)).collect()
}

#[tokio::test]
async fn every_fixture_converts() {
    for dir in ["extra", "tpch", "indexed", "parallel", "v14"] {
        for p in pg_plans(dir).await {
            assert!(!p.nodes.is_empty(), "{}", p.name);
            assert!(p.nodes[p.root].counted, "{dir}/{}: its output is not counted\n{p}", p.name);
        }
    }
}

/// Each fixture with its own profile as a reference plan: every operator
/// it counted is pinned, and the bounds hold the true count. A pin naming
/// other rows than the engine counted contradicts the constraints, and the
/// bounds then hold nothing in particular.
#[tokio::test]
async fn own_profile_pins_the_truth() {
    let catalog = catalog().await;
    let options = Options { foreign_keys: foreign_keys(), ..Default::default() };
    let (mut failures, mut exact, mut all) = (vec![], 0, 0);
    for dir in ["extra", "tpch", "indexed", "parallel", "v14"] {
        for p in pg_plans(dir).await {
            let b = Analysis::plan(&catalog, &p).options(options.clone()).with_plans([&p]).build().unwrap().bounds().unwrap();
            let truth = p.nodes[p.root].rows;
            all += 1;
            exact += usize::from(b.lower == truth && b.upper == Some(truth));
            if !b.holds(truth) {
                failures.push(format!("{dir}/{}: {b}, not {truth}", p.name));
            }
        }
    }
    println!("{exact} of {all} exact");
    assert!(failures.is_empty(), "{failures:#?}");
    assert!(exact * 4 >= all * 3, "only {exact} of {all} exact");
}

/// What ran more than once reports an average, which is no count where
/// what it read changed between runs, or a run stopped at a first match.
#[tokio::test]
async fn averages_are_not_counts() {
    let p = plan("tpch", "q20").await;
    let materialized = operators(&p, "Materialize", |_| true);
    assert!(!materialized.is_empty() && materialized.iter().all(|n| !n.counted), "{p}");
    assert!(p.to_string().contains("(Materialize) rows=?"), "{p}");
    // Nor is it pinned.
    let options = Options { trace: true, ..Default::default() };
    let a = Analysis::plan(&catalog().await, &p).options(options).with_plans([&p]).build().unwrap();
    let pinned: Vec<&str> = a.trace.as_ref().unwrap().constraints.iter().filter_map(|c| c.fact.as_ref()).map(|f| f.facts[0].text.as_str()).collect();
    assert!(!pinned.is_empty() && !pinned.iter().any(|t| t.contains("Materialize")), "{pinned:?}");
}

/// A sort a merge join stops reading has still read all of its input: its
/// rows are its input's.
#[tokio::test]
async fn a_sort_has_its_inputs_rows() {
    let p = plan("indexed", "not_exists").await;
    assert!(!operators(&p, "Merge Join", |_| true).is_empty(), "{p}");
    let [sort] = operators(&p, "Sort", |op| matches!(op, Op::Sort))[..] else { panic!("{p}") };
    assert!(sort.counted && sort.rows == p.nodes[sort.children[0]].rows, "{p}");
}

/// A plan printed without `VERBOSE` lists no outputs, and one printed
/// without `ANALYZE` counts nothing: each is refused, saying which.
#[tokio::test]
async fn plans_must_be_verbose() {
    let catalog = catalog().await;
    let json = std::fs::read_to_string(format!("{PG_DIR}/tpch/q06.json")).unwrap();
    let mut terse: Value = serde_json::from_str(&json).unwrap();
    fn strip(v: &mut Value) {
        let o = v.as_object_mut().unwrap();
        o.remove("Output");
        for c in o.get_mut("Plans").and_then(Value::as_array_mut).into_iter().flatten() {
            strip(c);
        }
    }
    strip(&mut terse[0]["Plan"]);
    let e = from_postgres(&catalog, "q", &terse.to_string(), None).unwrap_err().to_string();
    assert!(e.contains("VERBOSE"), "{e}");
    let explain = std::fs::read_to_string(format!("{PG_DIR}/explain/q06.json")).unwrap();
    let e = from_postgres(&catalog, "q", &explain, None).unwrap_err().to_string();
    assert!(e.contains("ANALYZE"), "{e}");
    assert!(!from_postgres_explain(&catalog, "q", &explain, None).unwrap().counted);
}
