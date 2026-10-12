//! Facts read off PostgreSQL `EXPLAIN (ANALYZE, VERBOSE)` profiles of TPC-H
//! at scale factor 0.01, checked against true counts. Regenerate the fixtures
//! with `scripts/postgres_fixtures.sh`; print every fact with
//! `cargo test --test postgres print_facts -- --nocapture`.

mod fixtures;

use std::collections::{BTreeMap, HashMap};

use cardinal::facts::{CountDialect, Fact, FactKind, FactSet, Ratio, State, derive_facts, states};
use cardinal::observed::{Catalog, ONode, ObservedPlan, Op, from_postgres, from_postgres_explain};
use datafusion::common::JoinType;
use fixtures::{PG_DIR, catalog, context, pg_plans, pg_query};
use serde_json::Value;

#[tokio::test]
async fn print_facts() {
    let mut all = vec![];
    let mut taints = BTreeMap::<String, usize>::new();
    for dir in ["extra", "tpch", "indexed", "parallel", "v14"] {
        for p in pg_plans(dir).await {
            println!("==== {dir}/{}\n{p}", p.name);
            for (i, s) in states(&p).iter().enumerate() {
                match s {
                    State::Clean(c) => println!("  #{i}: {}", c.canonical()),
                    State::Pending(c, pending) => println!("  #{i}: {} (pending {})", c.canonical(), pending.len()),
                    State::Tainted(t) => {
                        println!("  #{i}: tainted: {t}");
                        *taints.entry(t.to_string()).or_default() += 1;
                    }
                }
            }
            println!("{}", derive_facts(std::slice::from_ref(&p)));
            all.push(p);
        }
    }
    let facts = derive_facts(&all);
    println!("==== all {} plans: {} facts\n{facts}", all.len(), facts.len());
    println!("==== tainted operators, by reason");
    for (t, n) in taints {
        println!("{n:4} {t}");
    }
}

/// How much of each set of profiles gives facts: print it with
/// `cargo test --test postgres coverage -- --nocapture`.
#[tokio::test]
async fn coverage() {
    for dir in ["extra", "tpch", "indexed", "parallel", "v14"] {
        let plans = pg_plans(dir).await;
        let nodes: usize = plans.iter().map(|p| p.nodes.len()).sum();
        let counted: usize = plans.iter().map(|p| p.nodes.iter().filter(|n| n.counted).count()).sum();
        let facts = derive_facts(&plans);
        println!("{dir}: {counted} of {nodes} operators counted, {} facts, {} bounds", facts.len(), facts.bounds().count());
    }
}

/// Every plan's facts together: of the plans without indexes, with them,
/// and of version 14's.
async fn all_facts() -> FactSet {
    let mut all = pg_plans("extra").await;
    all.extend(pg_plans("tpch").await);
    all.extend(pg_plans("indexed").await);
    all.extend(pg_plans("parallel").await);
    all.extend(pg_plans("v14").await);
    derive_facts(&all)
}

/// Each fact (`=`) and bound (`<=`) as written in `fact_checks.json`.
fn label(f: &Fact, bound: bool) -> String {
    format!("{} {}", if bound { "<=" } else { "=" }, f.kind)
}

/// A fact no profile counted, as written there.
fn uncounted(kind: &FactKind) -> String {
    format!("? {kind}")
}

/// Writes a query counting what each fact and bound counts, for
/// `scripts/postgres_fixtures.sh` to run into `fact_checks.json`.
#[tokio::test]
async fn dump_fact_queries() {
    let facts = all_facts().await;
    let catalog = catalog().await;
    let all = facts.iter().map(|f| (f, false)).chain(facts.bounds().map(|f| (f, true)));
    let all = all.map(|(f, bound)| (&f.kind, label(f, bound))).chain(facts.unobserved().map(|k| (k, uncounted(k))));
    let rows: Vec<String> = all
        .filter_map(|(kind, label)| {
            let c = kind.count_sql_in(&catalog, &facts, CountDialect::Postgres)?;
            let of = c.of.map(|q| format!("({q})")).unwrap_or("NULL::bigint".into());
            Some(format!("SELECT '{}' AS fact, ({}) AS value, {of} AS of", label.replace('\'', "''"), c.value))
        })
        .collect();
    std::fs::write(format!("{PG_DIR}/fact_checks.sql"), rows.join("\nUNION ALL ") + ";\n").unwrap();
}

/// Every fact and bound, against PostgreSQL's count of what it counts: a
/// fact equal to it, a bound at least it.
#[tokio::test]
async fn facts_match_postgres() {
    let checks: Value = serde_json::from_str(&std::fs::read_to_string(format!("{PG_DIR}/fact_checks.json")).unwrap()).unwrap();
    let counted: HashMap<String, (u64, Option<u64>)> = checks
        .as_array()
        .unwrap()
        .iter()
        .map(|r| (r["fact"].as_str().unwrap().to_string(), (r["value"].as_u64().unwrap(), r["of"].as_u64())))
        .collect();
    let facts = all_facts().await;
    let catalog = catalog().await;
    let mut checked = 0;
    let all = facts.iter().map(|f| (f, false)).chain(facts.bounds().map(|f| (f, true)));
    for (f, bound) in all.filter(|(f, _)| f.kind.count_sql_in(&catalog, &facts, CountDialect::Postgres).is_some()) {
        let Some(&(n, of)) = counted.get(&label(f, bound)) else {
            panic!("{} is not in fact_checks.json: run scripts/postgres_fixtures.sh", label(f, bound))
        };
        let ok = match (bound, &f.kind, of) {
            (true, _, _) => f.value.as_int().is_some_and(|b| b >= n),
            (false, FactKind::Unique { .. }, Some(of)) => n == of,
            (false, _, Some(of)) => Ratio::new(n, of) == Some(f.value),
            (false, _, None) => f.value.as_int() == Some(n),
        };
        assert!(ok, "{} is {n}{}, from {:?}", label(f, bound), of.map(|o| format!("/{o}")).unwrap_or_default(), f.origins);
        checked += 1;
    }
    assert!(checked > 100, "only {checked} facts and bounds checked");
}

/// What stopped early or ran several times has rows no profile counted,
/// and still the rows its plan says: each of its facts is named, a query
/// counts it, and its count agrees with every fact the profiles gave.
#[tokio::test]
async fn what_was_not_counted_is_named() {
    let checks: Value = serde_json::from_str(&std::fs::read_to_string(format!("{PG_DIR}/fact_checks.json")).unwrap()).unwrap();
    let counted: HashMap<&str, (u64, Option<u64>)> =
        checks.as_array().unwrap().iter().map(|r| (r["fact"].as_str().unwrap(), (r["value"].as_u64().unwrap(), r["of"].as_u64()))).collect();
    let mut facts = all_facts().await;
    let catalog = catalog().await;
    let kinds: Vec<FactKind> = facts.unobserved().cloned().collect();
    // An `EXISTS` read orders to the first of them over a price: no
    // profile here counts them all.
    let exists = "|orders where orders.o_totalprice > 400000.00|";
    assert!(kinds.iter().any(|k| k.to_string() == exists), "{}", kinds.iter().map(|k| format!("{k}\n")).collect::<String>());
    let before = facts.len();
    let mut added = 0;
    let countable: Vec<&FactKind> = kinds.iter().filter(|k| k.count_sql_in(&catalog, &facts, CountDialect::Postgres).is_some()).collect();
    for kind in countable {
        let Some(&(n, of)) = counted.get(uncounted(kind).as_str()) else {
            panic!("{} is not in fact_checks.json: run scripts/postgres_fixtures.sh", uncounted(kind))
        };
        added += kind.counted(n, of).is_some_and(|f| facts.insert(f)) as usize;
    }
    assert!(added > 4, "only {added} of {} counted", kinds.len());
    assert_eq!(facts.find(exists).unwrap().value, Ratio::int(16));
    facts.close();
    assert!(facts.conflicts.is_empty(), "{:#?}", facts.conflicts);
    assert!(facts.len() >= before + added && facts.unobserved().all(|k| !kinds.contains(k) || facts.get(k).is_none()));
    println!("{added} of {} facts the profiles did not count, counted: {before} facts, then {}", kinds.len(), facts.len());

    // A plan that was not run has every fact of its profile to count.
    let explained = from_postgres_explain(&catalog, "q03", &std::fs::read_to_string(format!("{PG_DIR}/explain/q03.json")).unwrap(), Some(&pg_query("q03"))).unwrap();
    let profiled = derive_facts(&[plan("tpch", "q03").await]);
    let mut unrun = FactSet::default();
    unrun.observe(&explained);
    assert!(unrun.is_empty() && profiled.len() > 5);
    let named: Vec<&FactKind> = unrun.unobserved().collect();
    for f in profiled.iter().filter(|f| matches!(f.origins[..], [cardinal::facts::Origin::Observed { .. }])) {
        assert!(named.contains(&&f.kind), "{f} is not among {named:#?}");
    }
}

/// The same context seen in different plans must have one value: the main
/// check that the contexts name the rows they claim to. With indexes, the
/// same queries run as index scans, nested loops and merge joins, whose
/// rows are counted where they are whole, and must agree with the rest.
#[tokio::test]
async fn no_conflicts() {
    let mut all = pg_plans("extra").await;
    all.extend(pg_plans("tpch").await);
    let plain = derive_facts(&all);
    assert!(plain.conflicts.is_empty(), "{:#?}", plain.conflicts);
    assert!(plain.len() + plain.bounds().count() > 100, "{plain}");
    all.extend(pg_plans("indexed").await);
    all.extend(pg_plans("parallel").await);
    all.extend(pg_plans("v14").await);
    let facts = derive_facts(&all);
    assert!(facts.conflicts.is_empty(), "{:#?}", facts.conflicts);
    // Each fact of the plans without indexes is still one, with its value.
    for f in plain.iter() {
        assert_eq!(facts.get(&f.kind).map(|g| g.value), Some(f.value), "{f}");
    }
}

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

/// A scan reports the rows its filter left, and those it removed: the
/// table's rows, and the filter's share of them, both exactly. (DuckDB's
/// scan gives only a bound: its filter may let through more.)
#[tokio::test]
async fn a_scan_is_a_scan_and_its_filter() {
    let p = plan("extra", "scan_filter").await;
    let [scan] = operators(&p, "Seq Scan", |op| matches!(op, Op::Scan { .. }))[..] else { panic!("{p}") };
    let [filter] = operators(&p, "Seq Scan", |op| matches!(op, Op::Filter { .. }))[..] else { panic!("{p}") };
    assert_eq!((scan.rows, scan.counted), (60175, true));
    assert_eq!((filter.rows, filter.counted), (10816, true));
    let facts = derive_facts(&[p]);
    assert_eq!(facts.find("|lineitem|").unwrap().value, Ratio::int(60175));
    assert_eq!(facts.find("s(lineitem.l_quantity < 10.00 | lineitem)").unwrap().value, Ratio::new(10816, 60175).unwrap());
    assert_eq!(facts.bounds().count(), 0, "{facts}");
}

/// An index scan on the inner side of a nested loop looks up the join's
/// key: the condition printed on the scan is the join's. The scan ran once
/// per outer row, and its rows are an average: only the join's are counted.
#[tokio::test]
async fn an_index_lookup_is_its_joins_condition() {
    let p = plan("indexed", "q03").await;
    let [join] = operators(&p, "Nested Loop", |op| matches!(op, Op::Join { .. }))[..] else { panic!("{p}") };
    let Op::Join { kind: JoinType::Inner, on } = &join.op else { panic!("{p}") };
    assert!(on.iter().any(|c| c.text.contains("o_orderkey = lineitem#") && c.expr.is_some()), "{on:?}");
    assert!(join.counted);
    let [scan] = operators(&p, "Index Scan", |op| matches!(op, Op::Scan { .. }))[..] else { panic!("{p}") };
    let Op::Scan { table, filters, .. } = &scan.op else { unreachable!() };
    assert_eq!((table.as_str(), filters.len(), scan.counted), ("lineitem", 0, false));
    // The join's rows are the same as without indexes.
    let hashed = derive_facts(&[plan("tpch", "q03").await]);
    let looped = derive_facts(&[p]);
    let joined = "|customer × lineitem × orders where customer.c_custkey = orders.o_custkey and customer.c_mktsegment = 'BUILDING' \
                  and lineitem.l_orderkey = orders.o_orderkey and lineitem.l_shipdate > CAST('1995-03-15' AS DATE) \
                  and orders.o_orderdate < CAST('1995-03-15' AS DATE)|";
    assert_eq!(looped.find(joined).map(|f| f.value), hashed.find(joined).map(|f| f.value), "{looped}");
    assert!(looped.find(joined).is_some(), "{looped}");
}

/// What ran more than once reports an average, which is no count where
/// what it read changed between runs, or a run stopped at a first match.
#[tokio::test]
async fn averages_are_not_counts() {
    let p = plan("tpch", "q20").await;
    let materialized = operators(&p, "Materialize", |_| true);
    assert!(!materialized.is_empty() && materialized.iter().all(|n| !n.counted), "{p}");
    assert!(p.to_string().contains("(Materialize) rows=?"), "{p}");
}

/// The inner side of a nested loop that binds nothing in it outputs the
/// same rows each time it runs: their average is their count.
#[tokio::test]
async fn a_rescan_counts_its_rows() {
    let json = std::fs::read_to_string(format!("{PG_DIR}/extra/nested_rescan.json")).unwrap();
    assert!(json.contains("\"Actual Loops\": 2"), "{json}");
    let p = plan("extra", "nested_rescan").await;
    let [supplier] = operators(&p, "Seq Scan", |op| matches!(op, Op::Scan { table, .. } if table == "supplier"))[..] else { panic!("{p}") };
    assert!(supplier.counted && supplier.rows == 100, "{p}");
    let facts = derive_facts(&[p]);
    let join = "s(supplier.s_nationkey < nation.n_nationkey | nation × supplier where starts_with(nation.n_name, 'A'))";
    assert_eq!(facts.find(join).unwrap().value, Ratio::new(3, 2 * 100).unwrap(), "{facts}");
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

/// The processes of a parallel plan split a scan's rows, and each reports
/// an average over them all, to two decimals: times the processes, their
/// sum. Not the rows a filter removed, which are rounded to a whole
/// number, as versions before 18 round every average. Groups aggregated in
/// part are no rows of the query until the aggregate above finishes them.
#[tokio::test]
async fn rows_split_between_processes_sum() {
    let json = std::fs::read_to_string(format!("{PG_DIR}/parallel/q01.json")).unwrap();
    assert!(json.contains("\"Parallel Aware\": true") && json.contains("\"Partial Mode\": \"Partial\""), "{json}");
    let serial = plan("tpch", "q01").await;
    let [kept] = operators(&serial, "Seq Scan", |op| matches!(op, Op::Filter { .. }))[..] else { panic!("{serial}") };
    let p = plan("parallel", "q01").await;
    let [filter] = operators(&p, "Seq Scan", |op| matches!(op, Op::Filter { .. }))[..] else { panic!("{p}") };
    assert!(filter.counted && filter.rows == kept.rows, "{p}");
    let [scan] = operators(&p, "Seq Scan", |op| matches!(op, Op::Scan { .. }))[..] else { panic!("{p}") };
    assert!(!scan.counted, "{p}");
    for partial in ["Gather", "Gather Merge"] {
        assert!(operators(&p, partial, |_| true).iter().all(|n| !n.counted), "{p}");
    }
    assert_eq!(p.nodes[p.root].rows, serial.nodes[serial.root].rows, "{p}");
    let facts = derive_facts(&[p, serial]);
    assert!(facts.conflicts.is_empty(), "{facts}");

    // A `DISTINCT` each process computes of its own rows is not marked as
    // partial, and is: a value two of them met is two of its rows.
    let json = std::fs::read_to_string(format!("{PG_DIR}/parallel/distinct.json")).unwrap();
    assert!(!json.contains("\"Partial Mode\": \"Partial\""), "{json}");
    let p = plan("parallel", "distinct").await;
    let [below, last, _] = operators(&p, "Aggregate", |_| true)[..] else { panic!("{p}") };
    assert!(!below.counted && last.counted && matches!(last.op, Op::Aggregate { .. }), "{p}");
    assert!(operators(&p, "Gather", |_| true).iter().all(|n| !n.counted), "{p}");

    // Under a `Gather` that ran more than once (in a subquery, or the
    // inner side of a nested loop), each process ran several times: the
    // sum over its runs counts each row as often.
    let json = std::fs::read_to_string(format!("{PG_DIR}/parallel/q01.json")).unwrap();
    let mut value: Value = serde_json::from_str(&json).unwrap();
    let gather = &mut value[0]["Plan"]["Plans"][0];
    assert_eq!((gather["Node Type"].as_str(), gather["Actual Loops"].as_u64()), (Some("Gather Merge"), Some(1)), "{json}");
    gather["Actual Loops"] = 2.into();
    let p = from_postgres(&catalog().await, "q01", &value.to_string(), Some(&pg_query("q01"))).unwrap();
    let [filter] = operators(&p, "Seq Scan", |op| matches!(op, Op::Filter { .. }))[..] else { panic!("{p}") };
    assert!(!filter.counted, "{p}");

    // Rounded to whole numbers, the averages say no more than that.
    let mut rounded = String::new();
    for line in json.lines() {
        match line.split_once("\"Actual Rows\": ") {
            Some((before, n)) => rounded += &format!("{before}\"Actual Rows\": {:.0},\n", n.trim_end_matches(',').parse::<f64>().unwrap()),
            None => rounded += &format!("{line}\n"),
        }
    }
    let p = from_postgres(&catalog().await, "q01", &rounded, Some(&pg_query("q01"))).unwrap();
    let [filter] = operators(&p, "Seq Scan", |op| matches!(op, Op::Filter { .. }))[..] else { panic!("{p}") };
    assert!(!filter.counted, "{p}");
}

/// An uncorrelated scalar subquery is an InitPlan, run once: its one row
/// is joined to the rows of the filter that reads it. Before version 17 it
/// is printed as a parameter (`$0`), which reads the same.
#[tokio::test]
async fn an_init_plan_is_its_row_beside_every_row() {
    let p = plan("tpch", "q22").await;
    let [cross] = operators(&p, "InitPlan", |op| matches!(op, Op::Join { kind: JoinType::Inner, on } if on.is_empty()))[..] else { panic!("{p}") };
    assert_eq!((cross.rows, cross.counted), (1500, true));
    let facts = derive_facts(std::slice::from_ref(&p));
    assert!(facts.iter().any(|f| f.kind.to_string().contains("\"value\".\"avg(customer.c_acctbal) of aggregate(")), "{facts}");

    let json = std::fs::read_to_string(format!("{PG_DIR}/tpch/q22.json")).unwrap();
    let before = json.replace("\"InitPlan 1\"", "\"InitPlan 1 (returns $0)\"").replace("(InitPlan 1).col1", "$0").replace(".00,", ",");
    assert_ne!(before, json);
    let old = from_postgres(&catalog().await, "q22", &before, Some(&pg_query("q22"))).unwrap();
    assert_eq!(old.to_string(), p.to_string());
    assert_eq!(derive_facts(&[old]).to_string(), facts.to_string());
}

/// `x NOT IN (subquery)` is a hashed SubPlan in a filter: a mark join
/// against the subquery, run once, and a filter on the mark.
#[tokio::test]
async fn an_in_subplan_is_a_mark_join() {
    let p = plan("tpch", "q16").await;
    let [mark] = operators(&p, "SubPlan", |op| matches!(op, Op::Join { kind: JoinType::LeftMark, .. }))[..] else { panic!("{p}") };
    assert_eq!((mark.rows, mark.counted), (8000, true));
    let [kept] = operators(&p, "Seq Scan", |op| matches!(op, Op::MarkFilter { negated: true }))[..] else { panic!("{p}") };
    assert_eq!(kept.rows, 8000);
    let facts = derive_facts(&[p]);
    assert!(facts.iter().any(|f| f.kind.to_string().contains("not in[partsupp.ps_suppkey = supplier.s_suppkey]")), "{facts}");
}

/// PostgreSQL computes a CTE as it is read: under a limit, only as far as
/// the limit read, and none of its operators' rows are counts.
#[tokio::test]
async fn a_cte_read_short_is_not_counted() {
    let p = plan("extra", "cte_limit").await;
    let [scan] = operators(&p, "Seq Scan", |op| matches!(op, Op::Scan { .. }))[..] else { panic!("{p}") };
    assert!(!scan.counted, "{p}");
    assert!(derive_facts(&[p]).is_empty());
    // Read to the end, it is whole.
    let p = plan("extra", "cte").await;
    let [scan] = operators(&p, "Seq Scan", |op| matches!(op, Op::Scan { .. }))[..] else { panic!("{p}") };
    assert_eq!((scan.rows, scan.counted), (15000, true));
}

/// A subquery's columns are read by the names the query gives them: `rn`,
/// the row number, whose first rows are a group per partition. PostgreSQL
/// stops the window at `rn <= 1` and checks `rn = 1` above.
#[tokio::test]
async fn first_rows_of_a_window() {
    let p = plan("extra", "window_first").await;
    let p_text = p.to_string();
    assert!(operators(&p, "WindowAgg", |op| matches!(op, Op::Filter { .. })).len() == 1, "{p}");
    let s = states(&p);
    let State::Clean(c) = &s[p.root] else { panic!("{:?}", s[p.root]) };
    assert_eq!(c.canonical().to_string(), "group[orders.o_custkey](orders)");
    assert_eq!(derive_facts(&[p]).find("ndv(orders.o_custkey | orders)").unwrap().value, Ratio::int(1000));
    // Without the query, `s.rn` names nothing.
    let json = std::fs::read_to_string(format!("{PG_DIR}/extra/window_first.json")).unwrap();
    let unnamed = from_postgres(&catalog().await, "w", &json, None).unwrap();
    assert!(matches!(states(&unnamed)[unnamed.root], State::Tainted(_)), "{unnamed}");

    // Before version 18 a window function is printed without its window
    // (`row_number() OVER (?)`): the query's one `row_number()` defines it.
    // Version 14 has no run condition; 15 to 17 print one the same way.
    let group = |p: &ObservedPlan| match &states(p)[p.root] {
        State::Clean(c) => c.canonical().to_string(),
        s => panic!("{s:?}\n{p}"),
    };
    assert_eq!(group(&plan("v14", "window_first").await), "group[orders.o_custkey](orders)");
    let mut older: Value = serde_json::from_str(&json).unwrap();
    fn unname(v: &mut Value) {
        match v {
            Value::String(s) => *s = s.replace("OVER w1", "OVER (?)"),
            Value::Array(a) => a.iter_mut().for_each(unname),
            Value::Object(o) => {
                o.remove("Window");
                o.values_mut().for_each(unname);
            }
            _ => {}
        }
    }
    unname(&mut older);
    assert!(older.to_string().contains("(row_number() OVER (?) <= 1)"));
    let older = from_postgres(&catalog().await, "w", &older.to_string(), Some(&pg_query("window_first"))).unwrap();
    assert_eq!(group(&older), "group[orders.o_custkey](orders)");
    assert_eq!(older.to_string(), p_text);
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

/// A scan of a partial index keeps the rows of the index's predicate,
/// which the plan does not print, with the query's conditions the predicate
/// implies: here it counts the urgent orders before a date (90), and prints
/// only the date (388 orders are before it). So a scan of an index is read
/// only once the catalog has the partial indexes, and a scan of one of them
/// keeps the rows of its predicate too.
#[tokio::test]
async fn a_partial_index_hides_a_predicate() {
    let json = std::fs::read_to_string(format!("{PG_DIR}/partial/urgent.json")).unwrap();
    let sql = std::fs::read_to_string(format!("{PG_DIR}/partial/urgent.sql")).unwrap();
    assert!(json.contains("orders_urgent") && !json.contains("URGENT"), "{json}");
    let before = "|orders where orders.o_orderdate < CAST('1992-03-01' AS DATE)|";
    let urgent = "|orders where orders.o_orderdate < CAST('1992-03-01' AS DATE) and orders.o_orderpriority = '1-URGENT'|";
    let catalog = || async { Catalog::from_context(&context()).await.unwrap() };

    // Not given, any index may be partial.
    let p = from_postgres(&catalog().await, "urgent", &json, Some(&sql)).unwrap();
    assert!(matches!(&states(&p)[p.root], State::Tainted(t) if t.to_string().contains("orders_urgent")), "{p}");
    assert!(derive_facts(&[p]).is_empty());

    // As PostgreSQL's catalog prints them.
    let listed = std::fs::read_to_string(format!("{PG_DIR}/partial/indexes.txt")).unwrap();
    let indexes: Vec<(&str, &str)> = listed.lines().filter_map(|l| l.split_once('|')).collect();
    assert_eq!(indexes.len(), 1, "{listed}");
    let p = from_postgres(&catalog().await.with_partial_indexes(indexes), "urgent", &json, Some(&sql)).unwrap();
    assert!(matches!(&states(&p)[p.root], State::Clean(_)), "{p}");
    let facts = derive_facts(&[p]);
    assert_eq!(facts.find(urgent).unwrap().value, Ratio::int(90), "{facts}");
    assert!(facts.find(before).is_none(), "{facts}");

    // A predicate that cannot be read is one that does not resolve.
    let p = from_postgres(&catalog().await.with_partial_indexes([("orders_urgent", "(no_such_column > 1)")]), "urgent", &json, Some(&sql)).unwrap();
    assert!(matches!(&states(&p)[p.root], State::Tainted(t) if t.to_string().contains("orders_urgent")), "{p}");
    assert!(derive_facts(&[p]).is_empty());

    // Given wrongly as not partial, it reads as the date's count.
    let p = from_postgres(&catalog().await.with_partial_indexes([("another", "true")]), "urgent", &json, Some(&sql)).unwrap();
    assert_eq!(derive_facts(&[p]).find(before).unwrap().value, Ratio::int(90));

    // An index scan of the fixtures, whose indexes are all whole, is not
    // read either until that is said.
    let json = std::fs::read_to_string(format!("{PG_DIR}/indexed/q04.json")).unwrap();
    let p = from_postgres(&catalog().await, "q04", &json, None).unwrap();
    assert!(matches!(&states(&p)[p.root], State::Tainted(_)), "{p}");
    let p = plan("indexed", "q04").await;
    assert!(matches!(&states(&p)[p.root], State::Clean(_)), "{p}");
}

/// A `Hash` reports the rows it stored: not those whose key is NULL, which
/// match nothing (12 of 27 here). It passes its input's rows to the join,
/// so its rows are those counted below it, and the join's share is of them.
#[tokio::test]
async fn a_hash_has_its_inputs_rows() {
    let json = std::fs::read_to_string(format!("{PG_DIR}/extra/hash_null_keys.json")).unwrap();
    assert!(json.contains("\"Node Type\": \"Hash\"") && json.contains("\"Actual Rows\": 12.00"), "{json}");
    let p = plan("extra", "hash_null_keys").await;
    let hashes = operators(&p, "Hash", |_| true);
    assert!(!hashes.is_empty() && hashes.iter().all(|h| h.counted && h.rows == 27), "{p}");
    let facts = derive_facts(&[p]);
    assert!(facts.conflicts.is_empty(), "{facts}");
    assert_eq!(facts.find("|orders where orders.o_orderkey < 100|").unwrap().value, Ratio::int(27), "{facts}");
    let join = facts.iter().find(|f| matches!(&f.kind, FactKind::Selectivity { over, .. } if over.to_string().contains('×'))).expect("the join's share");
    assert_eq!(join.value, Ratio::new(7380, 60175 * 27).unwrap(), "{facts}");
}

/// An uncorrelated `EXISTS` is an InitPlan that reads to its first row:
/// what it read is no count. A semi join's nested loop likewise reads its
/// inner side to the first match.
#[tokio::test]
async fn what_stops_at_a_first_row_is_not_counted() {
    let p = plan("extra", "exists_uncorrelated").await;
    let scans = operators(&p, "Seq Scan", |op| matches!(op, Op::Scan { table, .. } if table == "orders"));
    assert!(!scans.is_empty() && scans.iter().all(|s| !s.counted), "{p}");
    let facts = derive_facts(&[p]);
    assert!(facts.iter().all(|f| !f.kind.to_string().contains("orders")), "{facts}");
    assert_eq!(facts.find("|customer|").unwrap().value, Ratio::int(1500));

    let p = plan("extra", "semi_first_match").await;
    let facts = derive_facts(&[p]);
    assert!(facts.conflicts.is_empty(), "{facts}");
    if let Some(f) = facts.find("|supplier|") {
        assert_eq!(f.value, Ratio::int(100), "{facts}");
    }
}
