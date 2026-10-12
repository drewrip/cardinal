//! Queries analyzed as DuckDB plans them, from a live `EXPLAIN (FORMAT JSON)`
//! of TPC-H at scale factor 0.01: each constant bound holds the query's true
//! count, and limits, which DuckDB prints without their counts, bound the
//! output as the query's clauses say. Needs the `duckdb` CLI.
//!
//! ```sh
//! cargo test --test plan_truth -- --nocapture
//! ```

mod fixtures;
mod live;

use cardinal::observed::from_duckdb_explain;
use fixtures::catalog;
use live::{database, duckdb_available, run};

/// Each query, and the bound its limits should give, if any.
const QUERIES: &[(&str, Option<u64>)] = &[
    ("select * from lineitem where l_quantity < 10 limit 5", Some(5)),
    // DuckDB's late materialization: the limit picks rowids, and a semi
    // join on them reads the rows' columns from another scan.
    ("select * from lineitem where l_quantity < 10 limit 5 offset 2", Some(5)),
    ("select * from lineitem limit 3 offset 60174", Some(3)),
    ("select * from lineitem limit 3 offset 70000", Some(3)),
    ("select * from orders order by o_totalprice limit 7", Some(7)),
    ("select * from orders order by o_totalprice desc limit 7 offset 3", Some(7)),
    ("select * from orders order by o_totalprice limit 7 offset 14998", Some(7)),
    ("select * from orders where o_orderstatus = 'F' order by o_orderdate, o_orderkey limit 12", Some(12)),
    ("select o_orderkey, o_totalprice from orders order by o_totalprice limit 7", Some(7)),
    ("select * from orders fetch first 4 rows only", Some(4)),
    ("select * from orders limit 4 offset 2", Some(4)),
    ("select count(*) from (select * from lineitem limit 100 offset 5)", Some(1)),
    ("select * from orders o1, orders o2 where o1.o_orderkey = o2.o_orderkey order by o1.o_totalprice limit 5", Some(5)),
    // Several limits: each is at most the largest.
    ("(select * from orders limit 10 offset 3) union all (select * from orders order by o_orderdate limit 20)", Some(40)),
    ("select * from (select * from orders limit 50) o join (select * from customer limit 20) c on o.o_custkey = c.c_custkey limit 2", Some(50)),
    ("with t as (select * from orders order by o_orderdate limit 9 offset 1) select * from t a join t b on a.o_orderkey = b.o_orderkey", Some(81)),
    ("select * from (select * from orders order by o_totalprice limit 50) o join lineitem l on l.l_orderkey = o.o_orderkey", None),
    ("select * from (select * from orders order by o_totalprice limit 50 offset 10) o join customer c on c.c_custkey = o.o_custkey", None),
    ("select * from orders where o_custkey in (select c_custkey from customer order by c_acctbal limit 10)", None),
    // Self-joins whose aliases' columns DuckDB prints by one name, or by
    // position above a join, which tells nothing apart: no bound, but sound.
    // (TPC-H q07, whose columns it prints by alias, is bounded: see
    // `fact_bounds`.)
    ("select n1.n_name, n2.n_name, count(*) from supplier, customer, nation n1, nation n2 \
      where s_nationkey = n1.n_nationkey and c_nationkey = n2.n_nationkey \
      and n1.n_name in ('FRANCE', 'GERMANY') and n2.n_name = 'CHINA' group by n1.n_name, n2.n_name", None),
    ("select a, b, count(*) from (select n1.n_name as a, n2.n_name as b from supplier, customer, nation n1, nation n2 \
      where s_nationkey = n1.n_nationkey and c_nationkey = n2.n_nationkey \
      and ((n1.n_name = 'FRANCE' and n2.n_name = 'CHINA') or (n1.n_name = 'CHINA' and n2.n_name = 'FRANCE'))) group by a, b", None),
    // DuckDB drops the subquery's limit: the clauses and limits do not
    // line up, and no limit is bounded.
    ("select * from orders where exists (select 1 from lineitem where l_orderkey = o_orderkey limit 1) limit 30", None),
    ("select * from orders limit 5 % 3", None),
    ("select * from orders order by o_orderdate limit 10 percent", None),
    ("select * from orders limit 0 offset 5", None),
];

#[tokio::test]
async fn bounds_hold() {
    if !duckdb_available() {
        eprintln!("skipped: no duckdb CLI");
        return;
    }
    let db = database();
    let catalog = catalog().await;
    let mut failures = vec![];
    for &(sql, expected) in QUERIES {
        let out = run(&db, &format!("EXPLAIN (FORMAT JSON) {sql};"), &["-list", "-noheader"]).unwrap();
        let json = &out[out.find('[').unwrap()..];
        let truth: u64 = run(&db, &format!("select count(*) from ({sql});"), &["-list", "-noheader"]).unwrap().trim().parse().unwrap();
        let plan = from_duckdb_explain(&catalog, "q", json, Some(sql)).unwrap();
        let a = cardinal::analyze_observed(&catalog, &plan, Default::default()).unwrap();
        let bound = a.bounds().unwrap().constant;
        println!("{truth} rows, X <= {bound:?}: {sql}");
        if bound.is_some_and(|b| b < truth) {
            failures.push(format!("{sql}: X <= {bound:?}, but {truth} rows\n{plan}"));
        } else if expected.is_some_and(|e| bound.is_none_or(|b| b > e)) {
            failures.push(format!("{sql}: X <= {bound:?}, not {expected:?}\n{plan}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}
