//! The 22 TPC-H queries, analyzed and validated on empty tables and on small
//! PK/FK-consistent TPC-H data. Run with `--nocapture` to see the summary table.

mod common;

use common::Expect::{MightGrow, Reduces};
use common::{Case, run_benchmark, tpch_datasets};

const CASES: &[Case] = &[
    Case {
        name: "tpch_q01",
        sql: include_str!("tpch/q01.sql"),
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "tpch_q02",
        sql: include_str!("tpch/q02.sql"),
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        name: "tpch_q03",
        sql: include_str!("tpch/q03.sql"),
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        name: "tpch_q04",
        sql: include_str!("tpch/q04.sql"),
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "tpch_q05",
        sql: include_str!("tpch/q05.sql"),
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        // ungrouped aggregate: 1 row even when lineitem is empty
        name: "tpch_q06",
        sql: include_str!("tpch/q06.sql"),
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "tpch_q07",
        sql: include_str!("tpch/q07.sql"),
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        name: "tpch_q08",
        sql: include_str!("tpch/q08.sql"),
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "tpch_q09",
        sql: include_str!("tpch/q09.sql"),
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        name: "tpch_q10",
        sql: include_str!("tpch/q10.sql"),
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        name: "tpch_q11",
        sql: include_str!("tpch/q11.sql"),
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "tpch_q12",
        sql: include_str!("tpch/q12.sql"),
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        // customer LEFT JOIN orders, grouped twice; bounded by |customer| via the group key
        name: "tpch_q13",
        sql: include_str!("tpch/q13.sql"),
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        // ungrouped aggregate
        name: "tpch_q14",
        sql: include_str!("tpch/q14.sql"),
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "tpch_q15",
        sql: include_str!("tpch/q15.sql"),
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        name: "tpch_q16",
        sql: include_str!("tpch/q16.sql"),
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        // ungrouped aggregate
        name: "tpch_q17",
        sql: include_str!("tpch/q17.sql"),
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "tpch_q18",
        sql: include_str!("tpch/q18.sql"),
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        // ungrouped aggregate
        name: "tpch_q19",
        sql: include_str!("tpch/q19.sql"),
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "tpch_q20",
        sql: include_str!("tpch/q20.sql"),
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        name: "tpch_q21",
        sql: include_str!("tpch/q21.sql"),
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "tpch_q22",
        sql: include_str!("tpch/q22.sql"),
        keys: Reduces,
        no_keys: Reduces,
    },
];

#[tokio::test]
async fn tpch_benchmark_with_keys() {
    run_benchmark(CASES, tpch_datasets(), true).await;
}

#[tokio::test]
async fn tpch_benchmark_without_keys() {
    run_benchmark(CASES, tpch_datasets(), false).await;
}
