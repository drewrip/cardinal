//! Harder queries over the shop schema, validated on real data: empty tables,
//! single rows, PK/FK-consistent data, and skewed data with duplicate keys and
//! NULLs. Each case runs twice: with primary keys declared on `users.id`,
//! `orders.id` and `products.id` (only on data where they hold), and with no
//! keys. Run with `--nocapture` to see the summary tables.

mod common;

use common::Expect::{MightGrow, Reduces};
use common::{Case, run_benchmark, shop_datasets};

const CASES: &[Case] = &[
    // --- Nested and correlated subqueries --------------------------------
    Case {
        name: "deep_nesting_semi",
        sql: "SELECT * FROM users WHERE id IN (
                SELECT user_id FROM orders
                WHERE amount > (SELECT avg(amount) FROM orders)
                  AND EXISTS (SELECT 1 FROM order_items oi WHERE oi.order_id = orders.id))",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        // Decorrelated into `users LEFT JOIN (orders grouped by user_id)`. The
        // grouped side is unique on user_id, so every user appears exactly once.
        name: "correlated_scalar_in_select",
        sql: "SELECT u.id, (SELECT max(o.amount) FROM orders o WHERE o.user_id = u.id) FROM users u",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "correlated_scalar_in_where",
        sql: "SELECT * FROM orders o
              WHERE o.amount > (SELECT avg(o2.amount) FROM orders o2 WHERE o2.user_id = o.user_id)",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "scalar_subquery_in_case",
        sql: "SELECT id, CASE WHEN age > (SELECT avg(age) FROM users) THEN 'old' ELSE 'young' END
              FROM users",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "not_exists_with_residual",
        sql: "SELECT * FROM users u WHERE NOT EXISTS (
                SELECT 1 FROM orders o WHERE o.user_id = u.id AND o.amount > 100)",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "not_in_null_aware",
        sql: "SELECT * FROM users WHERE id NOT IN (SELECT user_id FROM orders)",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "exists_or_mark_join",
        sql: "SELECT * FROM users u
              WHERE u.age > 40 OR EXISTS (SELECT 1 FROM orders o WHERE o.user_id = u.id)",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "in_grouped_having",
        sql: "SELECT * FROM orders WHERE user_id IN (
                SELECT user_id FROM orders GROUP BY user_id HAVING count(*) > 1)",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        // The optimizer turns the subquery's inner join into a semi join, since
        // only `o` columns are used, so no key is needed.
        name: "exists_over_join",
        sql: "SELECT * FROM users u WHERE EXISTS (
                SELECT 1 FROM orders o JOIN order_items oi ON o.id = oi.order_id
                WHERE o.user_id = u.id)",
        keys: Reduces,
        no_keys: Reduces,
    },
    // --- CTEs ------------------------------------------------------------
    Case {
        // Joins two GROUP BY outputs on their group key, which is unique.
        name: "cte_referenced_twice",
        sql: "WITH s AS (SELECT user_id, sum(amount) AS t FROM orders GROUP BY user_id)
              SELECT * FROM s a JOIN s b ON a.user_id = b.user_id",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "cte_chain",
        sql: "WITH a AS (SELECT * FROM orders WHERE amount > 10),
                   b AS (SELECT user_id, count(*) AS c FROM a GROUP BY user_id),
                   c AS (SELECT * FROM b JOIN users ON b.user_id = users.id)
              SELECT * FROM c WHERE c > 1",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "recursive_cte",
        sql: "WITH RECURSIVE r(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM r WHERE n < 100)
              SELECT count(*) FROM r",
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "recursive_cte_join_table",
        sql: "WITH RECURSIVE r(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM r WHERE n < 100)
              SELECT u.* FROM users u JOIN r ON u.age = r.n",
        keys: MightGrow,
        no_keys: MightGrow,
    },
    // --- Joins -----------------------------------------------------------
    Case {
        // `age` is not a key, so the bound is l * r.
        name: "many_to_many_self_join",
        sql: "SELECT * FROM users a JOIN users b ON a.age = b.age",
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "fk_chain_four_way",
        sql: "SELECT u.name, p.price, oi.qty FROM users u
              JOIN orders o ON u.id = o.user_id
              JOIN order_items oi ON o.id = oi.order_id
              JOIN products p ON p.id = oi.product_id",
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        name: "implicit_three_way",
        sql: "SELECT * FROM users, orders, products
              WHERE users.id = orders.user_id AND orders.id = products.id",
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        name: "join_with_residual_filter",
        sql: "SELECT * FROM users u JOIN orders o ON u.id = o.user_id AND o.amount > u.age",
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        name: "left_join_is_null_anti",
        sql: "SELECT u.* FROM users u LEFT JOIN orders o ON u.id = o.user_id WHERE o.id IS NULL",
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        name: "left_join_chain",
        sql: "SELECT * FROM users u
              LEFT JOIN orders o ON u.id = o.user_id
              LEFT JOIN order_items oi ON o.id = oi.order_id",
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "right_join",
        sql: "SELECT * FROM orders o RIGHT JOIN users u ON o.user_id = u.id",
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        name: "full_join_duplicates",
        sql: "SELECT * FROM users u FULL JOIN orders o ON u.id = o.user_id",
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        // Rewritten by the optimizer into a semi join under the DISTINCT.
        name: "distinct_over_join",
        sql: "SELECT DISTINCT u.id FROM users u JOIN orders o ON u.id = o.user_id",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "join_limited_subquery",
        sql: "SELECT * FROM (SELECT * FROM users ORDER BY age, id LIMIT 3) u
              JOIN orders o ON u.id = o.user_id",
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        // DataFusion plans INTERSECT ALL as a plain semi join.
        name: "intersect_all",
        sql: "SELECT id FROM users INTERSECT ALL SELECT user_id FROM orders",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "except_distinct",
        sql: "SELECT age FROM users EXCEPT SELECT user_id FROM orders",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "theta_join_then_group",
        sql: "SELECT u.id, count(*) FROM users u JOIN orders o ON o.amount > u.age GROUP BY u.id",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "cross_with_scalar_aggregate",
        sql: "SELECT * FROM users CROSS JOIN (SELECT count(*) AS c FROM orders)",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "values_join",
        sql: "SELECT * FROM users u JOIN (VALUES (1), (2), (3)) AS v(x) ON u.id = v.x",
        keys: MightGrow,
        no_keys: MightGrow,
    },
    // --- Set operations ----------------------------------------------------
    Case {
        name: "union_all_triple_self",
        sql: "SELECT id FROM users UNION ALL SELECT id FROM users UNION ALL SELECT id FROM users",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "union_all_of_joins",
        sql: "SELECT u.id FROM users u JOIN orders o ON u.id = o.user_id
              UNION ALL
              SELECT p.id FROM products p JOIN order_items oi ON p.id = oi.product_id",
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        name: "union_distinct_of_cross",
        sql: "SELECT u.id FROM users u CROSS JOIN products p UNION SELECT id FROM orders",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "union_all_of_aggregates",
        sql: "SELECT count(*) FROM users UNION ALL SELECT count(*) FROM orders",
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "aggregate_over_union",
        sql:
            "SELECT id, count(*) FROM (SELECT id FROM users UNION ALL SELECT user_id FROM orders) t
              GROUP BY id",
        keys: Reduces,
        no_keys: Reduces,
    },
    // --- Aggregation and windows ------------------------------------------
    Case {
        name: "nested_aggregates",
        sql: "SELECT cnt, count(*) FROM (
                SELECT user_id, count(*) AS cnt FROM orders GROUP BY user_id) t
              GROUP BY cnt",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "having_without_group_by",
        sql: "SELECT count(*) FROM users HAVING count(*) > 5",
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "count_distinct",
        sql: "SELECT count(DISTINCT user_id) FROM orders",
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "grouping_sets",
        sql: "SELECT age, name, count(*) FROM users GROUP BY GROUPING SETS ((age), (name), ())",
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "cube",
        sql: "SELECT age, name, count(*) FROM users GROUP BY CUBE (age, name)",
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "distinct_on",
        sql: "SELECT DISTINCT ON (age) id, age FROM users ORDER BY age, id",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "window_top_n_per_group",
        sql: "SELECT * FROM (
                SELECT id, age, row_number() OVER (PARTITION BY age ORDER BY id) AS rn FROM users) t
              WHERE rn <= 2",
        keys: Reduces,
        no_keys: Reduces,
    },
    // --- Row generators and trivial plans ---------------------------------
    Case {
        name: "unnest_expands_rows",
        sql: "SELECT unnest(make_array(id, age, id)) FROM users",
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "generate_series_cross",
        sql: "SELECT * FROM users CROSS JOIN generate_series(1, 3)",
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "where_false",
        sql: "SELECT * FROM users WHERE 1 = 0",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "limit_zero",
        sql: "SELECT * FROM users LIMIT 0",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "nested_derived_filters",
        sql: "SELECT * FROM (SELECT * FROM (SELECT * FROM users WHERE age > 20) a WHERE age < 60) b
              WHERE id > 2",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "select_constant",
        sql: "SELECT 1",
        keys: MightGrow,
        no_keys: MightGrow,
    },
    // --- Adversarial --------------------------------------------------------
    Case {
        // Validation must not flag a violation just because random() differs
        // between evaluations.
        name: "volatile_union_all",
        sql: "SELECT id FROM users WHERE random() < 0.5
              UNION ALL SELECT id FROM users WHERE random() < 0.5",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "volatile_filter_under_key_join",
        sql: "SELECT * FROM (SELECT * FROM users WHERE random() < 0.7) u
              JOIN orders o ON u.id = o.user_id",
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        // ORDER BY age LIMIT 2 has ties; which rows survive varies.
        name: "ties_top_n_join",
        sql: "SELECT * FROM (SELECT * FROM users ORDER BY age LIMIT 2) u
              JOIN orders o ON u.id = o.user_id",
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        // The key has to be traced through six levels of aliases, filters,
        // projections, sort and limit.
        name: "deep_derived_key_chain",
        sql: "SELECT * FROM (
                SELECT * FROM (
                  SELECT uid AS k FROM (
                    SELECT id AS uid, age FROM (
                      SELECT * FROM users WHERE age > 18) a
                    WHERE age < 90) b) c
                ORDER BY k LIMIT 50) d
              JOIN orders o ON d.k = o.user_id",
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        name: "wide_union_all",
        sql: "SELECT id FROM users UNION ALL SELECT id FROM orders UNION ALL
              SELECT id FROM products UNION ALL SELECT order_id FROM order_items UNION ALL
              SELECT id FROM users UNION ALL SELECT user_id FROM orders UNION ALL
              SELECT id FROM products UNION ALL SELECT product_id FROM order_items UNION ALL
              SELECT age FROM users UNION ALL SELECT qty FROM order_items",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "nested_set_operations",
        sql: "(SELECT id FROM users UNION SELECT user_id FROM orders)
              INTERSECT
              (SELECT id FROM products EXCEPT SELECT order_id FROM order_items)",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "anti_join_of_anti_join",
        sql: "SELECT * FROM users u WHERE NOT EXISTS (
                SELECT 1 FROM orders o WHERE o.user_id = u.id AND NOT EXISTS (
                  SELECT 1 FROM order_items oi WHERE oi.order_id = o.id))",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "not_of_exists_or_in",
        sql: "SELECT * FROM users u
              WHERE NOT (EXISTS (SELECT 1 FROM orders o WHERE o.user_id = u.id)
                         OR u.id IN (SELECT product_id FROM order_items))",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "scalar_subquery_in_join_condition",
        sql: "SELECT * FROM users u JOIN orders o
              ON o.user_id = u.id AND o.amount > (SELECT avg(amount) FROM orders)",
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        name: "grouping_sets_over_join",
        sql: "SELECT u.age, o.user_id, count(*) FROM users u JOIN orders o ON u.id = o.user_id
              GROUP BY GROUPING SETS ((u.age), (o.user_id))",
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "window_frame",
        sql: "SELECT id, sum(age) OVER (ORDER BY id ROWS BETWEEN 1 PRECEDING AND 1 FOLLOWING)
              FROM users",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "offset_without_limit",
        sql: "SELECT * FROM users ORDER BY id OFFSET 3",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "join_on_disjunction",
        sql: "SELECT * FROM users u JOIN orders o ON u.id = o.user_id OR u.age = o.id",
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "three_way_self_join_on_key",
        sql: "SELECT * FROM users a JOIN users b ON a.id = b.id JOIN users c ON b.id = c.id",
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        // DISTINCT output is unique on its columns.
        name: "distinct_outputs_are_keys",
        sql: "SELECT * FROM (SELECT DISTINCT user_id FROM orders) a
              JOIN (SELECT DISTINCT user_id FROM orders) b ON a.user_id = b.user_id",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "unnest_of_array_agg",
        sql: "SELECT unnest(array_agg(id)) FROM users",
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "lateral_join",
        sql: "SELECT * FROM users u, LATERAL (SELECT o.id FROM orders o WHERE o.user_id = u.id) t",
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        // orders.id comes from the NULL-padded side of a LEFT JOIN, so it is not
        // traced as a key on either side of the outer join.
        name: "key_from_null_padded_side",
        sql: "WITH t AS (SELECT o.id AS oid FROM users u LEFT JOIN orders o ON u.id = o.user_id)
              SELECT * FROM t a JOIN t b ON a.oid = b.oid",
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "in_list_and_in_subquery",
        sql: "SELECT * FROM orders WHERE user_id IN (1, 2, 3)
              AND id IN (SELECT order_id FROM order_items)",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "cross_join_single_row_values",
        sql: "SELECT * FROM users CROSS JOIN (VALUES (1)) AS v(x)",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "cross_join_two_scalar_aggregates",
        sql: "SELECT * FROM (SELECT count(*) FROM users) a CROSS JOIN (SELECT count(*) FROM orders) b",
        keys: MightGrow,
        no_keys: MightGrow,
    },
    Case {
        name: "union_all_joined_to_key",
        sql: "SELECT * FROM (SELECT id FROM users UNION ALL SELECT id FROM users) t
              JOIN users u ON t.id = u.id",
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        name: "having_with_scalar_subquery",
        sql: "SELECT user_id FROM orders GROUP BY user_id
              HAVING count(*) > (SELECT count(*) FROM users) / 10",
        keys: Reduces,
        no_keys: Reduces,
    },
    Case {
        name: "join_using",
        sql: "SELECT * FROM orders JOIN (SELECT id AS user_id, age FROM users) u USING (user_id)",
        keys: Reduces,
        no_keys: MightGrow,
    },
    Case {
        name: "correlated_exists_with_limit",
        sql: "SELECT * FROM users u
              WHERE EXISTS (SELECT 1 FROM orders o WHERE o.user_id = u.id LIMIT 1)",
        keys: Reduces,
        no_keys: Reduces,
    },
];

#[tokio::test]
async fn shop_benchmark_with_keys() {
    run_benchmark(CASES, shop_datasets(), true).await;
}

#[tokio::test]
async fn shop_benchmark_without_keys() {
    run_benchmark(CASES, shop_datasets(), false).await;
}
