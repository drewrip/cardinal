//! Randomized differential testing. Generates nested queries over the shop
//! schema from a small grammar covering every operator the analyzer handles,
//! then checks, on every dataset, with and without declared keys:
//!
//! - validation finds no violated constraint, Z3 never gives up, and every
//!   operator is checked against real data;
//! - a `Reduces` query really returns at most the rows it scanned;
//! - a `MightGrow` counterexample really violates the claim;
//! - every bound from `Analysis::bounds` holds on the real row counts;
//! - the verdict does not depend on the data;
//! - declaring keys never loses a proof.
//!
//! `CARDINAL_FUZZ_N` sets the number of queries (default 250),
//! `CARDINAL_FUZZ_SEED` the seed, and `CARDINAL_FUZZ_TRACE` (any value) prints
//! each query and its time to stderr, to find slow ones.

mod common;

use cardinal::{Verdict, analyze_sql};
use common::{Rng, check_bounds, shop_datasets};
use datafusion::prelude::SessionContext;

/// Generates queries whose output columns are always exactly `c0, c1`.
struct Gen {
    r: Rng,
    alias: usize,
}

impl Gen {
    fn alias(&mut self) -> String {
        self.alias += 1;
        format!("t{}", self.alias)
    }

    fn col(&mut self) -> &'static str {
        if self.r.chance(50) { "c0" } else { "c1" }
    }

    fn leaf(&mut self) -> String {
        match self.r.below(12) {
            0 | 1 => "SELECT id AS c0, age AS c1 FROM users".into(),
            2 | 3 => "SELECT id AS c0, user_id AS c1 FROM orders".into(),
            4 => "SELECT user_id AS c0, id AS c1 FROM orders".into(),
            5 => "SELECT id AS c0, TRY_CAST(price AS BIGINT) AS c1 FROM products".into(),
            6 => "SELECT order_id AS c0, product_id AS c1 FROM order_items".into(),
            7 => {
                "SELECT column1 AS c0, column2 AS c1 FROM (VALUES (0, 1), (1, 2), (2, 2)) v".into()
            }
            8 => "SELECT value AS c0, value AS c1 FROM generate_series(0, 3)".into(),
            // Float columns: -0.0, 0.0 and NaN in the skewed data.
            9 => "SELECT id AS c0, amount AS c1 FROM orders".into(),
            10 => "SELECT id AS c0, TRY_CAST(date_part('year', d) AS BIGINT) AS c1 \
                   FROM (SELECT id, make_date(1990 + age % 10, 1 + id % 12, 1) AS d FROM users) \
                   WHERE d BETWEEN DATE '1992-03-01' AND DATE '1994-06-30'"
                .into(),
            _ => "SELECT amount AS c0, user_id AS c1 FROM orders".into(),
        }
    }

    fn pred(&mut self, t: &str) -> String {
        let c = self.col();
        match self.r.below(13) {
            0 => format!("{t}.{c} > {}", self.r.range(0, 40)),
            7 => format!(
                "{t}.{c} = {} OR {t}.{c} = {}",
                self.r.range(0, 5),
                self.r.range(0, 40)
            ),
            // Often contradictory.
            8 => format!(
                "{t}.{c} > {} AND {t}.{c} < {}",
                self.r.range(0, 30),
                self.r.range(0, 30)
            ),
            9 => format!("{t}.{c} <> {}", self.r.range(0, 5)),
            10 => format!("{t}.{c} IS NULL"),
            11 => format!("NOT ({t}.{c} > {})", self.r.range(0, 40)),
            12 => format!("({t}.{c} IN (1, 2) OR {t}.{c} BETWEEN 18 AND 20) AND {t}.{c} <> 2"),
            1 => format!("{t}.{c} IS NOT NULL"),
            2 => format!("{t}.{c} % 2 = 0"),
            3 => format!("{t}.c0 <> {t}.c1"),
            4 => "random() < 0.5".into(),
            5 => format!(
                "{t}.{c} BETWEEN {} AND {}",
                self.r.range(0, 5),
                self.r.range(5, 60)
            ),
            _ => format!("{t}.{c} IN (0, 1, 2, 20, 30)"),
        }
    }

    fn rel(&mut self, depth: u32) -> String {
        if depth == 0 || self.r.chance(15) {
            return self.leaf();
        }
        let d = depth - 1;
        let t = self.alias();
        match self.r.below(23) {
            0 | 1 => {
                let a = self.rel(d);
                let p = self.pred(&t);
                format!("SELECT {t}.c0, {t}.c1 FROM ({a}) {t} WHERE {p}")
            }
            2 => {
                let a = self.rel(d);
                if self.r.chance(40) {
                    format!("SELECT {t}.c1 AS c0, {t}.c0 AS c1 FROM ({a}) {t}")
                } else if self.r.chance(30) {
                    let c = self.col();
                    format!(
                        "SELECT {t}.c0, CASE WHEN {t}.{c} > 20 THEN 1 WHEN {t}.{c} < 3 THEN {t}.c1 \
                         END AS c1 FROM ({a}) {t}"
                    )
                } else {
                    format!("SELECT {t}.c0, {t}.c0 + {t}.c1 AS c1 FROM ({a}) {t}")
                }
            }
            3..=5 => {
                let (a, b) = (self.rel(d), self.rel(d));
                let u = self.alias();
                let kind = ["JOIN", "JOIN", "LEFT JOIN", "RIGHT JOIN", "FULL JOIN"]
                    [self.r.below(5) as usize];
                let (p, q, x, y) = (self.col(), self.col(), self.col(), self.col());
                let on = match self.r.below(6) {
                    0 => format!("{t}.{p} < {u}.{q}"),
                    1 => format!("{t}.{p} = {u}.{q} AND {t}.{x} <> {u}.{y}"),
                    _ => format!("{t}.{p} = {u}.{q}"),
                };
                // Outer-join rows by whether they matched.
                let pad = match self.r.below(6) {
                    0 => format!(" WHERE {u}.{q} IS NULL"),
                    1 => format!(" WHERE {t}.{p} IS NULL"),
                    2 => format!(" WHERE {u}.{q} IS NOT NULL"),
                    _ => String::new(),
                };
                format!(
                    "SELECT {t}.{x} AS c0, {u}.{y} AS c1 FROM ({a}) {t} {kind} ({b}) {u} ON {on}{pad}"
                )
            }
            6 => {
                let (a, b) = (self.rel(d), self.rel(d));
                let u = self.alias();
                format!("SELECT {t}.c0, {u}.c1 FROM ({a}) {t} CROSS JOIN ({b}) {u}")
            }
            7 => {
                let a = self.rel(d);
                let c = self.col();
                if self.r.chance(50) {
                    format!("SELECT {t}.{c} AS c0, count(*) AS c1 FROM ({a}) {t} GROUP BY {t}.{c}")
                } else {
                    format!(
                        "SELECT {t}.c0, TRY_CAST(sum({t}.c1) AS BIGINT) AS c1 FROM ({a}) {t} \
                         GROUP BY {t}.c0 HAVING count(*) > 1"
                    )
                }
            }
            8 => {
                let a = self.rel(d);
                format!("SELECT count(*) AS c0, max({t}.c1) AS c1 FROM ({a}) {t}")
            }
            9 => {
                let a = self.rel(d);
                format!("SELECT DISTINCT {t}.c0, {t}.c1 FROM ({a}) {t}")
            }
            10 => {
                let a = self.rel(d);
                let n = self.r.range(0, 6);
                match self.r.below(3) {
                    0 => format!("SELECT {t}.c0, {t}.c1 FROM ({a}) {t} LIMIT {n}"),
                    1 => format!(
                        "SELECT {t}.c0, {t}.c1 FROM ({a}) {t} ORDER BY {t}.c1 LIMIT {n} OFFSET {}",
                        self.r.range(0, 3)
                    ),
                    _ => format!("SELECT {t}.c0, {t}.c1 FROM ({a}) {t} ORDER BY {t}.c0 OFFSET {n}"),
                }
            }
            11 => {
                let (a, b) = (self.rel(d), self.rel(d));
                let u = self.alias();
                let op = ["UNION ALL", "UNION ALL", "UNION", "INTERSECT", "EXCEPT"]
                    [self.r.below(5) as usize];
                format!(
                    "SELECT {t}.c0, {t}.c1 FROM ({a}) {t} {op} SELECT {u}.c0, {u}.c1 FROM ({b}) {u}"
                )
            }
            12 | 13 => {
                let (a, b) = (self.rel(d), self.rel(d));
                let u = self.alias();
                let (p, q) = (self.col(), self.col());
                let cond = match self.r.below(4) {
                    0 => format!("{t}.{p} IN (SELECT {u}.{q} FROM ({b}) {u})"),
                    1 => format!("{t}.{p} NOT IN (SELECT {u}.{q} FROM ({b}) {u})"),
                    2 => format!("EXISTS (SELECT 1 FROM ({b}) {u} WHERE {u}.{q} = {t}.{p})"),
                    _ => format!("NOT EXISTS (SELECT 1 FROM ({b}) {u} WHERE {u}.{q} = {t}.{p})"),
                };
                format!("SELECT {t}.c0, {t}.c1 FROM ({a}) {t} WHERE {cond}")
            }
            14 if self.r.chance(50) => {
                // Top-k per partition.
                let a = self.rel(d);
                let u = self.alias();
                let c = self.col();
                let part = if self.r.chance(70) {
                    format!("PARTITION BY {t}.{c}")
                } else {
                    String::new()
                };
                format!(
                    "SELECT {u}.c0, {u}.c1 FROM (SELECT {t}.c0, {t}.c1, row_number() OVER \
                     ({part} ORDER BY {t}.c0) AS rn FROM ({a}) {t}) {u} WHERE {u}.rn <= {}",
                    self.r.range(0, 4)
                )
            }
            14 => {
                let a = self.rel(d);
                format!(
                    "SELECT {t}.c0, TRY_CAST(row_number() OVER (PARTITION BY {t}.c1 ORDER BY {t}.c0) \
                     AS BIGINT) AS c1 FROM ({a}) {t}"
                )
            }
            15 => {
                let (a, b) = (self.rel(d), self.rel(d));
                let u = self.alias();
                format!(
                    "SELECT {t}.c0, {t}.c1 FROM ({a}) {t} \
                     WHERE {t}.c0 >= (SELECT TRY_CAST(avg({u}.c0) AS BIGINT) FROM ({b}) {u})"
                )
            }
            16 => {
                let (a, b) = (self.rel(d), self.rel(d));
                let u = self.alias();
                format!(
                    "SELECT {t}.c0, (SELECT count(*) FROM ({b}) {u} WHERE {u}.c0 = {t}.c1) AS c1 \
                     FROM ({a}) {t}"
                )
            }
            17 => {
                let a = self.rel(d);
                format!("SELECT {t}.c0, unnest(make_array({t}.c1, {t}.c0)) AS c1 FROM ({a}) {t}")
            }
            18 => {
                // EXISTS / IN under OR plans as a mark join.
                let (a, b) = (self.rel(d), self.rel(d));
                let u = self.alias();
                let (p, q) = (self.col(), self.col());
                let pred = self.pred(&t);
                let neg = if self.r.chance(50) { "NOT " } else { "" };
                format!(
                    "SELECT {t}.c0, {t}.c1 FROM ({a}) {t} WHERE {pred} OR {neg}EXISTS \
                     (SELECT 1 FROM ({b}) {u} WHERE {u}.{q} = {t}.{p})"
                )
            }
            19 => {
                let a = self.rel(d);
                let g = ["ROLLUP", "CUBE"][self.r.below(2) as usize];
                format!(
                    "SELECT {t}.c0, TRY_CAST(count(*) AS BIGINT) AS c1 FROM ({a}) {t} \
                     GROUP BY {g} ({t}.c0, {t}.c1)"
                )
            }
            20 => {
                let a = self.rel(d);
                format!(
                    "SELECT DISTINCT ON ({t}.c0) {t}.c0, {t}.c1 FROM ({a}) {t} \
                     ORDER BY {t}.c0, {t}.c1"
                )
            }
            21 => {
                // One relation split three ways by a threshold (and NULL).
                let a = self.rel(d);
                let (u, v) = (self.alias(), self.alias());
                let c = self.col();
                let k = self.r.range(0, 40);
                let dup = if self.r.chance(30) { "=" } else { "" };
                format!(
                    "SELECT {t}.c0, {t}.c1 FROM ({a}) {t} WHERE {t}.{c} < {k} \
                     UNION ALL SELECT {u}.c0, {u}.c1 FROM ({a}) {u} WHERE {u}.{c} >{dup} {k} \
                     UNION ALL SELECT {v}.c0, {v}.c1 FROM ({a}) {v} WHERE {v}.{c} IS NULL"
                )
            }
            _ => {
                // Outer joins on non-equality conditions.
                let (a, b) = (self.rel(d), self.rel(d));
                let u = self.alias();
                let kind =
                    ["LEFT JOIN", "RIGHT JOIN", "FULL JOIN", "JOIN"][self.r.below(4) as usize];
                let (p, q) = (self.col(), self.col());
                let on = if self.r.chance(50) {
                    format!("{t}.{p} <= {u}.{q}")
                } else {
                    format!("{t}.{p} = {u}.{q} OR {t}.{q} = {u}.{p}")
                };
                format!("SELECT {t}.c0, {u}.c1 FROM ({a}) {t} {kind} ({b}) {u} ON {on}")
            }
        }
    }
}

fn env(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

#[derive(Default)]
struct Stats {
    queries: usize,
    skipped: usize,
    proven: [usize; 2],
    refuted: [usize; 2],
    operators: usize,
    executions: usize,
    /// Queries (per mode) with a constant, table-relative, or fractional bound.
    bounded: usize,
}

/// Checks one query on every context of one mode; returns its verdict, or
/// `None` if DataFusion cannot plan it.
async fn check_mode(
    sql: &str,
    ctxs: &[(String, SessionContext)],
    failures: &mut Vec<String>,
    stats: &mut Stats,
) -> Option<bool> {
    let mut proven = None;
    let mut bounds = None;
    for (dname, ctx) in ctxs {
        // Skip queries DataFusion itself cannot run, e.g. its mark joins on
        // float keys fail with "Unsupported type for ArrayMap: Float64".
        let Ok(df) = ctx.sql(sql).await else {
            return None;
        };
        if df.collect().await.is_err() {
            return None;
        }
        let a = match analyze_sql(ctx, sql).await {
            Ok(a) => a,
            Err(_) => return None,
        };
        // Bounds depend only on the query; compute them once per mode.
        if bounds.is_none() {
            let b = a.bounds().unwrap();
            if b.constant.is_some() || !b.tables.is_empty() || b.sum.is_some_and(|s| s.num < s.den)
            {
                stats.bounded += 1;
            }
            bounds = Some(b);
        }
        let is_proven = match &a.verdict {
            Verdict::Reduces => true,
            Verdict::MightGrow(m) => {
                let total: i64 = a.scans.iter().map(|(s, _)| m.var(s)).sum();
                if m.var(&a.root) <= total {
                    failures.push(format!("counterexample does not refute the claim: {sql}"));
                }
                false
            }
            Verdict::Unknown(why) => {
                failures.push(format!("Unknown ({why}): {sql}"));
                false
            }
        };
        if *proven.get_or_insert(is_proven) != is_proven {
            failures.push(format!("verdict changed on {dname}: {sql}"));
        }
        let v = a.validate(ctx).await.unwrap();
        for f in check_bounds(bounds.as_ref().unwrap(), &a, &v) {
            failures.push(format!(
                "{dname}: {f}: {sql}\n  bounds: {}",
                bounds.as_ref().unwrap()
            ));
        }
        let declared = a.smtlib.matches("(declare-fun op").count();
        stats.operators = stats.operators.max(declared);
        stats.executions += 1;
        if let Some(op) = &v.violation {
            failures.push(format!("{dname}: {op} violated\n  {sql}\n{}", a.plan));
        }
        if v.undecided {
            failures.push(format!("{dname}: validation undecided: {sql}"));
        }
        if v.violation.is_none() && v.rows.len() < declared {
            failures.push(format!(
                "{dname}: only {}/{declared} operators pinned: {sql}\n{}",
                v.rows.len(),
                a.plan
            ));
        }
        let root = v.rows.get(&a.root).copied();
        let scanned: Option<u64> = a.scans.iter().map(|(s, _)| v.rows.get(s).copied()).sum();
        if is_proven
            && let (Some(root), Some(scanned)) = (root, scanned)
            && root > scanned
        {
            failures.push(format!(
                "{dname}: verdict Reduces, but returned {root} rows from {scanned} scanned: {sql}"
            ));
        }
    }
    proven
}

#[tokio::test]
async fn fuzz() {
    let n = env("CARDINAL_FUZZ_N", 250);
    let seed = env("CARDINAL_FUZZ_SEED", 7);
    let keyed: Vec<_> = shop_datasets()
        .into_iter()
        .filter(|d| d.unique_keys)
        .map(|d| (d.name.clone(), d.context(true)))
        .collect();
    let unkeyed: Vec<_> = shop_datasets()
        .into_iter()
        .map(|d| (d.name.clone(), d.context(false)))
        .collect();
    let mut g = Gen {
        r: Rng::new(seed),
        alias: 0,
    };
    let mut failures = vec![];
    let mut stats = Stats::default();
    let mut skipped_examples = vec![];
    for _ in 0..n {
        let depth = 1 + g.r.below(4) as u32;
        let sql = g.rel(depth);
        stats.queries += 1;
        let started = std::time::Instant::now();
        if std::env::var("CARDINAL_FUZZ_TRACE").is_ok() {
            eprintln!("TRACE start {}: {sql}", stats.queries);
        }
        let with_keys = check_mode(&sql, &keyed, &mut failures, &mut stats).await;
        let without = check_mode(&sql, &unkeyed, &mut failures, &mut stats).await;
        if std::env::var("CARDINAL_FUZZ_TRACE").is_ok() {
            eprintln!("TRACE done {} in {:?}", stats.queries, started.elapsed());
        }
        let (Some(with_keys), Some(without)) = (with_keys, without) else {
            stats.skipped += 1;
            if skipped_examples.len() < 3 {
                skipped_examples.push(sql);
            }
            continue;
        };
        for (i, p) in [with_keys, without].into_iter().enumerate() {
            if p {
                stats.proven[i] += 1;
            } else {
                stats.refuted[i] += 1;
            }
        }
        if without && !with_keys {
            failures.push(format!("declaring keys lost a proof: {sql}"));
        }
    }
    println!(
        "fuzz: {} queries (seed {seed}), {} skipped (DataFusion cannot plan or run them); with keys {} reduce / {} \
         might grow; without keys {} reduce / {} might grow; {} validated executions; largest plan {} \
         variables; {} bounds computed with a reduction claim",
        stats.queries,
        stats.skipped,
        stats.proven[0],
        stats.refuted[0],
        stats.proven[1],
        stats.refuted[1],
        stats.executions,
        stats.operators,
        stats.bounded
    );
    for s in &skipped_examples {
        println!("skipped: {s}");
    }
    // A generator that DataFusion mostly rejects would test nothing.
    assert!(
        stats.skipped * 10 <= stats.queries,
        "{} of {} generated queries could not be planned",
        stats.skipped,
        stats.queries
    );
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
