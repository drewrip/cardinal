//! The axiom encoding (`cardinal::uf`) against the truth, on generated
//! queries over small generated tables run live.
//!
//! Four tables, deterministically seeded: two with primary keys, one
//! referencing the other by a foreign key (and by a column like it, but
//! NULL and dangling in places), one with neither and many duplicates,
//! and one empty; their columns skewed, duplicated and NULL in places.
//! Queries are generated two ways: flat joins of the tables (self-joins
//! among them; inner, left, right, full and cross; semi and anti joins as
//! `EXISTS`, `IN` and `NOT IN` over columns with NULLs; scalar subqueries,
//! correlated or not, in filters and in projections) under filters (NULL
//! comparisons, `IS NULL`, `IN` and `NOT IN` lists with NULLs, `LIKE`,
//! `OR`, `CASE`), with a grouping, HAVING, DISTINCT, LIMIT or UNION on
//! top; and nested, as `tests/fuzz.rs` does.
//!
//! Each query runs in DuckDB (profiled with one thread and with four) and
//! in DataFusion. In groups of consecutive queries, every other query's
//! profiles are observed as facts; each query of the group is then
//! bounded, as DataFusion plans it and as DuckDB planned it, with every
//! observed plan's facts (an observed query's own too), and its true row
//! count must lie within the bound.
//!
//! Needs the `duckdb` CLI; skipped without. `CARDINAL_UF_TRUTH_N` sets the
//! number of generated queries (default 700, about 15 minutes),
//! `CARDINAL_UF_TRUTH_SEED` their seed, `CARDINAL_UF_TRUTH_ONLY`
//! (comma-separated names, `q007`) limits the queries to those and their
//! groups, `CARDINAL_UF_TRUTH_GROUP` the queries observed together
//! (default 10: an encoder observing many plans of the same tables is
//! slow), `CARDINAL_UF_TRUTH_THREADS` the groups bounded at once (default
//! 4), `CARDINAL_UF_TRUTH_SHOW` prints the queries and
//! `CARDINAL_UF_TRUTH_TRACE` each bound as it starts. Each bound's checks
//! are limited by `CARDINAL_UF_TIMEOUT_MS` (1000 is enough).
//!
//! `one` bounds a single query (`CARDINAL_UF_ONE`), with other queries'
//! profiles (`CARDINAL_UF_FACTS`), to minimize a case; `found` holds the
//! cases minimized so far.
//!
//! ```sh
//! CARDINAL_UF_TIMEOUT_MS=1000 cargo test --release --test uf_truth -- --nocapture
//! CARDINAL_UF_ONE="SELECT * FROM rc WHERE x IN (2, NULL)" cargo test --release --test uf_truth one -- --nocapture
//! ```

mod common;
mod live;

use std::path::PathBuf;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use cardinal::observed::{Catalog, ObservedPlan, from_duckdb};
use cardinal::uf::Encoder;
use common::{Col, Dataset, Table};
use datafusion::prelude::SessionContext;
use live::Rng;

const WORDS: &[&str] = &["apple", "apricot", "banana", "berry", "cherry", "date"];

/// The tables: `ra` and `rb` keyed by `id`, `rb.a_id` referencing `ra.id`
/// (a foreign key, so never NULL), `rb.m` holding `ra.id`s, others and
/// NULLs, `rc` unkeyed with duplicates, `re` empty.
fn dataset(seed: u64) -> Dataset {
    let mut r = Rng::new(seed);
    let null = |r: &mut Rng, p: usize| r.chance(p);
    // Half the values one value, the rest spread.
    let skew = |r: &mut Rng| if r.chance(45) { 1 } else { r.below(8) as i64 };
    let word = |r: &mut Rng, p: usize| (!r.chance(p)).then(|| r.pick(WORDS).to_string());
    let (na, nb, nc) = (40, 90, 30);
    let mut ra = (vec![], vec![], vec![], vec![]);
    for i in 0..na {
        ra.0.push(Some(i as i64));
        ra.1.push((!null(&mut r, 15)).then(|| skew(&mut r)));
        ra.2.push((!null(&mut r, 20)).then(|| r.below(20) as i64));
        ra.3.push(word(&mut r, 15));
    }
    let mut rb = (vec![], vec![], vec![], vec![], vec![], vec![]);
    for i in 0..nb {
        rb.0.push(Some(i as i64));
        rb.1.push(Some(if r.chance(40) { r.below(3) as i64 } else { r.below(na) as i64 }));
        rb.5.push((!null(&mut r, 25)).then(|| if r.chance(40) { r.below(3) as i64 } else { r.below(na + 5) as i64 }));
        rb.2.push((!null(&mut r, 10)).then(|| skew(&mut r)));
        rb.3.push((!null(&mut r, 10)).then(|| r.below(50) as i64));
        rb.4.push(word(&mut r, 10));
    }
    let mut rc = (vec![], vec![], vec![]);
    for _ in 0..nc {
        rc.0.push((!null(&mut r, 25)).then(|| r.below(6) as i64));
        rc.1.push(Some(r.below(10) as i64));
        rc.2.push(word(&mut r, 20));
    }
    Dataset {
        name: format!("uf{seed}"),
        unique_keys: true,
        tables: vec![
            Table {
                name: "ra",
                cols: vec![("id", Col::I(ra.0)), ("k", Col::I(ra.1)), ("v", Col::I(ra.2)), ("s", Col::S(ra.3))],
                key: &["id"],
            },
            Table {
                name: "rb",
                cols: vec![("id", Col::I(rb.0)), ("a_id", Col::I(rb.1)), ("m", Col::I(rb.5)), ("k", Col::I(rb.2)), ("w", Col::I(rb.3)), ("t", Col::S(rb.4))],
                key: &["id"],
            },
            Table { name: "rc", cols: vec![("k", Col::I(rc.0)), ("x", Col::I(rc.1)), ("s", Col::S(rc.2))], key: &[] },
            Table { name: "re", cols: vec![("k", Col::I(vec![])), ("x", Col::I(vec![]))], key: &[] },
        ],
    }
}

fn foreign_keys() -> Vec<cardinal::ForeignKey> {
    vec![cardinal::ForeignKey::new("rb", &["a_id"], "ra", &["id"])]
}

/// The dataset as a DuckDB script: its tables, keys and rows.
fn ddl(d: &Dataset) -> String {
    let mut out = String::new();
    for t in &d.tables {
        let mut cols: Vec<String> = t
            .cols
            .iter()
            .map(|(n, c)| format!("{n} {}", if matches!(c, Col::S(_)) { "VARCHAR" } else { "BIGINT" }))
            .collect();
        if !t.key.is_empty() {
            cols.push(format!("PRIMARY KEY ({})", t.key.join(", ")));
        }
        out.push_str(&format!("CREATE TABLE {} ({});\n", t.name, cols.join(", ")));
        let rows = match &t.cols[0].1 {
            Col::I(v) => v.len(),
            Col::S(v) => v.len(),
            _ => unreachable!(),
        };
        for i in 0..rows {
            let vals: Vec<String> = t
                .cols
                .iter()
                .map(|(_, c)| match c {
                    Col::I(v) => v[i].map_or("NULL".into(), |x| x.to_string()),
                    Col::S(v) => v[i].as_ref().map_or("NULL".into(), |x| format!("'{x}'")),
                    _ => unreachable!(),
                })
                .collect();
            out.push_str(&format!("INSERT INTO {} VALUES ({});\n", t.name, vals.join(", ")));
        }
    }
    out
}

/// Each table's integer columns, and its text column if any.
fn columns(table: &str) -> (&'static [&'static str], Option<&'static str>) {
    match table {
        "ra" => (&["id", "k", "v"], Some("s")),
        "rb" => (&["id", "a_id", "m", "k", "w"], Some("t")),
        "rc" => (&["k", "x"], Some("s")),
        _ => (&["k", "x"], None),
    }
}

/// Flat queries over the tables.
struct Flat<'r> {
    r: &'r mut Rng,
    n: usize,
}

impl Flat<'_> {
    fn alias(&mut self) -> String {
        self.n += 1;
        format!("x{}", self.n)
    }

    fn table(&mut self) -> &'static str {
        ["ra", "ra", "ra", "ra", "rb", "rb", "rb", "rb", "rb", "rb", "rc", "rc", "rc", "rc", "rc", "re"][self.r.below(16)]
    }

    fn int(&mut self, table: &str) -> &'static str {
        let (ints, _) = columns(table);
        ints[self.r.below(ints.len())]
    }

    /// A predicate on alias `a` of `table`.
    fn filter(&mut self, a: &str, table: &str) -> String {
        let (_, text) = columns(table);
        if let Some(s) = text
            && self.r.chance(30)
        {
            let w = self.r.pick(WORDS);
            let w2 = self.r.pick(WORDS);
            return match self.r.below(10) {
                0 => format!("{a}.{s} LIKE '{}%'", &w[..2]),
                1 => format!("{a}.{s} LIKE '%rr%'"),
                2 => format!("{a}.{s} NOT LIKE '{}%'", &w[..1]),
                3 => format!("{a}.{s} = '{w}'"),
                4 => format!("{a}.{s} IN ('{w}', '{w2}')"),
                5 => format!("{a}.{s} IS NULL"),
                6 => format!("{a}.{s} > '{}'", &w[..1]),
                7 => format!("{a}.{s} LIKE '_a%'"),
                8 => format!("({a}.{s} IS NULL OR {a}.{s} <> '{w}')"),
                _ => format!("{a}.{s} NOT IN ('{w}', NULL)"),
            };
        }
        let c = self.int(table);
        let d = self.int(table);
        let n = self.r.below(12) as i64;
        let m = n + self.r.below(10) as i64;
        match self.r.below(22) {
            0 => format!("{a}.{c} < {n}"),
            1 => format!("{a}.{c} = {n}"),
            2 => format!("{a}.{c} IS NULL"),
            3 => format!("{a}.{c} IS NOT NULL"),
            4 => format!("{a}.{c} BETWEEN {n} AND {m}"),
            5 => format!("{a}.{c} IN ({n}, {m})"),
            6 => format!("{a}.{c} NOT IN ({n}, NULL)"),
            7 => format!("{a}.{c} IN ({n}, NULL)"),
            8 => format!("{a}.{c} <> {n}"),
            9 => format!("NOT ({a}.{c} > {n})"),
            10 => format!("coalesce({a}.{c}, -1) = -1"),
            11 => format!("CASE WHEN {a}.{c} > {n} THEN 1 ELSE 0 END = 1"),
            12 => format!("({a}.{c} = {n} OR {a}.{d} > {m})"),
            13 => format!("{a}.{c} % 2 = 0"),
            14 => format!("{a}.{c} = NULL"),
            15 => format!("{a}.{c} IS DISTINCT FROM {n}"),
            16 => format!("{a}.{c} + {a}.{d} > {m}"),
            17 => format!("{a}.{c} < {a}.{d}"),
            18 => format!("{a}.{c} NOT IN ({n}, {m})"),
            19 => format!("CASE WHEN {a}.{c} IS NULL THEN {a}.{d} ELSE {a}.{c} END > {n}"),
            20 => format!("({a}.{c} > {m} AND {a}.{c} < {n})"),
            _ => format!("{a}.{c} >= {n}"),
        }
    }

    /// A join condition between `a` of `t` and `b` of `u`.
    fn on(&mut self, a: &str, t: &str, b: &str, u: &str) -> String {
        let (c, d) = match (t, u) {
            ("rb", "ra") if self.r.chance(60) => (if self.r.chance(60) { "a_id" } else { "m" }, "id"),
            ("ra", "rb") if self.r.chance(60) => ("id", if self.r.chance(60) { "a_id" } else { "m" }),
            _ if self.r.chance(50) && columns(u).0.contains(&"k") && columns(t).0.contains(&"k") => ("k", "k"),
            _ => (self.int(t), self.int(u)),
        };
        match self.r.below(8) {
            0 => format!("{a}.{c} = {b}.{d} AND {a}.{} <> {b}.{}", self.int(t), self.int(u)),
            1 => format!("{a}.{c} < {b}.{d}"),
            _ => format!("{a}.{c} = {b}.{d}"),
        }
    }

    /// A predicate relating `a` of `t` to another table, as a subquery.
    fn subquery(&mut self, a: &str, t: &str) -> String {
        let u = self.table();
        let b = self.alias();
        let c = if t == "rb" && u == "ra" && self.r.chance(50) { if self.r.chance(50) { "a_id" } else { "m" } } else { self.int(t) };
        let d = if (c == "a_id" || c == "m") && columns(u).0.contains(&"id") { "id" } else { self.int(u) };
        let f = if self.r.chance(50) { format!(" AND {}", self.filter(&b, u)) } else { String::new() };
        let w = if f.is_empty() { String::new() } else { format!(" WHERE {}", &f[5..]) };
        match self.r.below(11) {
            0 => format!("EXISTS (SELECT 1 FROM {u} {b} WHERE {b}.{d} = {a}.{c}{f})"),
            1 => format!("NOT EXISTS (SELECT 1 FROM {u} {b} WHERE {b}.{d} = {a}.{c}{f})"),
            2 => format!("{a}.{c} IN (SELECT {b}.{d} FROM {u} {b}{w})"),
            3 => format!("{a}.{c} NOT IN (SELECT {b}.{d} FROM {u} {b}{w})"),
            4 => format!("{a}.{c} > (SELECT avg({b}.{d}) FROM {u} {b}{w})"),
            5 => format!("{a}.{c} = (SELECT max({b}.{d}) FROM {u} {b}{w})"),
            6 => format!("{a}.{c} < (SELECT count(*) FROM {u} {b} WHERE {b}.{d} = {a}.{c})"),
            7 => format!("({} OR EXISTS (SELECT 1 FROM {u} {b} WHERE {b}.{d} = {a}.{c}))", self.filter(a, t)),
            8 => format!("{a}.{c} IN (SELECT {b}.{d} FROM {u} {b} GROUP BY {b}.{d} HAVING count(*) > {})", self.r.below(4)),
            9 => format!("{a}.{c} NOT IN (SELECT {b}.{d} FROM {u} {b} WHERE {b}.{d} IS NOT NULL{f})"),
            _ => format!("{a}.{c} = (SELECT min({b}.{d}) FROM {u} {b} WHERE {b}.k = {a}.{})", if columns(t).0.contains(&"k") { "k" } else { c }),
        }
    }

    fn query(&mut self) -> String {
        let t0 = self.table();
        let a0 = self.alias();
        let mut insts = vec![(a0.clone(), t0)];
        let mut from = format!("{t0} {a0}");
        let mut wheres = vec![];
        for _ in 0..self.r.below(4) {
            let (a, t) = insts[self.r.below(insts.len())].clone();
            let u = self.table();
            let b = self.alias();
            let on = self.on(&a, t, &b, u);
            match self.r.below(9) {
                0 => {
                    from.push_str(&format!(" CROSS JOIN {u} {b}"));
                    wheres.push(on);
                }
                1 | 2 => from.push_str(&format!(" JOIN {u} {b} ON {on}")),
                3 => {
                    let f = self.filter(&b, u);
                    from.push_str(&format!(" LEFT JOIN {u} {b} ON {on} AND {f}"));
                }
                4 => {
                    from.push_str(&format!(" LEFT JOIN {u} {b} ON {on}"));
                    let c = self.int(u);
                    wheres.push(format!("{b}.{c} IS NULL"));
                }
                5 => from.push_str(&format!(" LEFT JOIN {u} {b} ON {on}")),
                6 => from.push_str(&format!(" RIGHT JOIN {u} {b} ON {on}")),
                _ => from.push_str(&format!(" FULL JOIN {u} {b} ON {on}")),
            }
            insts.push((b, u));
        }
        for (a, t) in insts.clone() {
            if self.r.chance(30) {
                wheres.push(self.filter(&a, t));
            }
        }
        for _ in 0..[0, 0, 1, 1, 2][self.r.below(5)] {
            let (a, t) = insts[self.r.below(insts.len())].clone();
            wheres.push(self.subquery(&a, t));
        }
        let w = if wheres.is_empty() { String::new() } else { format!(" WHERE {}", wheres.join(" AND ")) };
        let (a, t) = insts[self.r.below(insts.len())].clone();
        let c = self.int(t);
        let (a2, t2) = insts[self.r.below(insts.len())].clone();
        let d = self.int(t2);
        let n = self.r.below(6);
        match self.r.below(12) {
            0 | 1 => format!("SELECT {a}.{c}, {a2}.{d} FROM {from}{w}"),
            2 => format!("SELECT DISTINCT {a}.{c} FROM {from}{w}"),
            3 => {
                let having = match self.r.below(4) {
                    0 => String::new(),
                    1 => format!(" HAVING count(*) > {n}"),
                    2 => format!(" HAVING {a}.{c} IS NOT NULL"),
                    _ => format!(" HAVING sum({a2}.{d}) > {}", n * 5),
                };
                format!("SELECT {a}.{c}, count(*) FROM {from}{w} GROUP BY {a}.{c}{having}")
            }
            4 => format!("SELECT {a}.{c}, {a2}.{d}, count(*) FROM {from}{w} GROUP BY {a}.{c}, {a2}.{d}"),
            5 => format!("SELECT {a}.{c} FROM {from}{w} LIMIT {}", n * 3),
            6 => {
                let u = self.table();
                let b = self.alias();
                let e = self.int(u);
                let all = if self.r.chance(50) { " ALL" } else { "" };
                let f = self.filter(&b, u);
                format!("SELECT {a}.{c} FROM {from}{w} UNION{all} SELECT {b}.{e} FROM {u} {b} WHERE {f}")
            }
            7 => format!("SELECT {a}.{c}, CASE WHEN {a}.{c} IS NULL THEN 'none' WHEN {a}.{c} > {n} THEN 'big' END AS z FROM {from}{w}"),
            8 => {
                let u = self.table();
                let b = self.alias();
                let e = self.int(u);
                format!("SELECT {a}.{c}, (SELECT count(*) FROM {u} {b} WHERE {b}.{e} = {a}.{c}) AS z FROM {from}{w}")
            }
            9 => format!("SELECT DISTINCT {a}.{c}, {a2}.{d} FROM {from}{w}"),
            10 => format!("SELECT count(*) FROM {from}{w}"),
            _ => format!("SELECT * FROM {from}{w}"),
        }
    }
}

/// Nested queries whose output columns are always `c0, c1`, as
/// `tests/fuzz.rs` generates them, over these tables.
struct Nested<'r> {
    r: &'r mut Rng,
    alias: usize,
}

impl Nested<'_> {
    fn alias(&mut self) -> String {
        self.alias += 1;
        format!("t{}", self.alias)
    }

    fn col(&mut self) -> &'static str {
        if self.r.chance(50) { "c0" } else { "c1" }
    }

    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + self.r.below((hi - lo + 1) as usize) as i64
    }

    fn leaf(&mut self) -> String {
        match self.r.below(13) {
            0 | 1 | 12 => "SELECT id AS c0, k AS c1 FROM ra".into(),
            2 => "SELECT k AS c0, v AS c1 FROM ra".into(),
            3 | 4 => "SELECT a_id AS c0, k AS c1 FROM rb".into(),
            5 => "SELECT id AS c0, w AS c1 FROM rb".into(),
            6 => "SELECT k AS c0, x AS c1 FROM rc".into(),
            7 => "SELECT x AS c0, k AS c1 FROM re".into(),
            8 => "SELECT id AS c0, v AS c1 FROM ra WHERE s LIKE 'a%'".into(),
            9 => "SELECT m AS c0, w AS c1 FROM rb WHERE t IS NULL OR t IN ('apple', 'cherry')".into(),
            10 => "SELECT k AS c0, x AS c1 FROM rc WHERE s NOT LIKE '%e%'".into(),
            _ => "SELECT v.c0, v.c1 FROM (VALUES (0, 1), (1, 2), (2, 2)) v(c0, c1)".into(),
        }
    }

    fn pred(&mut self, t: &str) -> String {
        let c = self.col();
        match self.r.below(15) {
            0 => format!("{t}.{c} > {}", self.range(0, 10)),
            1 => format!("{t}.{c} IS NOT NULL"),
            2 => format!("{t}.{c} % 2 = 0"),
            3 => format!("{t}.c0 <> {t}.c1"),
            4 => format!("{t}.{c} NOT IN ({}, NULL)", self.range(0, 5)),
            5 => format!("{t}.{c} BETWEEN {} AND {}", self.range(0, 3), self.range(3, 20)),
            6 => format!("{t}.{c} IN ({}, NULL)", self.range(0, 5)),
            7 => format!("{t}.{c} = {} OR {t}.{c} = {}", self.range(0, 5), self.range(0, 40)),
            8 => format!("{t}.{c} > {} AND {t}.{c} < {}", self.range(0, 10), self.range(0, 10)),
            9 => format!("{t}.{c} <> {}", self.range(0, 5)),
            10 => format!("{t}.{c} IS NULL"),
            11 => format!("NOT ({t}.{c} > {})", self.range(0, 10)),
            12 => format!("CASE WHEN {t}.c0 > {} THEN {t}.c1 END IS NULL", self.range(0, 10)),
            13 => format!("{t}.{c} = NULL"),
            _ => format!("{t}.{c} IN (0, 1, 2, 20, 30)"),
        }
    }

    fn rel(&mut self, depth: u32) -> String {
        if depth == 0 || self.r.chance(15) {
            return self.leaf();
        }
        let d = depth - 1;
        let t = self.alias();
        match self.r.below(20) {
            0 | 1 => {
                let a = self.rel(d);
                let p = self.pred(&t);
                format!("SELECT {t}.c0, {t}.c1 FROM ({a}) {t} WHERE {p}")
            }
            2 => {
                let a = self.rel(d);
                if self.r.chance(40) {
                    format!("SELECT {t}.c1 AS c0, {t}.c0 AS c1 FROM ({a}) {t}")
                } else if self.r.chance(40) {
                    let c = self.col();
                    format!("SELECT {t}.c0, CASE WHEN {t}.{c} > 5 THEN 1 WHEN {t}.{c} < 3 THEN {t}.c1 END AS c1 FROM ({a}) {t}")
                } else {
                    format!("SELECT {t}.c0, {t}.c0 + {t}.c1 AS c1 FROM ({a}) {t}")
                }
            }
            3..=5 => {
                let (a, b) = (self.rel(d), self.rel(d));
                let u = self.alias();
                let kind = ["JOIN", "JOIN", "LEFT JOIN", "RIGHT JOIN", "FULL JOIN"][self.r.below(5)];
                let (p, q, x, y) = (self.col(), self.col(), self.col(), self.col());
                let on = match self.r.below(6) {
                    0 => format!("{t}.{p} < {u}.{q}"),
                    1 => format!("{t}.{p} = {u}.{q} AND {t}.{x} <> {u}.{y}"),
                    _ => format!("{t}.{p} = {u}.{q}"),
                };
                let pad = match self.r.below(6) {
                    0 => format!(" WHERE {u}.{q} IS NULL"),
                    1 => format!(" WHERE {t}.{p} IS NULL"),
                    2 => format!(" WHERE {u}.{q} IS NOT NULL"),
                    _ => String::new(),
                };
                format!("SELECT {t}.{x} AS c0, {u}.{y} AS c1 FROM ({a}) {t} {kind} ({b}) {u} ON {on}{pad}")
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
                    format!("SELECT {t}.c0, TRY_CAST(sum({t}.c1) AS BIGINT) AS c1 FROM ({a}) {t} GROUP BY {t}.c0 HAVING count(*) > 1")
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
                let n = self.range(0, 6);
                if self.r.chance(50) {
                    format!("SELECT {t}.c0, {t}.c1 FROM ({a}) {t} LIMIT {n}")
                } else {
                    format!("SELECT {t}.c0, {t}.c1 FROM ({a}) {t} ORDER BY {t}.c1, {t}.c0 LIMIT {n} OFFSET {}", self.range(0, 3))
                }
            }
            11 => {
                let (a, b) = (self.rel(d), self.rel(d));
                let u = self.alias();
                let op = ["UNION ALL", "UNION ALL", "UNION", "INTERSECT", "EXCEPT"][self.r.below(5)];
                format!("SELECT {t}.c0, {t}.c1 FROM ({a}) {t} {op} SELECT {u}.c0, {u}.c1 FROM ({b}) {u}")
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
            14 => {
                let (a, b) = (self.rel(d), self.rel(d));
                let u = self.alias();
                let (op, agg) = [(">=", "avg"), ("=", "max"), ("=", "min")][self.r.below(3)];
                format!("SELECT {t}.c0, {t}.c1 FROM ({a}) {t} WHERE {t}.c0 {op} (SELECT TRY_CAST({agg}({u}.c0) AS BIGINT) FROM ({b}) {u})")
            }
            15 => {
                let (a, b) = (self.rel(d), self.rel(d));
                let u = self.alias();
                format!("SELECT {t}.c0, (SELECT count(*) FROM ({b}) {u} WHERE {u}.c0 = {t}.c1) AS c1 FROM ({a}) {t}")
            }
            16 => {
                let (a, b) = (self.rel(d), self.rel(d));
                let u = self.alias();
                let (p, q) = (self.col(), self.col());
                let pred = self.pred(&t);
                let neg = if self.r.chance(50) { "NOT " } else { "" };
                format!("SELECT {t}.c0, {t}.c1 FROM ({a}) {t} WHERE {pred} OR {neg}EXISTS (SELECT 1 FROM ({b}) {u} WHERE {u}.{q} = {t}.{p})")
            }
            17 => {
                let a = self.rel(d);
                format!("SELECT DISTINCT ON ({t}.c0) {t}.c0, {t}.c1 FROM ({a}) {t} ORDER BY {t}.c0, {t}.c1")
            }
            18 => {
                let a = self.rel(d);
                let (u, v) = (self.alias(), self.alias());
                let c = self.col();
                let k = self.range(0, 10);
                format!(
                    "SELECT {t}.c0, {t}.c1 FROM ({a}) {t} WHERE {t}.{c} < {k} \
                     UNION ALL SELECT {u}.c0, {u}.c1 FROM ({a}) {u} WHERE {u}.{c} >= {k} \
                     UNION ALL SELECT {v}.c0, {v}.c1 FROM ({a}) {v} WHERE {v}.{c} IS NULL"
                )
            }
            _ => {
                let a = self.rel(d);
                let u = self.alias();
                let c = self.col();
                let part = if self.r.chance(70) { format!("PARTITION BY {t}.{c}") } else { String::new() };
                format!(
                    "SELECT {u}.c0, {u}.c1 FROM (SELECT {t}.c0, {t}.c1, row_number() OVER ({part} ORDER BY {t}.c0, {t}.c1) AS rn \
                     FROM ({a}) {t}) {u} WHERE {u}.rn <= {}",
                    self.range(0, 4)
                )
            }
        }
    }
}

fn generate(r: &mut Rng) -> String {
    if r.chance(60) {
        Flat { r, n: 0 }.query()
    } else {
        let depth = 1 + r.below(3) as u32;
        Nested { r, alias: 0 }.rel(depth)
    }
}

/// A query, run both ways.
struct Case {
    name: String,
    /// Which group of consecutive generated queries it is in.
    group: usize,
    sql: String,
    observed: bool,
    /// DuckDB's profiles: with one thread, then four.
    plans: Vec<ObservedPlan>,
    /// The rows DataFusion returns.
    truth: u64,
}

fn show(lo: u64, hi: Option<u64>) -> String {
    match hi {
        Some(h) => format!("{lo}..{h}"),
        None => format!("{lo}.."),
    }
}

fn env<T: std::str::FromStr>(name: &str, default: T) -> T {
    std::env::var(name).ok().and_then(|v| v.parse().ok()).unwrap_or(default)
}

#[tokio::test(flavor = "multi_thread")]
async fn uf_bounds_hold() {
    if !live::duckdb_available() {
        eprintln!("skipped: no duckdb CLI");
        return;
    }
    let n: usize = env("CARDINAL_UF_TRUTH_N", 700);
    let seed: u64 = env("CARDINAL_UF_TRUTH_SEED", 11);
    let threads: usize = env("CARDINAL_UF_TRUTH_THREADS", 4);
    let group: usize = env("CARDINAL_UF_TRUTH_GROUP", 10);
    let only: Option<Vec<String>> = std::env::var("CARDINAL_UF_TRUTH_ONLY").ok().map(|o| o.split(',').map(str::to_string).collect());

    // The data, in DuckDB and DataFusion alike.
    let db = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("uf_truth_{seed}.duckdb"));
    let _ = std::fs::remove_file(&db);
    let _ = std::fs::remove_file(db.with_extension("duckdb.wal"));
    live::run(&db, &ddl(&dataset(seed)), &[]).unwrap();
    let ctx: SessionContext = dataset(seed).context(true);
    let catalog = Catalog::from_context(&ctx).await.unwrap().with_partial_indexes(Vec::<(String, String)>::new());
    let fks = foreign_keys();

    // The queries, each run in both.
    let mut r = Rng::new(seed);
    let mut cases = vec![];
    let (mut unplanned, mut differ) = (0, vec![]);
    // With `only`, just the groups of the queries named.
    let wanted: Option<Vec<usize>> = only.as_ref().map(|o| o.iter().filter_map(|q| q.trim_start_matches('q').parse::<usize>().ok()).map(|i| i / group).collect());
    for i in 0..n {
        let sql = generate(&mut r);
        let name = format!("q{i:03}");
        if wanted.as_ref().is_some_and(|w| !w.contains(&(i / group))) {
            continue;
        }
        if std::env::var("CARDINAL_UF_TRUTH_SHOW").is_ok() {
            println!("{name}: {sql}");
        }
        let truth = match ctx.sql(&sql).await {
            Ok(df) => match df.collect().await {
                Ok(batches) => batches.iter().map(|b| b.num_rows() as u64).sum::<u64>(),
                Err(_) => {
                    unplanned += 1;
                    continue;
                }
            },
            Err(_) => {
                unplanned += 1;
                continue;
            }
        };
        let mut plans = vec![];
        for threads in [1, 4] {
            let label = format!("{name}/t{threads}");
            match live::profile(&db, &sql, threads).and_then(|json| from_duckdb(&catalog, &label, &json, None).map_err(|e| e.to_string())) {
                Ok(p) => plans.push(p),
                // `count(*)` of a table is answered from metadata: no operators.
                Err(e) if e.contains("0 children") => {}
                Err(e) => eprintln!("{label}: does not profile: {e}\n  {sql}"),
            }
        }
        if plans.len() < 2 {
            unplanned += 1;
            continue;
        }
        let duck = plans[0].nodes[plans[0].root].rows;
        if duck != truth || plans[1].nodes[plans[1].root].rows != duck {
            // The engines read the query differently: no truth to hold.
            differ.push(format!("{name}: DataFusion {truth}, DuckDB {duck}: {sql}"));
            continue;
        }
        cases.push(Case { name, group: i / group, sql, observed: i % 2 == 0, plans, truth });
    }

    // Each query bounded, as each engine plans it, in groups: each with an
    // encoder of its own, which observes every other query of the group.
    let state = ctx.state();
    let mut logical = vec![];
    for c in &cases {
        let l = match state.create_logical_plan(&c.sql).await {
            Ok(p) => state.optimize(&p).ok(),
            Err(_) => None,
        };
        logical.push(l);
    }
    let mut groups: Vec<Vec<usize>> = vec![];
    for (i, c) in cases.iter().enumerate() {
        match groups.last_mut() {
            Some(g) if cases[g[0]].group == c.group => g.push(i),
            _ => groups.push(vec![i]),
        }
    }
    let trace = std::env::var("CARDINAL_UF_TRUTH_TRACE").is_ok();
    let failures = Mutex::new(vec![]);
    let next = AtomicUsize::new(0);
    let counts = Mutex::new((0usize, 0usize, 0usize, 0.0f64));
    let started = std::time::Instant::now();
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| {
                loop {
                    let g = next.fetch_add(1, Ordering::Relaxed);
                    let Some(members) = groups.get(g) else { break };
                    let g = cases[members[0]].group;
                    let mut enc = Encoder::new(&catalog, &fks);
                    for c in members.iter().map(|i| &cases[*i]).filter(|c| c.observed) {
                        for p in &c.plans {
                            enc.observe(p);
                        }
                    }
                    for &i in members {
                        let c = &cases[i];
                        if only.as_ref().is_some_and(|o| !o.contains(&c.name)) {
                            continue;
                        }
                        let mode = if c.observed { "own" } else { "others" };
                        for planner in ["df", "duck"] {
                            if trace {
                                eprintln!("start {} {planner}", c.name);
                            }
                            let b = match planner {
                                "df" => match &logical[i] {
                                    Some(l) => enc.bound(l, &[]),
                                    None => continue,
                                },
                                _ => enc.bound_observed(&c.plans[0], &[]),
                            };
                            let b = match b {
                                Ok(b) => b,
                                Err(e) => {
                                    failures.lock().unwrap().push(format!("{} {planner}: {e}\n  {}", c.name, c.sql));
                                    continue;
                                }
                            };
                            let unsound = b.lower > c.truth || b.upper.is_some_and(|u| u < c.truth);
                            println!(
                                "{} g{g} {planner:<4} {mode:<6} truth {:<5} uf {:<10} ({:.1}s){}",
                                c.name,
                                c.truth,
                                show(b.lower, b.upper),
                                b.time.as_secs_f64(),
                                if unsound { "  UNSOUND" } else { "" }
                            );
                            let mut k = counts.lock().unwrap();
                            k.0 += 1;
                            k.1 += b.upper.is_some() as usize;
                            k.2 += (b.upper == Some(c.truth) && b.lower == c.truth) as usize;
                            k.3 += b.time.as_secs_f64();
                            if unsound {
                                failures.lock().unwrap().push(format!(
                                    "{} (group {g}) {planner} ({mode}): {} but {} rows; dropped {:?}\n  {}",
                                    c.name,
                                    show(b.lower, b.upper),
                                    c.truth,
                                    b.dropped,
                                    c.sql
                                ));
                            }
                        }
                    }
                }
            });
        }
    });
    let (bounded, upper, exact, time) = *counts.lock().unwrap();
    let failures = failures.into_inner().unwrap();
    for d in &differ {
        println!("engines differ: {d}");
    }
    println!(
        "uf_truth: {n} queries (seed {seed}), {unplanned} not run, {} read differently; {} bounded ({} observed), {bounded} bounds: \
         {upper} with an upper bound, {exact} exact; {time:.0}s solving, {:.0}s in all",
        differ.len(),
        cases.len(),
        cases.iter().filter(|c| c.observed).count(),
        started.elapsed().as_secs_f64(),
    );
    assert!(failures.is_empty(), "{} unsound:\n{}", failures.len(), failures.join("\n"));
}

/// Bounds `sql` alone, then with each of `facts`' profiles observed in
/// turn, then with its own: each bound as DataFusion plans it (and alone,
/// as DuckDB planned it), with its label, against the true count.
/// `verbose` prints the plans, terms and facts.
async fn bounds_of(sql: &str, facts: &[&str], verbose: bool) -> (u64, Vec<(String, u64, Option<u64>)>) {
    let seed: u64 = env("CARDINAL_UF_TRUTH_SEED", 11);
    static N: AtomicUsize = AtomicUsize::new(0);
    let n = N.fetch_add(1, Ordering::Relaxed);
    let db = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("uf_one_{seed}_{}_{n}.duckdb", std::process::id()));
    let _ = std::fs::remove_file(&db);
    live::run(&db, &ddl(&dataset(seed)), &[]).unwrap();
    let ctx: SessionContext = dataset(seed).context(true);
    let catalog = Catalog::from_context(&ctx).await.unwrap().with_partial_indexes(Vec::<(String, String)>::new());
    let fks = foreign_keys();
    let truth: u64 = ctx.sql(sql).await.unwrap().collect().await.unwrap().iter().map(|b| b.num_rows() as u64).sum();
    let state = ctx.state();
    let l = state.optimize(&state.create_logical_plan(sql).await.unwrap()).unwrap();
    let plan = from_duckdb(&catalog, "one/t1", &live::profile(&db, sql, 1).unwrap(), None).unwrap();
    assert_eq!(plan.nodes[plan.root].rows, truth, "DuckDB and DataFusion differ on {sql}");
    let mut enc = Encoder::new(&catalog, &fks);
    if verbose {
        println!("{}\n{plan}", l.display_indent());
        println!("term: {}\nplanned: {}", enc.target_term(&l), enc.planned_term(&plan));
    }
    let mut out = vec![];
    let mut push = |label: String, b: cardinal::uf::Bound| {
        if verbose {
            println!("{label}: {} dropped {:?}", show(b.lower, b.upper), b.dropped);
        }
        out.push((label, b.lower, b.upper));
    };
    push("alone: df".into(), enc.bound(&l, &[]).unwrap());
    push("alone: duck".into(), enc.bound_observed(&plan, &[]).unwrap());
    for (i, q) in facts.iter().enumerate() {
        let name = format!("fact{i}/t1");
        enc.observe(&from_duckdb(&catalog, &name, &live::profile(&db, q, 1).unwrap(), None).unwrap());
        if verbose {
            enc.describe(&name).iter().for_each(|f| println!("  {f}"));
        }
        push(format!("with {name}: df"), enc.bound(&l, &[]).unwrap());
    }
    enc.observe(&plan);
    if verbose {
        enc.describe("one/t1").iter().for_each(|f| println!("  {f}"));
    }
    push("observed: df".into(), enc.bound(&l, &[]).unwrap());
    let _ = std::fs::remove_file(&db);
    (truth, out)
}

/// One query, `CARDINAL_UF_ONE`, bounded alone, with the profiles of
/// `CARDINAL_UF_FACTS` (`;` between queries) and with its own, against
/// its truth: to minimize an unsound case.
#[tokio::test(flavor = "multi_thread")]
async fn one() {
    let Ok(sql) = std::env::var("CARDINAL_UF_ONE") else { return };
    let facts = std::env::var("CARDINAL_UF_FACTS").unwrap_or_default();
    let facts: Vec<&str> = facts.split(';').map(str::trim).filter(|q| !q.is_empty()).collect();
    let (truth, _) = bounds_of(&sql, &facts, true).await;
    println!("truth {truth}");
}

/// The unsound cases this harness found, minimized: each bound must hold.
#[tokio::test(flavor = "multi_thread")]
async fn found() {
    if !live::duckdb_available() {
        eprintln!("skipped: no duckdb CLI");
        return;
    }
    let cases: &[(&str, &[&str])] = &[
        // `x IN (2, NULL)` is TRUE where `x = 2` is, but never FALSE: it
        // was one predicate with `x = 2`, so `NOT x = 2` kept no rows, and
        // `NULL` was the constant `false`, whose negation kept every row.
        ("SELECT * FROM rc WHERE x IN (2, NULL)", &[]),
        // `k IS DISTINCT FROM 2` was NULL, not TRUE, where `k` is NULL.
        ("SELECT * FROM rc WHERE (k IS DISTINCT FROM 2) AND k IS NULL", &[]),
        // `id IN (0, NULL)` and its negation do not split `ra` though `id`
        // is never NULL: the literal NULL makes either NULL.
        ("SELECT * FROM ra WHERE id IN (0, NULL)", &["SELECT * FROM ra"]),
        ("SELECT id, k FROM ra WHERE k IN (4, NULL)", &["SELECT x1.id FROM ra x1 WHERE x1.id IN (0, NULL)"]),
    ];
    let mut failures = vec![];
    for (sql, facts) in cases {
        let (truth, bounds) = bounds_of(sql, facts, false).await;
        for (label, lo, hi) in bounds {
            if lo > truth || hi.is_some_and(|h| h < truth) {
                failures.push(format!("{sql} {label}: {} but {truth} rows", show(lo, hi)));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
