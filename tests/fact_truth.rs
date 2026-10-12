//! Facts against the truth, on many queries run live.
//!
//! Every query (TPC-H, the hand-written fixtures, the larger ones in
//! `tests/truth/queries.sql`, and generated ones) runs in DuckDB, profiled
//! with one thread and with four, so that plans and runtime filters differ;
//! and in PostgreSQL, profiled as it plans them, with hash joins only, and
//! with merge joins.
//! Every fact derived from all the profiles is then counted from what its
//! context means ([`FactKind::count_sql`]) and must equal its value, every
//! bound must be at least the true count, and no two plans may disagree.
//! Last, each query DataFusion can plan is bounded with the facts, and each
//! bound must hold its true row count.
//!
//! Needs the `duckdb` CLI, and for PostgreSQL a server with the database
//! `scripts/postgres_fixtures.sh` loads; each is skipped without.
//! `CARDINAL_TRUTH_N` sets the
//! number of generated queries (default 120), `CARDINAL_TRUTH_SEED` their
//! seed, and `CARDINAL_TRUTH_ONLY` (a substring of names) limits the queries.
//!
//! ```sh
//! cargo test --release --test fact_truth -- --nocapture
//! ```

mod fixtures;
mod live;

use std::collections::HashMap;

use cardinal::facts::{Fact, FactKind, Ratio, derive_facts};
use cardinal::observed::{Catalog, ObservedPlan};
use cardinal::{FactMode, Options};
use fixtures::{DIR, catalog, context, foreign_keys};
use live::{Engine, Rng, TIMED_OUT};

/// The hand-written larger queries, by name.
fn written() -> Vec<(String, String)> {
    let text = std::fs::read_to_string(format!("{}/tests/truth/queries.sql", env!("CARGO_MANIFEST_DIR"))).unwrap();
    let mut out = vec![];
    for part in text.split("-- name: ").skip(1) {
        let (name, sql) = part.split_once('\n').unwrap();
        out.push((format!("w_{}", name.trim()), sql.trim().to_string()));
    }
    out
}

/// The fixture queries: TPC-H and the hand-written extras.
fn fixture_queries() -> Vec<(String, String)> {
    let mut out = vec![];
    for dir in ["tpch", "extra"] {
        for (name, _) in fixtures::fixtures(dir) {
            out.push((format!("{dir}_{name}"), fixtures::query(dir, &name)));
        }
    }
    out
}

/// TPC-H's joins: two tables and the condition relating them.
const EDGES: &[(&str, &str, &str)] = &[
    ("lineitem", "orders", "l_orderkey = o_orderkey"),
    ("orders", "customer", "o_custkey = c_custkey"),
    ("customer", "nation", "c_nationkey = n_nationkey"),
    ("supplier", "nation", "s_nationkey = n_nationkey"),
    ("nation", "region", "n_regionkey = r_regionkey"),
    ("lineitem", "part", "l_partkey = p_partkey"),
    ("lineitem", "supplier", "l_suppkey = s_suppkey"),
    ("partsupp", "part", "ps_partkey = p_partkey"),
    ("partsupp", "supplier", "ps_suppkey = s_suppkey"),
];

/// A random predicate on `table`.
fn filter(r: &mut Rng, table: &str) -> String {
    let n = |r: &mut Rng, lo: usize, hi: usize| lo + r.below(hi - lo + 1);
    let date = |r: &mut Rng| format!("date '199{}-{:02}-01'", 2 + r.below(7), 1 + r.below(12));
    match table {
        "lineitem" => match r.below(6) {
            0 => format!("l_quantity < {}", n(r, 1, 50)),
            1 => format!("l_discount > 0.0{}", n(r, 1, 9)),
            2 => format!("l_shipdate > {}", date(r)),
            3 => format!("l_returnflag = '{}'", r.pick(&["R", "A", "N"])),
            4 => format!("l_shipmode in ('{}', '{}')", r.pick(&["AIR", "MAIL"]), r.pick(&["SHIP", "RAIL", "TRUCK"])),
            _ => "l_commitdate < l_receiptdate".into(),
        },
        "orders" => match r.below(4) {
            0 => format!("o_totalprice > {}", n(r, 1000, 400000)),
            1 => format!("o_orderstatus = '{}'", r.pick(&["F", "O", "P"])),
            2 => format!("o_orderdate < {}", date(r)),
            _ => format!("o_orderpriority = '{}'", r.pick(&["1-URGENT", "2-HIGH", "5-LOW"])),
        },
        "customer" => match r.below(3) {
            0 => format!("c_acctbal > {}", n(r, 0, 10000) as i64 - 1000),
            1 => format!("c_mktsegment = '{}'", r.pick(&["BUILDING", "AUTOMOBILE", "MACHINERY", "HOUSEHOLD", "FURNITURE"])),
            _ => format!("c_custkey < {}", n(r, 1, 1500)),
        },
        "nation" => match r.below(2) {
            0 => format!("n_name in ('{}', '{}')", r.pick(&["FRANCE", "GERMANY", "CHINA"]), r.pick(&["BRAZIL", "JAPAN", "KENYA"])),
            _ => format!("n_nationkey < {}", n(r, 0, 25)),
        },
        "region" => format!("r_name = '{}'", r.pick(&["ASIA", "EUROPE", "AMERICA", "AFRICA", "MIDDLE EAST"])),
        "part" => match r.below(3) {
            0 => format!("p_size < {}", n(r, 1, 50)),
            1 => format!("p_brand = 'Brand#{}{}'", n(r, 1, 5), n(r, 1, 5)),
            _ => format!("p_type like '%{}'", r.pick(&["BRASS", "STEEL", "TIN", "COPPER"])),
        },
        "supplier" => match r.below(2) {
            0 => format!("s_acctbal > {}", n(r, 0, 10000) as i64 - 1000),
            _ => format!("s_suppkey < {}", n(r, 1, 100)),
        },
        _ => match r.below(2) {
            0 => format!("ps_availqty < {}", n(r, 1, 10000)),
            _ => format!("ps_supplycost > {}", n(r, 1, 1000)),
        },
    }
}

/// A column of `table` worth grouping on.
fn key(r: &mut Rng, table: &str) -> &'static str {
    match table {
        "lineitem" => ["l_suppkey", "l_returnflag", "l_orderkey"][r.below(3)],
        "orders" => ["o_custkey", "o_orderstatus", "o_orderpriority"][r.below(3)],
        "customer" => ["c_nationkey", "c_mktsegment"][r.below(2)],
        "nation" => ["n_regionkey", "n_name"][r.below(2)],
        "region" => "r_name",
        "part" => ["p_brand", "p_size"][r.below(2)],
        "supplier" => "s_nationkey",
        _ => "ps_suppkey",
    }
}

/// The table on the other side of `edge` from `t`, and the columns joined:
/// `t`'s, then the other's.
fn across<'a>(edge: &(&'a str, &'a str, &'a str), t: &str) -> (&'a str, &'a str, &'a str) {
    let (a, b, on) = *edge;
    let (x, y) = on.split_once(" = ").unwrap();
    let (mine, theirs) = if x.starts_with(prefix(t)) { (x, y) } else { (y, x) };
    (if a == t { b } else { a }, mine, theirs)
}

/// A predicate relating a row of `inside` to table `n` across an edge: a
/// semi or anti join in one of its spellings, some nested, grouped, or
/// against a column that may be NULL.
fn subquery(r: &mut Rng, inside: &str, n: &str, on: &str, mine: &str, theirs: &str) -> String {
    let f = filter(r, n);
    match r.below(9) {
        0 => format!("EXISTS (SELECT * FROM {n} WHERE {on} AND {f})"),
        1 => format!("NOT EXISTS (SELECT * FROM {n} WHERE {on} AND {f})"),
        2 => format!("{mine} IN (SELECT {theirs} FROM {n} WHERE {f})"),
        3 => format!("{mine} NOT IN (SELECT {theirs} FROM {n} WHERE {f})"),
        // NOT IN a column with NULLs: no row passes where one exists.
        4 => format!("{mine} NOT IN (SELECT CASE WHEN {f} THEN NULL ELSE {theirs} END FROM {n})"),
        5 => format!("{mine} IN (SELECT {theirs} FROM {n} GROUP BY {theirs} HAVING count(*) > {})", r.below(30)),
        // Nested: a further table across another edge of `n`.
        6 | 7 => {
            let next: Vec<&(&str, &str, &str)> = EDGES.iter().filter(|e| (e.0 == n || e.1 == n) && e.0 != inside && e.1 != inside).collect();
            match next.first() {
                Some(e) => {
                    let (m, _, _) = across(e, n);
                    let g = filter(r, m);
                    let not = if r.chance(50) { "NOT " } else { "" };
                    format!("EXISTS (SELECT * FROM {n} WHERE {on} AND {not}EXISTS (SELECT * FROM {m} WHERE {} AND {g}))", e.2)
                }
                None => format!("EXISTS (SELECT * FROM {n} WHERE {on} AND {f})"),
            }
        }
        _ => format!("{mine} > (SELECT min({theirs}) FROM {n} WHERE {f})"),
    }
}

/// A random query: a tree of joins (inner, left with the joined table's
/// filter in ON, in WHERE or as IS NULL, or full), some tables replaced by
/// a grouping of them, filters, semi and anti joins to tables outside the
/// tree, and a count, grouping, DISTINCT or rows on top.
fn generate(r: &mut Rng) -> String {
    let start = EDGES[r.below(EDGES.len())].0;
    let mut tables = vec![start];
    // Tables replaced by a grouping on one column: only that column remains.
    let mut grouped: HashMap<&str, &str> = HashMap::new();
    let mut from = start.to_string();
    let mut wheres: Vec<String> = vec![];
    for _ in 0..r.below(6) {
        let options: Vec<(&str, &str, &str, &str)> = EDGES
            .iter()
            .filter_map(|e| {
                let t = [e.0, e.1].into_iter().find(|t| tables.contains(t) && !grouped.contains_key(t))?;
                let (other, mine, theirs) = across(e, t);
                (!tables.contains(&other)).then_some((other, e.2, mine, theirs))
            })
            .collect();
        if options.is_empty() {
            break;
        }
        let (t, on, _, theirs) = options[r.below(options.len())];
        tables.push(t);
        let leaf = if r.chance(20) {
            grouped.insert(t, theirs);
            let f = if r.chance(50) { format!(" WHERE {}", filter(r, t)) } else { String::new() };
            let having = if r.chance(40) { format!(" HAVING count(*) > {}", r.below(20)) } else { String::new() };
            format!("(SELECT {theirs}, count(*) AS n_{t} FROM {t}{f} GROUP BY {theirs}{having}) AS g_{t}")
        } else {
            t.to_string()
        };
        let f = if grouped.contains_key(t) { format!("n_{t} > {}", r.below(10)) } else { filter(r, t) };
        match r.below(9) {
            0 | 1 => {
                from.push_str(&format!(" CROSS JOIN {leaf}"));
                wheres.push(on.into());
            }
            2 | 3 => from.push_str(&format!(" JOIN {leaf} ON {on}")),
            4 => from.push_str(&format!(" LEFT JOIN {leaf} ON {on} AND {f}")),
            5 => {
                from.push_str(&format!(" LEFT JOIN {leaf} ON {on}"));
                wheres.push(f);
            }
            6 => {
                from.push_str(&format!(" LEFT JOIN {leaf} ON {on} AND {f}"));
                wheres.push(format!("{theirs} IS NULL"));
            }
            7 => {
                from.push_str(&format!(" FULL JOIN {leaf} ON {on}"));
                if r.chance(60) {
                    wheres.push(f);
                }
            }
            _ => {
                from.push_str(&format!(" LEFT JOIN {leaf} ON {on}"));
                wheres.push(format!("({theirs} IS NULL OR {f})"));
            }
        }
    }
    for &t in &tables {
        if !grouped.contains_key(t) && r.chance(40) {
            wheres.push(filter(r, t));
        }
    }
    for _ in 0..r.below(3) {
        let outside: Vec<(&str, &str, &str, &str, &str)> = EDGES
            .iter()
            .filter_map(|e| {
                let t = [e.0, e.1].into_iter().find(|t| tables.contains(t) && !grouped.contains_key(t))?;
                let (other, mine, theirs) = across(e, t);
                (!tables.contains(&other)).then_some((t, other, e.2, mine, theirs))
            })
            .collect();
        if outside.is_empty() {
            break;
        }
        let (inside, n, on, mine, theirs) = outside[r.below(outside.len())];
        wheres.push(subquery(r, inside, n, on, mine, theirs));
    }
    let filter = if wheres.is_empty() { String::new() } else { format!(" WHERE {}", wheres.join(" AND ")) };
    let t = tables[r.below(tables.len())];
    let k = match grouped.get(t) {
        Some(c) => *c,
        None => key(r, t),
    };
    match r.below(6) {
        0 | 1 => format!("SELECT count(*) FROM {from}{filter}"),
        2 => {
            let having = match r.below(3) {
                0 => String::new(),
                1 => format!(" HAVING count(*) > {}", r.below(50)),
                _ => format!(" HAVING {k} IS NOT NULL"),
            };
            format!("SELECT {k}, count(*) FROM {from}{filter} GROUP BY {k}{having}")
        }
        3 => format!("SELECT DISTINCT {k} FROM {from}{filter}"),
        4 => format!("SELECT count(*) FROM (SELECT DISTINCT {k} FROM {from}{filter})"),
        _ => format!("SELECT {k} FROM {from}{filter}"),
    }
}

fn prefix(table: &str) -> &'static str {
    match table {
        "lineitem" => "l_",
        "orders" => "o_",
        "customer" => "c_",
        "nation" => "n_",
        "region" => "r_",
        "part" => "p_",
        "supplier" => "s_",
        _ => "ps_",
    }
}

/// Whether `value` is what `counts` give for `kind`.
fn agrees(kind: &FactKind, value: Ratio, n: u64, of: Option<u64>) -> bool {
    match (kind, of) {
        (FactKind::Unique { .. }, Some(of)) => n == of,
        (_, Some(of)) => Ratio::new(n, of) == Some(value),
        (_, None) => value.as_int() == Some(n),
    }
}

#[tokio::test]
async fn facts_are_true() {
    match Engine::duckdb() {
        Some(engine) => truth(engine).await,
        None => eprintln!("skipped: no duckdb CLI"),
    }
}

#[tokio::test]
async fn facts_are_true_in_postgres() {
    match Engine::postgres() {
        Some(engine) => truth(engine).await,
        None => eprintln!("skipped: no PostgreSQL with the fixtures' database"),
    }
}

/// Every query's facts, read off `engine`'s profiles, against its counts.
async fn truth(engine: Engine) {
    let catalog: Catalog = catalog().await;
    let n: usize = std::env::var("CARDINAL_TRUTH_N").ok().and_then(|n| n.parse().ok()).unwrap_or(120);
    let seed: u64 = std::env::var("CARDINAL_TRUTH_SEED").ok().and_then(|n| n.parse().ok()).unwrap_or(7);
    let only = std::env::var("CARDINAL_TRUTH_ONLY").ok();
    let mut queries = fixture_queries();
    queries.extend(written());
    let mut r = Rng::new(seed);
    queries.extend((0..n).map(|i| (format!("g{i:03}"), generate(&mut r))));
    queries.retain(|(name, _)| only.as_ref().is_none_or(|o| name.contains(o.as_str())));
    if std::env::var("CARDINAL_TRUTH_SHOW").is_ok() {
        for (name, sql) in &queries {
            println!("{name}: {sql}");
        }
    }

    // Profile each query in each way.
    let mut failures = vec![];
    let mut slow = 0;
    let mut plans: Vec<(String, String, ObservedPlan)> = vec![];
    let variants = engine.variants();
    for (name, sql) in &queries {
        for variant in &variants {
            let label = format!("{name}/{variant}");
            let profiled = engine.profile(sql, variant).and_then(|json| engine.read(&catalog, &label, &json, sql));
            match profiled {
                Ok(p) => plans.push((name.clone(), sql.clone(), p)),
                // `count(*)` of a table is answered from metadata: no operators.
                Err(e) if e.contains("0 children") => {}
                Err(e) if e == TIMED_OUT => slow += 1,
                Err(e) => failures.push(format!("{label}: does not profile: {e}\n  {sql}")),
            }
        }
    }
    let all: Vec<ObservedPlan> = plans.iter().map(|(.., p)| p.clone()).collect();
    let mut facts = derive_facts(&all);
    for c in &facts.conflicts {
        failures.push(format!("conflict: {} = {} vs {}\n  {:?}\n  {:?}", c.kind, c.values.0, c.values.1, c.origins.0, c.origins.1));
    }

    // Every fact and bound, counted.
    let mut checks: Vec<(&Fact, bool, usize, Option<usize>)> = vec![];
    let mut sql: Vec<String> = vec![];
    let mut index: HashMap<String, usize> = HashMap::new();
    let mut at = |q: String, sql: &mut Vec<String>| {
        *index.entry(q.clone()).or_insert_with(|| {
            sql.push(q);
            sql.len() - 1
        })
    };
    let mut unchecked = 0;
    let mut uncountable: std::collections::BTreeMap<&str, usize> = Default::default();
    for (f, bound) in facts.iter().map(|f| (f, false)).chain(facts.bounds().map(|f| (f, true))) {
        match f.kind.count_sql_in(&catalog, &facts, engine.dialect()) {
            Some(c) => {
                let v = at(c.value, &mut sql);
                let of = c.of.map(|q| at(q, &mut sql));
                checks.push((f, bound, v, of));
            }
            None => {
                unchecked += 1;
                let text = f.kind.to_string();
                let why = if text.contains("Mark join") {
                    "a mark join"
                } else if text.contains("\"value\".") {
                    "an aggregate's value"
                } else if text.contains("top ") {
                    "a top-n"
                } else if text.contains("union(") {
                    "a union"
                } else {
                    "other"
                };
                *uncountable.entry(why).or_default() += 1;
                if why == "other" || std::env::var("CARDINAL_TRUTH_SHOW").is_ok() {
                    eprintln!("not countable: {text}");
                }
            }
        }
    }
    let counted = engine.values(&sql);
    let (mut exact, mut bounded) = (0, 0);
    for (f, bound, v, of) in &checks {
        let (n, of) = match (&counted[*v], of.map(|o| &counted[o])) {
            (Ok(n), None) => (*n, None),
            (Ok(n), Some(Ok(o))) => (*n, Some(*o)),
            (Err(e), _) | (_, Some(Err(e))) if e == TIMED_OUT => {
                slow += 1;
                continue;
            }
            (Err(e), _) | (_, Some(Err(e))) => {
                failures.push(format!("{}: does not count: {e}\n  {}", f.kind, sql[*v]));
                continue;
            }
        };
        if *bound {
            bounded += 1;
            if f.value.as_int().is_none_or(|b| b < n) {
                failures.push(format!("{} <= {} but is {n}, from {:?}", f.kind, f.value, f.origins));
            }
        } else {
            exact += 1;
            if !agrees(&f.kind, f.value, n, of) {
                failures.push(format!("{} = {} but is {n}{}, from {:?}", f.kind, f.value, of.map(|o| format!("/{o}")).unwrap_or_default(), f.origins));
            }
        }
    }

    // What the profiles did not count, counted: it must agree with what
    // they did, and bound the queries as well.
    let (observed, conflicts) = (facts.len(), facts.conflicts.len());
    let (filled, unfilled) = engine.fill(&catalog, &mut facts);
    for c in &facts.conflicts[conflicts..] {
        failures.push(format!("conflict, once counted: {} = {} vs {}\n  {:?}\n  {:?}", c.kind, c.values.0, c.values.1, c.origins.0, c.origins.1));
    }

    // Bounds with the facts hold each query's true count.
    let ctx = context();
    let mut analyzed = 0;
    let mut matched = 0;
    let first = format!("/{}", variants[0]);
    for (name, sql, plan) in plans.iter().filter(|(_, _, p)| p.name.ends_with(&first)) {
        let options = Options { selectivity: true, foreign_keys: foreign_keys(), ..Default::default() };
        let Ok(a) = cardinal::analyze_sql_with(&ctx, sql, options).await else { continue };
        let truth = plan.nodes[plan.root].rows;
        analyzed += 1;
        for mode in [FactMode::Ratios, FactMode::Pinned] {
            let i = match a.with_facts(&facts, mode) {
                Ok(i) => i,
                Err(e) => {
                    failures.push(format!("{name} {mode:?}: {e}"));
                    continue;
                }
            };
            if mode == FactMode::Ratios {
                matched += i.matched.len();
            }
            if !i.rejected.is_empty() {
                failures.push(format!("{name} {mode:?}: rejected {:?}\n  {sql}", i.rejected));
            }
            if mode == FactMode::Pinned
                && let Ok((lo, hi)) = i.range()
                && (lo > truth || hi.is_some_and(|hi| hi < truth))
            {
                failures.push(format!("{name}: {lo} <= X <= {hi:?}, not {truth}\n  {sql}\n  {i}"));
            }
        }
    }
    println!(
        "{}: {} queries, {} plans: {observed} facts and {} bounds; {exact} facts and {bounded} bounds counted, {unchecked} not countable; \
         {filled} facts the profiles did not count counted since ({unfilled} not), {} with what follows; \
         {analyzed} queries bounded, {matched} selectivities matched; {slow} timed out; not countable: {uncountable:?}",
        engine.name(),
        queries.len(),
        plans.len(),
        facts.bounds().count(),
        facts.len(),
    );
    let _ = DIR;
    assert!(failures.is_empty(), "{} failures:\n{}", failures.len(), failures.join("\n"));
}
