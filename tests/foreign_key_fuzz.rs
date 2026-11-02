//! Randomized soundness testing of the rules that follow foreign keys and
//! ranges: random data satisfying declared foreign keys, random queries of
//! those shapes (range filters; equi, semi and anti joins on foreign and
//! other keys, through joins; groupings), each validated: every constraint,
//! with real row counts, distinct counts, and least and greatest values
//! substituted, must hold.
//!
//! `CARDINAL_FUZZ_N` sets the number of queries (default 200),
//! `CARDINAL_FUZZ_SEED` the seed.

mod common;

use cardinal::{ForeignKey, Options, analyze_sql};
use common::Rng;
use datafusion::prelude::SessionContext;

fn keys() -> Vec<ForeignKey> {
    vec![
        ForeignKey::new("child", &["fk"], "parent", &["id"]),
        ForeignKey::new("other", &["fk"], "parent", &["id"]),
        ForeignKey::new("parent", &["gid"], "grand", &["id"]),
    ]
}

/// `parent(id, a)`, `child(fk, x, y, amt, t)`, `other(fk, x, amt)`: ids
/// distinct and maybe sparse, every `fk` some parent's id, `x`/`a`/`y` small
/// ints, `amt` small decimals in quarters, `t` timestamps on whole days, all
/// with NULLs.
async fn dataset(r: &mut Rng) -> SessionContext {
    let ctx = SessionContext::new();
    let n_parent = 1 + r.below(12) as i64;
    let sparse = r.chance(50);
    let mut ids = vec![];
    let mut next = 1 + r.below(5) as i64;
    for _ in 0..n_parent {
        ids.push(next);
        next += if sparse { 1 + r.below(4) as i64 } else { 1 };
    }
    let val = |r: &mut Rng| if r.chance(15) { "NULL".to_string() } else { r.range(0, 12).to_string() };
    let n_grand = 1 + r.below(5) as i64;
    let grand: Vec<String> = (1..=n_grand).map(|id| format!("({id}, {})", val(r))).collect();
    let parent: Vec<String> = ids.iter().map(|id| format!("({id}, {}, {})", val(r), 1 + r.below(n_grand as u64))).collect();
    let amt = |r: &mut Rng| {
        let v = if r.chance(15) { "NULL".to_string() } else { format!("{}.{:02}", r.range(0, 4), 25 * r.below(4)) };
        format!("CAST({v} AS DECIMAL(6, 2))")
    };
    let t = |r: &mut Rng| {
        let v = if r.chance(15) { "NULL".to_string() } else { format!("'2020-01-{:02} 00:00:00'", 1 + r.below(9)) };
        format!("CAST({v} AS TIMESTAMP)")
    };
    let rows = |r: &mut Rng, ints: usize, times: bool| -> Vec<String> {
        let n = r.below(25) as usize;
        (0..n)
            .map(|_| {
                let fk = ids[r.below(ids.len() as u64) as usize];
                let mut rest: Vec<String> = (1..ints).map(|_| val(r)).collect();
                rest.push(amt(r));
                if times {
                    rest.push(t(r));
                }
                format!("({fk}, {})", rest.join(", "))
            })
            .collect()
    };
    let child = rows(r, 3, true);
    let other = rows(r, 2, false);
    let table = |name: &str, cols: &str, rows: &[String], types: &str| {
        if rows.is_empty() {
            format!("CREATE TABLE {name} AS SELECT {types} WHERE false")
        } else {
            format!("CREATE TABLE {name} AS SELECT * FROM (VALUES {}) AS t({cols})", rows.join(", "))
        }
    };
    for sql in [
        table("grand", "id, b", &grand, "CAST(1 AS BIGINT) AS id, CAST(1 AS BIGINT) AS b"),
        table("parent", "id, a, gid", &parent, "CAST(1 AS BIGINT) AS id, CAST(1 AS BIGINT) AS a, CAST(1 AS BIGINT) AS gid"),
        table(
            "child",
            "fk, x, y, amt, t",
            &child,
            "CAST(1 AS BIGINT) AS fk, CAST(1 AS BIGINT) AS x, CAST(1 AS BIGINT) AS y, CAST(1 AS DECIMAL(6, 2)) AS amt, CAST('2020-01-01' AS TIMESTAMP) AS t",
        ),
        table("other", "fk, x, amt", &other, "CAST(1 AS BIGINT) AS fk, CAST(1 AS BIGINT) AS x, CAST(1 AS DECIMAL(6, 2)) AS amt"),
    ] {
        ctx.sql(&sql).await.unwrap().collect().await.unwrap();
    }
    ctx
}

/// A range predicate on column `c`, or a non-range one.
fn pred(r: &mut Rng, c: &str) -> String {
    let v = |r: &mut Rng| r.range(-1, 14);
    if c.ends_with(".amt") {
        return amt_pred(r, c);
    }
    if c.ends_with(".t") {
        let day = 1 + r.below(10);
        let op = ["<", "<=", ">", ">=", "="][r.below(5) as usize];
        return if r.chance(50) { format!("{c} {op} TIMESTAMP '2020-01-{day:02} 00:00:00'") } else { format!("{c} {op} DATE '2020-01-{day:02}'") };
    }
    match r.below(14) {
        8 => format!("{c} + {} < {}", r.range(-3, 4), v(r)),
        9 => format!("{c} * {} >= {}", 1 + r.below(3), v(r)),
        10 => format!("{} - {c} <= {}", v(r), v(r)),
        11 => format!("CAST({c} AS DOUBLE) < {}.5", v(r)),
        12 => format!("CAST({c} AS DECIMAL(10, 3)) <= {}.125", v(r)),
        13 => format!("{c} + 1 IN ({}, {})", v(r), v(r)),
        _ => pred_plain(r, c, v),
    }
}

/// A comparison of decimal `c` with literals at its scale, coarser, and
/// finer.
fn amt_pred(r: &mut Rng, c: &str) -> String {
    let v = |r: &mut Rng| ["0.125", "1.5", "3", "0.25", "2.75", "1.255"][r.below(6) as usize];
    match r.below(5) {
        0 => format!("{c} < {}", v(r)),
        1 => format!("{c} >= {}", v(r)),
        2 => format!("{c} BETWEEN {} AND {}", v(r), v(r)),
        3 => format!("{c} = {}", v(r)),
        _ => format!("{c} <= {}", v(r)),
    }
}

fn pred_plain(r: &mut Rng, c: &str, v: impl Fn(&mut Rng) -> i64) -> String {
    match r.below(8) {
        0 => format!("{c} < {}", v(r)),
        1 => format!("{c} >= {}", v(r)),
        2 => {
            let a = v(r);
            format!("{c} BETWEEN {a} AND {}", a + r.range(0, 6))
        }
        3 => format!("{c} = {}", v(r)),
        4 => {
            let a = v(r);
            format!("{c} > {a} AND {c} <= {}", a + r.range(0, 8))
        }
        5 => format!("{c} <> {}", v(r)),
        6 => format!("{c} IS NOT NULL"),
        _ => "true".into(),
    }
}

fn query(r: &mut Rng) -> String {
    let pf = |r: &mut Rng| { let c = if r.chance(50) { "p.id" } else { "p.a" }; pred(r, c) };
    let cf = |r: &mut Rng| { let c = ["c.fk", "c.x", "c.y", "c.amt", "c.t"][r.below(5) as usize]; pred(r, c) };
    let of = |r: &mut Rng| { let c = ["o.fk", "o.x", "o.amt"][r.below(3) as usize]; pred(r, c) };
    let gf = |r: &mut Rng| { let c = if r.chance(50) { "g.id" } else { "g.b" }; pred(r, c) };
    match r.below(20) {
        // Ranges of different units meeting: an integer cast to a decimal.
        15 => format!("SELECT * FROM child c JOIN other o ON CAST(c.x AS DECIMAL(6, 2)) = o.amt WHERE {} AND {}", cf(r), of(r)),
        16 => format!("SELECT * FROM child c JOIN other o ON c.amt = o.amt WHERE {} AND {}", cf(r), of(r)),
        17 => format!(
            "SELECT z, count(*) FROM (SELECT CAST(c.x AS DECIMAL(10, 2)) AS z FROM child c WHERE {}) s WHERE {} GROUP BY z",
            cf(r),
            amt_pred(r, "z")
        ),
        18 => format!("SELECT * FROM (SELECT c.x AS v FROM child c WHERE {} UNION ALL SELECT o.amt FROM other o WHERE {}) u WHERE {}", cf(r), of(r), amt_pred(r, "u.v")),
        19 => format!("SELECT c.t, count(*) FROM child c WHERE {} AND {} GROUP BY c.t", pred(r, "c.t"), cf(r)),
        10 => format!("SELECT * FROM child c JOIN (SELECT p.id, g.b FROM parent p JOIN grand g ON p.gid = g.id) pg ON c.fk = pg.id WHERE {}", cf(r)),
        11 => format!("SELECT * FROM child c WHERE c.fk IN (SELECT p.id FROM parent p JOIN grand g ON p.gid = g.id WHERE {})", gf(r)),
        12 => format!("SELECT * FROM child c JOIN parent p ON c.fk = p.id JOIN other o ON o.fk = p.id WHERE {} AND {}", cf(r), of(r)),
        13 => format!("SELECT * FROM child c JOIN (SELECT p.id, g.b FROM parent p LEFT JOIN grand g ON p.gid = g.id) pg ON c.fk = pg.id WHERE {}", cf(r)),
        14 => format!(
            "SELECT pg.b, count(*) FROM child c JOIN (SELECT p.id, g.b FROM parent p JOIN grand g ON p.gid = g.id WHERE {}) pg ON c.fk = pg.id GROUP BY pg.b",
            gf(r)
        ),
        0 => format!("SELECT * FROM child c JOIN parent p ON c.fk = p.id WHERE {} AND {}", cf(r), pf(r)),
        1 => format!("SELECT * FROM parent p WHERE EXISTS (SELECT 1 FROM child c WHERE c.fk = p.id AND {}) AND {}", cf(r), pf(r)),
        2 => format!("SELECT * FROM parent p WHERE NOT EXISTS (SELECT 1 FROM child c WHERE c.fk = p.id AND {}) AND {}", cf(r), pf(r)),
        3 => format!("SELECT * FROM parent p WHERE p.id NOT IN (SELECT c.x FROM child c WHERE {})", cf(r)),
        4 => format!("SELECT * FROM child c JOIN other o ON c.fk = o.fk WHERE {} AND {}", cf(r), of(r)),
        5 => format!("SELECT * FROM child c JOIN other o ON c.x = o.x WHERE {} AND {}", cf(r), of(r)),
        6 => format!("SELECT c.fk, count(*) FROM child c WHERE {} GROUP BY c.fk", cf(r)),
        7 => format!("SELECT * FROM child c WHERE c.x IN (SELECT p.a FROM parent p WHERE {})", pf(r)),
        8 => format!(
            "SELECT * FROM (SELECT c.fk, count(*) AS n FROM child c WHERE {} GROUP BY c.fk) g JOIN parent p ON g.fk = p.id WHERE {}",
            cf(r),
            pf(r)
        ),
        _ => format!("SELECT * FROM other o WHERE NOT EXISTS (SELECT 1 FROM child c WHERE c.x = o.x AND {}) AND {}", cf(r), of(r)),
    }
}

#[tokio::test]
async fn constraints_hold_on_data() {
    let n: u64 = std::env::var("CARDINAL_FUZZ_N").ok().and_then(|s| s.parse().ok()).unwrap_or(200);
    let seed: u64 = std::env::var("CARDINAL_FUZZ_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(7);
    let mut r = Rng::new(seed);
    let mut failures = vec![];
    let (mut checked, mut undecided) = (0, 0);
    for i in 0..n {
        let ctx = dataset(&mut r).await;
        let sql = query(&mut r);
        let options = Options { foreign_keys: keys(), ..Default::default() };
        let a = match analyze_sql(&ctx, &sql, options).await {
            Ok(a) => a,
            Err(e) => {
                println!("{i}: not analyzed: {e}\n  {sql}");
                continue;
            }
        };
        let v = a.validate(&ctx).await.unwrap();
        checked += 1;
        undecided += usize::from(v.undecided);
        if let Some(why) = v.violation {
            failures.push(format!("{i}: {why}\n  {sql}"));
        }
    }
    println!("{checked} checked, {undecided} undecided, {} violations", failures.len());
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
