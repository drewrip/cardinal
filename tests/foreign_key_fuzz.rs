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

use cardinal::{ForeignKey, Options, analyze_sql_with};
use common::Rng;
use datafusion::prelude::SessionContext;

fn keys() -> Vec<ForeignKey> {
    vec![
        ForeignKey::new("child", &["fk"], "parent", &["id"]),
        ForeignKey::new("other", &["fk"], "parent", &["id"]),
        ForeignKey::new("parent", &["gid"], "grand", &["id"]),
    ]
}

/// `parent(id, a)`, `child(fk, x, y)`, `other(fk, x)`: ids distinct and
/// maybe sparse, every `fk` some parent's id, `x`/`a`/`y` small ints with
/// NULLs.
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
    let rows = |r: &mut Rng, cols: usize| -> Vec<String> {
        let n = r.below(25) as usize;
        (0..n)
            .map(|_| {
                let fk = ids[r.below(ids.len() as u64) as usize];
                let rest: Vec<String> = (1..cols).map(|_| val(r)).collect();
                format!("({fk}, {})", rest.join(", "))
            })
            .collect()
    };
    let child = rows(r, 3);
    let other = rows(r, 2);
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
        table("child", "fk, x, y", &child, "CAST(1 AS BIGINT) AS fk, CAST(1 AS BIGINT) AS x, CAST(1 AS BIGINT) AS y"),
        table("other", "fk, x", &other, "CAST(1 AS BIGINT) AS fk, CAST(1 AS BIGINT) AS x"),
    ] {
        ctx.sql(&sql).await.unwrap().collect().await.unwrap();
    }
    ctx
}

/// A range predicate on column `c`, or a non-range one.
fn pred(r: &mut Rng, c: &str) -> String {
    let v = |r: &mut Rng| r.range(-1, 14);
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
    let cf = |r: &mut Rng| { let c = ["c.fk", "c.x", "c.y"][r.below(3) as usize]; pred(r, c) };
    let of = |r: &mut Rng| { let c = if r.chance(50) { "o.fk" } else { "o.x" }; pred(r, c) };
    let gf = |r: &mut Rng| { let c = if r.chance(50) { "g.id" } else { "g.b" }; pred(r, c) };
    match r.below(15) {
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
        let options = Options { selectivity: false, foreign_keys: keys(), ..Default::default() };
        let a = match analyze_sql_with(&ctx, &sql, options).await {
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
