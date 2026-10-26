//! The spec's worked examples (CARDINAL-SPEC.md §10.1–§10.11) against the
//! axiom encoding (`cardinal::uf`), with §10.6's negative controls.
//!
//! Each example builds its small schema twice: as DataFusion tables, which
//! give the catalog and the plans to bound, and as a DuckDB database with
//! data matching the example's observations, whose `EXPLAIN ANALYZE`
//! profiles are the executed plans observed. Every probe is also checked
//! against the true count, which DuckDB computes.
//!
//! ```sh
//! CARDINAL_UF_TIMEOUT_MS=2000 cargo test --release --test uf_spec -- --nocapture
//! ```
//!
//! Inputs the encoder has no way to take are left out, with a note where
//! they would be: functional dependencies (§10.2's `a → k`), CHECK
//! constraints and storage statistics (§10.7's domain of `t.g`), and
//! counted `max` facts (§10.5, stood in for by counts that imply it).

mod live;

use std::path::PathBuf;

use cardinal::ForeignKey;
use cardinal::observed::{Catalog, ObservedPlan, from_duckdb};
use cardinal::uf::{Bound, Encoder};
use datafusion::common::JoinType;
use datafusion::logical_expr::LogicalPlan;
use datafusion::prelude::SessionContext;
use datafusion::prelude::{col, lit};

/// One example's schema and data.
struct Ex {
    db: PathBuf,
    ctx: SessionContext,
    catalog: Catalog,
    fks: Vec<ForeignKey>,
    observed: std::cell::Cell<usize>,
}

impl Ex {
    /// Tables from `ddl` (valid in DataFusion and DuckDB), filled in
    /// DuckDB by `data`.
    async fn new(name: &str, ddl: &[&str], data: &[&str]) -> Ex {
        assert!(live::duckdb_available(), "the duckdb CLI is needed");
        let db = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("uf_spec_{name}.duckdb"));
        let _ = std::fs::remove_file(&db);
        let _ = std::fs::remove_file(db.with_extension("duckdb.wal"));
        let script = format!("{};\n{};\n", ddl.join(";\n"), data.join(";\n"));
        live::run(&db, &script, &[]).unwrap();
        let ctx = SessionContext::new();
        for d in ddl {
            ctx.sql(d).await.unwrap().collect().await.unwrap();
        }
        let catalog = Catalog::from_context(&ctx)
            .await
            .unwrap()
            .with_partial_indexes(Vec::<(String, String)>::new());
        Ex {
            db,
            ctx,
            catalog,
            fks: vec![],
            observed: std::cell::Cell::new(0),
        }
    }

    fn fk(mut self, t: &str, a: &str, u: &str, b: &str) -> Ex {
        self.fks.push(ForeignKey::new(t, &[a], u, &[b]));
        self
    }

    fn encoder(&self) -> Encoder<'_> {
        Encoder::new(&self.catalog, &self.fks)
    }

    /// Runs `sql` in DuckDB and gives its executed plan to `enc`.
    fn observe(&self, enc: &mut Encoder, sql: &str) -> u64 {
        self.observe_with(enc, sql, "")
    }

    /// `observe`, with DuckDB `settings` first.
    fn observe_with(&self, enc: &mut Encoder, sql: &str, settings: &str) -> u64 {
        self.observed.set(self.observed.get() + 1);
        let name = format!("obs{}", self.observed.get());
        let script = format!(
            "PRAGMA disable_print_progress_bar;\nSET threads = 1;\n{settings}\nEXPLAIN (ANALYZE, FORMAT JSON) {sql};\n"
        );
        let out = live::run(&self.db, &script, &["-readonly", "-list", "-noheader"]).unwrap();
        let json = &out[out.find('{').unwrap()..];
        let plan: ObservedPlan = from_duckdb(&self.catalog, &name, json, Some(sql)).unwrap();
        let rows = plan.nodes[plan.root].rows;
        enc.observe(&plan);
        println!("  observed {name} = {rows}: {sql}");
        for f in enc.describe(&name) {
            println!("      {f}");
        }
        rows
    }

    fn truth(&self, sql: &str) -> u64 {
        let q = format!("SELECT count(*) FROM ({sql}) t");
        live::values(&self.db, &[q]).remove(0).unwrap()
    }

    async fn plan(&self, sql: &str, optimize: bool) -> LogicalPlan {
        let state = self.ctx.state();
        let p = state.create_logical_plan(sql).await.unwrap();
        if optimize {
            state.optimize(&p).unwrap()
        } else {
            p
        }
    }
}

/// What a probe must show, besides containing the truth.
#[derive(Default, Clone, Copy)]
struct Want {
    /// The spec's upper bound: the bound found is at most this.
    upper: Option<u64>,
    /// The spec's lower bound: the bound found is at least this.
    lower: Option<u64>,
    /// A negative control: the upper bound found MUST NOT be below this.
    upper_not_below: Option<u64>,
    /// A negative control: the lower bound found MUST NOT be above this.
    lower_not_above: Option<u64>,
}

fn at_most(u: u64) -> Want {
    Want {
        upper: Some(u),
        ..Default::default()
    }
}
fn at_least(l: u64) -> Want {
    Want {
        lower: Some(l),
        ..Default::default()
    }
}
fn exactly(n: u64) -> Want {
    Want {
        upper: Some(n),
        lower: Some(n),
        ..Default::default()
    }
}

fn show(b: &Bound) -> String {
    match b.upper {
        Some(u) => format!("[{}, {u}]", b.lower),
        None => format!("[{}, -]", b.lower),
    }
}

/// Collects each probe's outcome, to fail once at the end with all of them.
#[derive(Default)]
struct Report {
    failures: Vec<String>,
    unsound: Vec<String>,
}

impl Report {
    /// Bounds `sql` (as DataFusion plans it, optimized or not) and checks it.
    async fn probe(
        &mut self,
        ex: &Ex,
        enc: &Encoder<'_>,
        label: &str,
        sql: &str,
        optimize: bool,
        want: Want,
    ) {
        let plan = ex.plan(sql, optimize).await;
        self.probe_plan(ex, enc, label, sql, &plan, want);
    }

    /// Bounds `plan`, whose rows are those of `sql`, and checks it.
    fn probe_plan(
        &mut self,
        ex: &Ex,
        enc: &Encoder<'_>,
        label: &str,
        sql: &str,
        plan: &LogicalPlan,
        want: Want,
    ) {
        let truth = ex.truth(sql);
        let b = enc.bound(plan, &[]).unwrap();
        let mut problems = vec![];
        let mut unsound = vec![];
        if b.lower > truth || b.upper.is_some_and(|u| u < truth) {
            unsound.push(format!("excludes the truth {truth}"));
        }
        if let Some(n) = want.upper_not_below
            && b.upper.is_some_and(|u| u < n)
        {
            unsound.push(format!("NEGATIVE CONTROL VIOLATED: proved upper < {n}"));
        }
        if let Some(n) = want.lower_not_above
            && b.lower > n
        {
            unsound.push(format!("NEGATIVE CONTROL VIOLATED: proved lower > {n}"));
        }
        if let Some(u) = want.upper
            && b.upper.is_none_or(|x| x > u)
        {
            problems.push(format!("spec upper {u}"));
        }
        if let Some(l) = want.lower
            && b.lower < l
        {
            problems.push(format!("spec lower {l}"));
        }
        let status = if !unsound.is_empty() {
            "UNSOUND"
        } else if !problems.is_empty() {
            "FAIL"
        } else {
            "ok"
        };
        println!(
            "{status:<7} {label}: bound {} truth {truth} ({:.1}s, {} checks){}{}",
            show(&b),
            b.time.as_secs_f64(),
            b.checks,
            if problems.is_empty() {
                String::new()
            } else {
                format!(" -- wanted {}", problems.join(", "))
            },
            if unsound.is_empty() {
                String::new()
            } else {
                format!(" -- {}", unsound.join(", "))
            },
        );
        if !b.dropped.is_empty() {
            println!("        dropped as contradictory: {:?}", b.dropped);
        }
        if std::env::var("UF_SPEC_TERMS").is_ok() {
            println!("        term {}", enc.target_term(plan));
        }
        let line = format!(
            "{label}: bound {} truth {truth}: {}",
            show(&b),
            [problems, unsound.clone()].concat().join(", ")
        );
        if !unsound.is_empty() {
            self.unsound.push(line);
        } else if status == "FAIL" {
            self.failures.push(line);
        }
    }

    fn finish(self) {
        assert!(
            self.unsound.is_empty() && self.failures.is_empty(),
            "unsound: {:#?}\nfailed: {:#?}",
            self.unsound,
            self.failures
        );
    }
}

// ---------------------------------------------------------------- §10.1

/// `R ⊆ Q`: a filter above an observed query's is at most its count.
#[tokio::test]
async fn s10_1_r_in_q() {
    let ex = Ex::new(
        "10_1",
        &["CREATE TABLE foo (a INTEGER NOT NULL, b INTEGER NOT NULL)"],
        // 300 rows with a > 1, all with b > 2.
        &[
            "INSERT INTO foo SELECT CASE WHEN i < 300 THEN 2 + i % 5 ELSE i % 2 END, \
           CASE WHEN i < 300 THEN 3 + i % 4 ELSE i % 5 END FROM range(1000) t(i)",
        ],
    )
    .await;
    let mut enc = ex.encoder();
    assert_eq!(
        ex.observe(&mut enc, "SELECT a, b FROM foo WHERE a > 1"),
        300
    );
    let mut r = Report::default();
    r.probe(
        &ex,
        &enc,
        "10.1 |R| <= 300",
        "SELECT a, b FROM foo WHERE a > 1 AND b > 2",
        true,
        at_most(300),
    )
    .await;
    r.probe(
        &ex,
        &enc,
        "10.1 |R| <= 300 (unoptimized)",
        "SELECT a, b FROM foo WHERE a > 1 AND b > 2",
        false,
        at_most(300),
    )
    .await;
    r.finish();
}

// ---------------------------------------------------------------- §10.2

const FOO_BAR_10_2: &[&str] = &[
    "CREATE TABLE foo (a INTEGER NOT NULL, k INTEGER NOT NULL)",
    "CREATE TABLE bar (k INTEGER NOT NULL PRIMARY KEY, c INTEGER NOT NULL)",
];

/// `bar`: 50 keys, 10 with `c > 0`. `foo`: 1000 rows with `a → k`; 300
/// with `a > 1`, over 12 values of `a`, of which 6 (150 rows) have a `k`
/// with `c > 0`.
const DATA_10_2: &[&str] = &[
    "INSERT INTO bar SELECT i, CASE WHEN i < 10 THEN 1 ELSE 0 END FROM range(50) t(i)",
    "INSERT INTO foo SELECT a, CASE WHEN a <= 1 THEN 40 + a WHEN a <= 7 THEN a - 2 ELSE 20 + a END \
     FROM (SELECT CASE WHEN i < 300 THEN 2 + i % 12 ELSE i % 2 END AS a FROM range(1000) t(i))",
];

async fn observe_10_2(ex: &Ex, enc: &mut Encoder<'_>) {
    assert_eq!(ex.observe(enc, "SELECT * FROM foo"), 1000);
    assert_eq!(ex.observe(enc, "SELECT * FROM bar"), 50);
    assert_eq!(ex.observe(enc, "SELECT * FROM foo WHERE a > 1"), 300);
    assert_eq!(ex.observe(enc, "SELECT * FROM bar WHERE c > 0"), 10);
    assert_eq!(
        ex.observe(
            enc,
            "SELECT * FROM foo JOIN bar ON foo.k = bar.k WHERE bar.c > 0"
        ),
        150
    );
    assert_eq!(
        ex.observe(enc, "SELECT a FROM foo WHERE a > 1 GROUP BY a"),
        12
    );
}

/// Facts from other queries, and (where the schema can say so) an FD chain.
#[tokio::test]
async fn s10_2_facts_and_fds() {
    let ex = Ex::new("10_2", FOO_BAR_10_2, DATA_10_2).await;
    let mut enc = ex.encoder();
    observe_10_2(&ex, &mut enc).await;
    let j = "SELECT * FROM foo JOIN bar ON foo.k = bar.k WHERE foo.a > 1 AND bar.c > 0";
    let mut r = Report::default();
    r.probe(&ex, &enc, "10.2 |J| <= 150", j, true, at_most(150))
        .await;
    // The spec's shape: an equi-join on `k`, the filters above it.
    // `inner_push` makes it the same term as `J`.
    let above = ex
        .ctx
        .table("foo")
        .await
        .unwrap()
        .join(
            ex.ctx.table("bar").await.unwrap(),
            JoinType::Inner,
            &["k"],
            &["k"],
            None,
        )
        .unwrap()
        .filter(col("foo.a").gt(lit(1)).and(col("bar.c").gt(lit(0))))
        .unwrap()
        .into_unoptimized_plan();
    r.probe_plan(
        &ex,
        &enc,
        "10.2 |J| <= 150, filters above the join",
        j,
        &above,
        at_most(150),
    );
    // DataFusion's unoptimized plan of the SQL: the filters above the
    // join, and the join's `ON` as a join filter, not keys.
    r.probe(
        &ex,
        &enc,
        "10.2 |J| <= 150, unoptimized (ON as a join filter)",
        j,
        false,
        at_most(150),
    )
    .await;
    r.probe(
        &ex,
        &enc,
        "10.2 |GROUP BY a| <= 12",
        "SELECT foo.a FROM foo JOIN bar ON foo.k = bar.k WHERE foo.a > 1 AND bar.c > 0 GROUP BY foo.a",
        true,
        at_most(12),
    )
    .await;
    // The spec's 12 needs the FD `a → k`, which the encoder's schema
    // (keys, foreign keys, NOT NULL) cannot state. Without it, the spec's
    // ablation row: `ndv_product`, 12 · 10.
    r.probe(
        &ex,
        &enc,
        "10.2 |GROUP BY a, c| <= 120 (no FD input)",
        "SELECT foo.a, bar.c FROM foo JOIN bar ON foo.k = bar.k WHERE foo.a > 1 AND bar.c > 0 GROUP BY foo.a, bar.c",
        true,
        at_most(120),
    )
    .await;
    r.finish();
}

// ---------------------------------------------------------------- §10.3

/// Five axioms combine into a lower bound no rule spelled out.
#[tokio::test]
async fn s10_3_left_join_lower() {
    let ex = Ex::new(
        "10_3",
        &[
            "CREATE TABLE cust (id INTEGER NOT NULL PRIMARY KEY, seg INTEGER NOT NULL)",
            "CREATE TABLE ord (id INTEGER NOT NULL PRIMARY KEY, cust INTEGER NOT NULL)",
        ],
        &[
            "INSERT INTO cust SELECT i, CASE WHEN i < 30 THEN 1 ELSE 0 END FROM range(100) t(i)",
            // 280 orders of the 30 seg=1 customers, 40 of 40 others.
            "INSERT INTO ord SELECT i, CASE WHEN i < 280 THEN i % 30 ELSE i - 250 END FROM range(320) t(i)",
        ],
    )
    .await;
    let mut enc = ex.encoder();
    assert_eq!(ex.observe(&mut enc, "SELECT * FROM cust"), 100);
    assert_eq!(ex.observe(&mut enc, "SELECT * FROM cust WHERE seg = 1"), 30);
    assert_eq!(
        ex.observe(
            &mut enc,
            "SELECT * FROM ord JOIN cust ON ord.cust = cust.id WHERE cust.seg = 1"
        ),
        280
    );
    assert_eq!(
        ex.observe(&mut enc, "SELECT cust FROM ord GROUP BY cust"),
        70
    );
    let mut r = Report::default();
    let lj = "SELECT * FROM cust LEFT JOIN ord ON cust.id = ord.cust";
    r.probe(
        &ex,
        &enc,
        "10.3 |cust LEFT JOIN ord| >= 350",
        lj,
        true,
        at_least(350),
    )
    .await;
    // The derivation splits the left join by `seg = 1`, which needs the
    // term `σ seg=1 (cust ⟕ ord)`: nothing creates it from the probe
    // (the prototype's case had it from another probe in the same
    // program). With the split written out, the rest of the derivation:
    let split = "SELECT * FROM cust LEFT JOIN ord ON cust.id = ord.cust WHERE cust.seg = 1 \
                 UNION ALL SELECT * FROM cust LEFT JOIN ord ON cust.id = ord.cust WHERE cust.seg <> 1";
    r.probe(
        &ex,
        &enc,
        "10.3 split by hand: σ seg=1 (cust ⟕ ord) ∪ σ seg<>1 (cust ⟕ ord) >= 350",
        split,
        true,
        at_least(350),
    )
    .await;
    r.finish();
}

// ---------------------------------------------------------------- §10.4

/// A foreign key pins an anti join (TPC-H's customer and orders, shaped).
#[tokio::test]
async fn s10_4_fk_pins_anti_join() {
    let ex = Ex::new(
        "10_4",
        &[
            "CREATE TABLE customer (c_custkey INTEGER NOT NULL PRIMARY KEY, c_name VARCHAR NOT NULL)",
            "CREATE TABLE orders (o_orderkey INTEGER NOT NULL PRIMARY KEY, o_custkey INTEGER NOT NULL)",
        ],
        &[
            "INSERT INTO customer SELECT i, 'c' || i FROM range(1500) t(i)",
            "INSERT INTO orders SELECT i, (i % 1000) * 3 // 2 FROM range(15000) t(i)",
        ],
    )
    .await
    .fk("orders", "o_custkey", "customer", "c_custkey");
    let mut enc = ex.encoder();
    assert_eq!(ex.observe(&mut enc, "SELECT * FROM customer"), 1500);
    assert_eq!(ex.observe(&mut enc, "SELECT * FROM orders"), 15000);
    assert_eq!(
        ex.observe(&mut enc, "SELECT o_custkey FROM orders GROUP BY o_custkey"),
        1000
    );
    let mut r = Report::default();
    r.probe(
        &ex,
        &enc,
        "10.4 |customer anti orders| = 500",
        "SELECT * FROM customer WHERE NOT EXISTS (SELECT 1 FROM orders WHERE o_custkey = c_custkey)",
        true,
        exactly(500),
    )
    .await;
    r.finish();
}

// ---------------------------------------------------------------- §10.5

const FOO_A: &[&str] = &["CREATE TABLE foo (a INTEGER NOT NULL)"];

/// Value ranges: a filter's range, and an integer column's width.
#[tokio::test]
async fn s10_5_value_ranges() {
    // `a` in 0..=3.
    let ex = Ex::new(
        "10_5",
        FOO_A,
        &["INSERT INTO foo SELECT i % 4 FROM range(100) t(i)"],
    )
    .await;
    let mut r = Report::default();
    {
        // `max(foo, {a}) = 3` is not a fact the encoder takes. It follows
        // from counts: `σ a<=3 foo` keeps every row, so by `sub_eq` it is
        // `foo`, and its literal's range bounds `max(foo, {a})`. (DuckDB
        // would drop that filter by its statistics, unless told not to.)
        let mut enc = ex.encoder();
        assert_eq!(ex.observe(&mut enc, "SELECT * FROM foo"), 100);
        let keep = "SET disabled_optimizers = 'statistics_propagation';";
        assert_eq!(
            ex.observe_with(&mut enc, "SELECT * FROM foo WHERE a <= 3", keep),
            100
        );
        r.probe(
            &ex,
            &enc,
            "10.5 |σ a>=5 foo| = 0",
            "SELECT * FROM foo WHERE a >= 5",
            true,
            exactly(0),
        )
        .await;
    }
    {
        let enc = ex.encoder();
        r.probe(
            &ex,
            &enc,
            "10.5 ndv(σ a<5 σ a>1 foo, a) <= 3",
            "SELECT DISTINCT a FROM foo WHERE a > 1 AND a < 5",
            true,
            at_most(3),
        )
        .await;
    }
    r.finish();
}

// ---------------------------------------------------------------- §10.6

/// Negative controls: none of these may be proven. Each example's data
/// makes the forbidden bound false, so proving it would also exclude the
/// truth.
#[tokio::test]
async fn s10_6_negative_controls() {
    let mut r = Report::default();
    let not_below = |n| Want {
        upper_not_below: Some(n),
        ..Default::default()
    };

    // |σ a>1 foo| <= 299 when 300 is observed.
    {
        let ex = Ex::new(
            "10_6a",
            &["CREATE TABLE foo (a INTEGER NOT NULL, b INTEGER NOT NULL)"],
            &["INSERT INTO foo SELECT CASE WHEN i < 300 THEN 2 + i % 5 ELSE i % 2 END, i % 5 FROM range(1000) t(i)"],
        )
        .await;
        let mut enc = ex.encoder();
        assert_eq!(
            ex.observe(&mut enc, "SELECT a, b FROM foo WHERE a > 1"),
            300
        );
        let w = Want {
            lower: Some(300),
            upper: Some(300),
            ..not_below(300)
        };
        r.probe(
            &ex,
            &enc,
            "10.6 |σ a>1 foo| not <= 299",
            "SELECT * FROM foo WHERE a > 1",
            true,
            w,
        )
        .await;
    }

    // |(ord ∪ ord) ⋈ cust| <= 1999, true value 2000 (rule 3).
    {
        let ex = Ex::new(
            "10_6b",
            &[
                "CREATE TABLE cust (id INTEGER NOT NULL PRIMARY KEY, seg INTEGER NOT NULL)",
                "CREATE TABLE ord (id INTEGER NOT NULL PRIMARY KEY, cust INTEGER NOT NULL)",
            ],
            &[
                "INSERT INTO cust SELECT i, i % 3 FROM range(100) t(i)",
                "INSERT INTO ord SELECT i, i % 100 FROM range(1000) t(i)",
            ],
        )
        .await
        .fk("ord", "cust", "cust", "id");
        let mut enc = ex.encoder();
        assert_eq!(ex.observe(&mut enc, "SELECT * FROM ord"), 1000);
        assert_eq!(ex.observe(&mut enc, "SELECT * FROM cust"), 100);
        let sql = "SELECT * FROM (SELECT * FROM ord UNION ALL SELECT * FROM ord) u JOIN cust ON u.cust = cust.id";
        r.probe(
            &ex,
            &enc,
            "10.6 |(ord ∪ ord) ⋈ cust| not <= 1999",
            sql,
            true,
            not_below(2000),
        )
        .await;
    }

    // |σ a IN (1,2) foo| <= 64 when |σ a=1| = 40 and |σ a=2| = 25.
    {
        let ex = Ex::new("10_6c", FOO_A, &[DATA_10_8]).await;
        let mut enc = ex.encoder();
        assert_eq!(ex.observe(&mut enc, "SELECT * FROM foo WHERE a = 1"), 40);
        assert_eq!(ex.observe(&mut enc, "SELECT * FROM foo WHERE a = 2"), 25);
        r.probe(
            &ex,
            &enc,
            "10.6 |σ a IN (1,2) foo| not <= 64",
            "SELECT * FROM foo WHERE a IN (1, 2)",
            true,
            not_below(65),
        )
        .await;
    }

    // |scalar count(*) (σ a>1 foo)| <= 0 when |σ a>1 foo| = 0.
    {
        let ex = Ex::new(
            "10_6d",
            FOO_A,
            &["INSERT INTO foo SELECT i % 2 FROM range(100) t(i)"],
        )
        .await;
        let mut enc = ex.encoder();
        assert_eq!(ex.observe(&mut enc, "SELECT * FROM foo WHERE a > 1"), 0);
        let w = Want {
            lower: Some(1),
            upper: Some(1),
            ..not_below(1)
        };
        r.probe(
            &ex,
            &enc,
            "10.6 |SELECT count(*) .. WHERE a>1| not <= 0",
            "SELECT count(*) FROM foo WHERE a > 1",
            true,
            w,
        )
        .await;
    }

    // |GROUP BY a % 3| <= 3 with nothing known about a's sign.
    {
        let ex = Ex::new(
            "10_6e",
            FOO_A,
            &["INSERT INTO foo SELECT i - 5 FROM range(11) t(i)"],
        )
        .await;
        let mut enc = ex.encoder();
        ex.observe(&mut enc, "SELECT * FROM foo");
        r.probe(
            &ex,
            &enc,
            "10.6 |GROUP BY a % 3| not <= 3",
            "SELECT a % 3 FROM foo GROUP BY a % 3",
            true,
            not_below(4),
        )
        .await;
    }

    // |σ b>1 OR b<=1 (foo ⟕ bar)| >= |foo ⟕ bar|: NULL rows fail both.
    {
        let ex = Ex::new(
            "10_6f",
            &[
                "CREATE TABLE foo (k INTEGER NOT NULL)",
                "CREATE TABLE bar (k INTEGER NOT NULL PRIMARY KEY, b INTEGER NOT NULL)",
            ],
            &[
                "INSERT INTO foo SELECT i FROM range(100) t(i)",
                "INSERT INTO bar SELECT i, i % 5 FROM range(50) t(i)",
            ],
        )
        .await;
        let mut enc = ex.encoder();
        let lj = ex.observe(&mut enc, "SELECT * FROM foo LEFT JOIN bar ON foo.k = bar.k");
        assert_eq!(lj, 100);
        let sql = "SELECT * FROM foo LEFT JOIN bar ON foo.k = bar.k WHERE bar.b > 1 OR bar.b <= 1";
        let w = Want {
            lower_not_above: Some(lj - 1),
            ..Default::default()
        };
        r.probe(
            &ex,
            &enc,
            "10.6 |σ b>1 OR b<=1 (foo ⟕ bar)| not >= |foo ⟕ bar|",
            sql,
            true,
            w,
        )
        .await;
        r.probe(
            &ex,
            &enc,
            "10.6 |σ b>1 OR b<=1 (foo ⟕ bar)| not >= |foo ⟕ bar| (unoptimized)",
            sql,
            false,
            w,
        )
        .await;
    }
    r.finish();
}

// ---------------------------------------------------------------- §10.7

/// Value domains of expressions, from their types alone.
#[tokio::test]
async fn s10_7_value_domains() {
    let ex = Ex::new(
        "10_7",
        &[
            "CREATE TABLE foo (a INTEGER NOT NULL)",
            "CREATE TABLE t (g INTEGER NOT NULL)",
        ],
        &[
            "INSERT INTO foo SELECT i - 50 FROM range(100) t(i)",
            "INSERT INTO t SELECT i % 3 FROM range(90) t(i)",
        ],
    )
    .await;
    let enc = ex.encoder();
    let mut r = Report::default();
    r.probe(
        &ex,
        &enc,
        "10.7 |σ a%3>2 foo| = 0",
        "SELECT * FROM foo WHERE a % 3 > 2",
        true,
        exactly(0),
    )
    .await;
    let sub = "SELECT * FROM (SELECT a % 3 AS g FROM foo) s WHERE g > 2";
    r.probe(
        &ex,
        &enc,
        "10.7 |σ g>2 (SELECT a%3 AS g FROM foo)| = 0",
        sub,
        true,
        exactly(0),
    )
    .await;
    r.probe(
        &ex,
        &enc,
        "10.7 |σ g>2 (SELECT a%3 AS g FROM foo)| = 0 (unoptimized)",
        sub,
        false,
        exactly(0),
    )
    .await;
    r.probe(
        &ex,
        &enc,
        "10.7 |GROUP BY a % 3| <= 5",
        "SELECT a % 3 FROM foo GROUP BY a % 3",
        true,
        at_most(5),
    )
    .await;
    // `|σ g>2 t| = 0` and `ndv(t, {g}) <= 3` need `t.g`'s domain, from a
    // CHECK constraint or storage statistics: neither is an input the
    // encoder takes (`Encoder::new` reads keys, foreign keys and NOT NULL).
    r.finish();
}

// ---------------------------------------------------------------- §10.8

/// 1000 rows: 40 with a = 1, 25 with a = 2, the rest in 6..=9.
const DATA_10_8: &str = "INSERT INTO foo SELECT CASE WHEN i < 40 THEN 1 WHEN i < 65 THEN 2 ELSE 6 + i % 4 END FROM range(1000) t(i)";

#[tokio::test]
async fn s10_8_or_and_in() {
    let ex = Ex::new("10_8", FOO_A, &[DATA_10_8]).await;
    let mut enc = ex.encoder();
    assert_eq!(ex.observe(&mut enc, "SELECT * FROM foo"), 1000);
    assert_eq!(ex.observe(&mut enc, "SELECT * FROM foo WHERE a = 1"), 40);
    assert_eq!(ex.observe(&mut enc, "SELECT * FROM foo WHERE a = 2"), 25);
    let mut r = Report::default();
    r.probe(
        &ex,
        &enc,
        "10.8 |σ a IN (1,2) foo| = 65",
        "SELECT * FROM foo WHERE a IN (1, 2)",
        true,
        exactly(65),
    )
    .await;
    r.probe(
        &ex,
        &enc,
        "10.8 |σ a NOT IN (1,2) foo| = 935",
        "SELECT * FROM foo WHERE a NOT IN (1, 2)",
        true,
        exactly(935),
    )
    .await;
    r.probe(
        &ex,
        &enc,
        "10.8 ndv(σ a IN (1,2) foo, a) <= 2",
        "SELECT DISTINCT a FROM foo WHERE a IN (1, 2)",
        true,
        at_most(2),
    )
    .await;
    r.probe(
        &ex,
        &enc,
        "10.8 |σ a IN (1,2) σ a>5 foo| = 0",
        "SELECT * FROM foo WHERE a IN (1, 2) AND a > 5",
        true,
        exactly(0),
    )
    .await;
    r.finish();
}

// ---------------------------------------------------------------- §10.9

#[tokio::test]
async fn s10_9_having() {
    let ex = Ex::new(
        "10_9",
        &["CREATE TABLE foo (k INTEGER NOT NULL, v INTEGER NOT NULL)"],
        &["INSERT INTO foo SELECT i % 40, i FROM range(1000) t(i)"],
    )
    .await;
    let having = "SELECT k, count(*) FROM foo GROUP BY k HAVING count(*) > 9";
    let mut r = Report::default();
    {
        let mut enc = ex.encoder();
        assert_eq!(ex.observe(&mut enc, "SELECT * FROM foo"), 1000);
        r.probe(
            &ex,
            &enc,
            "10.9 HAVING count(*) > 9 <= 100",
            having,
            true,
            at_most(100),
        )
        .await;
        r.probe(
            &ex,
            &enc,
            "10.9 HAVING count(*) > 1000 = 0",
            "SELECT k, count(*) FROM foo GROUP BY k HAVING count(*) > 1000",
            true,
            exactly(0),
        )
        .await;
        assert_eq!(ex.observe(&mut enc, "SELECT k FROM foo GROUP BY k"), 40);
        r.probe(
            &ex,
            &enc,
            "10.9 HAVING count(*) > 9 <= 40, ndv(foo, k) = 40",
            having,
            true,
            at_most(40),
        )
        .await;
    }
    r.finish();
}

// ---------------------------------------------------------------- §10.10

#[tokio::test]
async fn s10_10_self_join() {
    let ddl = &["CREATE TABLE emp (id INTEGER NOT NULL PRIMARY KEY, mgr INTEGER NOT NULL)"];
    let data = &["INSERT INTO emp SELECT i, i // 2 FROM range(500) t(i)"];
    let sql = "SELECT * FROM emp e JOIN emp m ON e.mgr = m.id";
    let mut r = Report::default();
    {
        let ex = Ex::new("10_10", ddl, data)
            .await
            .fk("emp", "mgr", "emp", "id");
        let mut enc = ex.encoder();
        assert_eq!(ex.observe(&mut enc, "SELECT * FROM emp"), 500);
        r.probe(
            &ex,
            &enc,
            "10.10 |emp ⋈ emp#2| = 500 (FK)",
            sql,
            true,
            exactly(500),
        )
        .await;
    }
    {
        let ex = Ex::new("10_10n", ddl, data).await;
        let mut enc = ex.encoder();
        assert_eq!(ex.observe(&mut enc, "SELECT * FROM emp"), 500);
        r.probe(
            &ex,
            &enc,
            "10.10 |emp ⋈ emp#2| <= 500 (no FK)",
            sql,
            true,
            at_most(500),
        )
        .await;
    }
    r.finish();
}

// ---------------------------------------------------------------- §10.11

#[tokio::test]
async fn s10_11_scalar_subqueries() {
    let ex = Ex::new(
        "10_11",
        FOO_A,
        &["INSERT INTO foo SELECT i % 17 FROM range(100) t(i)"],
    )
    .await;
    let enc = ex.encoder();
    let mut r = Report::default();
    r.probe(
        &ex,
        &enc,
        "10.11 |σ a > (max a) foo| = 0",
        "SELECT * FROM foo WHERE a > (SELECT max(a) FROM foo)",
        true,
        exactly(0),
    )
    .await;
    r.probe(
        &ex,
        &enc,
        "10.11 ndv(σ a = (max a) foo, a) <= 1",
        "SELECT DISTINCT a FROM foo WHERE a = (SELECT max(a) FROM foo)",
        true,
        at_most(1),
    )
    .await;
    r.finish();
}
