//! Shared harness: schemas, deterministic data generation and the benchmark
//! runner that checks each query's verdict and validates it on real data.

#![allow(dead_code)]

use std::sync::Arc;

use cardinal::{Analysis, Bounds, Options, Validation, Verdict, analyze_sql_with};
use datafusion::arrow::array::{ArrayRef, Date32Array, Float64Array, Int64Array, StringArray};
use datafusion::arrow::datatypes::{DataType, Field, Schema};
use datafusion::arrow::record_batch::RecordBatch;
use datafusion::common::{Constraint, Constraints};
use datafusion::datasource::MemTable;
use datafusion::prelude::SessionContext;

/// xorshift64*: small, deterministic, dependency-free.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)
    }
    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    /// Uniform in `0..n`.
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
    /// Uniform in `lo..=hi`.
    pub fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + self.below((hi - lo + 1) as u64) as i64
    }
    pub fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }
    pub fn pick<'a>(&mut self, xs: &[&'a str]) -> &'a str {
        xs[self.below(xs.len() as u64) as usize]
    }
}

/// A column of generated values.
pub enum Col {
    I(Vec<Option<i64>>),
    F(Vec<Option<f64>>),
    S(Vec<Option<String>>),
    D(Vec<Option<i32>>),
}

impl Col {
    fn data_type(&self) -> DataType {
        match self {
            Col::I(_) => DataType::Int64,
            Col::F(_) => DataType::Float64,
            Col::S(_) => DataType::Utf8,
            Col::D(_) => DataType::Date32,
        }
    }
    fn array(self) -> ArrayRef {
        match self {
            Col::I(v) => Arc::new(Int64Array::from(v)),
            Col::F(v) => Arc::new(Float64Array::from(v)),
            Col::S(v) => Arc::new(StringArray::from(v)),
            Col::D(v) => Arc::new(Date32Array::from(v)),
        }
    }
    fn len(&self) -> usize {
        match self {
            Col::I(v) => v.len(),
            Col::F(v) => v.len(),
            Col::S(v) => v.len(),
            Col::D(v) => v.len(),
        }
    }
}

pub struct Table {
    pub name: &'static str,
    pub cols: Vec<(&'static str, Col)>,
    /// Primary key columns, declared when a context is built with keys.
    pub key: &'static [&'static str],
}

pub struct Dataset {
    pub name: String,
    pub tables: Vec<Table>,
    /// Whether every table's primary key really is unique in this data, so that
    /// declaring it tells the truth.
    pub unique_keys: bool,
}

impl Dataset {
    /// A session with every table registered as an in-memory table, with its
    /// primary key declared if `declare_keys`.
    pub fn context(self, declare_keys: bool) -> SessionContext {
        let ctx = SessionContext::new();
        for t in self.tables {
            let rows = t.cols.first().map_or(0, |(_, c)| c.len());
            let schema = Arc::new(Schema::new(
                t.cols
                    .iter()
                    .map(|(n, c)| Field::new(*n, c.data_type(), true))
                    .collect::<Vec<_>>(),
            ));
            let partitions = if rows == 0 {
                vec![vec![]]
            } else {
                let arrays = t.cols.into_iter().map(|(_, c)| c.array()).collect();
                vec![vec![RecordBatch::try_new(schema.clone(), arrays).unwrap()]]
            };
            let mut mem = MemTable::try_new(schema.clone(), partitions).unwrap();
            if declare_keys && !t.key.is_empty() {
                let key = t.key.iter().map(|c| schema.index_of(c).unwrap()).collect();
                mem = mem.with_constraints(Constraints::new_unverified(vec![
                    Constraint::PrimaryKey(key),
                ]));
            }
            ctx.register_table(t.name, Arc::new(mem)).unwrap();
        }
        ctx
    }
}

// ---------------------------------------------------------------------------
// Shop schema: users, orders, products, order_items.

/// Knobs for shop data. `key_domain = None` gives unique primary keys and valid
/// foreign keys; `Some(k)` draws every key from `0..k`, producing duplicate
/// "primary" keys and many-to-many joins.
pub struct ShopShape {
    pub users: usize,
    pub orders: usize,
    pub products: usize,
    pub items: usize,
    pub key_domain: Option<u64>,
    pub age_domain: u64,
    pub null_percent: u64,
}

pub fn shop(name: &str, seed: u64, s: ShopShape) -> Dataset {
    let mut r = Rng::new(seed);
    let key = |r: &mut Rng, i: usize| match s.key_domain {
        None => i as i64,
        Some(k) => r.below(k) as i64,
    };
    let fk = |r: &mut Rng, n: usize| -> Option<i64> {
        if r.chance(s.null_percent) {
            return None;
        }
        Some(match s.key_domain {
            None => r.below(n as u64) as i64,
            Some(k) => r.below(k) as i64,
        })
    };
    let mut users = (vec![], vec![], vec![]);
    for i in 0..s.users {
        users.0.push(Some(key(&mut r, i)));
        users.1.push(Some(format!("u{}", r.below(4))));
        users
            .2
            .push((!r.chance(s.null_percent)).then(|| 18 + r.below(s.age_domain) as i64));
    }
    let mut orders = (vec![], vec![], vec![]);
    for i in 0..s.orders {
        orders.0.push(Some(key(&mut r, i)));
        orders.1.push(fk(&mut r, s.users));
        // Skewed data also stresses float equality: -0.0 and 0.0 are equal in
        // SQL but distinct as bits, and NaN is its own value.
        orders
            .2
            .push(Some(if s.key_domain.is_some() && s.null_percent > 0 {
                [-0.0, 0.0, f64::NAN, 1.5, 2.5][r.below(5) as usize]
            } else {
                r.below(200) as f64
            }));
    }
    let mut products = (vec![], vec![]);
    for i in 0..s.products {
        products.0.push(Some(key(&mut r, i)));
        products.1.push(Some(1.0 + r.below(100) as f64));
    }
    let mut items = (vec![], vec![], vec![]);
    for _ in 0..s.items {
        items.0.push(fk(&mut r, s.orders));
        items.1.push(fk(&mut r, s.products));
        items.2.push(Some(1 + r.below(5) as i64));
    }
    Dataset {
        name: name.to_string(),
        unique_keys: s.key_domain.is_none() || s.users.max(s.orders).max(s.products) <= 1,
        tables: vec![
            Table {
                name: "users",
                cols: vec![
                    ("id", Col::I(users.0)),
                    ("name", Col::S(users.1)),
                    ("age", Col::I(users.2)),
                ],
                key: &["id"],
            },
            Table {
                name: "orders",
                cols: vec![
                    ("id", Col::I(orders.0)),
                    ("user_id", Col::I(orders.1)),
                    ("amount", Col::F(orders.2)),
                ],
                key: &["id"],
            },
            Table {
                name: "products",
                cols: vec![("id", Col::I(products.0)), ("price", Col::F(products.1))],
                key: &["id"],
            },
            Table {
                name: "order_items",
                cols: vec![
                    ("order_id", Col::I(items.0)),
                    ("product_id", Col::I(items.1)),
                    ("qty", Col::I(items.2)),
                ],
                key: &[],
            },
        ],
    }
}

/// Empty tables, single rows, three PK/FK-consistent datasets and three skewed
/// datasets with duplicate keys and NULLs.
pub fn shop_datasets() -> Vec<Dataset> {
    let mut out = vec![
        shop(
            "empty",
            0,
            ShopShape {
                users: 0,
                orders: 0,
                products: 0,
                items: 0,
                key_domain: None,
                age_domain: 1,
                null_percent: 0,
            },
        ),
        shop(
            "single",
            0,
            ShopShape {
                users: 1,
                orders: 1,
                products: 1,
                items: 1,
                key_domain: Some(1),
                age_domain: 1,
                null_percent: 0,
            },
        ),
    ];
    for seed in 1..=3 {
        out.push(shop(
            &format!("keyed{seed}"),
            seed,
            ShopShape {
                users: 8,
                orders: 15,
                products: 6,
                items: 25,
                key_domain: None,
                age_domain: 50,
                null_percent: 0,
            },
        ));
    }
    for seed in 1..=3 {
        out.push(shop(
            &format!("skewed{seed}"),
            seed,
            ShopShape {
                users: 10,
                orders: 12,
                products: 5,
                items: 15,
                key_domain: Some(3),
                age_domain: 2,
                null_percent: 10,
            },
        ));
    }
    out
}

// ---------------------------------------------------------------------------
// TPC-H schema with small, PK/FK-consistent data drawn from TPC-H vocabularies
// so that the queries' filters select some rows.

const REGIONS: [&str; 5] = ["AFRICA", "AMERICA", "ASIA", "EUROPE", "MIDDLE EAST"];
const NATIONS: [(&str, i64); 25] = [
    ("ALGERIA", 0),
    ("ARGENTINA", 1),
    ("BRAZIL", 1),
    ("CANADA", 1),
    ("EGYPT", 4),
    ("ETHIOPIA", 0),
    ("FRANCE", 3),
    ("GERMANY", 3),
    ("INDIA", 2),
    ("INDONESIA", 2),
    ("IRAN", 4),
    ("IRAQ", 4),
    ("JAPAN", 2),
    ("JORDAN", 4),
    ("KENYA", 0),
    ("MOROCCO", 0),
    ("MOZAMBIQUE", 0),
    ("PERU", 1),
    ("CHINA", 2),
    ("ROMANIA", 3),
    ("SAUDI ARABIA", 4),
    ("VIETNAM", 2),
    ("RUSSIA", 3),
    ("UNITED KINGDOM", 3),
    ("UNITED STATES", 1),
];
const COLORS: [&str; 8] = [
    "green", "forest", "blue", "red", "almond", "khaki", "navy", "linen",
];
const TYPE1: [&str; 6] = ["STANDARD", "SMALL", "MEDIUM", "LARGE", "ECONOMY", "PROMO"];
const TYPE2: [&str; 5] = ["ANODIZED", "BURNISHED", "PLATED", "POLISHED", "BRUSHED"];
const TYPE3: [&str; 5] = ["TIN", "NICKEL", "BRASS", "STEEL", "COPPER"];
const CONT1: [&str; 5] = ["SM", "MED", "LG", "JUMBO", "WRAP"];
const CONT2: [&str; 8] = ["CASE", "BOX", "BAG", "JAR", "PKG", "PACK", "CAN", "DRUM"];
const SIZES: [i64; 10] = [1, 3, 9, 14, 15, 19, 23, 36, 45, 49];
const SEGMENTS: [&str; 5] = [
    "AUTOMOBILE",
    "BUILDING",
    "FURNITURE",
    "HOUSEHOLD",
    "MACHINERY",
];
const PRIORITIES: [&str; 5] = ["1-URGENT", "2-HIGH", "3-MEDIUM", "4-NOT SPECIFIED", "5-LOW"];
const INSTRUCT: [&str; 4] = [
    "DELIVER IN PERSON",
    "COLLECT COD",
    "NONE",
    "TAKE BACK RETURN",
];
const MODES: [&str; 7] = ["REG AIR", "AIR", "RAIL", "SHIP", "TRUCK", "MAIL", "FOB"];

/// Days since 1970-01-01 for 1992-01-01 and 1998-08-02.
const START_DATE: i64 = 8035;
const END_DATE: i64 = 10440;

pub struct TpchShape {
    pub suppliers: usize,
    pub parts: usize,
    pub customers: usize,
    pub orders: usize,
}

fn s(v: impl Into<String>) -> Option<String> {
    Some(v.into())
}

pub fn tpch(name: &str, seed: u64, sh: TpchShape) -> Dataset {
    let mut r = Rng::new(seed);
    let empty = sh.orders == 0;

    let region = Table {
        name: "region",
        cols: vec![
            (
                "r_regionkey",
                Col::I((0..5).filter(|_| !empty).map(Some).collect()),
            ),
            (
                "r_name",
                Col::S(REGIONS.iter().filter(|_| !empty).map(|n| s(*n)).collect()),
            ),
            (
                "r_comment",
                Col::S((0..5).filter(|_| !empty).map(|_| s("c")).collect()),
            ),
        ],
        key: &["r_regionkey"],
    };
    let nation = Table {
        name: "nation",
        cols: vec![
            (
                "n_nationkey",
                Col::I((0..25).filter(|_| !empty).map(Some).collect()),
            ),
            (
                "n_name",
                Col::S(NATIONS.iter().filter(|_| !empty).map(|n| s(n.0)).collect()),
            ),
            (
                "n_regionkey",
                Col::I(
                    NATIONS
                        .iter()
                        .filter(|_| !empty)
                        .map(|n| Some(n.1))
                        .collect(),
                ),
            ),
            (
                "n_comment",
                Col::S((0..25).filter(|_| !empty).map(|_| s("c")).collect()),
            ),
        ],
        key: &["n_nationkey"],
    };

    let phone = |r: &mut Rng, nation: i64| {
        format!("{}-{:03}-{:04}", nation + 10, r.below(1000), r.below(10000))
    };

    let mut sup: [Vec<Option<String>>; 4] = Default::default();
    let (mut s_key, mut s_nat, mut s_bal) = (vec![], vec![], vec![]);
    for i in 1..=sh.suppliers {
        let nat = r.below(25) as i64;
        s_key.push(Some(i as i64));
        sup[0].push(s(format!("Supplier#{i:09}")));
        sup[1].push(s(format!("addr{i}")));
        s_nat.push(Some(nat));
        sup[2].push(s(phone(&mut r, nat)));
        s_bal.push(Some(r.range(-999, 9999) as f64));
        sup[3].push(s(if r.chance(20) {
            "wake Customer carefully Complaints"
        } else {
            "quickly regular"
        }));
    }
    let [s_name, s_addr, s_phone, s_comment] = sup;
    let supplier = Table {
        name: "supplier",
        cols: vec![
            ("s_suppkey", Col::I(s_key)),
            ("s_name", Col::S(s_name)),
            ("s_address", Col::S(s_addr)),
            ("s_nationkey", Col::I(s_nat)),
            ("s_phone", Col::S(s_phone)),
            ("s_acctbal", Col::F(s_bal)),
            ("s_comment", Col::S(s_comment)),
        ],
        key: &["s_suppkey"],
    };

    let mut p: [Vec<Option<String>>; 6] = Default::default();
    let (mut p_key, mut p_size, mut p_price) = (vec![], vec![], vec![]);
    for i in 1..=sh.parts {
        p_key.push(Some(i as i64));
        p[0].push(s(format!("{} {}", r.pick(&COLORS), r.pick(&COLORS))));
        let m = r.range(1, 5);
        p[1].push(s(format!("Manufacturer#{m}")));
        p[2].push(s(format!("Brand#{m}{}", r.range(1, 5))));
        p[3].push(s(format!(
            "{} {} {}",
            r.pick(&TYPE1),
            r.pick(&TYPE2),
            r.pick(&TYPE3)
        )));
        p_size.push(Some(SIZES[r.below(SIZES.len() as u64) as usize]));
        p[4].push(s(format!("{} {}", r.pick(&CONT1), r.pick(&CONT2))));
        p_price.push(Some(900.0 + r.below(1100) as f64));
        p[5].push(s("c"));
    }
    let [p_name, p_mfgr, p_brand, p_type, p_container, p_comment] = p;
    let part = Table {
        name: "part",
        cols: vec![
            ("p_partkey", Col::I(p_key)),
            ("p_name", Col::S(p_name)),
            ("p_mfgr", Col::S(p_mfgr)),
            ("p_brand", Col::S(p_brand)),
            ("p_type", Col::S(p_type)),
            ("p_size", Col::I(p_size)),
            ("p_container", Col::S(p_container)),
            ("p_retailprice", Col::F(p_price)),
            ("p_comment", Col::S(p_comment)),
        ],
        key: &["p_partkey"],
    };

    // Two distinct suppliers per part; lineitems pick one of them, so
    // (l_partkey, l_suppkey) is always a valid partsupp key.
    let mut part_supps: Vec<[i64; 2]> = vec![];
    let (mut ps_part, mut ps_supp, mut ps_qty, mut ps_cost, mut ps_comment) =
        (vec![], vec![], vec![], vec![], vec![]);
    for i in 1..=sh.parts {
        let a = 1 + r.below(sh.suppliers as u64) as i64;
        let b = 1 + (a % sh.suppliers as i64);
        part_supps.push([a, b]);
        for sk in [a, b] {
            ps_part.push(Some(i as i64));
            ps_supp.push(Some(sk));
            ps_qty.push(Some(r.range(1, 9999)));
            ps_cost.push(Some(1.0 + r.below(1000) as f64));
            ps_comment.push(s("c"));
        }
    }
    let partsupp = Table {
        name: "partsupp",
        cols: vec![
            ("ps_partkey", Col::I(ps_part)),
            ("ps_suppkey", Col::I(ps_supp)),
            ("ps_availqty", Col::I(ps_qty)),
            ("ps_supplycost", Col::F(ps_cost)),
            ("ps_comment", Col::S(ps_comment)),
        ],
        key: &["ps_partkey", "ps_suppkey"],
    };

    let mut c: [Vec<Option<String>>; 5] = Default::default();
    let (mut c_key, mut c_nat, mut c_bal) = (vec![], vec![], vec![]);
    for i in 1..=sh.customers {
        let nat = r.below(25) as i64;
        c_key.push(Some(i as i64));
        c[0].push(s(format!("Customer#{i:09}")));
        c[1].push(s(format!("addr{i}")));
        c_nat.push(Some(nat));
        c[2].push(s(phone(&mut r, nat)));
        c_bal.push(Some(r.range(-999, 9999) as f64));
        c[3].push(s(r.pick(&SEGMENTS)));
        c[4].push(s("c"));
    }
    let [c_name, c_addr, c_phone, c_seg, c_comment] = c;
    let customer = Table {
        name: "customer",
        cols: vec![
            ("c_custkey", Col::I(c_key)),
            ("c_name", Col::S(c_name)),
            ("c_address", Col::S(c_addr)),
            ("c_nationkey", Col::I(c_nat)),
            ("c_phone", Col::S(c_phone)),
            ("c_acctbal", Col::F(c_bal)),
            ("c_mktsegment", Col::S(c_seg)),
            ("c_comment", Col::S(c_comment)),
        ],
        key: &["c_custkey"],
    };

    let (mut o_key, mut o_cust, mut o_status, mut o_total, mut o_date) =
        (vec![], vec![], vec![], vec![], vec![]);
    let (mut o_prio, mut o_clerk, mut o_ship, mut o_comment) = (vec![], vec![], vec![], vec![]);
    let mut l_i: [Vec<Option<i64>>; 4] = Default::default();
    let mut l_f: [Vec<Option<f64>>; 4] = Default::default();
    let mut l_s: [Vec<Option<String>>; 5] = Default::default();
    let mut l_d: [Vec<Option<i32>>; 3] = Default::default();
    // Only two thirds of customers place orders, so outer joins and NOT EXISTS
    // over customers have something to find.
    let ordering = (sh.customers * 2 / 3).max(1) as u64;
    for i in 1..=sh.orders {
        let date = r.range(START_DATE, END_DATE);
        o_key.push(Some(i as i64));
        o_cust.push(Some(1 + r.below(ordering) as i64));
        o_status.push(s(r.pick(&["F", "O", "P"])));
        o_total.push(Some(r.below(500_000) as f64));
        o_date.push(Some(date as i32));
        o_prio.push(s(r.pick(&PRIORITIES)));
        o_clerk.push(s(format!("Clerk#{:09}", r.below(10))));
        o_ship.push(Some(0));
        o_comment.push(s(if r.chance(15) {
            "about special deposits requests"
        } else {
            "furiously"
        }));
        for line in 1..=r.range(1, 4) {
            let pk = 1 + r.below(sh.parts as u64) as usize;
            let ship = date + r.range(1, 121);
            let qty = r.range(1, 50);
            l_i[0].push(Some(i as i64));
            l_i[1].push(Some(pk as i64));
            l_i[2].push(Some(part_supps[pk - 1][r.below(2) as usize]));
            l_i[3].push(Some(line));
            l_f[0].push(Some(qty as f64));
            l_f[1].push(Some(qty as f64 * 1000.0));
            l_f[2].push(Some(r.below(11) as f64 / 100.0));
            l_f[3].push(Some(r.below(9) as f64 / 100.0));
            l_s[0].push(s(r.pick(&["R", "A", "N"])));
            l_s[1].push(s(r.pick(&["O", "F"])));
            l_d[0].push(Some(ship as i32));
            l_d[1].push(Some((date + r.range(30, 90)) as i32));
            l_d[2].push(Some((ship + r.range(1, 30)) as i32));
            l_s[2].push(s(r.pick(&INSTRUCT)));
            l_s[3].push(s(r.pick(&MODES)));
            l_s[4].push(s("c"));
        }
    }
    let orders = Table {
        name: "orders",
        cols: vec![
            ("o_orderkey", Col::I(o_key)),
            ("o_custkey", Col::I(o_cust)),
            ("o_orderstatus", Col::S(o_status)),
            ("o_totalprice", Col::F(o_total)),
            ("o_orderdate", Col::D(o_date)),
            ("o_orderpriority", Col::S(o_prio)),
            ("o_clerk", Col::S(o_clerk)),
            ("o_shippriority", Col::I(o_ship)),
            ("o_comment", Col::S(o_comment)),
        ],
        key: &["o_orderkey"],
    };
    let [l_ok, l_pk, l_sk, l_ln] = l_i;
    let [l_qty, l_price, l_disc, l_tax] = l_f;
    let [l_rf, l_ls, l_instr, l_mode, l_comment] = l_s;
    let [l_ship, l_commit, l_receipt] = l_d;
    let lineitem = Table {
        name: "lineitem",
        cols: vec![
            ("l_orderkey", Col::I(l_ok)),
            ("l_partkey", Col::I(l_pk)),
            ("l_suppkey", Col::I(l_sk)),
            ("l_linenumber", Col::I(l_ln)),
            ("l_quantity", Col::F(l_qty)),
            ("l_extendedprice", Col::F(l_price)),
            ("l_discount", Col::F(l_disc)),
            ("l_tax", Col::F(l_tax)),
            ("l_returnflag", Col::S(l_rf)),
            ("l_linestatus", Col::S(l_ls)),
            ("l_shipdate", Col::D(l_ship)),
            ("l_commitdate", Col::D(l_commit)),
            ("l_receiptdate", Col::D(l_receipt)),
            ("l_shipinstruct", Col::S(l_instr)),
            ("l_shipmode", Col::S(l_mode)),
            ("l_comment", Col::S(l_comment)),
        ],
        key: &["l_orderkey", "l_linenumber"],
    };

    Dataset {
        name: name.to_string(),
        tables: vec![
            region, nation, supplier, part, partsupp, customer, orders, lineitem,
        ],
        unique_keys: true,
    }
}

/// Empty tables plus three PK/FK-consistent datasets.
pub fn tpch_datasets() -> Vec<Dataset> {
    let mut out = vec![tpch(
        "empty",
        0,
        TpchShape {
            suppliers: 0,
            parts: 0,
            customers: 0,
            orders: 0,
        },
    )];
    for seed in 1..=3 {
        out.push(tpch(
            &format!("tpch{seed}"),
            seed,
            TpchShape {
                suppliers: 10,
                parts: 40,
                customers: 30,
                orders: 120,
            },
        ));
    }
    out
}

// ---------------------------------------------------------------------------
// Benchmark runner.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expect {
    Reduces,
    MightGrow,
    Unknown,
}

pub struct Case {
    pub name: &'static str,
    pub sql: &'static str,
    /// Expected verdict when primary keys are declared.
    pub keys: Expect,
    /// Expected verdict when no keys are declared.
    pub no_keys: Expect,
}

fn verdict_kind(v: &Verdict) -> Expect {
    match v {
        Verdict::Reduces => Expect::Reduces,
        Verdict::MightGrow(_) => Expect::MightGrow,
        Verdict::Unknown(_) => Expect::Unknown,
    }
}

/// Runs every case: analyzes it on each dataset, checks the verdict, validates
/// the constraints against real execution, and for `Reduces` queries checks the
/// claim directly (actual output rows <= total rows scanned). Any violated
/// constraint is a failure. Prints a summary table and panics with every
/// mismatch at the end.
///
/// With `declare_keys`, only datasets whose keys really are unique are used, so
/// the declared constraints are true.
pub async fn run_benchmark(cases: &[Case], datasets: Vec<Dataset>, declare_keys: bool) {
    let ctxs: Vec<(String, SessionContext)> = datasets
        .into_iter()
        .filter(|d| d.unique_keys || !declare_keys)
        .map(|d| (d.name.clone(), d.context(declare_keys)))
        .collect();
    let mut failures = vec![];
    println!(
        "\n{} keys declared, datasets: {}",
        if declare_keys { "With" } else { "No" },
        ctxs.iter()
            .map(|(n, _)| n.as_str())
            .collect::<Vec<_>>()
            .join(", ")
    );
    println!(
        "{:<34} {:<9} {:<9} {:>7}  {:<24} {:<11} bounds",
        "query", "verdict", "expected", "pinned", "root rows per dataset", "violations"
    );
    for case in cases {
        let expect = if declare_keys {
            case.keys
        } else {
            case.no_keys
        };
        let mut verdict = None;
        let mut violations = vec![];
        let mut nodes = String::new();
        let mut root_rows = vec![];
        let mut bounds: Option<Bounds> = None;
        let mut formula = None;
        for (dname, ctx) in &ctxs {
            let a = match analyze_sql_with(ctx, case.sql, SELECTIVITY).await {
                Ok(a) => a,
                Err(e) => {
                    failures.push(format!("{}: analysis failed: {e}", case.name));
                    break;
                }
            };
            // Bounds depend only on the query; compute them once.
            if bounds.is_none() {
                bounds = Some(a.bounds().unwrap());
            }
            // Constraints don't depend on data, so the verdict must be stable.
            let kind = verdict_kind(&a.verdict);
            if *verdict.get_or_insert(kind) != kind {
                failures.push(format!("{}: verdict changed on {dname}", case.name));
            }
            let v = a.validate(ctx).await.unwrap();
            let declared = a.smtlib.matches("(declare-fun op").count();
            nodes = format!("{}/{declared}", v.rows.len());
            // Every operator must be checked against real data; only a recursive
            // CTE's recursive branch (which reads its work table) cannot run alone.
            if v.violation.is_none()
                && v.rows.len() < declared
                && !case.sql.to_lowercase().contains("recursive")
            {
                failures.push(format!(
                    "{}: validation pinned only {nodes} operators on {dname}",
                    case.name
                ));
            }
            if v.undecided {
                failures.push(format!("{}: validation undecided on {dname}", case.name));
            }
            if let Some(op) = &v.violation {
                violations.push(format!("{dname}:{op}"));
            }
            root_rows.push(
                v.rows
                    .get(&a.root)
                    .map_or("?".to_string(), |n| n.to_string()),
            );
            for f in check_bounds(bounds.as_ref().unwrap(), &a, &v) {
                failures.push(format!("{}: on {dname}, {f}", case.name));
            }
            for f in check_selectivity(&v) {
                failures.push(format!("{}: on {dname}, {f}", case.name));
            }
            formula = a.selectivity.as_ref().map(|s| s.to_string());
            if kind == Expect::Reduces {
                let root = v.rows.get(&a.root).copied();
                let scanned: Option<u64> =
                    a.scans.iter().map(|(s, _)| v.rows.get(s).copied()).sum();
                if let (Some(root), Some(scanned)) = (root, scanned)
                    && root > scanned
                    && v.violation.is_none()
                {
                    failures.push(format!(
                        "{}: verdict Reduces, but {dname} returned {root} rows from {scanned} scanned, \
                         and validation found no violated constraint",
                        case.name
                    ));
                }
            }
        }
        let Some(verdict) = verdict else { continue };
        println!(
            "{:<34} {:<9} {:<9} {:>7}  {:<24} {:<11} {}",
            case.name,
            format!("{verdict:?}"),
            format!("{expect:?}"),
            nodes,
            root_rows.join("/"),
            if violations.is_empty() {
                "-".to_string()
            } else {
                violations.join(" ")
            },
            bounds.as_ref().map_or(String::new(), |b| b.to_string())
        );
        if let Some(formula) = formula {
            println!("    {}", formula.replace('\n', "\n    "));
        }
        if verdict != expect {
            failures.push(format!(
                "{}: expected {expect:?}, got {verdict:?}",
                case.name
            ));
        }
        if !violations.is_empty() {
            failures.push(format!(
                "{}: constraints violated by real data: {}",
                case.name,
                violations.join(", ")
            ));
        }
    }
    assert!(failures.is_empty(), "\n{}", failures.join("\n"));
}

/// Default options, plus the selectivity formula.
pub const SELECTIVITY: Options = Options {
    max_product: 3,
    selectivity: true,
};

/// The formula or selectivity range that one real execution contradicts, if
/// any. The analysis must have been run with [`SELECTIVITY`].
pub fn check_selectivity(v: &Validation) -> Vec<String> {
    // A violated constraint ends validation early, with nothing to measure.
    if v.violation.is_some() {
        return vec![];
    }
    let check = v.selectivity.as_ref().expect("selectivity was enabled");
    check
        .violation
        .iter()
        .map(|f| format!("selectivity: {f}"))
        .collect()
}

/// Checks every claimed bound against one real execution: the actual output
/// rows against the actual table sizes and total rows scanned. This does not go
/// through the constraints, so it independently tests the claims.
pub fn check_bounds(b: &Bounds, a: &Analysis, v: &Validation) -> Vec<String> {
    let mut failures = vec![];
    let Some(&out) = v.rows.get(&a.root) else {
        return failures;
    };
    if let Some(n) = b.constant
        && out > n
    {
        failures.push(format!("output {out} exceeds constant bound {n}"));
    }
    let scanned: Option<u64> = a.scans.iter().map(|(s, _)| v.rows.get(s).copied()).sum();
    if let (Some(s), Some(scanned)) = (b.sum, scanned)
        && !s.holds(out, scanned)
    {
        failures.push(format!(
            "output {out} exceeds {} with Σ = {scanned}",
            s.render("Σ")
        ));
    }
    for t in &b.tables {
        let size = a
            .scans
            .iter()
            .find(|(_, table)| *table == t.table)
            .and_then(|(s, _)| v.rows.get(s).copied());
        let Some(size) = size else { continue };
        let x = format!("|{}|", t.table);
        if !t.bound.holds(out, size) {
            failures.push(format!(
                "output {out} exceeds {} with {x} = {size}",
                t.bound.render(&x)
            ));
        }
        let expected = t.bound.num as u128 * size as u128;
        if t.exact
            && (t.bound.den as u128 * (out as u128 - t.bound.add.min(out) as u128)) != expected
        {
            failures.push(format!(
                "output {out} is not exactly {} with {x} = {size}",
                t.bound.render(&x)
            ));
        }
    }
    failures
}
