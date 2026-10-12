//! The rewrites into a context's normal form keep its rows, on random trees
//! of operators run live.
//!
//! Each tree is written to SQL twice: straight from the tree, operator by
//! operator, and from the context the tree's operators build
//! ([`Context`]'s constructors, then canonical names), through
//! [`FactKind::count_sql`]. The two must count the same rows. The trees join
//! TPC-H tables, self-joins among them, on equalities of key columns (so
//! that classes of equal columns form), and use every operator a context
//! models: filters (strict ones, and ones that hold of NULL), inner, semi,
//! anti, `NOT IN`, left and full joins (conditions with terms on either side
//! alone), GROUP BY with filters above it, HAVING on an aggregate's value
//! (and on the keys), and DuckDB's decorrelated `EXISTS`, exactly and
//! nearly.
//!
//! Needs the `duckdb` CLI, and for PostgreSQL a server with the database
//! `scripts/postgres_fixtures.sh` loads; each is skipped without.
//! `CARDINAL_REWRITE_N` sets the
//! number of trees (default 2000), `CARDINAL_REWRITE_SEED` their seed.

mod fixtures;
mod live;

use std::collections::BTreeSet;

use cardinal::facts::{Context, ExistsKind, FactKind, FactSet, Term, Value};
use datafusion::functions_aggregate::expr_fn::{avg, count, max, min, sum};
use datafusion::common::{Column, JoinType, TableReference};
use datafusion::common::tree_node::{Transformed, TreeNode};
use datafusion::logical_expr::{BinaryExpr, Expr, Operator, when};
use datafusion::prelude::lit;
use datafusion::sql::unparser::Unparser;
use fixtures::catalog;
use live::{Engine, Rng, TIMED_OUT};

/// A column a tree reads: its instance, name, and what values it holds.
#[derive(Clone, Debug)]
struct Col {
    instance: String,
    name: &'static str,
    kind: Kind,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Kind {
    /// A key, joinable with others of the same domain; values in `0..n`.
    Key(&'static str, i64),
    /// A number in `lo..hi`.
    Num(i64, i64),
    /// Text, one of some values.
    Text(&'static [&'static str]),
}

const SEGMENTS: &[&str] = &["BUILDING", "AUTOMOBILE", "MACHINERY"];
const STATUS: &[&str] = &["F", "O", "P"];
const NATIONS: &[&str] = &["FRANCE", "GERMANY", "CHINA", "BRAZIL"];
const REGIONS: &[&str] = &["ASIA", "EUROPE", "AMERICA"];

/// The columns of each table the trees read.
fn columns(table: &str) -> Vec<(&'static str, Kind)> {
    use Kind::*;
    match table {
        "nation" => vec![("n_nationkey", Key("nation", 25)), ("n_regionkey", Key("region", 5)), ("n_name", Text(NATIONS))],
        "region" => vec![("r_regionkey", Key("region", 5)), ("r_name", Text(REGIONS))],
        "supplier" => vec![("s_suppkey", Key("supp", 101)), ("s_nationkey", Key("nation", 25)), ("s_acctbal", Num(-999, 9999))],
        "customer" => vec![
            ("c_custkey", Key("cust", 1501)),
            ("c_nationkey", Key("nation", 25)),
            ("c_acctbal", Num(-999, 9999)),
            ("c_mktsegment", Text(SEGMENTS)),
        ],
        "part" => vec![("p_partkey", Key("part", 2001)), ("p_size", Num(1, 50))],
        "partsupp" => vec![("ps_partkey", Key("part", 2001)), ("ps_suppkey", Key("supp", 101)), ("ps_availqty", Num(1, 9999))],
        _ => vec![
            ("o_orderkey", Key("order", 60000)),
            ("o_custkey", Key("cust", 1501)),
            ("o_totalprice", Num(1000, 500000)),
            ("o_orderstatus", Text(STATUS)),
        ],
    }
}

const TABLES: &[&str] = &["nation", "region", "supplier", "customer", "part", "partsupp", "orders"];

#[derive(Clone, Debug)]
enum Node {
    Scan { table: &'static str, instance: String },
    Filter { input: Box<Node>, pred: Expr },
    Inner { l: Box<Node>, r: Box<Node>, on: Vec<Expr> },
    Exists { kind: ExistsKind, l: Box<Node>, r: Box<Node>, on: Vec<Expr> },
    Left { l: Box<Node>, r: Box<Node>, on: Vec<Expr> },
    Full { l: Box<Node>, r: Box<Node>, on: Vec<Expr> },
    Group { input: Box<Node>, keys: Vec<Col> },
    /// A GROUP BY's rows whose aggregate passes `cmp` against `value`: a
    /// HAVING, maybe with a predicate on the keys too.
    Having { input: Box<Node>, keys: Vec<Col>, aggregate: Expr, cmp: Operator, value: i64, on_keys: Option<Expr> },
}

impl Node {
    /// The columns of its rows.
    fn cols(&self) -> Vec<Col> {
        match self {
            Node::Scan { table, instance } => columns(table)
                .into_iter()
                .map(|(name, kind)| Col { instance: instance.clone(), name, kind })
                .collect(),
            Node::Filter { input, .. } => input.cols(),
            Node::Inner { l, r, .. } | Node::Left { l, r, .. } | Node::Full { l, r, .. } => {
                l.cols().into_iter().chain(r.cols()).collect()
            }
            Node::Exists { l, .. } => l.cols(),
            Node::Group { keys, .. } | Node::Having { keys, .. } => keys.clone(),
        }
    }

    /// The tree with each instance renamed by `f`.
    fn rename(&self, f: &dyn Fn(&str) -> String) -> Node {
        let e = |e: &Expr| rename_expr(e, f);
        let es = |es: &[Expr]| es.iter().map(e).collect();
        let b = |n: &Node| Box::new(n.rename(f));
        match self {
            Node::Scan { table, instance } => Node::Scan { table, instance: f(instance) },
            Node::Filter { input, pred } => Node::Filter { input: b(input), pred: e(pred) },
            Node::Inner { l, r, on } => Node::Inner { l: b(l), r: b(r), on: es(on) },
            Node::Exists { kind, l, r, on } => Node::Exists { kind: *kind, l: b(l), r: b(r), on: es(on) },
            Node::Left { l, r, on } => Node::Left { l: b(l), r: b(r), on: es(on) },
            Node::Full { l, r, on } => Node::Full { l: b(l), r: b(r), on: es(on) },
            Node::Group { input, keys } => Node::Group {
                input: b(input),
                keys: keys.iter().map(|k| Col { instance: f(&k.instance), ..k.clone() }).collect(),
            },
            Node::Having { input, keys, aggregate, cmp, value, on_keys } => Node::Having {
                input: b(input),
                keys: keys.iter().map(|k| Col { instance: f(&k.instance), ..k.clone() }).collect(),
                aggregate: e(aggregate),
                cmp: *cmp,
                value: *value,
                on_keys: on_keys.as_ref().map(e),
            },
        }
    }

    /// Its rows as SQL, straight from the tree.
    fn sql(&self, next: &mut usize) -> String {
        let mut alias = || {
            *next += 1;
            format!("\"_s{next}\"")
        };
        match self {
            Node::Scan { table, instance } => {
                let cols: Vec<String> = columns(table).iter().map(|(c, _)| format!("{c} AS \"{instance}.{c}\"")).collect();
                format!("SELECT {} FROM {table}", cols.join(", "))
            }
            Node::Filter { input, pred } => {
                let a = alias();
                format!("SELECT * FROM ({}) AS {a} WHERE {}", input.sql(next), sql(pred))
            }
            Node::Inner { l, r, on } => {
                let (a, b) = (alias(), alias());
                format!("SELECT * FROM ({}) AS {a}, ({}) AS {b} WHERE {}", l.sql(next), r.sql(next), all(on))
            }
            Node::Exists { kind, l, r, on } => {
                let (a, b) = (alias(), alias());
                let (l, r) = (l.sql(next), r.sql(next));
                match kind {
                    ExistsKind::Semi => format!("SELECT * FROM ({l}) AS {a} WHERE EXISTS (SELECT 1 FROM ({r}) AS {b} WHERE {})", all(on)),
                    ExistsKind::Anti => format!("SELECT * FROM ({l}) AS {a} WHERE NOT EXISTS (SELECT 1 FROM ({r}) AS {b} WHERE {})", all(on)),
                    ExistsKind::NotIn => {
                        let Expr::BinaryExpr(BinaryExpr { left, right, .. }) = &on[0] else { unreachable!() };
                        format!("SELECT * FROM ({l}) AS {a} WHERE {} NOT IN (SELECT {} FROM ({r}) AS {b})", sql(left), sql(right))
                    }
                }
            }
            Node::Left { l, r, on } | Node::Full { l, r, on } => {
                let kind = if matches!(self, Node::Left { .. }) { "LEFT" } else { "FULL" };
                let (a, b) = (alias(), alias());
                format!("SELECT * FROM ({}) AS {a} {kind} JOIN ({}) AS {b} ON {}", l.sql(next), r.sql(next), all(on))
            }
            Node::Group { input, keys } => {
                let a = alias();
                let keys: Vec<String> = keys.iter().map(|k| format!("\"{}.{}\"", k.instance, k.name)).collect();
                format!("SELECT DISTINCT {} FROM ({}) AS {a}", keys.join(", "), input.sql(next))
            }
            Node::Having { input, keys, aggregate, cmp, value, on_keys } => {
                let a = alias();
                let keys: Vec<String> = keys.iter().map(|k| format!("\"{}.{}\"", k.instance, k.name)).collect();
                let having = Expr::BinaryExpr(BinaryExpr::new(Box::new(aggregate.clone()), *cmp, Box::new(lit(*value))));
                let mut conds = vec![sql(&having)];
                conds.extend(on_keys.iter().map(sql));
                format!(
                    "SELECT {k} FROM ({}) AS {a} GROUP BY {k} HAVING {}",
                    input.sql(next),
                    conds.iter().map(|c| format!("({c})")).collect::<Vec<_>>().join(" AND "),
                    k = keys.join(", ")
                )
            }
        }
    }

    /// Its rows as a context, through the constructors that rewrite, with
    /// the values it reads defined in `facts`, named as plans name them.
    fn context(&self, facts: &mut FactSet) -> Context {
        let terms = |es: &[Expr]| -> BTreeSet<Term> { es.iter().cloned().map(Term::new).collect() };
        match self {
            Node::Scan { instance, .. } => Context::table(instance),
            Node::Filter { input, pred } => input.context(facts).filter(&terms(std::slice::from_ref(pred))),
            Node::Inner { l, r, on } => l.context(facts).cross(&r.context(facts)).unwrap().filter(&terms(on)),
            Node::Exists { kind, l, r, on } => match kind {
                ExistsKind::Semi => Context::join(JoinType::LeftSemi, terms(on), l.context(facts), r.context(facts)),
                ExistsKind::Anti => Context::join(JoinType::LeftAnti, terms(on), l.context(facts), r.context(facts)),
                ExistsKind::NotIn => l.context(facts).exists(ExistsKind::NotIn, terms(on), r.context(facts)),
            },
            Node::Left { l, r, on } => Context::join(JoinType::Left, terms(on), l.context(facts), r.context(facts)),
            Node::Full { l, r, on } => Context::join(JoinType::Full, terms(on), l.context(facts), r.context(facts)),
            Node::Group { input, keys } => {
                let keys: BTreeSet<Term> = keys.iter().map(|k| Term::new(column(k))).collect();
                Context::Derived { op: "group".into(), args: keys.into_iter().collect(), inputs: vec![input.context(facts)] }
            }
            Node::Having { input, keys, aggregate, cmp, value, on_keys } => {
                let keys: BTreeSet<Term> = keys.iter().map(|k| Term::new(column(k))).collect();
                let group = Context::Derived { op: "group".into(), args: keys.into_iter().collect(), inputs: vec![input.context(facts)] };
                // Named as `Values::definition` names it.
                let FactKind::Distinct { keys, over } =
                    (FactKind::Distinct { keys: [Term::new(aggregate.clone())].into(), over: group.clone() }).canonical()
                else {
                    unreachable!()
                };
                let aggregate = keys.into_iter().next().unwrap();
                let name = format!("{aggregate} of {over}");
                facts.insert_value(Value { name: name.clone(), aggregate, over });
                let read = Expr::Column(Column::new(Some(TableReference::bare("value")), name));
                let mut preds: BTreeSet<Term> = [Term::new(Expr::BinaryExpr(BinaryExpr::new(Box::new(read), *cmp, Box::new(lit(*value)))))].into();
                preds.extend(on_keys.iter().cloned().map(Term::new));
                group.filter(&preds)
            }
        }
    }
}

fn column(c: &Col) -> Expr {
    Expr::Column(Column::new(Some(TableReference::bare(c.instance.as_str())), c.name))
}

fn rename_expr(e: &Expr, f: &dyn Fn(&str) -> String) -> Expr {
    e.clone()
        .transform_up(|e| match e {
            Expr::Column(c) => {
                let r = c.relation.as_ref().map(|r| f(r.table()));
                Ok(Transformed::yes(Expr::Column(Column::new(r.map(TableReference::bare), c.name))))
            }
            e => Ok(Transformed::no(e)),
        })
        .unwrap()
        .data
}

/// `e` as SQL, each column `i.c` as `"i.c"`.
fn sql(e: &Expr) -> String {
    let e = e
        .clone()
        .transform_up(|e| match e {
            Expr::Column(c) => {
                let name = format!("{}.{}", c.relation.as_ref().unwrap().table(), c.name);
                Ok(Transformed::yes(Expr::Column(Column::new_unqualified(name))))
            }
            e => Ok(Transformed::no(e)),
        })
        .unwrap()
        .data;
    Unparser::default().expr_to_sql(&e).unwrap().to_string()
}

fn all(es: &[Expr]) -> String {
    if es.is_empty() {
        return "true".into();
    }
    es.iter().map(|e| format!("({})", sql(e))).collect::<Vec<_>>().join(" AND ")
}

struct Gen {
    r: Rng,
    next: usize,
}

impl Gen {
    fn instance(&mut self, table: &str) -> String {
        self.next += 1;
        format!("{table}#{}", self.next)
    }

    fn scan(&mut self) -> Node {
        let table = TABLES[self.r.below(TABLES.len())];
        Node::Scan { table, instance: self.instance(table) }
    }

    fn value(&mut self, c: &Col) -> Expr {
        match c.kind {
            Kind::Key(_, n) => lit(self.r.below(n as usize) as i64),
            Kind::Num(lo, hi) => lit(lo + self.r.below((hi - lo) as usize) as i64),
            Kind::Text(xs) => lit(xs[self.r.below(xs.len())]),
        }
    }

    /// A predicate on `cols`: strict (NULL on NULL input) or not.
    fn pred(&mut self, cols: &[Col]) -> Expr {
        let c = cols[self.r.below(cols.len())].clone();
        let v = self.value(&c);
        let x = column(&c);
        let compare = |r: &mut Rng, x: Expr, v: Expr| match (c.kind, r.below(3)) {
            (Kind::Text(_), _) => x.eq(v),
            (_, 0) => x.lt(v),
            (_, 1) => x.gt(v),
            _ => x.not_eq(v),
        };
        match self.r.below(10) {
            0 => x.is_null(),
            1 => x.is_not_null(),
            2 => {
                let d = cols[self.r.below(cols.len())].clone();
                let w = self.value(&d);
                let other = compare(&mut self.r, column(&d), w);
                compare(&mut self.r, x, v).or(other)
            }
            // Holds of NULL: a CASE.
            3 => when(x.clone().is_null(), lit(1)).otherwise(lit(0)).unwrap().eq(lit(1)).or(compare(&mut self.r, x, v)),
            _ => compare(&mut self.r, x, v),
        }
    }

    /// Equalities joining `l` and `r` on keys of a common domain, maybe
    /// several; empty if they share none.
    fn equalities(&mut self, l: &[Col], r: &[Col]) -> Vec<Expr> {
        let mut pairs = vec![];
        for a in l {
            for b in r {
                if let (Kind::Key(x, _), Kind::Key(y, _)) = (a.kind, b.kind)
                    && x == y
                {
                    pairs.push((a.clone(), b.clone()));
                }
            }
        }
        let mut out = vec![];
        for _ in 0..1 + usize::from(self.r.chance(30)) {
            if pairs.is_empty() {
                break;
            }
            let (a, b) = pairs.remove(self.r.below(pairs.len()));
            out.push(column(&a).eq(column(&b)));
        }
        out
    }

    fn tree(&mut self, depth: usize) -> Node {
        if depth == 0 || self.r.chance(25) {
            let s = self.scan();
            return if self.r.chance(40) {
                let pred = self.pred(&s.cols());
                Node::Filter { input: Box::new(s), pred }
            } else {
                s
            };
        }
        let l = self.tree(depth - 1);
        match self.r.below(10) {
            0 => {
                let pred = self.pred(&l.cols());
                Node::Filter { input: Box::new(l), pred }
            }
            1 => self.group(l),
            2 => self.decorrelated(l),
            k => {
                let r = self.tree(depth - 1);
                let on = self.equalities(&l.cols(), &r.cols());
                if on.is_empty() {
                    return l;
                }
                let (lc, rc) = (l.cols(), r.cols());
                let (l, r) = (Box::new(l), Box::new(r));
                match k {
                    3 | 4 => Node::Inner { l, r, on },
                    5 => Node::Exists { kind: if self.r.chance(50) { ExistsKind::Semi } else { ExistsKind::Anti }, l, r, on },
                    6 => Node::Exists { kind: ExistsKind::NotIn, l, r, on: on[..1].to_vec() },
                    7 | 8 => {
                        // Terms of the condition on one side alone.
                        let mut on = on;
                        if self.r.chance(40) {
                            on.push(self.pred(&rc));
                        }
                        if self.r.chance(25) {
                            on.push(self.pred(&lc));
                        }
                        let node = Node::Left { l, r, on };
                        self.above(node)
                    }
                    _ => {
                        let node = Node::Full { l, r, on };
                        self.above(node)
                    }
                }
            }
        }
    }

    /// `n`, maybe filtered: on a padded side's columns, strictly or not.
    fn above(&mut self, n: Node) -> Node {
        if self.r.chance(60) {
            let pred = self.pred(&n.cols());
            Node::Filter { input: Box::new(n), pred }
        } else {
            n
        }
    }

    fn group(&mut self, input: Node) -> Node {
        let cols = input.cols();
        let mut keys = vec![cols[self.r.below(cols.len())].clone()];
        if self.r.chance(30) {
            let k = cols[self.r.below(cols.len())].clone();
            if !keys.iter().any(|c| c.instance == k.instance && c.name == k.name) {
                keys.push(k);
            }
        }
        if self.r.chance(40) {
            // A HAVING on an aggregate, and maybe on the keys.
            let cols = input.cols();
            let nums: Vec<Col> = cols.iter().filter(|c| !matches!(c.kind, Kind::Text(_))).cloned().collect();
            let x = nums.get(self.r.below(nums.len().max(1))).map(column);
            let (aggregate, value) = match (self.r.below(5), x) {
                (0, Some(x)) => (sum(x), self.r.below(20000) as i64),
                (1, Some(x)) => (min(x), self.r.below(1000) as i64),
                (2, Some(x)) => (max(x), self.r.below(1000) as i64),
                (3, Some(x)) => (avg(x), self.r.below(1000) as i64),
                _ => (count(lit(1)), self.r.below(10) as i64),
            };
            let cmp = if self.r.chance(50) { Operator::Gt } else { Operator::LtEq };
            let on_keys = self.r.chance(40).then(|| {
                let ks: Vec<Col> = keys.clone();
                self.pred(&ks)
            });
            return Node::Having { input: Box::new(input), keys, aggregate, cmp, value, on_keys };
        }
        let g = Node::Group { input: Box::new(input), keys };
        // A filter on the keys, above it.
        if self.r.chance(50) {
            let pred = self.pred(&g.cols());
            Node::Filter { input: Box::new(g), pred }
        } else {
            g
        }
    }

    /// `k ⋉ σ(x = k')(X × group_k'(copy of k))` on `k IS NOT DISTINCT FROM
    /// k'`, as DuckDB decorrelates `EXISTS`; sometimes a near miss: a copy of
    /// other rows, or `=` for the condition.
    fn decorrelated(&mut self, kept: Node) -> Node {
        let keys: Vec<Col> = kept.cols().into_iter().filter(|c| matches!(c.kind, Kind::Key(..))).collect();
        if keys.is_empty() {
            return kept;
        }
        let k = keys[self.r.below(keys.len())].clone();
        let suffix = format!("~c{}", self.next);
        self.next += 1;
        let mut copy = kept.rename(&|i| format!("{i}{suffix}"));
        if self.r.chance(20) {
            let pred = self.pred(&copy.cols());
            copy = Node::Filter { input: Box::new(copy), pred };
        }
        let k2 = Col { instance: format!("{}{suffix}", k.instance), ..k.clone() };
        let x = self.scan();
        let joins: Vec<Col> = x.cols().into_iter().filter(|c| c.kind == k.kind || matches!((c.kind, k.kind), (Kind::Key(a, _), Kind::Key(b, _)) if a == b)).collect();
        let Some(xk) = joins.first().cloned() else { return kept };
        let group = Node::Group { input: Box::new(copy), keys: vec![k2.clone()] };
        let mut on = vec![column(&xk).eq(column(&k2))];
        if self.r.chance(40) {
            on.push(self.pred(&x.cols()));
        }
        let other = Node::Inner { l: Box::new(x), r: Box::new(group), on };
        let cond = match self.r.below(5) {
            0 => column(&k).eq(column(&k2)),
            _ => Expr::BinaryExpr(BinaryExpr::new(Box::new(column(&k)), Operator::IsNotDistinctFrom, Box::new(column(&k2)))),
        };
        let kind = if self.r.chance(70) { ExistsKind::Semi } else { ExistsKind::Anti };
        Node::Exists { kind, l: Box::new(kept), r: Box::new(other), on: vec![cond] }
    }
}

#[tokio::test]
async fn rewrites_keep_rows() {
    match Engine::duckdb() {
        Some(engine) => check(engine).await,
        None => eprintln!("skipped: no duckdb CLI"),
    }
}

/// The same trees, counted by PostgreSQL, each context's count written in
/// its dialect.
#[tokio::test]
async fn rewrites_keep_rows_in_postgres() {
    match Engine::postgres() {
        Some(engine) => check(engine).await,
        None => eprintln!("skipped: no PostgreSQL with the fixtures' database"),
    }
}

async fn check(engine: Engine) {
    let catalog = catalog().await;
    let n: usize = std::env::var("CARDINAL_REWRITE_N").ok().and_then(|n| n.parse().ok()).unwrap_or(2000);
    let seed: u64 = std::env::var("CARDINAL_REWRITE_SEED").ok().and_then(|n| n.parse().ok()).unwrap_or(3);
    let mut g = Gen { r: Rng::new(seed), next: 0 };
    let mut cases = vec![];
    let mut queries = vec![];
    let mut unwritten = 0;
    for _ in 0..n {
        let tree = g.tree(3);
        let mut facts = FactSet::default();
        let context = tree.context(&mut facts);
        let Some(counts) = FactKind::Cardinality(context.clone()).canonical().count_sql_in(&catalog, &facts, engine.dialect()) else {
            if std::env::var("CARDINAL_REWRITE_SHOW").is_ok() {
                eprintln!("not writable: {}\n  values: {:?}\n  tree: {tree:?}", context.canonical(), facts.values().map(|v| &v.name).collect::<Vec<_>>());
            }
            unwritten += 1;
            continue;
        };
        queries.push(format!("SELECT count(*) FROM ({}) AS \"_s0\"", tree.sql(&mut 0)));
        queries.push(counts.value);
        cases.push((tree, context));
    }
    let counted = engine.values(&queries);
    let mut failures = vec![];
    let (mut checked, mut slow) = (0, 0);
    for (i, (tree, context)) in cases.iter().enumerate() {
        match (&counted[2 * i], &counted[2 * i + 1]) {
            (Ok(a), Ok(b)) if a == b => checked += 1,
            (Ok(a), Ok(b)) => failures.push(format!(
                "tree gives {a} rows, its context {b}\n  tree: {tree:?}\n  context: {}\n  tree sql: {}\n  context sql: {}",
                context.canonical(),
                queries[2 * i],
                queries[2 * i + 1]
            )),
            (Err(e), _) | (_, Err(e)) if e == TIMED_OUT => slow += 1,
            (Err(e), _) | (_, Err(e)) => failures.push(format!("does not count: {e}\n  {}\n  {}", queries[2 * i], queries[2 * i + 1])),
        }
    }
    println!("{}: {n} trees: {checked} agree, {unwritten} contexts not writable, {slow} timed out", engine.name());
    assert!(failures.is_empty(), "{} failures:\n{}", failures.len(), failures.join("\n\n"));
}
