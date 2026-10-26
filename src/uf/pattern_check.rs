//! §11 item 4's static check, over every quantified axiom of the programs
//! built for a spread of plans: each multi-pattern names every bound
//! variable, and every atom a pattern holds (`sub`, `key`, `fd`,
//! `implies`, `point`, `csub`, `orof`, `andof`, `dom`) is also a
//! hypothesis of its body (§7.1, rule 3).

use std::collections::BTreeSet;

use datafusion::logical_expr::LogicalPlan;
use datafusion::prelude::SessionContext;

use super::translate::{self, Builder, Fact, Tables};
use super::{Encoder, program, prune, remap};
use crate::ForeignKey;
use crate::observed::{Catalog, ObservedPlan};

#[derive(Debug, Clone, PartialEq)]
enum S {
    Atom(String),
    List(Vec<S>),
}

impl std::fmt::Display for S {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            S::Atom(a) => write!(f, "{a}"),
            S::List(xs) => {
                write!(f, "(")?;
                for (i, x) in xs.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{x}")?;
                }
                write!(f, ")")
            }
        }
    }
}

fn parse(text: &str) -> Vec<S> {
    let cs: Vec<char> = text.chars().collect();
    let mut stack: Vec<Vec<S>> = vec![vec![]];
    let mut i = 0;
    while i < cs.len() {
        let c = cs[i];
        match c {
            '(' => stack.push(vec![]),
            ')' => {
                let l = stack.pop().unwrap();
                stack.last_mut().unwrap().push(S::List(l));
            }
            ';' => {
                while i < cs.len() && cs[i] != '\n' {
                    i += 1;
                }
            }
            c if c.is_whitespace() => {}
            '|' | '"' => {
                let mut j = i + 1;
                while cs[j] != c {
                    j += 1;
                }
                stack
                    .last_mut()
                    .unwrap()
                    .push(S::Atom(cs[i..=j].iter().collect()));
                i = j;
            }
            _ => {
                let mut j = i;
                while j < cs.len() && !cs[j].is_whitespace() && !"()|;".contains(cs[j]) {
                    j += 1;
                }
                stack
                    .last_mut()
                    .unwrap()
                    .push(S::Atom(cs[i..j].iter().collect()));
                i = j - 1;
            }
        }
        i += 1;
    }
    assert_eq!(stack.len(), 1, "unbalanced program text");
    stack.pop().unwrap()
}

fn atoms(s: &S, out: &mut BTreeSet<String>) {
    match s {
        S::Atom(a) => {
            out.insert(a.clone());
        }
        S::List(xs) => xs.iter().for_each(|x| atoms(x, out)),
    }
}

/// The terms in hypothesis position: the conjuncts of an implication's
/// antecedent, under any `and`s and implications' consequents.
fn hypotheses(s: &S, out: &mut Vec<S>) {
    if let S::List(xs) = s {
        if let [S::Atom(h), a, b] = &xs[..]
            && h == "=>"
        {
            conjuncts(a, out);
            hypotheses(b, out);
            return;
        }
        if let Some(S::Atom(h)) = xs.first()
            && h == "and"
        {
            xs[1..].iter().for_each(|x| hypotheses(x, out));
        }
    }
}

fn conjuncts(s: &S, out: &mut Vec<S>) {
    if let S::List(xs) = s
        && let Some(S::Atom(h)) = xs.first()
        && h == "and"
    {
        xs[1..].iter().for_each(|x| conjuncts(x, out));
        return;
    }
    out.push(s.clone());
}

fn contains(s: &S, t: &S) -> bool {
    s == t || matches!(s, S::List(xs) if xs.iter().any(|x| contains(x, t)))
}

const GUARDS: &[&str] = &[
    "sub", "key", "fd", "implies", "point", "csub", "orof", "andof", "dom",
];

/// Axioms whose guard atom in a pattern is their conclusion: they derive
/// `csub` of a union of columns when it is asked for, from the parts,
/// instead of assuming it. No instance creates a new `csub` atom of
/// sets not already in the program, so they cannot loop.
const DERIVING: &[&str] = &["csub_cup", "csub_split"];

/// Every violation in `text`'s quantified axioms, and how many it has.
fn check(text: &str) -> (Vec<String>, usize) {
    let mut out = vec![];
    let mut n = 0;
    for top in parse(text) {
        let S::List(a) = &top else { continue };
        let [S::Atom(h), S::List(q)] = &a[..] else {
            continue;
        };
        if h != "assert" || q.first() != Some(&S::Atom("forall".into())) {
            continue;
        }
        n += 1;
        let S::List(vars) = &q[1] else {
            panic!("{top}")
        };
        let vars: Vec<String> = vars
            .iter()
            .map(|v| match v {
                S::List(p) => p[0].to_string(),
                _ => panic!("{top}"),
            })
            .collect();
        let S::List(bang) = &q[2] else {
            panic!("{top}")
        };
        assert_eq!(bang[0], S::Atom("!".into()), "{top}");
        let body = &bang[1];
        let mut name = String::new();
        let mut patterns = vec![];
        let mut k = 2;
        while k + 1 < bang.len() {
            match &bang[k] {
                S::Atom(a) if a == ":pattern" => patterns.push(bang[k + 1].clone()),
                S::Atom(a) if a == ":qid" => name = bang[k + 1].to_string(),
                _ => {}
            }
            k += 2;
        }
        if name.is_empty() {
            out.push(format!("no :qid: {top}"));
        }
        if patterns.is_empty() {
            out.push(format!("{name}: no pattern"));
        }
        let mut hyps = vec![];
        hypotheses(body, &mut hyps);
        for p in &patterns {
            let mut seen = BTreeSet::new();
            atoms(p, &mut seen);
            for v in &vars {
                if !seen.contains(v) {
                    out.push(format!("{name}: pattern {p} misses bound variable {v}"));
                }
            }
            let S::List(terms) = p else { continue };
            for t in terms {
                let S::List(xs) = t else { continue };
                let Some(S::Atom(f)) = xs.first() else {
                    continue;
                };
                if !GUARDS.contains(&f.as_str()) || DERIVING.contains(&name.trim_matches('|')) {
                    continue;
                }
                if !hyps.iter().any(|h| h == t) {
                    let where_ = if contains(body, t) {
                        "in the body but not as a hypothesis"
                    } else {
                        "not in the body"
                    };
                    out.push(format!("{name}: pattern atom {t} is {where_}"));
                }
            }
        }
    }
    out.sort();
    out.dedup();
    (out, n)
}

/// The program `solve` would build for the target, a DataFusion plan or
/// a planned one, with every observed plan's facts.
fn program(enc: &Encoder, target: Option<&LogicalPlan>, planned: Option<&ObservedPlan>) -> String {
    let mut terms = enc.terms.clone();
    let tables = Tables {
        catalog: enc.catalog,
    };
    let mut shape = vec![];
    let root = {
        let mut b = Builder {
            terms: &mut terms,
            tables: &tables,
        };
        match (target, planned) {
            (Some(t), _) => translate::logical(&mut b, t, "target", &mut shape),
            (_, Some(p)) => {
                let mut p = p.clone();
                p.name = "target".into();
                translate::planned(&mut b, &p)
            }
            _ => unreachable!(),
        }
    };
    let map = prune(&mut terms, &[root]);
    let root = map.get(&root).copied().unwrap_or(root);
    let mut facts: Vec<(String, Fact)> = shape
        .into_iter()
        .map(|(n, f)| (n, remap(&f, &map)))
        .collect();
    let mut groups = vec![];
    for (_, fs, rels) in &enc.plans {
        facts.extend(fs.iter().cloned());
        groups.push(rels.clone());
    }
    program::build(&mut terms, &tables, &enc.schema, &facts, &groups, root).text
}

#[test]
fn parses_and_flags() {
    let good = "(assert (forall ((x Rel) (y Rel)) (! (=> (sub x y) (<= (card x) (card y))) :pattern ((sub x y)) :weight 0 :qid |sub_card|)))";
    assert_eq!(check(good), (vec![], 1));
    // §7.1 rule 3's counterexample: the trigger is not a guard.
    let bad = "(assert (forall ((x Rel) (y Rel)) (! (<= (card x) (card y)) :pattern ((sub x y)) :weight 0 :qid |sub_card|)))";
    assert_eq!(check(bad).0.len(), 1);
    let partial =
        "(assert (forall ((x Rel) (y Rel)) (! (>= (card x) 0) :pattern ((card x)) :qid |p|)))";
    assert_eq!(check(partial).0.len(), 1);
}

#[tokio::test]
async fn every_pattern_covers_its_variables_and_guards() {
    let ctx = SessionContext::new();
    for d in [
        "CREATE TABLE foo (a INTEGER NOT NULL, b INTEGER NOT NULL, k INTEGER NOT NULL)",
        "CREATE TABLE bar (k INTEGER NOT NULL PRIMARY KEY, b INTEGER NOT NULL, c INTEGER)",
        "CREATE TABLE emp (id INTEGER NOT NULL PRIMARY KEY, mgr INTEGER NOT NULL)",
    ] {
        ctx.sql(d).await.unwrap().collect().await.unwrap();
    }
    let catalog = Catalog::from_context(&ctx).await.unwrap();
    let fks = vec![
        ForeignKey::new("foo", &["k"], "bar", &["k"]),
        ForeignKey::new("emp", &["mgr"], "emp", &["id"]),
    ];
    let enc = Encoder::new(&catalog, &fks);
    let queries = [
        "SELECT a, b FROM foo WHERE a > 1 AND b > 2",
        "SELECT * FROM foo JOIN bar ON foo.k = bar.k WHERE foo.a > 1 AND bar.c > 0",
        "SELECT foo.a, bar.c FROM foo JOIN bar ON foo.k = bar.k GROUP BY foo.a, bar.c",
        "SELECT * FROM foo LEFT JOIN bar ON foo.k = bar.k WHERE bar.b > 1 OR bar.b <= 1",
        "SELECT * FROM foo WHERE NOT EXISTS (SELECT 1 FROM bar WHERE bar.k = foo.k)",
        "SELECT * FROM foo WHERE EXISTS (SELECT 1 FROM bar WHERE bar.k = foo.k AND bar.b = 3)",
        "SELECT * FROM foo WHERE a IN (1, 2) AND b NOT IN (3, 4) AND (a = 7 OR b < 2)",
        "SELECT * FROM (SELECT a % 3 AS g, b FROM foo) s WHERE g > 1",
        "SELECT a % 3, count(*) FROM foo GROUP BY a % 3 HAVING count(*) > 9",
        "SELECT k, min(a), max(a), avg(a), count(b), sum(b) FROM foo GROUP BY k HAVING max(a) < 4",
        "SELECT * FROM emp e JOIN emp m ON e.mgr = m.id WHERE m.mgr = 3",
        "SELECT * FROM foo WHERE a > (SELECT max(a) FROM foo) AND b = (SELECT min(b) FROM bar)",
        "SELECT * FROM (SELECT * FROM foo UNION ALL SELECT * FROM foo) u JOIN bar ON u.k = bar.k",
        "SELECT * FROM foo JOIN bar ON foo.k = bar.k AND foo.b = bar.b ORDER BY foo.a LIMIT 10",
        "SELECT * FROM foo JOIN bar ON foo.a + 1 = bar.k",
        "SELECT DISTINCT a FROM foo WHERE a > 1 AND a < 5",
    ];
    let mut all = vec![];
    let mut total = 0;
    for q in queries {
        let state = ctx.state();
        let p = state
            .optimize(&state.create_logical_plan(q).await.unwrap())
            .unwrap();
        let (v, n) = check(&program(&enc, Some(&p), None));
        total += n;
        all.extend(v.into_iter().map(|v| format!("[{q}] {v}")));
    }
    // Executed plans, for the physical operators' axioms (`part`, `opt`,
    // `rt`): DuckDB's TPC-H profiles, over their tables.
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/duckdb");
    let cat: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(format!("{dir}/catalog.json")).unwrap())
            .unwrap();
    let tpch = SessionContext::new();
    let mut tables: Vec<(String, Vec<String>)> = vec![];
    for c in cat.as_array().unwrap() {
        let t = c["table_name"].as_str().unwrap().to_string();
        let col = format!(
            "{} {}",
            c["column_name"].as_str().unwrap(),
            c["data_type"].as_str().unwrap()
        );
        match tables.last_mut() {
            Some((n, cols)) if *n == t => cols.push(col),
            _ => tables.push((t, vec![col])),
        }
    }
    for (t, cols) in tables {
        tpch.sql(&format!("CREATE TABLE {t} ({})", cols.join(", ")))
            .await
            .unwrap()
            .collect()
            .await
            .unwrap();
    }
    let tcat = Catalog::from_context(&tpch)
        .await
        .unwrap()
        .with_partial_indexes(Vec::<(String, String)>::new());
    let tfks = vec![
        ForeignKey::new("lineitem", &["l_orderkey"], "orders", &["o_orderkey"]),
        ForeignKey::new("orders", &["o_custkey"], "customer", &["c_custkey"]),
        ForeignKey::new("customer", &["c_nationkey"], "nation", &["n_nationkey"]),
        ForeignKey::new("nation", &["n_regionkey"], "region", &["r_regionkey"]),
    ];
    for q in ["q03", "q05", "q10", "q13", "q18", "q21", "q22"] {
        let json = std::fs::read_to_string(format!("{dir}/tpch/{q}.json")).unwrap();
        let plan = crate::observed::from_duckdb(&tcat, q, &json, None).unwrap();
        let mut enc = Encoder::new(&tcat, &tfks);
        enc.observe(&plan);
        let (v, n) = check(&program(&enc, None, Some(&plan)));
        total += n;
        all.extend(v.into_iter().map(|v| format!("[{q}] {v}")));
    }
    // One line per violated axiom, whatever plan showed it.
    let mut by_axiom: Vec<String> = all
        .iter()
        .map(|l| l.split_once("] ").map_or(l.clone(), |(_, v)| v.to_string()))
        .collect();
    by_axiom.sort();
    by_axiom.dedup();
    println!("{total} quantified axioms checked");
    assert!(
        total > 500,
        "only {total} axioms found: the parse missed them"
    );
    assert!(
        by_axiom.is_empty(),
        "{} violations:\n{}",
        by_axiom.len(),
        by_axiom.join("\n")
    );
}
