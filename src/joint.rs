//! Facts as plans: a query analyzed together with the executed plans of
//! other queries, each counted operator pinned to its rows.
//!
//! An alternative to [`Analysis::with_facts`](crate::Analysis::with_facts),
//! and an experiment. No rules read facts off the plans, combine them, or
//! match them to the query's operators: the profiles' operators get the
//! constraints any operator does, the axioms between contexts
//! ([`crate::axioms`]) relate them to the query's, and Z3 finds what
//! follows.
//!
//! ```text
//!  query ───────────┐
//!                   ├─ rules ─ axioms ─ pins ─ linearize ─▶ Analysis
//!  profiles ─ select┘                 X = rows
//! ```
//!
//! # Spec
//!
//! - **Input**: the query's plan, executed plans of other queries over the
//!   same data (their counts read as [`observe`](crate::facts::observe)
//!   reads a translated plan's), and the options.
//! - **Output**: an [`Analysis`] of the query, without a trace.
//! - **Selection**: of each profile, the maximal subtrees that scan only
//!   tables the query scans (`maximal`), and its unfiltered scans of the
//!   tables those reference by foreign keys, transitively: those pin the
//!   tables' sizes, which the `referenced size` axiom
//!   ([`Analyzer::referenced_size`]) bounds the referencing columns'
//!   distinct counts by. Other subtrees share no context with the query's.
//! - **Linearize**: pins substituted, products bounded linearly
//!   (`linearize`), so the bounds search's checks stay decidable.
//! - **Not done**: no check that the pins are consistent with the
//!   constraints. Facts of other data, or a wrong rule, make the set
//!   unsatisfiable, and an unsatisfiable set proves any bound.
//!   Slower than [`Analysis::with_facts`](crate::Analysis::with_facts):
//!   the 46 DuckDB fixtures take about 7× as long in all.

use std::collections::{BTreeSet, HashMap, HashSet};

use datafusion::common::tree_node::TreeNodeRecursion;
use datafusion::logical_expr::LogicalPlan;
use datafusion::logical_expr::logical_plan::TableScan;
use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{AstKind, DeclKind, SortKind};

use crate::analysis::{Analyzer, ranged_columns};
use crate::observed::{Catalog, ObservedPlan};
use crate::{Analysis, Options, Result, axioms, base_kind};

/// `plan` analyzed together with the parts of `profiles` it could share
/// rows with, each of their counted operators pinned to its rows (or, a
/// runtime filter pruned its rows, bounded below by them).
///
/// The profiles must have run on the data the bounds are for. Plans that
/// were not run, or do not translate, are left out.
pub fn analyze_joint(
    catalog: &Catalog,
    plan: &ObservedPlan,
    profiles: &[ObservedPlan],
    options: Options,
) -> Result<Analysis> {
    let query = catalog.to_logical(plan)?;
    let translated: Vec<_> = profiles
        .iter()
        .filter(|p| p.counted)
        .filter_map(|p| Some((p, catalog.to_logical_mapped(p).ok()?)))
        .collect();
    let resolve = |scan: &TableScan| base_kind(&scan.table_name, "datafusion", "public");
    let mut a = Analyzer::new(&resolve, options.max_product, &options.foreign_keys, false)
        .with_ranges(&query);
    a.referenced_sizes = true;
    for (_, (root, _)) in &translated {
        a.ranged.extend(ranged_columns(root));
    }
    let root = a.visit(&query).card;
    let (own, own_scans) = (a.nodes.len(), a.scans.len());

    let tables = tables_of(&query);
    let referenced: BTreeSet<String> = reachable(&tables, &options)
        .difference(&tables)
        .cloned()
        .collect();
    let mut pins = vec![];
    for (p, (root, built)) in &translated {
        let mut parts = vec![];
        maximal(root, &tables, &referenced, &mut parts);
        for t in parts {
            let start = a.nodes.len();
            a.visit(t);
            for (m, j, floor) in crate::facts::observe::counts(p, &a.nodes[start..], built) {
                pins.push((a.nodes[start + m].var.clone(), p.nodes[j].rows, floor));
            }
        }
    }
    axioms::assert_all(&mut a);
    for (var, rows, floor) in pins {
        let (v, n) = (Int::new_const(var.as_str()), Int::from_u64(rows));
        a.solver.assert(&if floor { v.ge(&n) } else { v.eq(&n) });
    }

    let root = a.name_of(&root);
    let linear = linearize(a.solver.get_assertions());
    let solver = z3::Solver::new();
    for b in &linear {
        solver.assert(b);
    }
    let scans = a.scans[..own_scans]
        .iter()
        .map(|(s, t, _)| (s.clone(), t.clone()))
        .collect();
    let mut nodes = a.nodes;
    nodes.truncate(own);
    Ok(Analysis {
        root,
        scans,
        plan: query.display_indent().to_string(),
        trace: None,
        constraints: solver.to_string(),
        assertions: linear.len(),
        nodes,
        check_facts: options.check_facts,
    })
}

/// The base tables `plan` scans, subqueries included.
fn tables_of(plan: &LogicalPlan) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let _ = plan.apply_with_subqueries(|p| {
        if let LogicalPlan::TableScan(s) = p {
            out.insert(s.table_name.table().to_string());
        }
        Ok(TreeNodeRecursion::Continue)
    });
    out
}

/// `tables`, and every table one of them references by a foreign key,
/// transitively.
fn reachable(tables: &BTreeSet<String>, options: &Options) -> BTreeSet<String> {
    let mut out = tables.clone();
    loop {
        let more: Vec<String> = options
            .foreign_keys
            .iter()
            .filter(|fk| out.contains(&fk.table) && !out.contains(&fk.references))
            .map(|fk| fk.references.clone())
            .collect();
        if more.is_empty() {
            return out;
        }
        out.extend(more);
    }
}

/// Into `out`: the maximal subtrees of `plan` that scan only tables of
/// `within` (and some), and its unfiltered scans of a table of `bare`.
/// Going up a plan, the tables scanned only grow, so a subtree's are
/// within if its parent's are.
fn maximal<'p>(
    plan: &'p LogicalPlan,
    within: &BTreeSet<String>,
    bare: &BTreeSet<String>,
    out: &mut Vec<&'p LogicalPlan>,
) {
    // Translated, a scan is aliased by its instance.
    let scan = match plan {
        LogicalPlan::SubqueryAlias(a) => a.input.as_ref(),
        p => p,
    };
    if let LogicalPlan::TableScan(s) = scan
        && s.filters.is_empty()
        && bare.contains(s.table_name.table())
    {
        out.push(plan);
        return;
    }
    let l = tables_of(plan);
    if !l.is_empty() && l.is_subset(within) {
        out.push(plan);
        return;
    }
    for c in plan.inputs() {
        maximal(c, within, bare, out);
    }
}

/// `assertions`, linear: every pinned value (`v = n`) substituted, to a
/// fixpoint, and each product left a fresh variable that only linear
/// bounds constrain ([`envelope`]). A product whose factors the linear
/// constraints do not bound stays.
///
/// The result is weaker than `assertions` and still sound: each bound
/// follows from `assertions`, so any of their models extends to one of
/// it, each fresh variable its product's value.
fn linearize(assertions: Vec<Bool>) -> Vec<Bool> {
    // `v = n`, for a variable `v` and a numeral `n`.
    let pin_of = |a: &Bool| -> Option<(Int, Int)> {
        if a.kind() != AstKind::App || a.num_children() != 2 || a.decl().kind() != DeclKind::Eq {
            return None;
        }
        let c = a.children();
        let (v, n) = if is_int_var(&c[0]) && c[1].kind() == AstKind::Numeral {
            (&c[0], &c[1])
        } else if is_int_var(&c[1]) && c[0].kind() == AstKind::Numeral {
            (&c[1], &c[0])
        } else {
            return None;
        };
        Some((v.as_int()?, n.as_int()?))
    };
    let mut pins: Vec<(Int, Int)> = vec![];
    let mut seen = HashSet::new();
    let mut cur = assertions;
    loop {
        let new: Vec<(Int, Int)> = cur
            .iter()
            .filter_map(pin_of)
            .filter(|(v, _)| seen.insert(v.to_string()))
            .collect();
        if new.is_empty() {
            break;
        }
        let subs: Vec<(&Int, &Int)> = new.iter().map(|(v, n)| (v, n)).collect();
        cur = cur
            .iter()
            .map(|a| a.substitute(&subs).simplify())
            .filter(|a| a.as_bool() != Some(true))
            .collect();
        pins.extend(new);
        if cur.iter().any(|a| a.as_bool() == Some(false)) {
            break;
        }
    }
    // Keep the pins themselves: the search reads the root's variable.
    let mut out: Vec<Bool> = pins.iter().map(|(v, n)| v.eq(n)).collect();
    let forms: Vec<Lin> = cur
        .iter()
        .filter_map(|a| linear_le(&Dynamic::from_ast(a), false))
        .flatten()
        .collect();
    let bounds = propagate(&forms);
    let bound = |v: &str| bounds.get(v).copied().unwrap_or((None, None));
    // Every product of two or more variables (and numerals).
    let mut products: Vec<Dynamic> = vec![];
    let mut seen = HashSet::new();
    for a in &cur {
        let mut stack = vec![Dynamic::from_ast(a)];
        while let Some(d) = stack.pop() {
            if d.kind() != AstKind::App || d.num_children() == 0 || !seen.insert(d.clone()) {
                continue;
            }
            let kids = d.children();
            if d.decl().kind() == DeclKind::Mul
                && kids.iter().filter(|k| is_int_var(k)).count() >= 2
                && kids.iter().all(|k| is_int_var(k) || numeral(k).is_some())
            {
                products.push(d.clone());
            }
            stack.extend(kids);
        }
    }
    let mut subs: Vec<(Dynamic, Dynamic)> = vec![];
    let mut lemmas: Vec<Bool> = vec![];
    for (k, m) in products.iter().enumerate() {
        let kids = m.children();
        let coef: i128 = kids.iter().filter_map(numeral).product();
        let vars: Vec<Int> = kids
            .iter()
            .filter(|k| is_int_var(k))
            .map(|k| k.as_int().unwrap())
            .collect();
        let bs: Vec<(Option<i128>, Option<i128>)> =
            vars.iter().map(|v| bound(&v.to_string())).collect();
        if coef <= 0 || bs.iter().any(|(lo, _)| lo.is_none_or(|l| l < 0)) {
            continue;
        }
        let mono = Int::new_const(format!("lin{k}"));
        let Some(mut l) = envelope(&mono, &vars, &bs) else {
            continue;
        };
        lemmas.append(&mut l);
        let rep: Int = if coef == 1 { mono } else { &mono * int(coef) };
        subs.push((m.clone(), Dynamic::from_ast(&rep)));
    }
    let pairs: Vec<(&Dynamic, &Dynamic)> = subs.iter().map(|(a, b)| (a, b)).collect();
    out.extend(cur.iter().map(|a| a.substitute(&pairs)));
    out.extend(lemmas);
    out
}

/// Linear bounds on `mono`, standing for the product of `vars`, which are
/// non-negative with bounds `bs`: `Π ≤ (Π_{i≠j} hi_i) · v_j` and
/// `Π ≥ (Π_{i≠j} lo_i) · v_j` for each `j`, and McCormick's envelope for
/// two factors with both ends known. `None` if no bound but `Π ≥ 0` holds.
fn envelope(mono: &Int, vars: &[Int], bs: &[(Option<i128>, Option<i128>)]) -> Option<Vec<Bool>> {
    let i = int;
    let mut l: Vec<Bool> = vec![mono.ge(Int::from_i64(0))];
    for j in 0..vars.len() {
        let others = (0..vars.len()).filter(|&x| x != j);
        // Π ≤ (Π_{i≠j} hi_i) · v_j, and Π ≥ (Π_{i≠j} lo_i) · v_j.
        let hi: Option<i128> = others.clone().try_fold(1i128, |p, x| {
            p.checked_mul(bs[x].1?).filter(|p| *p < 1 << 62)
        });
        if let Some(h) = hi {
            l.push(mono.le(&vars[j] * i(h)));
        }
        let lo: Option<i128> = others.clone().try_fold(1i128, |p, x| {
            p.checked_mul(bs[x].0?).filter(|p| *p < 1 << 62)
        });
        if let Some(lw) = lo {
            l.push(mono.ge(&vars[j] * i(lw)));
        }
    }
    // McCormick for two factors with both ends known.
    if vars.len() == 2
        && let ((Some(la), Some(ua)), (Some(lb), Some(ub))) = (bs[0], bs[1])
        && ua.checked_mul(ub).is_some_and(|p| p < 1 << 62)
    {
        let (a, b) = (&vars[0], &vars[1]);
        l.push(mono.le(&(b * i(ua)) + &(a * i(lb)) - i(ua * lb)));
        l.push(mono.le(&(b * i(la)) + &(a * i(ub)) - i(la * ub)));
        l.push(mono.ge(&(b * i(la)) + &(a * i(lb)) - i(la * lb)));
        l.push(mono.ge(&(b * i(ua)) + &(a * i(ub)) - i(ua * ub)));
    }
    (l.len() > 1).then_some(l)
}

/// A linear form: coefficients by variable, and a constant.
type Lin = (HashMap<String, i128>, i128);

fn is_int_var(d: &Dynamic) -> bool {
    d.kind() == AstKind::App && d.is_const() && d.sort_kind() == SortKind::Int
}

fn numeral(d: &Dynamic) -> Option<i128> {
    if d.kind() != AstKind::Numeral {
        return None;
    }
    d.to_string().parse::<i128>().ok().or_else(|| {
        // `(- 5)`
        let t = d.to_string();
        t.strip_prefix("(- ")?
            .strip_suffix(')')?
            .parse::<i128>()
            .ok()
            .map(|n| -n)
    })
}

/// `d` as a linear form, if it is one.
fn linear(d: &Dynamic) -> Option<Lin> {
    if let Some(n) = numeral(d) {
        return Some((HashMap::new(), n));
    }
    if is_int_var(d) {
        return Some((HashMap::from([(d.to_string(), 1)]), 0));
    }
    if d.kind() != AstKind::App || d.num_children() == 0 {
        return None;
    }
    let kids = d.children();
    let add = |mut a: Lin, b: Lin, sign: i128| -> Lin {
        for (v, c) in b.0 {
            *a.0.entry(v).or_default() += sign * c;
        }
        a.1 += sign * b.1;
        a
    };
    match d.decl().kind() {
        DeclKind::Add => kids
            .iter()
            .try_fold((HashMap::new(), 0), |acc, k| Some(add(acc, linear(k)?, 1))),
        DeclKind::Sub => {
            let first = linear(&kids[0])?;
            kids[1..]
                .iter()
                .try_fold(first, |acc, k| Some(add(acc, linear(k)?, -1)))
        }
        DeclKind::Uminus => Some(add((HashMap::new(), 0), linear(&kids[0])?, -1)),
        DeclKind::Mul => {
            let mut coef = 1i128;
            let mut rest = None;
            for k in &kids {
                if let Some(n) = numeral(k) {
                    coef = coef.checked_mul(n)?;
                } else if rest.is_none() {
                    rest = Some(linear(k)?);
                } else {
                    return None;
                }
            }
            let (m, c) = rest.unwrap_or((HashMap::new(), 1));
            Some((
                m.into_iter().map(|(v, x)| (v, x * coef)).collect(),
                c * coef,
            ))
        }
        _ => None,
    }
}

/// `a` as linear forms `f ≤ 0`, if it is a linear comparison.
fn linear_le(a: &Dynamic, negated: bool) -> Option<Vec<Lin>> {
    if a.kind() != AstKind::App || a.num_children() == 0 {
        return None;
    }
    let k = a.children();
    let diff = |x: &Dynamic, y: &Dynamic, off: i128| -> Option<Lin> {
        let (mut m, c) = linear(x)?;
        let (n, d) = linear(y)?;
        for (v, c) in n {
            *m.entry(v).or_default() -= c;
        }
        Some((m, c - d + off))
    };
    let kind = a.decl().kind();
    if kind == DeclKind::Not {
        return linear_le(&k[0], !negated);
    }
    if k.len() != 2 {
        return None;
    }
    // x ≤ y is x − y ≤ 0; not(x ≤ y) is y − x + 1 ≤ 0.
    Some(match (kind, negated) {
        (DeclKind::Le, false) | (DeclKind::Gt, true) => vec![diff(&k[0], &k[1], 0)?],
        (DeclKind::Ge, false) | (DeclKind::Lt, true) => vec![diff(&k[1], &k[0], 0)?],
        (DeclKind::Lt, false) | (DeclKind::Ge, true) => vec![diff(&k[0], &k[1], 1)?],
        (DeclKind::Gt, false) | (DeclKind::Le, true) => vec![diff(&k[1], &k[0], 1)?],
        (DeclKind::Eq, false) if k[0].sort_kind() == SortKind::Int => {
            vec![diff(&k[0], &k[1], 0)?, diff(&k[1], &k[0], 0)?]
        }
        _ => return None,
    })
}

/// Bounds on every variable the linear constraints `forms` give, by
/// propagation.
fn propagate(forms: &[Lin]) -> HashMap<String, (Option<i128>, Option<i128>)> {
    let mut b: HashMap<String, (Option<i128>, Option<i128>)> = HashMap::new();
    let cap = 1i128 << 62;
    for _ in 0..30 {
        let mut changed = false;
        for (m, k) in forms {
            // Σ c v + k ≤ 0: c_j v_j ≤ −k − Σ_{i≠j} min(c_i v_i).
            let mins: Vec<Option<i128>> = m
                .iter()
                .map(|(v, &c)| {
                    let (lo, hi) = b.get(v).copied().unwrap_or((None, None));
                    if c > 0 {
                        lo.map(|l| c * l)
                    } else if c < 0 {
                        hi.map(|h| c * h)
                    } else {
                        Some(0)
                    }
                })
                .collect();
            let unknown = mins.iter().filter(|x| x.is_none()).count();
            if unknown > 1 {
                continue;
            }
            let total: i128 = mins.iter().flatten().sum();
            for ((v, &c), mn) in m.iter().zip(&mins) {
                if c == 0 || (unknown == 1 && mn.is_some()) {
                    continue;
                }
                let rest = total - mn.unwrap_or(0);
                let rhs = -k - rest;
                let e = b.entry(v.clone()).or_insert((None, None));
                if c > 0 {
                    let hi = rhs.div_euclid(c);
                    if hi.abs() < cap && e.1.is_none_or(|h| hi < h) {
                        e.1 = Some(hi);
                        changed = true;
                    }
                } else {
                    // c v ≤ rhs, c < 0: v ≥ ⌈rhs / c⌉.
                    let lo = num_ceil(rhs, c);
                    if lo.abs() < cap && e.0.is_none_or(|l| lo > l) {
                        e.0 = Some(lo);
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    b
}

/// ⌈a / b⌉.
fn num_ceil(a: i128, b: i128) -> i128 {
    let (q, r) = (a / b, a % b);
    if r != 0 && ((r > 0) == (b > 0)) {
        q + 1
    } else {
        q
    }
}

/// `n` as a Z3 integer.
fn int(n: i128) -> Int {
    Int::from_i64(n as i64)
}
