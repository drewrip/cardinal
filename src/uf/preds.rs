//! Predicates as terms (§5), and the facts about them Z3 decides (§6.2).
//!
//! Every decision is made in SQL's three-valued logic, with each column
//! possibly NULL: `implies(p, q)` means that wherever `p` is TRUE, so is
//! `q`, and `neg p` is SQL's `NOT p`. So the facts hold over any data, and
//! `filter p` and `filter (neg p)` split a relation only where `p`'s
//! columns are known non-NULL (`filter_complement`).

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Mutex;

use z3::{Optimize, Params, SatResult, Solver};

use super::expr::{Cmp, Col, E, Lit, Smt, Ty, flat_and, flat_or};
use super::terms::{AtomOp, Pred, PredId, Terms};

/// The predicates of `e`'s top-level conjunction, `e` a predicate.
pub(crate) fn conjuncts(terms: &mut Terms, e: &E) -> Vec<PredId> {
    let e = e.nnf(false);
    let parts = match e {
        E::And(xs) => xs,
        e => vec![e],
    };
    let mut out: Vec<PredId> = parts.iter().map(|p| make(terms, p)).collect();
    // Atoms sorted by column, operator, literal and negation, then compound
    // predicates by their text (§5).
    out.sort_by_cached_key(|p| order(terms, *p));
    out.dedup();
    out
}

fn order(terms: &Terms, p: PredId) -> (u8, String) {
    match terms.get_pred(p) {
        Pred::Atom { .. } => (0, terms.pred_text(p)),
        Pred::Neg(q) => (0, format!("{}~", terms.pred_text(*q))),
        _ => (1, terms.pred_text(p)),
    }
}

/// The predicate term for `e`, a predicate in negation normal form.
pub(crate) fn make(terms: &mut Terms, e: &E) -> PredId {
    if let E::Lit(Lit::Bool(b), _) = e {
        return terms.pred(if *b { Pred::True } else { Pred::False });
    }
    if let Some((col, op, lit, ty, negated)) = atom(e) {
        let p = terms.pred(Pred::Atom { col, op, lit, ty });
        return if negated { terms.pred(Pred::Neg(p)) } else { p };
    }
    let e = e.sorted();
    terms.pred(Pred::Compound(e.text(), e))
}

/// `e` as an atom `col op lit` in its positive form, and whether it is
/// negated: `a <= 1` is `NOT a > 1`.
fn atom(e: &E) -> Option<(Col, AtomOp, Lit, Ty, bool)> {
    let E::Cmp(op, a, b) = e else { return None };
    let (col, ty, lit, op) = match (a.as_ref(), b.as_ref()) {
        (E::Col(c, t), E::Lit(l, _)) => (c, *t, l, *op),
        (E::Lit(l, _), E::Col(c, t)) => (c, *t, l, op.flip()),
        _ => return None,
    };
    if matches!(lit, Lit::Null | Lit::Bool(_)) {
        return None;
    }
    // Strings only with `=`; numbers with any comparison.
    match (ty, lit) {
        (Ty::Int | Ty::Real, Lit::Int(_) | Lit::Dec(..)) => {}
        (Ty::Str, Lit::Str(_)) if matches!(op, Cmp::Eq | Cmp::Ne) => {}
        _ => return None,
    }
    let (op, negated) = match op {
        Cmp::Gt => (AtomOp::Gt, false),
        Cmp::Ge => (AtomOp::Ge, false),
        Cmp::Eq => (AtomOp::Eq, false),
        Cmp::Le => (AtomOp::Gt, true),
        Cmp::Lt => (AtomOp::Ge, true),
        Cmp::Ne => (AtomOp::Eq, true),
    };
    Some((col.clone(), op, lit.clone(), ty, negated))
}

/// `p` as an expression, if it is a literal (an atom, a compound, or the
/// negation of one).
pub(crate) fn expr_of(terms: &Terms, p: PredId) -> Option<E> {
    Some(match terms.get_pred(p) {
        Pred::Atom { col, op, lit, ty } => {
            let c = match op {
                AtomOp::Gt => Cmp::Gt,
                AtomOp::Ge => Cmp::Ge,
                AtomOp::Eq => Cmp::Eq,
            };
            let lt = match lit {
                Lit::Str(_) => Ty::Str,
                _ => *ty,
            };
            E::Cmp(c, Box::new(E::Col(col.clone(), *ty)), Box::new(E::Lit(lit.clone(), lt)))
        }
        Pred::Neg(q) => E::Not(Box::new(expr_of(terms, *q)?)),
        Pred::Compound(_, e) => e.clone(),
        Pred::True => E::Lit(Lit::Bool(true), Ty::Bool),
        Pred::False => E::Lit(Lit::Bool(false), Ty::Bool),
        _ => return None,
    })
}

/// A disjunction's or conjunction's chain links (§6.2): `p = d₁ ∨ p₂`,
/// `p₂ = d₂ ∨ p₃`, ..., each `pᵢ` the compound of the remaining parts.
pub(crate) struct Link {
    pub or: bool,
    pub p: PredId,
    pub first: PredId,
    pub rest: PredId,
}

/// The links of every chain under `p`, adding the predicates they need.
pub(crate) fn chains(terms: &mut Terms, p: PredId, out: &mut Vec<Link>, seen: &mut BTreeSet<PredId>) {
    if !seen.insert(p) {
        return;
    }
    let Pred::Compound(_, e) = terms.get_pred(p).clone() else { return };
    let (or, parts) = match e {
        E::Or(xs) => (true, xs),
        E::And(xs) => (false, xs),
        _ => return,
    };
    let first = make(terms, &parts[0]);
    let rest_e = if or { flat_or(parts[1..].to_vec()) } else { flat_and(parts[1..].to_vec()) };
    let rest = make(terms, &rest_e);
    out.push(Link { or, p, first, rest });
    chains(terms, first, out, seen);
    chains(terms, rest, out, seen);
}

/// What Z3 decided about a set of predicate literals.
#[derive(Default)]
pub(crate) struct Decided {
    /// `implies(p, q)`, between representatives.
    pub implies: Vec<(PredId, PredId)>,
    /// `p = q`: each merged literal with its representative.
    pub equal: Vec<(PredId, PredId)>,
    /// Literals FALSE on every row (so never TRUE, and their negations
    /// TRUE on every row).
    pub never: Vec<PredId>,
    /// Literals never TRUE, but NULL on some rows: no constant, since
    /// their negations are not TRUE on every row (`x = NULL`, `NULL`).
    pub empty: Vec<PredId>,
    /// Literals TRUE on every row.
    pub always: Vec<PredId>,
    /// Each literal's facts.
    pub facts: HashMap<PredId, Facts>,
    /// Literals NULL only where a column they read is (`total`).
    pub total: Vec<PredId>,
}

/// What one literal says about the rows it keeps.
#[derive(Debug, Clone, Default, PartialEq)]
pub(crate) struct Facts {
    /// At most this many tuples of its columns make it TRUE, if ≤ 64.
    pub width: Option<u64>,
    /// Columns it is TRUE only where non-NULL.
    pub nonnull: BTreeSet<Col>,
    /// Each numeric column's values where it is TRUE, if bounded on a side.
    pub hull: BTreeMap<Col, Hull>,
}

#[derive(Debug, Clone, Default, PartialEq)]
pub(crate) struct Hull {
    pub ty: Option<Ty>,
    /// The infimum, as a fraction, and whether it is excluded.
    pub lo: Option<((i128, i128), bool)>,
    pub hi: Option<((i128, i128), bool)>,
}

/// Decisions are pure functions of the predicates' text, so they are
/// shared by every session.
#[derive(Default)]
struct Cache {
    implies: HashMap<(String, String), bool>,
    facts: HashMap<String, Option<Facts>>,
}

static CACHE: Mutex<Option<Cache>> = Mutex::new(None);

/// Per-check time limit for decisions, in milliseconds.
const DECIDE_MS: u32 = 2_000;

fn solver() -> Solver {
    let s = Solver::new();
    let mut p = Params::new();
    p.set_u32("timeout", DECIDE_MS);
    s.set_params(&p);
    s
}

/// Decides the facts of §6.2 about `literals`.
pub(crate) fn decide(terms: &Terms, literals: &[PredId]) -> Decided {
    let mut out = Decided::default();
    // Each literal's expression, SMT and columns.
    let mut smt = Smt::default();
    let mut lits: Vec<(PredId, E, String, String, BTreeSet<Col>)> = vec![];
    for &p in literals {
        let Some(e) = expr_of(terms, p) else { continue };
        let Some(t) = smt.truth(&e) else { continue };
        lits.push((p, e.clone(), t.t, t.f, e.reads()));
    }
    let decls = smt.declarations();
    let mut cache = CACHE.lock().unwrap();
    let cache = cache.get_or_insert_with(Cache::default);

    // Constants.
    let s = solver();
    s.from_string(decls.clone());
    let check = |s: &Solver, f: &str| {
        s.push();
        s.from_string(format!("(assert {f})"));
        let r = s.check();
        s.pop(1);
        r
    };
    let mut constant: HashMap<PredId, bool> = HashMap::new();
    for (p, _, t, f, _) in &lits {
        let key = (t.clone(), "#never".to_string());
        let never = *cache.implies.entry(key).or_insert_with(|| check(&s, t) == SatResult::Unsat);
        let key = (t.clone(), "#always".to_string());
        let always = *cache.implies.entry(key).or_insert_with(|| check(&s, &format!("(not {t})")) == SatResult::Unsat);
        let key = (f.clone(), "#always".to_string());
        let false_always = never && *cache.implies.entry(key).or_insert_with(|| check(&s, &format!("(not {f})")) == SatResult::Unsat);
        if never && false_always {
            out.never.push(*p);
            constant.insert(*p, false);
        } else if never {
            out.empty.push(*p);
            constant.insert(*p, false);
        } else if always {
            out.always.push(*p);
            constant.insert(*p, true);
        }
    }

    // Implications between literals that read a common column.
    let mut implied: BTreeSet<(usize, usize)> = BTreeSet::new();
    for i in 0..lits.len() {
        for j in 0..lits.len() {
            if i == j || lits[i].4.is_disjoint(&lits[j].4) {
                continue;
            }
            if constant.contains_key(&lits[i].0) || constant.contains_key(&lits[j].0) {
                continue;
            }
            let key = (lits[i].2.clone(), lits[j].2.clone());
            let holds = *cache
                .implies
                .entry(key)
                .or_insert_with(|| check(&s, &format!("(and {} (not {}))", lits[i].2, lits[j].2)) == SatResult::Unsat);
            if holds {
                implied.insert((i, j));
            }
        }
    }
    // Literals that imply each other, and whose negations do, are one
    // constant: the least by id. (`a = 2` and `a = 2 OR NULL` are TRUE on
    // the same rows, but their negations are not: one term would make
    // them so.)
    let mut rep: Vec<usize> = (0..lits.len()).collect();
    for &(i, j) in &implied {
        if i < j && implied.contains(&(j, i)) {
            let (fi, fj) = (&lits[i].3, &lits[j].3);
            let key = (format!("#f{fi}"), fj.clone());
            let same = *cache.implies.entry(key).or_insert_with(|| {
                check(&s, &format!("(and {fi} (not {fj}))")) == SatResult::Unsat
                    && check(&s, &format!("(and {fj} (not {fi}))")) == SatResult::Unsat
            });
            if !same {
                continue;
            }
            let (a, b) = (find(&mut rep, i), find(&mut rep, j));
            if a != b {
                rep[a.max(b)] = a.min(b);
            }
        }
    }
    for i in 0..lits.len() {
        let r = find(&mut rep, i);
        if r != i {
            out.equal.push((lits[i].0, lits[r].0));
        }
    }
    for &(i, j) in &implied {
        let (a, b) = (find(&mut rep, i), find(&mut rep, j));
        if a == i && b == j {
            out.implies.push((lits[i].0, lits[j].0));
        }
    }

    // Literals TRUE or FALSE wherever their columns are non-NULL.
    for (p, e, t, f, reads) in &lits {
        let key = (format!("#total{t}"), f.clone());
        let total = *cache.implies.entry(key).or_insert_with(|| {
            let mut smt = Smt::default();
            let mut known = vec!["true".to_string()];
            e.visit(&mut |x| {
                if let E::Col(c, ty) = x
                    && reads.contains(c)
                {
                    known.push(format!("(not {})", smt.var(c, *ty).null));
                }
            });
            check(&s, &format!("(and {} (not {t}) (not {f}))", known.join(" "))) == SatResult::Unsat
        });
        if total {
            out.total.push(*p);
        }
    }
    // Each literal's width, NULL-rejected columns and hull.
    for (p, e, t, _, reads) in &lits {
        if constant.contains_key(p) {
            continue;
        }
        let key = t.clone();
        let facts = cache.facts.entry(key).or_insert_with(|| facts(&s, &decls, e, t, reads)).clone();
        if let Some(f) = facts {
            out.facts.insert(*p, f);
        }
    }
    out
}

fn find(rep: &mut [usize], i: usize) -> usize {
    let mut r = i;
    while rep[r] != r {
        r = rep[r];
    }
    rep[i] = r;
    r
}

/// The width, non-NULL columns and hull of a literal TRUE where `t` holds.
fn facts(s: &Solver, decls: &str, e: &E, t: &str, reads: &BTreeSet<Col>) -> Option<Facts> {
    let mut smt = Smt::default();
    let mut out = Facts::default();
    let mut types: BTreeMap<Col, Ty> = BTreeMap::new();
    e.visit(&mut |x| {
        if let E::Col(c, ty) = x {
            types.insert(c.clone(), *ty);
        }
    });
    for c in reads {
        let v = smt.var(c, types[c]);
        s.push();
        s.from_string(format!("(assert (and {t} {}))", v.null));
        if s.check() == SatResult::Unsat {
            out.nonnull.insert(c.clone());
        }
        s.pop(1);
    }
    // Width: tuples of its columns, enumerated, when all are non-NULL.
    if out.nonnull.len() == reads.len() && !reads.is_empty() && reads.iter().all(|c| types[c] != Ty::Other) {
        out.width = width(s, t, reads, &types);
    }
    // Hull: each numeric column's infimum and supremum.
    for c in reads {
        let ty = types[c];
        if !ty.numeric() {
            continue;
        }
        let v = smt.var(c, ty).v;
        let lo = optimum(decls, t, &v, ty, false);
        let hi = optimum(decls, t, &v, ty, true);
        if lo.is_some() || hi.is_some() {
            out.hull.insert(c.clone(), Hull { ty: Some(ty), lo, hi });
        }
    }
    Some(out)
}

/// How many tuples of `reads` satisfy `t`, if at most 64.
fn width(s: &Solver, t: &str, reads: &BTreeSet<Col>, types: &BTreeMap<Col, Ty>) -> Option<u64> {
    s.push();
    s.from_string(format!("(assert {t})"));
    let mut n = 0;
    let result = loop {
        match s.check() {
            SatResult::Sat => {}
            SatResult::Unsat => break Some(n),
            SatResult::Unknown => break None,
        }
        n += 1;
        if n > 64 {
            break None;
        }
        let model = s.get_model()?;
        let mut differ = vec![];
        for c in reads {
            let name = format!("|v!{c}|");
            let var: z3::ast::Dynamic = match types[c] {
                Ty::Int => z3::ast::Int::new_const(name.trim_matches('|')).into(),
                Ty::Real => z3::ast::Real::new_const(name.trim_matches('|')).into(),
                Ty::Str => z3::ast::String::new_const(name.trim_matches('|')).into(),
                Ty::Bool => z3::ast::Bool::new_const(name.trim_matches('|')).into(),
                Ty::Other => break,
            };
            let value = model.eval(&var, true)?;
            differ.push(format!("(not (= {name} {value}))"));
        }
        s.from_string(format!("(assert (or {}))", differ.join(" ")));
    };
    s.pop(1);
    result
}

/// The least (or greatest, with `max`) value of `v` where `t` holds, and
/// whether it is not attained; `None` if unbounded or undecided.
fn optimum(decls: &str, t: &str, v: &str, ty: Ty, max: bool) -> Option<((i128, i128), bool)> {
    let o = Optimize::new();
    let mut p = Params::new();
    p.set_u32("timeout", DECIDE_MS);
    o.set_params(&p);
    let goal = if max { "maximize" } else { "minimize" };
    o.from_string(format!("{decls}(assert {t})\n({goal} {v})"));
    if o.check(&[]) != SatResult::Sat {
        return None;
    }
    let bound = if max { o.get_upper(0)? } else { o.get_lower(0)? };
    let text = bound.to_string();
    if text.contains("oo") {
        return None;
    }
    let strict = text.contains("epsilon");
    let value = parse_number(&text.replace("epsilon", "0"))?;
    // An Int column's optimum is attained.
    let strict = strict && ty == Ty::Real;
    Some((value, strict))
}

/// A number as Z3 prints it: `5`, `(- 5)`, `(/ 1 2)`, `2.5`, `(+ 5 0)`.
pub(crate) fn parse_number(s: &str) -> Option<(i128, i128)> {
    let tokens: Vec<String> = s.replace('(', " ( ").replace(')', " ) ").split_whitespace().map(str::to_string).collect();
    let mut i = 0;
    let r = expr(&tokens, &mut i)?;
    (i == tokens.len()).then_some(r)
}

fn expr(t: &[String], i: &mut usize) -> Option<(i128, i128)> {
    let tok = t.get(*i)?.clone();
    *i += 1;
    if tok != "(" {
        return atom_number(&tok);
    }
    let op = t.get(*i)?.clone();
    *i += 1;
    let mut args = vec![];
    while t.get(*i)? != ")" {
        args.push(expr(t, i)?);
    }
    *i += 1;
    let reduce = |n: i128, d: i128| {
        let g = gcd(n.unsigned_abs(), d.unsigned_abs()) as i128;
        (n / g, d / g)
    };
    match (op.as_str(), &args[..]) {
        ("-", [(n, d)]) => Some((-n, *d)),
        ("-", [(a, b), (c, d)]) => Some(reduce(a.checked_mul(*d)?.checked_sub(c.checked_mul(*b)?)?, b.checked_mul(*d)?)),
        ("+", xs) => xs.iter().try_fold((0i128, 1i128), |(a, b), (c, d)| {
            Some(reduce(a.checked_mul(*d)?.checked_add(c.checked_mul(b)?)?, b.checked_mul(*d)?))
        }),
        ("/", [(a, b), (c, d)]) if *c != 0 => {
            let (n, m) = (a.checked_mul(*d)?, b.checked_mul(*c)?);
            let (n, m) = if m < 0 { (-n, -m) } else { (n, m) };
            Some(reduce(n, m))
        }
        ("*", [(a, b), (c, d)]) => Some(reduce(a.checked_mul(*c)?, b.checked_mul(*d)?)),
        _ => None,
    }
}

fn atom_number(s: &str) -> Option<(i128, i128)> {
    if let Some((w, f)) = s.split_once('.') {
        let den = 10i128.checked_pow(f.len() as u32)?;
        let n: i128 = format!("{w}{f}").parse().ok()?;
        let g = gcd(n.unsigned_abs(), den as u128) as i128;
        return Some((n / g, den / g));
    }
    Some((s.parse().ok()?, 1))
}

fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a.max(1)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn col(c: &str) -> Box<E> {
        Box::new(E::Col(c.into(), Ty::Int))
    }

    fn int(n: i128) -> Box<E> {
        Box::new(E::Lit(Lit::Int(n), Ty::Int))
    }

    #[test]
    fn numbers() {
        assert_eq!(parse_number("5"), Some((5, 1)));
        assert_eq!(parse_number("(- 5)"), Some((-5, 1)));
        assert_eq!(parse_number("(/ 1.0 2.0)"), Some((1, 2)));
        assert_eq!(parse_number("(+ 5.0 0)"), Some((5, 1)));
    }

    #[test]
    fn decisions() {
        let mut t = Terms::default();
        let gt5 = make(&mut t, &E::Cmp(Cmp::Gt, col("foo.a"), int(5)));
        let gt1 = make(&mut t, &E::Cmp(Cmp::Gt, col("foo.a"), int(1)));
        let ge2 = make(&mut t, &E::Cmp(Cmp::Ge, col("foo.a"), int(2)));
        let le1 = make(&mut t, &E::Cmp(Cmp::Le, col("foo.a"), int(1)));
        let inl = make(
            &mut t,
            &flat_or(vec![E::Cmp(Cmp::Eq, col("foo.a"), int(1)), E::Cmp(Cmp::Eq, col("foo.a"), int(2))]),
        );
        let m3 = make(
            &mut t,
            &E::Cmp(Cmp::Gt, Box::new(E::Arith(super::super::expr::Arith::Mod, col("foo.a"), int(3), Ty::Int)), int(2)),
        );
        let d = decide(&t, &[gt5, gt1, ge2, le1, inl, m3]);
        assert!(d.implies.contains(&(gt5, gt1)) || d.implies.contains(&(gt5, ge2.min(gt1))));
        assert!(d.equal.contains(&(ge2, gt1)) || d.equal.contains(&(gt1, ge2)));
        // Never TRUE, but NULL where `a` is: no constant.
        assert!(d.empty.contains(&m3) && !d.never.contains(&m3));
        assert_eq!(d.facts[&inl].width, Some(2));
        let h = &d.facts[&inl].hull["foo.a"];
        assert_eq!((h.lo, h.hi), (Some(((1, 1), false)), Some(((2, 1), false))));
        assert!(d.facts[&le1].nonnull.contains("foo.a"));
    }

    /// `a IN (2, NULL)` is TRUE where `a = 2` is, but never FALSE: the two
    /// are no one predicate, or `NOT a = 2` would keep nothing. Nor is
    /// `NULL` the constant `false`, whose negation keeps every row.
    #[test]
    fn null_three_valued() {
        let mut t = Terms::default();
        let eq2 = E::Cmp(Cmp::Eq, col("foo.a"), int(2));
        let null = E::Lit(Lit::Null, Ty::Bool);
        let p = make(&mut t, &eq2);
        let q = make(&mut t, &flat_or(vec![eq2.clone(), null.clone()]));
        let n = make(&mut t, &null);
        let lits: Vec<PredId> = [p, q, n].iter().flat_map(|x| [*x, t.pred(Pred::Neg(*x))]).collect();
        let d = decide(&t, &lits);
        assert!(d.implies.contains(&(p, q)) && d.implies.contains(&(q, p)));
        assert!(d.equal.is_empty());
        assert!(d.empty.contains(&n) && d.empty.contains(&t.pred(Pred::Neg(n))) && d.never.is_empty());
    }
}
