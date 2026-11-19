//! Whether one context has no more rows than another, read off their terms.
//!
//! A fact is about one context, but it also bounds others: dropping a filter
//! can only add rows, so `|σp(C)| ≤ |C|` whatever the data. A fact about a
//! context with more or narrower filters (`c < 5` against `c < 10`) is a
//! lower bound on one with fewer or wider, and the reverse an upper bound.
//! Facts are matched to contexts that have no variable of their own in a
//! plan with these; the constraints relate the ones that do.
//!
//! Each test is conservative: `false` loses a bound, `true` must hold for any
//! data.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use datafusion::common::ScalarValue;
use datafusion::logical_expr::{BinaryExpr, Expr, Operator};

use std::sync::Arc;

use super::canonical::{Canonical, Canonicals, MAX_ORDERS, Names, each_order, term_numbered};
use super::{Context, Exists, ExistsKind, Term};
use super::rewrite::Spj;

/// True if `a`'s rows are among `b`'s, as many times or fewer: `a` is `b`
/// with more predicates, more existence conditions, or a semi join's other
/// side narrowed or an anti join's widened (filtering the side an anti join
/// excludes keeps more rows). An outer join's rows include its inner join's.
pub(crate) fn subset(a: &Context, b: &Context) -> bool {
    if a == b {
        return true;
    }
    if let Some(inner) = inner_part(b)
        && subset(a, &inner)
    {
        return true;
    }
    let (x, y) = (Spj::of(a), Spj::of(b));
    x.tables == y.tables
        && x.atoms == y.atoms
        && y.preds.iter().all(|q| x.preds.contains(q) || implied(&x.preds, q))
        && y.exists.iter().all(|e| x.exists.iter().any(|f| stricter(f, e)))
}

/// True if every row passing `preds` passes `q`: `q` compares one
/// expression with literals (a comparison, or an `OR` of them such as an
/// `IN` list), and `preds`' comparisons of it let through only values one of
/// `q`'s does. Those comparisons drop NULL, so a passing row has a value in
/// their interval. Strings are compared only for equality, as their order
/// is the collation's.
pub(crate) fn implied(preds: &BTreeSet<Term>, q: &Term) -> bool {
    let mut disjuncts = vec![];
    let mut todo = vec![&q.expr];
    while let Some(e) = todo.pop() {
        match e {
            Expr::BinaryExpr(BinaryExpr { left, op: Operator::Or, right }) => todo.extend([left.as_ref(), right.as_ref()]),
            e => disjuncts.push(comparison(e)),
        }
    }
    let Some(disjuncts) = disjuncts.into_iter().collect::<Option<Vec<_>>>() else { return false };
    let ordered = |op: Operator, v: &ScalarValue| op == Operator::Eq || !v.data_type().is_string();
    let target = disjuncts[0].0.to_string();
    if disjuncts.iter().any(|(e, op, v)| e.to_string() != target || !ordered(*op, v)) {
        return false;
    }
    let mut have: Option<Interval> = None;
    for p in preds {
        let Some((e, op, v)) = comparison(&p.expr) else { continue };
        if e.to_string() != target {
            continue;
        }
        if !ordered(op, &v) {
            return false;
        }
        let next = Interval::of(op, v);
        have = match have {
            None => Some(next),
            Some(h) => match h.and(&next) {
                Some(both) => Some(both),
                None => return false,
            },
        };
    }
    have.is_some_and(|h| disjuncts.into_iter().any(|(_, op, v)| h.within(&Interval::of(op, v))))
}

/// `e op v`, for a comparison of an expression with a non-NULL literal, the
/// literal on the right as [`Term`] writes it.
pub(crate) fn comparison(e: &Expr) -> Option<(&Expr, Operator, ScalarValue)> {
    let Expr::BinaryExpr(BinaryExpr { left, op, right }) = e else { return None };
    if !matches!(op, Operator::Eq | Operator::Lt | Operator::LtEq | Operator::Gt | Operator::GtEq) {
        return None;
    }
    let v = match right.as_ref() {
        Expr::Literal(v, _) => v.clone(),
        Expr::Cast(c) => match c.expr.as_ref() {
            Expr::Literal(v, _) => v.cast_to(c.field.data_type()).ok()?,
            _ => return None,
        },
        _ => return None,
    };
    (!v.is_null() && !matches!(left.as_ref(), Expr::Literal(..))).then_some((left.as_ref(), *op, v))
}

/// An interval's end: the value, and whether it is let through. `None` is
/// open.
type End = Option<(ScalarValue, bool)>;

/// The values a conjunction of comparisons lets through.
#[derive(Clone)]
struct Interval {
    lo: End,
    hi: End,
}

impl Interval {
    fn of(op: Operator, v: ScalarValue) -> Interval {
        match op {
            Operator::Eq => Interval { lo: Some((v.clone(), true)), hi: Some((v, true)) },
            Operator::Lt => Interval { lo: None, hi: Some((v, false)) },
            Operator::LtEq => Interval { lo: None, hi: Some((v, true)) },
            Operator::Gt => Interval { lo: Some((v, false)), hi: None },
            _ => Interval { lo: Some((v, true)), hi: None },
        }
    }

    /// The values both let through; `None` if their ends do not compare.
    fn and(&self, o: &Interval) -> Option<Interval> {
        // The tighter end: the greater lower end, the lesser upper one.
        let pick = |a: &End, b: &End, tighter: Ordering| -> Option<End> {
            Some(match (a, b) {
                (None, x) | (x, None) => x.clone(),
                (Some((x, xin)), Some((y, yin))) => match x.partial_cmp(y)? {
                    Ordering::Equal => Some((x.clone(), *xin && *yin)),
                    c if c == tighter => Some((x.clone(), *xin)),
                    _ => Some((y.clone(), *yin)),
                },
            })
        };
        Some(Interval { lo: pick(&self.lo, &o.lo, Ordering::Greater)?, hi: pick(&self.hi, &o.hi, Ordering::Less)? })
    }

    /// True if every value `self` lets through, `o` does.
    fn within(&self, o: &Interval) -> bool {
        let end = |mine: &End, theirs: &End, inside: Ordering| match (mine, theirs) {
            (_, None) => true,
            (None, Some(_)) => false,
            (Some((x, xin)), Some((y, yin))) => match x.partial_cmp(y) {
                Some(Ordering::Equal) => *yin || !*xin,
                Some(c) => c == inside,
                None => false,
            },
        };
        end(&self.lo, &o.lo, Ordering::Greater) && end(&self.hi, &o.hi, Ordering::Less)
    }
}

/// True if `|a| ≤ |b|`: `a`'s rows are among `b`'s, or both are outer joins
/// over inputs with that relation. An outer join emits each preserved row
/// once per partner, or once without one, so narrowing either input never
/// adds rows; and a full join keeps all of a left join's rows. Those rows
/// are not all among the other's (a row may lose its partner and be padded
/// instead), so this holds only of the joins themselves, not under a filter.
pub(crate) fn fewer(a: &Context, b: &Context) -> bool {
    if subset(a, b) {
        return true;
    }
    let (Context::Derived { op: oa, args: xa, inputs: ia }, Context::Derived { op: ob, args: xb, inputs: ib }) = (a, b)
    else {
        return false;
    };
    let pairwise = |x: &[Context], y: &[&Context]| x.len() == y.len() && x.iter().zip(y).all(|(x, y)| subset(x, y));
    let either_way = || {
        let fwd: Vec<&Context> = ib.iter().collect();
        let back: Vec<&Context> = ib.iter().rev().collect();
        pairwise(ia, &fwd) || pairwise(ia, &back)
    };
    xa == xb
        && match (oa.as_str(), ob.as_str()) {
            ("Left join", "Left join") => pairwise(ia, &ib.iter().collect::<Vec<_>>()),
            ("Left join" | "Full join", "Full join") => either_way(),
            _ => false,
        }
}

/// True if GROUP BY `a` has no more groups than GROUP BY `b`: the same keys
/// over rows among `b`'s input's ([`subset`]). Fewer rows can only drop
/// groups, so `b`'s distinct count bounds `a`'s.
pub(crate) fn groups_among(a: &Context, b: &Context) -> bool {
    let (Context::Derived { op: oa, args: ka, inputs: ia }, Context::Derived { op: ob, args: kb, inputs: ib }) = (a, b)
    else {
        return false;
    };
    oa == "group" && ob == "group" && ka == kb && ia.len() == 1 && ib.len() == 1 && subset(&ia[0], &ib[0])
}

/// [`subset`]'s test of a condition `f` of the narrower rows against `e`,
/// one of the wider rows'.
fn stricter(f: &Exists, e: &Exists) -> bool {
    f.kind == e.kind
        && f.on == e.on
        && match e.kind {
            ExistsKind::Semi => subset(&f.other, &e.other),
            ExistsKind::Anti | ExistsKind::NotIn => subset(&e.other, &f.other),
        }
}

/// The inner join of an outer join, whose rows are among its own.
pub(crate) fn inner_part(c: &Context) -> Option<Context> {
    let Context::Derived { op, args, inputs } = c else { return None };
    if !matches!(op.as_str(), "Left join" | "Full join") || inputs.len() != 2 {
        return None;
    }
    Some(inputs[0].cross(&inputs[1])?.filter(&args.iter().cloned().collect()))
}

/// True if `test(a, b)` holds with `a`'s instances of each table renamed
/// among themselves some way. Canonical contexts number a table's several
/// instances (`t@1`, `t@2`) to make each least, so two related contexts may
/// number the same instances differently. Only the renamings
/// [`candidates`] finds are tried; past `MAX_ORDERS` renamings, only the
/// names as they are.
#[cfg(test)]
pub(crate) fn renamed(a: &Context, b: &Context, test: impl Fn(&Context, &Context) -> bool) -> bool {
    renamed_in(a, b, test, &mut Canonicals::default())
}

/// [`renamed`], with the canonical forms of the parts it aligns kept in
/// `canonicals`.
pub(crate) fn renamed_in(a: &Context, b: &Context, test: impl Fn(&Context, &Context) -> bool, canonicals: &mut Canonicals) -> bool {
    if test(a, b) {
        return true;
    }
    candidates(a, b, canonicals).iter().any(|names| test(&a.rename(&|r| names.get(r).cloned()), b))
}

/// A renaming being built: each of `a`'s numbered instances renamed so far,
/// to one of the same table's.
type Partial = BTreeMap<String, String>;

/// Every renaming of `a`'s numbered instances among themselves, other than
/// none, under which [`subset`], [`fewer`], [`groups_among`] or same inputs
/// may relate `a` to `b`; empty past `MAX_ORDERS` renamings.
///
/// Each route between contexts needs one part of the renamed `a` equal to
/// one of the context it is compared with, `t`: `b`, the inner join of `b`
/// if an outer join (and so on), or `b` as an SPJ of itself alone.
///
/// | Route | Must be equal |
/// |---|---|
/// | SPJ ⊆ SPJ, same inputs | tables, atoms |
/// | outer join `fewer` | the join condition; inputs ⊆ as SPJs |
/// | [`groups_among`] | the keys; inputs ⊆ as SPJs |
///
/// An atom is equal to another under the renamings that take it to the
/// other's canonical form ([`Canonicals::numbered`]); tables and terms
/// under those that take their names to the other's. Instances no part
/// pins are renamed every way. Predicates and existence conditions need
/// only be covered, so they pin nothing.
pub(crate) fn candidates(a: &Context, b: &Context, canonicals: &mut Canonicals) -> Vec<Names> {
    let tables = a.tables();
    let mut labels: BTreeMap<&str, Vec<&String>> = BTreeMap::new();
    for t in &tables {
        if let Some((table, _)) = t.split_once('@') {
            labels.entry(table).or_default().push(t);
        }
    }
    let groups: Vec<(&str, Vec<&String>)> = labels.into_iter().collect();
    let orders = groups.iter().try_fold(1usize, |n, (_, g)| (1..=g.len()).try_fold(n, |n, k| n.checked_mul(k)));
    if groups.is_empty() || orders.is_none_or(|n| n > MAX_ORDERS) {
        return vec![];
    }
    let space: BTreeSet<&str> = groups.iter().flat_map(|(_, g)| g.iter().map(|t| t.as_str())).collect();
    let mut partials = subset_partials(a, b, canonicals);
    partials.extend(fewer_partials(a, b, canonicals));
    partials.extend(group_partials(a, b, canonicals));
    // Each renamed every way among what no part pinned.
    let mut out: BTreeSet<Vec<(String, String)>> = BTreeSet::new();
    for p in partials {
        if p.iter().any(|(_, to)| !space.contains(to.as_str())) {
            continue;
        }
        complete(&groups, &p, &mut |full| {
            if out.len() < MAX_ORDERS {
                out.insert(full.iter().filter(|(f, t)| f != t).map(|(f, t)| (f.clone(), t.clone())).collect());
            }
        });
    }
    out.into_iter().filter(|m| !m.is_empty()).map(|m| m.into_iter().collect()).collect()
}

/// Calls `f` with `partial` completed every way: each instance of
/// `groups` not renamed yet renamed to one of its table's not taken.
fn complete(groups: &[(&str, Vec<&String>)], partial: &Partial, f: &mut dyn FnMut(&Partial)) {
    let taken: BTreeSet<&String> = partial.values().collect();
    let (mut targets, mut sources) = (vec![], vec![]);
    for (table, g) in groups {
        let from: Vec<&String> = g.iter().copied().filter(|t| !partial.contains_key(*t)).collect();
        let to: Vec<&String> = g.iter().copied().filter(|t| !taken.contains(t)).collect();
        if from.len() != to.len() {
            return;
        }
        if !from.is_empty() {
            targets.push((*table, to));
            sources.push(from);
        }
    }
    // Each order of the free targets, matched to the free sources in order.
    each_order(&targets, 0, &mut vec![], &mut |order| {
        let mut full = partial.clone();
        for (from, to) in sources.iter().zip(order) {
            full.extend(from.iter().zip(to).map(|(f, t)| ((*f).clone(), (*t).clone())));
        }
        f(&full);
    });
}

/// `p` with `q` added, if they rename no instance two ways and no two to
/// one.
fn merge(p: &Partial, q: &Partial) -> Option<Partial> {
    let mut out = p.clone();
    let taken: BTreeSet<&String> = p.values().collect();
    for (f, t) in q {
        match p.get(f) {
            Some(u) if u != t => return None,
            Some(_) => {}
            None if taken.contains(t) => return None,
            None => {
                out.insert(f.clone(), t.clone());
            }
        }
    }
    Some(out)
}

/// Every consistent merge of one of each of `parts`.
fn product(parts: Vec<Vec<Partial>>) -> Vec<Partial> {
    parts.into_iter().fold(vec![Partial::new()], |acc, part| {
        acc.iter().flat_map(|p| part.iter().filter_map(move |q| merge(p, q))).take(MAX_ORDERS).collect()
    })
}

/// The partial renamings under which `a` renamed may be [`subset`] of `b`:
/// with the same tables and atoms as `b`, or as an SPJ of `b` alone, or as
/// the inner join of `b` if an outer join, and so on.
fn subset_partials(a: &Context, b: &Context, canonicals: &mut Canonicals) -> Vec<Partial> {
    let mut out = vec![];
    let mut target = Some(b.clone());
    while let Some(t) = target {
        out.extend(spj_partials(&Spj::of(a), &Spj::of(&t), canonicals));
        target = inner_part(&t);
    }
    out
}

/// The partial renamings of `x`'s instances under which its tables and
/// atoms are `y`'s.
fn spj_partials(x: &Spj, y: &Spj, canonicals: &mut Canonicals) -> Vec<Partial> {
    if x.atoms.len() != y.atoms.len() {
        return vec![];
    }
    // Tables: the same unnumbered ones, and each numbered one to one of
    // `y`'s of its table.
    fn split(s: &Spj) -> (BTreeSet<&String>, BTreeMap<&str, Vec<&String>>) {
        let (mut bare, mut numbered): (BTreeSet<&String>, BTreeMap<&str, Vec<&String>>) = (BTreeSet::new(), BTreeMap::new());
        for t in &s.tables {
            match t.split_once('@') {
                Some((table, _)) => numbered.entry(table).or_default().push(t),
                None => _ = bare.insert(t),
            }
        }
        (bare, numbered)
    }
    let ((xb, xn), (yb, yn)) = (split(x), split(y));
    if xb != yb || xn.keys().ne(yn.keys()) || xn.iter().zip(&yn).any(|((_, f), (_, t))| f.len() != t.len()) {
        return vec![];
    }
    let mut tables = vec![];
    let groups: Vec<(&str, Vec<&String>)> = yn.iter().map(|(t, g)| (*t, g.clone())).collect();
    each_order(&groups, 0, &mut vec![], &mut |order| {
        let p: Partial = xn.values().zip(order).flat_map(|(f, t)| f.iter().zip(t).map(|(f, t)| ((*f).clone(), (*t).clone()))).collect();
        tables.push(p);
    });
    // Atoms: each to one of `y`'s with its canonical form, by a renaming
    // that gives it.
    let xs: Vec<(Arc<Canonical>, &Context)> = x.atoms.iter().map(|a| (canonicals.numbered(a), a)).collect();
    let ys: Vec<Arc<Canonical>> = y.atoms.iter().map(|a| canonicals.numbered(a)).collect();
    let mut out = vec![];
    for p in tables {
        atoms(&xs, &ys, 0, &mut vec![false; ys.len()], p, &mut out);
    }
    out
}

/// Extends `p` to `xs[k..]`, each atom to an unmatched one of `ys` with
/// its canonical form, every way, into `out`.
fn atoms(xs: &[(Arc<Canonical>, &Context)], ys: &[Arc<Canonical>], k: usize, matched: &mut Vec<bool>, p: Partial, out: &mut Vec<Partial>) {
    if out.len() >= MAX_ORDERS {
        return;
    }
    let Some((cx, _)) = xs.get(k) else {
        out.push(p);
        return;
    };
    for j in 0..ys.len() {
        if matched[j] || ys[j].context != cx.context {
            continue;
        }
        // `y`'s instance by canonical name.
        let back: BTreeMap<&String, &String> = ys[j].maps[0].iter().map(|(n, l)| (l, n)).collect();
        matched[j] = true;
        for m in &cx.maps {
            let q: Option<Partial> = m.iter().map(|(n, l)| Some((n.clone(), (*back.get(l)?).clone()))).collect();
            if let Some(next) = q.and_then(|q| merge(&p, &q)) {
                atoms(xs, ys, k + 1, matched, next, out);
            }
        }
        matched[j] = false;
    }
}

/// The partial renamings of `xs`' instances under which they are `ys`, as
/// sets.
fn term_partials(xs: &[Term], ys: &[Term]) -> Vec<Partial> {
    fn go(xs: &[Term], ys: &[Term], used: &mut Vec<bool>, p: Partial, out: &mut Vec<Partial>) {
        let Some((x, rest)) = xs.split_first() else {
            out.push(p);
            return;
        };
        let from = term_numbered(x);
        for j in 0..ys.len() {
            if used[j] {
                continue;
            }
            let to = term_numbered(&ys[j]);
            if to.len() != from.len() {
                continue;
            }
            // Each order of `ys[j]`'s instances, matched to `x`'s in order.
            let mut by: BTreeMap<&str, Vec<&String>> = BTreeMap::new();
            for t in &to {
                by.entry(t.split_once('@').unwrap().0).or_default().push(t);
            }
            let groups: Vec<(&str, Vec<&String>)> = by.into_iter().collect();
            let mut found = vec![];
            each_order(&groups, 0, &mut vec![], &mut |order| {
                let mut q = Partial::new();
                for ((table, _), to) in groups.iter().zip(order) {
                    let from: Vec<&String> = from.iter().filter(|f| f.split_once('@').unwrap().0 == *table).collect();
                    if from.len() != to.len() {
                        return;
                    }
                    q.extend(from.into_iter().zip(to).map(|(f, t)| (f.clone(), (*t).clone())));
                }
                if q.len() == from.len() && x.rename(&|r| q.get(r).cloned()) == ys[j] {
                    found.push(q);
                }
            });
            used[j] = true;
            for q in found {
                if let Some(next) = merge(&p, &q) {
                    go(rest, ys, used, next, out);
                }
            }
            used[j] = false;
        }
    }
    let mut out = vec![];
    if xs.len() == ys.len() {
        go(xs, ys, &mut vec![false; ys.len()], Partial::new(), &mut out);
    }
    out
}

/// The partial renamings under which `a` renamed may have [`fewer`] rows
/// than `b` as outer joins: the same condition, over inputs among `b`'s,
/// either way round for a full join.
fn fewer_partials(a: &Context, b: &Context, canonicals: &mut Canonicals) -> Vec<Partial> {
    let (Context::Derived { op: oa, args: xa, inputs: ia }, Context::Derived { op: ob, args: xb, inputs: ib }) = (a, b) else {
        return vec![];
    };
    let outer = |op: &str| matches!(op, "Left join" | "Full join");
    if !outer(oa) || !outer(ob) || ia.len() != 2 || ib.len() != 2 {
        return vec![];
    }
    let on = term_partials(xa, xb);
    let mut out = vec![];
    for (l, r) in [(&ib[0], &ib[1]), (&ib[1], &ib[0])] {
        let (pl, pr) = (subset_partials(&ia[0], l, canonicals), subset_partials(&ia[1], r, canonicals));
        out.extend(product(vec![on.clone(), pl, pr]));
    }
    out
}

/// The partial renamings under which GROUP BY `a` renamed may have its
/// groups among GROUP BY `b`'s ([`groups_among`]).
fn group_partials(a: &Context, b: &Context, canonicals: &mut Canonicals) -> Vec<Partial> {
    match (a, b) {
        (Context::Derived { op: oa, args: ka, inputs: ia }, Context::Derived { op: ob, args: kb, inputs: ib })
            if oa == "group" && ob == "group" && ia.len() == 1 && ib.len() == 1 =>
        {
            product(vec![term_partials(ka, kb), subset_partials(&ia[0], &ib[0], canonicals)])
        }
        _ => vec![],
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use datafusion::common::JoinType;
    use datafusion::prelude::{col, lit};

    use super::*;
    use crate::rows::{ExistsKind, Term, terms};

    /// SPJs over the same inputs and conditions.
    fn same_inputs(a: &Context, b: &Context) -> bool {
        let (Context::Spj { tables: ta, atoms: aa, exists: ea, .. }, Context::Spj { tables: tb, atoms: ab, exists: eb, .. }) = (a, b) else {
            return false;
        };
        ta == tb && aa == ab && ea == eb
    }

    fn t(name: &str) -> Context {
        Context::table(name)
    }

    fn eq(a: &str, b: &str) -> BTreeSet<Term> {
        terms([col(a).eq(col(b))])
    }

    fn p(c: &str, v: i64) -> BTreeSet<Term> {
        terms([col(c).eq(lit(v))])
    }

    /// `products × sales` joined on their key.
    fn joined() -> Context {
        t("products").cross(&t("sales")).unwrap().filter(&eq("products.id", "sales.product_id"))
    }

    #[test]
    fn filters_narrow() {
        let filtered = joined().filter(&p("products.category", 7));
        assert!(subset(&filtered, &joined()));
        assert!(!subset(&joined(), &filtered));
        let below = t("products").filter(&p("products.category", 7)).cross(&t("sales")).unwrap();
        assert!(subset(&below.filter(&eq("products.id", "sales.product_id")), &joined()));
        // A context over other tables is no narrower.
        assert!(!subset(&t("products"), &joined()));
    }

    #[test]
    fn semi_joins_narrow_with_their_other_side() {
        let on = eq("sales.product_id", "products.id");
        let semi = |other: Context| Context::join(JoinType::LeftSemi, on.clone(), t("sales"), other);
        let narrow = semi(t("products").filter(&p("products.category", 7)));
        assert!(subset(&narrow, &semi(t("products"))));
        assert!(!subset(&semi(t("products")), &narrow));
        // A semi join is a condition: dropping it widens.
        assert!(subset(&semi(t("products")), &t("sales")));
    }

    #[test]
    fn anti_joins_widen_with_their_other_side() {
        let on = eq("sales.product_id", "products.id");
        let anti = |other: Context| Context::join(JoinType::LeftAnti, on.clone(), t("sales"), other);
        let excluded = anti(t("products").filter(&p("products.category", 7)));
        // Excluding fewer products keeps more sales.
        assert!(!subset(&excluded, &anti(t("products"))));
        assert!(subset(&anti(t("products")), &excluded));
        // A filter on the kept side narrows as anywhere.
        assert!(subset(&anti(t("products")).filter(&p("sales.store", 1)), &anti(t("products"))));
    }

    #[test]
    fn outer_joins_shrink_with_either_input() {
        let on = eq("sales.product_id", "products.id");
        let left = |l: Context, r: Context| Context::join(JoinType::Left, on.clone(), l, r);
        let full = left(t("sales"), t("products"));
        let fewer_sales = left(t("sales").filter(&p("sales.store", 1)), t("products"));
        let fewer_products = left(t("sales"), t("products").filter(&p("products.category", 7)));
        assert!(fewer(&fewer_sales, &full));
        assert!(fewer(&fewer_products, &full));
        assert!(!fewer(&full, &fewer_products));
        // A filter that rejects the padded rows leaves the inner join.
        let rejected = full.filter(&p("products.category", 7));
        assert!(matches!(rejected, Context::Spj { .. }));
        assert!(fewer(&rejected, &full));
        // A padded row of the narrower join is no row of the wider: under a
        // filter, the outer join rule does not apply.
        let unmatched = |c: Context| c.filter(&terms([col("products.id").is_null()]));
        assert!(!fewer(&unmatched(fewer_products.clone()), &unmatched(full.clone())));
        // A full join has a left join's rows, and more.
        let both = Context::join(JoinType::Full, on.clone(), t("sales"), t("products"));
        assert!(fewer(&full, &both));
    }

    #[test]
    fn instances_of_one_table_may_be_numbered_apart() {
        let pair = |a: &str, b: &str| {
            t(a).cross(&t(b)).unwrap().filter(&eq(&format!("{a}.manager"), &format!("{b}.id")))
        };
        let wide = pair("emp@1", "emp@2");
        let narrow = pair("emp@2", "emp@1").filter(&p("emp@1.dept", 3));
        assert!(!subset(&narrow, &wide));
        assert!(renamed(&narrow, &wide, subset));
    }

    /// `test(a, b)` under some order of `a`'s numbered instances, trying
    /// every one.
    fn every_order(a: &Context, b: &Context, test: impl Fn(&Context, &Context) -> bool) -> bool {
        let tables = a.tables();
        let mut groups: BTreeMap<&str, Vec<&String>> = BTreeMap::new();
        for t in &tables {
            if let Some((table, _)) = t.split_once('@') {
                groups.entry(table).or_default().push(t);
            }
        }
        let groups: Vec<(&str, Vec<&String>)> = groups.into_iter().collect();
        let mut found = test(a, b);
        each_order(&groups, 0, &mut vec![], &mut |order| {
            let names: BTreeMap<&str, &str> = groups
                .iter()
                .zip(order)
                .flat_map(|((_, from), to)| from.iter().zip(to).map(|(f, t)| (f.as_str(), t.as_str())))
                .collect();
            found = found || test(&a.rename(&|r| names.get(r).map(|n| n.to_string())), b);
        });
        found
    }

    /// Contexts over several instances of `emp`, and of `dept`, each with
    /// its instances renamed every way.
    fn family() -> Vec<Context> {
        let e = |i: u8, c: &str| col(format!("emp@{i}.{c}"));
        let emp = |i: u8| t(&format!("emp@{i}"));
        let manages = |a: u8, b: u8| terms([e(a, "manager").eq(e(b, "id"))]);
        let pair = |a: u8, b: u8| emp(a).cross(&emp(b)).unwrap().filter(&manages(a, b));
        let chain = pair(1, 2).cross(&emp(3)).unwrap().filter(&manages(2, 3));
        let group = |i: u8, c: Context| Context::Derived { op: "group".into(), args: vec![Term::new(e(i, "dept"))], inputs: vec![c] };
        let left = |l: Context, r: Context| Context::join(JoinType::Left, manages(1, 2), l, r);
        let full = |l: Context, r: Context| Context::join(JoinType::Full, manages(1, 2), l, r);
        let dept = |i: u8, c: Context| c.cross(&t("dept")).unwrap().filter(&terms([e(i, "dept").eq(col("dept.id"))]));
        let base = vec![
            pair(1, 2),
            pair(1, 2).filter(&p("emp@1.dept", 3)),
            pair(1, 2).filter(&p("emp@2.dept", 3)),
            emp(1).cross(&emp(2)).unwrap(),
            emp(1).cross(&emp(2)).unwrap().filter(&p("emp@2.level", 1)),
            chain.clone(),
            chain.filter(&p("emp@3.level", 1)),
            chain.filter(&terms([e(1, "level").lt(lit(5))])),
            chain.filter(&terms([e(1, "level").lt(lit(9))])),
            dept(2, pair(1, 2)),
            dept(1, pair(1, 2).filter(&p("emp@2.level", 1))),
            emp(1).cross(&group(2, emp(2))).unwrap().filter(&terms([e(1, "dept").eq(e(2, "dept"))])),
            emp(1).cross(&group(2, emp(2).filter(&p("emp@2.level", 1)))).unwrap().filter(&terms([e(1, "dept").eq(e(2, "dept"))])),
            emp(3).cross(&group(2, pair(1, 2))).unwrap().filter(&terms([e(3, "dept").eq(e(2, "dept"))])),
            group(1, pair(1, 2)),
            group(1, pair(1, 2).filter(&p("emp@2.level", 1))),
            group(2, pair(1, 2)),
            left(emp(1), emp(2)),
            left(emp(1).filter(&p("emp@1.level", 1)), emp(2)),
            left(emp(1), emp(2).filter(&p("emp@2.level", 1))),
            full(emp(1), emp(2)),
            full(emp(1), emp(2).filter(&p("emp@2.level", 1))),
            left(emp(1), emp(2)).filter(&p("emp@2.level", 1)),
            emp(1).exists(ExistsKind::Semi, manages(2, 1), emp(2)),
            emp(1).exists(ExistsKind::Semi, manages(2, 1), emp(2).filter(&p("emp@2.level", 1))),
            emp(1).exists(ExistsKind::Anti, manages(2, 1), emp(2).filter(&p("emp@2.level", 1))),
            emp(1).exists(ExistsKind::Anti, manages(2, 1), emp(2)),
            emp(1).cross(&emp(3)).unwrap().exists(ExistsKind::Semi, manages(2, 1), emp(2)),
        ];
        let mut out = BTreeSet::new();
        for c in base {
            let tables = c.tables();
            let mut groups: BTreeMap<&str, Vec<&String>> = BTreeMap::new();
            for t in &tables {
                if let Some((table, _)) = t.split_once('@') {
                    groups.entry(table).or_default().push(t);
                }
            }
            let groups: Vec<(&str, Vec<&String>)> = groups.into_iter().collect();
            each_order(&groups, 0, &mut vec![], &mut |order| {
                let names: BTreeMap<&str, &str> = groups
                    .iter()
                    .zip(order)
                    .flat_map(|((_, from), to)| from.iter().zip(to).map(|(f, t)| (f.as_str(), t.as_str())))
                    .collect();
                out.insert(c.rename(&|r| names.get(r).map(|n| n.to_string())));
            });
        }
        out.into_iter().collect()
    }

    #[test]
    fn candidate_renamings_relate_as_every_order() {
        let family = family();
        let mut canonicals = Canonicals::default();
        let (mut pairs, mut related, mut renaming, mut tried, mut orders) = (0, 0, 0, 0, 0);
        for a in &family {
            for b in family.iter().filter(|b| b.tables() == a.tables() && *b != a) {
                pairs += 1;
                let tests: [(&str, fn(&Context, &Context) -> bool); 4] =
                    [("subset", subset), ("fewer", fewer), ("groups among", groups_among), ("same inputs", same_inputs)];
                for (name, test) in tests {
                    let all = every_order(a, b, test);
                    assert_eq!(renamed_in(a, b, test, &mut canonicals), all, "{name}: {a}  vs  {b}");
                    related += all as usize;
                    renaming += (all && !test(a, b)) as usize;
                }
                tried += candidates(a, b, &mut canonicals).len();
                let n = a.tables().iter().filter(|t| t.contains('@')).count();
                orders += (1..=n).product::<usize>() - 1;
            }
        }
        assert!(pairs > 500 && related > 200 && renaming > 100, "{pairs} pairs, {related} related, {renaming} only renamed");
        // Fewer renamings than every order.
        assert!(tried * 2 < orders, "{tried} candidates of {orders} renamings");
    }

    #[test]
    fn narrower_ranges_imply_wider_ones() {
        let f = |e: datafusion::logical_expr::Expr| t("lineitem").filter(&terms([e]));
        let q = "lineitem.l_quantity";
        assert!(subset(&f(col(q).lt(lit(5))), &f(col(q).lt(lit(10)))));
        assert!(subset(&f(col(q).lt_eq(lit(9))), &f(col(q).lt(lit(10)))));
        assert!(!subset(&f(col(q).lt_eq(lit(10))), &f(col(q).lt(lit(10)))));
        assert!(!subset(&f(col(q).lt(lit(10))), &f(col(q).lt(lit(5)))));
        assert!(subset(&f(col(q).eq(lit(3))), &f(col(q).gt_eq(lit(3)))));
        assert!(subset(&f(col(q).eq(lit(3))), &f(col(q).in_list(vec![lit(1), lit(3)], false))));
        let both = t("lineitem").filter(&terms([col(q).gt(lit(2)), col(q).lt(lit(4))]));
        assert!(subset(&both, &f(col(q).gt(lit(1)))));
        assert!(!subset(&both, &f(col(q).gt(lit(2)).and(col(q).lt(lit(3))))));
        // Other columns, other types, and strings' order are not compared.
        assert!(!subset(&f(col("lineitem.l_tax").lt(lit(5))), &f(col(q).lt(lit(10)))));
        assert!(!subset(&f(col(q).lt(lit(5i32))), &f(col(q).lt(lit(10i64)))));
        assert!(!subset(&f(col(q).lt(lit("a"))), &f(col(q).lt(lit("b")))));
        assert!(subset(&f(col(q).eq(lit("a"))), &f(col(q).in_list(vec![lit("a"), lit("b")], false))));
    }
}
