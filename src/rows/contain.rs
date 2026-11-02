//! Whether one context has no more rows than another, read off their terms.
//!
//! A fact is about one context, but it also bounds others: dropping a filter
//! can only add rows, so `|σp(C)| ≤ |C|` whatever the data. A fact about a
//! context with more or narrower filters (`c < 5` against `c < 10`) is a
//! lower bound on one with fewer or wider, and the reverse an upper bound. Facts are matched to contexts that have no
//! variable of their own in a plan with these; the constraints relate the
//! ones that do.
//!
//! Each test is conservative: `false` loses a bound, `true` must hold for any
//! data.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap};

use datafusion::common::ScalarValue;
use datafusion::logical_expr::{BinaryExpr, Expr, Operator};

use super::canonical::{MAX_ORDERS, each_order};
use super::{Context, Exists, ExistsKind, Term};
use crate::axioms::comparison;
use crate::facts::FactKind;
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
fn implied(preds: &BTreeSet<Term>, q: &Term) -> bool {
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
fn inner_part(c: &Context) -> Option<Context> {
    let Context::Derived { op, args, inputs } = c else { return None };
    if !matches!(op.as_str(), "Left join" | "Full join") || inputs.len() != 2 {
        return None;
    }
    Some(inputs[0].cross(&inputs[1])?.filter(&args.iter().cloned().collect()))
}

/// True if `test(a, b)` holds with `a`'s instances of each table renamed
/// among themselves some way. Canonical contexts number a table's several
/// instances (`t@1`, `t@2`) to make each least, so two related contexts may
/// number the same instances differently. Past `MAX_ORDERS` renamings, only
/// the names as they are are tried.
pub(crate) fn renamed(a: &Context, b: &Context, test: impl Fn(&Context, &Context) -> bool) -> bool {
    if test(a, b) {
        return true;
    }
    let mut groups: BTreeMap<&str, Vec<&String>> = BTreeMap::new();
    let tables = a.tables();
    for t in &tables {
        if let Some((table, _)) = t.split_once('@') {
            groups.entry(table).or_default().push(t);
        }
    }
    let groups: Vec<(&str, Vec<&String>)> = groups.into_iter().collect();
    let orders = groups.iter().try_fold(1usize, |n, (_, g)| (1..=g.len()).try_fold(n, |n, k| n.checked_mul(k)));
    if groups.is_empty() || orders.is_none_or(|n| n > MAX_ORDERS) {
        return false;
    }
    let mut found = false;
    each_order(&groups, 0, &mut vec![], &mut |order| {
        if found {
            return;
        }
        let names: BTreeMap<&str, &str> = groups
            .iter()
            .zip(order)
            .flat_map(|((_, from), to)| from.iter().zip(to).map(|(f, t)| (f.as_str(), t.as_str())))
            .collect();
        let renamed = a.rename(&|r| names.get(r).map(|n| n.to_string()));
        found = test(&renamed, b);
    });
    found
}

/// [`renamed`] for whole facts: true if `test(a, b)` holds with `a`'s
/// instances of each table renamed among themselves some way, its keys
/// with its contexts.
pub(crate) fn renamed_kind(a: &FactKind, b: &FactKind, test: impl Fn(&FactKind, &FactKind) -> bool) -> bool {
    if test(a, b) {
        return true;
    }
    let mut groups: BTreeMap<&str, Vec<&String>> = BTreeMap::new();
    let instances = a.instances();
    for t in &instances {
        if let Some((table, _)) = t.split_once('@') {
            groups.entry(table).or_default().push(t);
        }
    }
    let groups: Vec<(&str, Vec<&String>)> = groups.into_iter().collect();
    let orders = groups.iter().try_fold(1usize, |n, (_, g)| (1..=g.len()).try_fold(n, |n, k| n.checked_mul(k)));
    if groups.is_empty() || orders.is_none_or(|n| n > MAX_ORDERS) {
        return false;
    }
    let mut found = false;
    each_order(&groups, 0, &mut vec![], &mut |order| {
        if found {
            return;
        }
        let names: HashMap<String, String> = groups
            .iter()
            .zip(order)
            .flat_map(|((_, from), to)| from.iter().zip(to).map(|(f, t)| (f.to_string(), t.to_string())))
            .collect();
        found = test(&a.rename(&names), b);
    });
    found
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use datafusion::common::JoinType;
    use datafusion::prelude::{col, lit};

    use super::*;
    use crate::rows::{Term, terms};

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
