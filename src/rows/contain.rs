//! Whether one context has no more rows than another, read off their terms.
//!
//! A fact is about one context, but it also bounds others: dropping a filter
//! can only add rows, so `|σp(C)| ≤ |C|` whatever the data. A fact about a
//! context with more filters is a lower bound on one with fewer, and the
//! reverse an upper bound. Facts are matched to contexts that have no
//! variable of their own in a plan with these; the constraints relate the
//! ones that do.
//!
//! Each test is conservative: `false` loses a bound, `true` must hold for any
//! data.

use std::collections::{BTreeMap, HashMap};

use super::canonical::{MAX_ORDERS, each_order};
use super::{Context, Exists, ExistsKind};
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
        && x.preds.is_superset(&y.preds)
        && y.exists.iter().all(|e| x.exists.iter().any(|f| stricter(f, e)))
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
}
