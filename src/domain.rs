//! Value domains: which values an expression can take on the rows of a relation.
//!
//! Filters and join conditions only pass rows on which they evaluate to TRUE, so
//! every row above them satisfies facts such as `x BETWEEN 1 AND 10` or
//! `name IN ('a', 'b')`. A domain records these as a range of integers or a
//! finite set of values, plus whether NULL can occur. Domains flow up the plan
//! with the columns they describe, and bound NDVs: a column whose values lie in
//! a domain of `k` values has at most `k` distinct values. An empty domain means
//! the relation has no rows at all.
//!
//! Only data-independent reasoning is used: a fact holds on every database.

use std::collections::BTreeSet;

use datafusion::arrow::datatypes::{DataType, TimeUnit};
use datafusion::common::tree_node::{Transformed, TreeNode};
use datafusion::common::{Column, DFSchema, ScalarValue};
use datafusion::logical_expr::utils::split_conjunction;
use datafusion::logical_expr::{
    Between, BinaryExpr, Case, Cast, Expr, ExprSchemable, Operator, TryCast,
};

/// A non-NULL value, compared by SQL equality. Integers, dates and decimals of
/// one scale are all integers here: a domain only ever describes one type.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Key {
    Int(i128),
    Str(String),
    Bool(bool),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Vals {
    /// Any value of the type.
    Any,
    /// The integers in `lo..=hi`, either end possibly open.
    Range(Option<i128>, Option<i128>),
    /// Exactly these values (possibly none).
    Set(BTreeSet<Key>),
    /// At most this many values, not known which: an expression compared
    /// with a query parameter or a scalar subquery.
    Count(u128),
}

/// Integer ranges with fewer values are kept as sets.
const SMALL: i128 = 64;

/// An over-approximation of the values an expression takes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Dom {
    vals: Vals,
    null: bool,
}

impl Dom {
    pub(crate) fn top() -> Dom {
        Dom {
            vals: Vals::Any,
            null: true,
        }
    }

    pub(crate) fn non_null() -> Dom {
        Dom {
            vals: Vals::Any,
            null: false,
        }
    }

    /// No values at all, not even NULL.
    pub(crate) fn nothing() -> Dom {
        Dom {
            vals: Vals::Set(BTreeSet::new()),
            null: false,
        }
    }

    fn null_only() -> Dom {
        Dom {
            vals: Vals::Set(BTreeSet::new()),
            null: true,
        }
    }

    /// At most `n` values, not known which.
    fn count(n: u128) -> Dom {
        Dom {
            vals: Vals::Count(n),
            null: false,
        }
        .normalized()
    }

    fn values(vals: &Vals) -> Dom {
        Dom {
            vals: vals.clone(),
            null: false,
        }
    }

    fn range(lo: Option<i128>, hi: Option<i128>) -> Dom {
        Dom {
            vals: Vals::Range(lo, hi),
            null: false,
        }
        .normalized()
    }

    fn set(keys: impl IntoIterator<Item = Key>) -> Dom {
        Dom {
            vals: Vals::Set(keys.into_iter().collect()),
            null: false,
        }
        .normalized()
    }

    fn normalized(self) -> Dom {
        let vals = match self.vals {
            Vals::Range(None, None) => Vals::Any,
            Vals::Count(0) => Vals::Set(BTreeSet::new()),
            // Small ranges are listed, so they can lose single values.
            Vals::Range(Some(lo), Some(hi)) if hi - lo < SMALL => {
                Vals::Set((lo..=hi).map(Key::Int).collect())
            }
            v => v,
        };
        Dom {
            vals,
            null: self.null,
        }
    }

    pub(crate) fn with_null(mut self) -> Dom {
        self.null = true;
        self
    }

    pub(crate) fn without_null(mut self) -> Dom {
        self.null = false;
        self
    }

    /// The number of values (NULL counting as one), if finite.
    pub(crate) fn size(&self) -> Option<u128> {
        let n = match &self.vals {
            Vals::Any | Vals::Range(None, _) | Vals::Range(_, None) => return None,
            Vals::Range(Some(lo), Some(hi)) => (hi - lo) as u128 + 1,
            Vals::Set(s) => s.len() as u128,
            Vals::Count(n) => *n,
        };
        Some(n + self.null as u128)
    }

    /// The least and greatest value, if all values are known integers.
    fn int_bounds(&self) -> Option<(i128, i128)> {
        match &self.vals {
            Vals::Range(Some(lo), Some(hi)) => Some((*lo, *hi)),
            Vals::Set(s) => {
                let ints: Option<Vec<i128>> = s
                    .iter()
                    .map(|k| match k {
                        Key::Int(v) => Some(*v),
                        _ => None,
                    })
                    .collect();
                let ints = ints?;
                Some((*ints.iter().min()?, *ints.iter().max()?))
            }
            _ => None,
        }
    }

    /// The integers from `lo` up.
    pub(crate) fn at_least(lo: i128) -> Dom {
        Dom::range(Some(lo), None)
    }

    /// The image under `f`, which must be increasing, if every value maps.
    fn map_increasing(&self, f: impl Fn(i128) -> Option<i128>) -> Option<Dom> {
        let vals = match &self.vals {
            Vals::Any => Vals::Any,
            Vals::Count(n) => Vals::Count(*n),
            Vals::Range(lo, hi) => Vals::Range(lo.map(&f).flatten(), hi.map(&f).flatten()),
            Vals::Set(s) => Vals::Set(
                s.iter()
                    .map(|k| match k {
                        Key::Int(v) => f(*v).map(Key::Int),
                        _ => None,
                    })
                    .collect::<Option<_>>()?,
            ),
        };
        Some(Dom { vals, null: self.null }.normalized())
    }

    /// The least value, if every value is a known integer (and never NULL).
    pub(crate) fn min(&self) -> Option<i128> {
        if self.null {
            return None;
        }
        match &self.vals {
            Vals::Range(lo, _) => *lo,
            Vals::Set(_) => self.int_bounds().map(|(lo, _)| lo),
            Vals::Any | Vals::Count(_) => None,
        }
    }

    /// True if the only possible value is NULL.
    pub(crate) fn is_null_only(&self) -> bool {
        self.null && self.vals == Vals::Set(BTreeSet::new())
    }

    pub(crate) fn never_null(&self) -> bool {
        !self.null
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.size() == Some(0)
    }

    pub(crate) fn intersect(&self, o: &Dom) -> Dom {
        let vals = match (&self.vals, &o.vals) {
            (Vals::Any, v) | (v, Vals::Any) => v.clone(),
            (Vals::Count(a), Vals::Count(b)) => Vals::Count(*a.min(b)),
            // Keep the known values if there are no more of them.
            (Vals::Count(n), v) | (v, Vals::Count(n)) => match Dom::values(v).size() {
                Some(m) if m <= *n => v.clone(),
                _ => Vals::Count(*n),
            },
            (Vals::Range(a, b), Vals::Range(c, d)) => {
                let lo = match (a, c) {
                    (Some(a), Some(c)) => Some(*a.max(c)),
                    (x, y) => x.or(*y),
                };
                let hi = match (b, d) {
                    (Some(b), Some(d)) => Some(*b.min(d)),
                    (x, y) => x.or(*y),
                };
                Vals::Range(lo, hi)
            }
            (Vals::Set(s), Vals::Range(lo, hi)) | (Vals::Range(lo, hi), Vals::Set(s)) => {
                Vals::Set(
                    s.iter()
                        .filter(|k| match k {
                            Key::Int(v) => lo.is_none_or(|lo| *v >= lo) && hi.is_none_or(|hi| *v <= hi),
                            // Not an integer, so not comparable: keep it.
                            _ => true,
                        })
                        .cloned()
                        .collect(),
                )
            }
            (Vals::Set(a), Vals::Set(b)) => Vals::Set(a.intersection(b).cloned().collect()),
        };
        Dom {
            vals,
            null: self.null && o.null,
        }
        .normalized()
    }

    pub(crate) fn union(&self, o: &Dom) -> Dom {
        let vals = match (&self.vals, &o.vals) {
            (Vals::Any, _) | (_, Vals::Any) => Vals::Any,
            (Vals::Count(n), v) | (v, Vals::Count(n)) => match Dom::values(v).size() {
                Some(m) => Vals::Count(n + m),
                None => Vals::Any,
            },
            (Vals::Set(a), Vals::Set(b)) => Vals::Set(a.union(b).cloned().collect()),
            (Vals::Range(a, b), Vals::Range(c, d)) => Vals::Range(
                a.zip(*c).map(|(a, c)| a.min(c)),
                b.zip(*d).map(|(b, d)| b.max(d)),
            ),
            (Vals::Set(s), Vals::Range(lo, hi)) | (Vals::Range(lo, hi), Vals::Set(s)) => {
                if s.is_empty() {
                    Vals::Range(*lo, *hi)
                } else if let Some((a, b)) = Dom::set(s.iter().cloned()).int_bounds() {
                    Vals::Range(lo.map(|lo| lo.min(a)), hi.map(|hi| hi.max(b)))
                } else {
                    Vals::Any
                }
            }
        };
        Dom {
            vals,
            null: self.null || o.null,
        }
        .normalized()
    }
}

/// Domains of expressions over one relation's output columns. An expression
/// without a fact can still get a domain from its type or its structure; see
/// [`Facts::dom`].
#[derive(Debug, Clone, Default)]
pub(crate) struct Facts {
    doms: Vec<(Expr, Dom)>,
    /// `(column, expression)`: the column equals the deterministic expression
    /// on every row, so a fact on one is a fact on the other. This links a
    /// computed column to later recomputations of its expression.
    defs: Vec<(Expr, Expr)>,
}

impl Facts {
    /// Records that `e` takes values in `d`, on top of what is known.
    pub(crate) fn add(&mut self, e: &Expr, d: Dom, schema: &DFSchema) {
        self.add_normalized(normalize(e, schema), d);
    }

    fn add_normalized(&mut self, e: Expr, d: Dom) {
        let same: Vec<Expr> = self
            .defs
            .iter()
            .filter_map(|(c, x)| {
                if *c == e {
                    Some(x.clone())
                } else if *x == e {
                    Some(c.clone())
                } else {
                    None
                }
            })
            .collect();
        for e in std::iter::once(e).chain(same) {
            match self.doms.iter_mut().find(|(x, _)| *x == e) {
                Some((_, old)) => *old = old.intersect(&d),
                None => self.doms.push((e, d.clone())),
            }
        }
    }

    /// Records that column `c` equals `e` on every row, if `e` is deterministic.
    pub(crate) fn define(&mut self, c: &Expr, e: &Expr, schema: &DFSchema) {
        if !deterministic(e) {
            return;
        }
        let e = normalize(e, schema);
        if matches!(e, Expr::Column(_)) {
            return;
        }
        if let Some(d) = self.get(&e).cloned() {
            self.add_normalized(c.clone(), d);
        }
        self.defs.push((c.clone(), e));
        if let Some(d) = self.get(c).cloned() {
            self.add_normalized(c.clone(), d);
        }
    }

    fn get(&self, e: &Expr) -> Option<&Dom> {
        self.doms.iter().find(|(x, _)| x == e).map(|(_, d)| d)
    }

    /// True if some expression can take no value at all: there are no rows.
    pub(crate) fn contradictory(&self) -> bool {
        self.doms.iter().any(|(_, d)| d.is_empty())
    }

    /// The same facts where every value may also be NULL, as on the padded
    /// side of an outer join. Definitions do not survive padding: a padded
    /// column is NULL whatever its expression gives on NULL inputs.
    pub(crate) fn nullable(&self) -> Facts {
        Facts {
            doms: self
                .doms
                .iter()
                .map(|(e, d)| (e.clone(), d.clone().with_null()))
                .collect(),
            defs: vec![],
        }
    }

    /// Adds every fact of `other`, which must describe the same columns.
    pub(crate) fn extend(&mut self, other: &Facts) {
        self.defs.extend(other.defs.iter().cloned());
        for (e, d) in &other.doms {
            self.add_normalized(e.clone(), d.clone());
        }
    }

    /// The facts whose columns all map to another relation's columns through
    /// `map`, rewritten over those columns.
    pub(crate) fn rename(&self, map: &dyn Fn(&Column) -> Option<Column>) -> Facts {
        Facts {
            doms: self
                .doms
                .iter()
                .filter_map(|(e, d)| Some((rename(e, map)?, d.clone())))
                .collect(),
            defs: self
                .defs
                .iter()
                .filter_map(|(c, e)| Some((rename(c, map)?, rename(e, map)?)))
                .collect(),
        }
    }

    /// Facts relating output columns by position to `from`'s, for operators
    /// that pass their input's columns through at the same positions.
    pub(crate) fn by_position(&self, from: &DFSchema, to: &DFSchema) -> Facts {
        self.rename(&|c| {
            let i = from.index_of_column(c).ok()?;
            (i < to.fields().len()).then(|| Column::from(to.qualified_field(i)))
        })
    }

    /// The domain of `e`, evaluated on a row of a relation with `schema`.
    pub(crate) fn dom(&self, e: &Expr, schema: &DFSchema) -> Dom {
        let e = normalize(e, schema);
        let known = self.get(&e).cloned().unwrap_or_else(Dom::top);
        known.intersect(&self.structural(&e, schema))
    }

    /// A domain for `e` from its type and shape alone, given the facts on its
    /// subexpressions.
    fn structural(&self, e: &Expr, schema: &DFSchema) -> Dom {
        match e {
            Expr::Literal(v, _) => match key(v) {
                _ if v.is_null() => Dom::null_only(),
                Some(k) => Dom::set([k]),
                None => Dom::non_null(),
            },
            Expr::Column(_) => e
                .get_type(schema)
                .map(|t| type_dom(&t))
                .unwrap_or_else(|_| Dom::top()),
            Expr::Case(Case {
                when_then_expr,
                else_expr,
                ..
            }) => {
                let otherwise = match else_expr {
                    Some(x) => self.dom(x, schema),
                    None => Dom::null_only(),
                };
                when_then_expr
                    .iter()
                    .fold(otherwise, |acc, (_, then)| acc.union(&self.dom(then, schema)))
            }
            Expr::ScalarFunction(f) if f.name() == "date_part" => {
                self.date_part(&f.args, schema).unwrap_or_else(Dom::top)
            }
            Expr::ScalarFunction(f) if f.name() == "date_trunc" => {
                self.date_trunc(&f.args, schema).unwrap_or_else(Dom::top)
            }
            Expr::BinaryExpr(BinaryExpr { left, op, right }) => {
                self.arithmetic(e, left, *op, right, schema).unwrap_or_else(Dom::top)
            }
            // A date as a timestamp: the same days, in the timestamp's unit.
            Expr::Cast(Cast { expr, field }) | Expr::TryCast(TryCast { expr, field }) => {
                match (expr.get_type(schema), field.data_type()) {
                    (Ok(DataType::Date32), DataType::Timestamp(unit, None)) => {
                        let per_day = per_day(unit);
                        self.dom(expr, schema)
                            .map_increasing(|d| d.checked_mul(per_day).filter(|v| i64::try_from(*v).is_ok()))
                            .unwrap_or_else(Dom::top)
                    }
                    _ => Dom::top(),
                }
            }
            _ => Dom::top(),
        }
    }

    /// `x op k` or `k op x` for an integer literal `k`, where the result
    /// provably stays in its type's range (Arrow arithmetic wraps).
    fn arithmetic(&self, e: &Expr, left: &Expr, op: Operator, right: &Expr, schema: &DFSchema) -> Option<Dom> {
        use Operator::*;
        if !matches!(op, Plus | Minus | Multiply | Divide | Modulo) {
            return None;
        }
        let (tmin, tmax) = int_range(&e.get_type(schema).ok()?)?;
        let (x, k, k_right) = match (left, right) {
            (x, Expr::Literal(v, _)) => (x, v, true),
            (Expr::Literal(v, _), x) => (x, v, false),
            _ => return None,
        };
        if !x.get_type(schema).ok()?.is_integer() {
            return None;
        }
        let Some(Key::Int(k)) = key(k) else {
            return None;
        };
        let apply = |v: i128| -> Option<i128> {
            let r = match (op, k_right) {
                (Plus, _) => v.checked_add(k)?,
                (Minus, true) => v.checked_sub(k)?,
                (Minus, false) => k.checked_sub(v)?,
                (Multiply, _) => v.checked_mul(k)?,
                // Truncating, as in SQL, and increasing in `v`.
                (Divide, true) if k > 0 => v / k,
                (Modulo, true) if k != 0 => v % k,
                _ => return None,
            };
            (tmin..=tmax).contains(&r).then_some(r)
        };
        let d = self.dom(x, schema);
        let vals = match &d.vals {
            // Few values: each one's result.
            Vals::Set(s) => {
                let out: Option<Vec<Key>> = s
                    .iter()
                    .map(|k| match k {
                        Key::Int(v) => apply(*v).map(Key::Int),
                        _ => None,
                    })
                    .collect();
                Dom::set(out?)
            }
            _ => {
                let (lo, hi) = match &d.vals {
                    Vals::Range(lo, hi) => (*lo, *hi),
                    _ => (None, None),
                };
                let m = k.abs() - 1;
                let r = match op {
                    // The remainder has the dividend's sign and is smaller than `k`.
                    Modulo if k_right && k != 0 => match (lo, hi) {
                        (Some(lo), hi) if lo >= 0 => Dom::range(Some(0), Some(hi.map_or(m, |h| h.min(m)))),
                        (lo, Some(hi)) if hi <= 0 => Dom::range(Some(lo.map_or(-m, |l| l.max(-m))), Some(0)),
                        _ => Dom::range(Some(-m), Some(m)),
                    },
                    // Increasing and never overflowing: open ends stay open.
                    Divide if k_right && k > 0 => Dom::range(lo.map(|v| v / k), hi.map(|v| v / k)),
                    // Otherwise both ends must be known to rule out overflow.
                    _ => {
                        let (a, b) = (apply(lo?)?, apply(hi?)?);
                        Dom::range(Some(a.min(b)), Some(a.max(b)))
                    }
                };
                // Never more results than arguments.
                match d.clone().without_null().size() {
                    Some(n) => r.intersect(&Dom::count(n)),
                    None => r,
                }
            }
        };
        Some(if d.null { vals.with_null() } else { vals })
    }

    /// `date_trunc(unit, t)` takes one value per unit that `t`'s range meets.
    fn date_trunc(&self, args: &[Expr], schema: &DFSchema) -> Option<Dom> {
        let [Expr::Literal(part, _), arg] = args else {
            return None;
        };
        let part = part.try_as_str()??.to_lowercase();
        let t = arg.get_type(schema).ok()?;
        let d = self.dom(arg, schema);
        let values = d.clone().without_null();
        let mut n = values.size();
        if let Some((lo, hi)) = values.int_bounds() {
            let bucket = |v: i128| -> Option<i128> {
                let days = days_of(&t, v)?;
                let (year, month) = civil(i64::try_from(days).ok()?);
                let (year, month) = (year as i128, month as i128);
                let units = |per_day: i128| Some(v.div_euclid(per_second(&t)? * 86_400 / per_day));
                Some(match part.as_str() {
                    "year" => year,
                    "quarter" => year * 4 + (month - 1) / 3,
                    "month" => year * 12 + month - 1,
                    // Weeks start on Monday; day 0 was a Thursday.
                    "week" => (days + 3).div_euclid(7),
                    "day" => days,
                    "hour" => units(24)?,
                    "minute" => units(24 * 60)?,
                    "second" => units(86_400)?,
                    _ => return None,
                })
            };
            if let (Some(a), Some(b)) = (bucket(lo), bucket(hi)) {
                let buckets = (b - a + 1).max(0) as u128;
                n = Some(n.map_or(buckets, |n| n.min(buckets)));
            }
        }
        let d2 = Dom::count(n?);
        Some(if d.null { d2.with_null() } else { d2 })
    }

    fn date_part(&self, args: &[Expr], schema: &DFSchema) -> Option<Dom> {
        let [Expr::Literal(part, _), arg] = args else {
            return None;
        };
        let part = part.try_as_str()??.to_lowercase();
        let t = arg.get_type(schema).ok()?;
        if !matches!(t, DataType::Date32 | DataType::Date64 | DataType::Timestamp(..)) {
            return None;
        }
        let arg_dom = self.dom(arg, schema);
        // NULL in, NULL out; no dates in, no parts out.
        if arg_dom.vals == Vals::Set(BTreeSet::new()) {
            return Some(arg_dom);
        }
        let fixed = |lo, hi| Dom::range(Some(lo), Some(hi));
        let d = match part.as_str() {
            // Years are monotone in the date, so a date range gives a year range.
            "year" | "years" => {
                let (lo, hi) = arg_dom.int_bounds()?;
                let year = |v: i128| -> Option<i128> {
                    let days = days_of(&t, v)?;
                    Some(civil(i64::try_from(days).ok()?).0 as i128)
                };
                fixed(year(lo)?, year(hi)?)
            }
            "month" | "months" => fixed(1, 12),
            "qtr" | "quarter" => fixed(1, 4),
            "day" | "days" => fixed(1, 31),
            "dow" => fixed(0, 6),
            "isodow" => fixed(1, 7),
            "doy" => fixed(1, 366),
            "week" | "weeks" => fixed(1, 53),
            "hour" | "hours" => fixed(0, 23),
            "minute" | "minutes" => fixed(0, 59),
            _ => return None,
        };
        Some(if arg_dom.null { d.with_null() } else { d })
    }

    /// Adds what `predicate` being TRUE says about the rows it passes.
    pub(crate) fn assume(&mut self, predicate: &Expr, schema: &DFSchema) {
        for conj in split_conjunction(predicate) {
            let facts = self.implied(conj, schema);
            for (e, d) in facts.doms {
                self.add_normalized(e, d);
            }
            // `a = b` on non-float values: both sides take the same values.
            if let Expr::BinaryExpr(BinaryExpr {
                left,
                op: Operator::Eq,
                right,
            }) = conj
            {
                self.equate(left, right, schema);
            }
        }
    }

    /// `a = b` holds on every row (so neither is NULL).
    fn equate(&mut self, a: &Expr, b: &Expr, schema: &DFSchema) {
        self.equate_keys(a, b, false, schema)
    }

    /// `a` and `b` are equal on every row, or both NULL if `nulls_match`.
    pub(crate) fn equate_keys(&mut self, a: &Expr, b: &Expr, nulls_match: bool, schema: &DFSchema) {
        let floating = |e: &Expr| e.get_type(schema).map_or(true, |t| t.is_floating());
        if floating(a) || floating(b) || !comparable(a, b, schema) {
            return;
        }
        let mut both = self.dom(a, schema).intersect(&self.dom(b, schema));
        if !nulls_match {
            both = both.without_null();
        }
        self.add(a, both.clone(), schema);
        self.add(b, both, schema);
    }

    /// Facts that hold on every row where `p` is TRUE, over `self`'s rows.
    fn implied(&self, p: &Expr, schema: &DFSchema) -> Facts {
        let mut out = Facts::default();
        let mut add = |e: &Expr, d: Dom| out.add(e, d, schema);
        match p {
            Expr::BinaryExpr(BinaryExpr { left, op, right }) => match op {
                Operator::And => {
                    let mut f = self.clone();
                    f.assume(p, schema);
                    return f;
                }
                Operator::Or => {
                    // A row passes one side or the other.
                    let mut a = self.clone();
                    a.assume(left, schema);
                    let mut b = self.clone();
                    b.assume(right, schema);
                    if a.contradictory() {
                        return b;
                    }
                    if b.contradictory() {
                        return a;
                    }
                    for (e, da) in &a.doms {
                        if let Some(db) = b.get(e) {
                            add(e, da.union(db));
                        }
                    }
                }
                Operator::Eq
                | Operator::NotEq
                | Operator::Lt
                | Operator::LtEq
                | Operator::Gt
                | Operator::GtEq => {
                    // A comparison with NULL is never TRUE.
                    add(left, Dom::non_null());
                    add(right, Dom::non_null());
                    // Equal to one value, whichever it is.
                    if *op == Operator::Eq {
                        for (e, x) in [(left, right), (right, left)] {
                            if invariant(x) && exact_equality(e, schema) {
                                add(e, Dom::count(1));
                            }
                        }
                    }
                    let (e, op, lit) = match (&**left, &**right) {
                        (e, Expr::Literal(v, _)) => (e, *op, v),
                        (Expr::Literal(v, _), e) => (e, op.swap().unwrap_or(*op), v),
                        _ => return out,
                    };
                    if let Some(d) = compare(e, op, lit, schema) {
                        add(e, d);
                    } else if op == Operator::NotEq
                        && literal_fits(e, lit, schema)
                        && let Some(k) = key(lit)
                        && let Vals::Set(s) = self.dom(e, schema).vals
                    {
                        add(e, Dom::set(s.into_iter().filter(|x| *x != k)));
                    }
                }
                _ => {}
            },
            Expr::Between(Between {
                expr,
                negated: false,
                low,
                high,
            }) => {
                add(expr, Dom::non_null());
                if let (Expr::Literal(lo, _), Expr::Literal(hi, _)) = (&**low, &**high)
                    && let Some(a) = compare(expr, Operator::GtEq, lo, schema)
                    && let Some(b) = compare(expr, Operator::LtEq, hi, schema)
                {
                    add(expr, a.intersect(&b));
                }
            }
            Expr::InList(list) if !list.negated => {
                let e = &list.expr;
                let doms: Option<Vec<Dom>> = list
                    .list
                    .iter()
                    .filter(|x| !matches!(x, Expr::Literal(v, _) if v.is_null()))
                    .map(|x| match x {
                        Expr::Literal(v, _) if literal_fits(e, v, schema) => Some(Dom::set([key(v)?])),
                        x if invariant(x) && exact_equality(e, schema) => Some(Dom::count(1)),
                        _ => None,
                    })
                    .collect();
                let d = doms.map_or_else(Dom::non_null, |ds| {
                    ds.iter().fold(Dom::nothing(), |acc, d| acc.union(d))
                });
                add(e, d);
            }
            Expr::IsNull(e) => add(e, Dom::null_only()),
            Expr::IsNotNull(e) => add(e, Dom::non_null()),
            Expr::IsTrue(e) => add(e, Dom::set([Key::Bool(true)])),
            Expr::IsFalse(e) => add(e, Dom::set([Key::Bool(false)])),
            Expr::Not(e) if matches!(e.get_type(schema), Ok(DataType::Boolean)) => {
                add(e, Dom::set([Key::Bool(false)]))
            }
            Expr::Column(_) => add(p, Dom::set([Key::Bool(true)])),
            _ => {}
        }
        out
    }
}

/// `e` over the columns `map` gives, if it maps all of them.
pub(crate) fn rename(e: &Expr, map: &dyn Fn(&Column) -> Option<Column>) -> Option<Expr> {
    let mut ok = true;
    let e = e
        .clone()
        .transform(|x| match x {
            Expr::Column(c) => match map(&c) {
                Some(c) => Ok(Transformed::yes(Expr::Column(c))),
                None => {
                    ok = false;
                    Ok(Transformed::no(Expr::Column(c)))
                }
            },
            x => Ok(Transformed::no(x)),
        })
        .ok()?
        .data;
    ok.then_some(e)
}

/// True if `e` takes one value for the whole query: it reads no column, and
/// is built from literals, parameters and uncorrelated scalar subqueries.
fn invariant(e: &Expr) -> bool {
    !matches!(e, Expr::Literal(..))
        && !e.is_volatile()
        && e
            .exists(|x| {
                Ok(match x {
                    Expr::ScalarSubquery(sq) => !sq.outer_ref_columns.is_empty(),
                    Expr::Column(_)
                    | Expr::OuterReferenceColumn(..)
                    | Expr::Exists(_)
                    | Expr::InSubquery(_)
                    | Expr::SetComparison(_)
                    | Expr::AggregateFunction(_)
                    | Expr::WindowFunction(_) => true,
                    _ => false,
                })
            })
            .is_ok_and(|found| !found)
}

/// True if values of `e` equal under SQL `=` are the same value. Not so for
/// floats, where `-0.0 = 0.0`.
fn exact_equality(e: &Expr, schema: &DFSchema) -> bool {
    e.get_type(schema).is_ok_and(|t| !t.is_floating())
}

/// True if `e` gives the same value whenever its columns do.
fn deterministic(e: &Expr) -> bool {
    !e.is_volatile()
        && !e
            .exists(|x| {
                Ok(matches!(
                    x,
                    Expr::ScalarSubquery(_)
                        | Expr::Exists(_)
                        | Expr::InSubquery(_)
                        | Expr::SetComparison(_)
                        | Expr::OuterReferenceColumn(..)
                        | Expr::Placeholder(_)
                        | Expr::AggregateFunction(_)
                        | Expr::WindowFunction(_)
                ))
            })
            .unwrap_or(true)
}

/// The values `e` can take where `e op lit` is TRUE, if expressible.
fn compare(e: &Expr, op: Operator, lit: &ScalarValue, schema: &DFSchema) -> Option<Dom> {
    if lit.is_null() || !literal_fits(e, lit, schema) {
        return None;
    }
    let k = key(lit)?;
    if op == Operator::Eq {
        return Some(Dom::set([k]));
    }
    let Key::Int(v) = k else {
        return None;
    };
    Some(match op {
        Operator::Lt => Dom::range(None, Some(v - 1)),
        Operator::LtEq => Dom::range(None, Some(v)),
        Operator::Gt => Dom::range(Some(v + 1), None),
        Operator::GtEq => Dom::range(Some(v), None),
        _ => return None,
    })
}

/// True if a literal compared with `e` is compared as a value of `e`'s type,
/// so that its key means the same as `e`'s values' keys.
fn literal_fits(e: &Expr, lit: &ScalarValue, schema: &DFSchema) -> bool {
    let Ok(t) = e.get_type(schema) else {
        return false;
    };
    let l = lit.data_type();
    let int = |t: &DataType| t.is_integer();
    let string = |t: &DataType| matches!(t, DataType::Utf8 | DataType::LargeUtf8 | DataType::Utf8View);
    match (&t, &l) {
        _ if int(&t) && int(&l) => true,
        _ if string(&t) && string(&l) => true,
        (DataType::Decimal128(_, a), DataType::Decimal128(_, b)) => a == b,
        (a, b) => {
            a == b
                && matches!(
                    a,
                    DataType::Date32 | DataType::Date64 | DataType::Boolean | DataType::Timestamp(..)
                )
        }
    }
}

fn comparable(a: &Expr, b: &Expr, schema: &DFSchema) -> bool {
    match (a.get_type(schema), b.get_type(schema)) {
        (Ok(x), Ok(y)) => {
            x == y
                || x.is_integer() && y.is_integer()
                || matches!(
                    (&x, &y),
                    (
                        DataType::Utf8 | DataType::LargeUtf8 | DataType::Utf8View,
                        DataType::Utf8 | DataType::LargeUtf8 | DataType::Utf8View
                    )
                )
        }
        _ => false,
    }
}

/// The key of a non-NULL literal of a supported type.
fn key(v: &ScalarValue) -> Option<Key> {
    use ScalarValue::*;
    Some(match v {
        Int8(Some(x)) => Key::Int(*x as i128),
        Int16(Some(x)) => Key::Int(*x as i128),
        Int32(Some(x)) => Key::Int(*x as i128),
        Int64(Some(x)) => Key::Int(*x as i128),
        UInt8(Some(x)) => Key::Int(*x as i128),
        UInt16(Some(x)) => Key::Int(*x as i128),
        UInt32(Some(x)) => Key::Int(*x as i128),
        UInt64(Some(x)) => Key::Int(*x as i128),
        Date32(Some(x)) => Key::Int(*x as i128),
        Date64(Some(x)) => Key::Int(*x as i128),
        TimestampSecond(Some(x), _)
        | TimestampMillisecond(Some(x), _)
        | TimestampMicrosecond(Some(x), _)
        | TimestampNanosecond(Some(x), _) => Key::Int(*x as i128),
        Decimal128(Some(x), _, _) => Key::Int(*x),
        Utf8(Some(s)) | LargeUtf8(Some(s)) | Utf8View(Some(s)) => Key::Str(s.clone()),
        Boolean(Some(b)) => Key::Bool(*b),
        _ => return None,
    })
}

/// The values of a type with few of them.
fn type_dom(t: &DataType) -> Dom {
    let d = match t {
        DataType::Boolean => Dom::set([Key::Bool(false), Key::Bool(true)]),
        DataType::Int8 => Dom::range(Some(i8::MIN as i128), Some(i8::MAX as i128)),
        DataType::UInt8 => Dom::range(Some(0), Some(u8::MAX as i128)),
        DataType::Int16 => Dom::range(Some(i16::MIN as i128), Some(i16::MAX as i128)),
        DataType::UInt16 => Dom::range(Some(0), Some(u16::MAX as i128)),
        _ => Dom::non_null(),
    };
    d.with_null()
}

/// `e` without aliases and without casts that map distinct values to distinct
/// values in the same order, so every spelling of one value has one key.
fn normalize(e: &Expr, schema: &DFSchema) -> Expr {
    match e {
        Expr::Alias(a) => normalize(&a.expr, schema),
        Expr::Cast(Cast { expr, field }) | Expr::TryCast(TryCast { expr, field }) => {
            match expr.get_type(schema) {
                Ok(from) if widening(&from, field.data_type()) => normalize(expr, schema),
                _ => e.clone(),
            }
        }
        _ => e.clone(),
    }
}

/// Casts that keep every value, and its order, unchanged.
fn widening(from: &DataType, to: &DataType) -> bool {
    use DataType::*;
    from == to
        || matches!(
            (from, to),
            (Int8, Int16 | Int32 | Int64)
                | (Int16, Int32 | Int64)
                | (Int32, Int64)
                | (UInt8, UInt16 | UInt32 | UInt64 | Int16 | Int32 | Int64)
                | (UInt16, UInt32 | UInt64 | Int32 | Int64)
                | (UInt32, UInt64 | Int64)
                | (Utf8 | LargeUtf8 | Utf8View, Utf8 | LargeUtf8 | Utf8View)
        )
}

/// The proleptic Gregorian year of a day count since 1970-01-01.
fn civil(days: i64) -> (i64, i64) {
    // Howard Hinnant's `civil_from_days`.
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    (yoe + era * 400 + (month <= 2) as i64, month)
}

/// The day (since 1970-01-01) of value `v` of a date or time-zone-free
/// timestamp type.
fn days_of(t: &DataType, v: i128) -> Option<i128> {
    Some(match t {
        DataType::Date32 => v,
        DataType::Date64 => v.div_euclid(86_400_000),
        DataType::Timestamp(unit, None) => v.div_euclid(per_day(unit)),
        _ => return None,
    })
}

/// Units of a time-zone-free timestamp type per second.
fn per_second(t: &DataType) -> Option<i128> {
    match t {
        DataType::Timestamp(unit, None) => Some(per_day(unit) / 86_400),
        DataType::Date32 | DataType::Date64 => None,
        _ => None,
    }
}

fn per_day(unit: &TimeUnit) -> i128 {
    86_400
        * match unit {
            TimeUnit::Second => 1,
            TimeUnit::Millisecond => 1_000,
            TimeUnit::Microsecond => 1_000_000,
            TimeUnit::Nanosecond => 1_000_000_000,
        }
}

/// The values of an integer type.
fn int_range(t: &DataType) -> Option<(i128, i128)> {
    use DataType::*;
    Some(match t {
        Int8 => (i8::MIN as i128, i8::MAX as i128),
        Int16 => (i16::MIN as i128, i16::MAX as i128),
        Int32 => (i32::MIN as i128, i32::MAX as i128),
        Int64 => (i64::MIN as i128, i64::MAX as i128),
        UInt8 => (0, u8::MAX as i128),
        UInt16 => (0, u16::MAX as i128),
        UInt32 => (0, u32::MAX as i128),
        UInt64 => (0, u64::MAX as i128),
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn years() {
        assert_eq!(civil(0).0, 1970);
        assert_eq!(civil(-1).0, 1969);
        assert_eq!(civil(9131).0, 1995); // 1995-01-01
        assert_eq!(civil(9861).0, 1996); // 1996-12-31
        assert_eq!(civil(9862).0, 1997);
        assert_eq!(civil(59), (1970, 3)); // 1970-03-01
        assert_eq!(civil(-1), (1969, 12));
    }

    #[test]
    fn domains() {
        let r = Dom::range(Some(1), Some(10));
        assert_eq!(r.size(), Some(10));
        assert_eq!(r.clone().with_null().size(), Some(11));
        assert!(r.intersect(&Dom::range(Some(11), None)).is_empty());
        let s = Dom::set([Key::Int(3), Key::Int(30)]);
        assert_eq!(r.intersect(&s).size(), Some(1));
        assert_eq!(r.union(&s).size(), Some(11));
        let wide = Dom::range(Some(0), Some(1000));
        assert_eq!(wide.union(&s).size(), Some(1001));
        assert_eq!(wide.union(&Dom::set([Key::Int(2000)])).size(), Some(2001));
        assert_eq!(Dom::set([Key::Str("a".into())]).union(&wide), Dom::non_null());
    }
}
