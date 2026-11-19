//! Properties: what holds of any rows, as claims on their quantities.
//!
//! Each property is a function of the quantities of the rows it is about
//! (Z3 terms: row counts, distinct counts, ends of ranges), and returns its
//! claims. It asserts nothing, reads no plan and finds nothing: its caller
//! knows how the rows relate, the [rules](crate::rules) from the plan's
//! shape, [`link`](crate::link) otherwise. This is the one place
//! to check each claim's soundness, given that its premise holds.
//!
//! Properties of rows related to other rows take [`Pair`]s: one quantity of
//! rows `a` and the same kind of quantity of rows `b`. Which pairs a caller
//! passes says how the rows relate:
//!
//! | Relationship | Property | Pairs |
//! |---|---|---|
//! | same rows | [`same`] | `Card` and each column's |
//! | subset | [`within`] | `Card` and each column's |
//! | wider | [`within`] | each column's, no `Card` |

use z3::ast::{Bool, Int};


/// A quantity of rows `a` and the same kind of quantity of rows `b`.
#[derive(Clone, Copy)]
pub enum Pair<'a> {
    /// Their cardinalities: `|a|`, `|b|`.
    Card(&'a Int, &'a Int),
    /// Distinct values of some keys of `a`, and of the same keys (or more)
    /// of `b`.
    Ndv(&'a Int, &'a Int),
    /// Ends of the intervals holding one column's non-NULL values, in one
    /// unit.
    Min(&'a Int, &'a Int),
    Max(&'a Int, &'a Int),
}

impl<'a> Pair<'a> {
    fn terms(&self) -> (&'a Int, &'a Int) {
        match *self {
            Pair::Card(a, b) | Pair::Ndv(a, b) | Pair::Min(a, b) | Pair::Max(a, b) => (a, b),
        }
    }
}

/// `a` and `b` are the same rows: each pair is equal.
pub fn same(pairs: &[Pair]) -> Vec<Bool> {
    pairs
        .iter()
        .map(|p| {
            let (a, b) = p.terms();
            a.eq(b)
        })
        .collect()
}

/// Each of `a`'s rows or values is one of `b`'s: `Card`, `Ndv` and `Max`
/// are `≤`, `Min` `≥`.
pub fn within(pairs: &[Pair]) -> Vec<Bool> {
    pairs
        .iter()
        .map(|p| match *p {
            Pair::Min(a, b) => a.ge(b),
            Pair::Card(a, b) | Pair::Ndv(a, b) | Pair::Max(a, b) => a.le(b),
        })
        .collect()
}

/// `a ⊆ b` with as many rows are the same rows: `|a| = |b| ⇒` each pair is
/// equal.
pub fn same_if_as_many(a: &Int, b: &Int, pairs: &[Pair]) -> Vec<Bool> {
    if pairs.is_empty() {
        return vec![];
    }
    let equal: Vec<Bool> = pairs.iter().map(|p| p.terms().0.eq(p.terms().1)).collect();
    vec![a.eq(b).implies(Bool::and(&equal))]
}

/// `|a| ≤ |b|`, nothing said of values: an outer join over narrower inputs
/// emits each preserved row once per partner or once padded.
pub fn fewer(a: &Int, b: &Int) -> Vec<Bool> {
    vec![a.le(b)]
}

/// Rows apart within `whole`: `Σ |part| ≤ |whole|`.
pub fn disjoint(parts: &[&Int], whole: &Int) -> Vec<Bool> {
    vec![Int::add(parts).le(whole)]
}

/// `d ⊆ c`: `d`'s rows failing `P` are among `c`'s, `|d| − |d ∧ P| ≤ |c| −
/// |c ∧ P|`.
pub fn failing(d: &Int, dp: &Int, c: &Int, cp: &Int) -> Vec<Bool> {
    vec![Int::sub(&[d, dp]).le(Int::sub(&[c, cp]))]
}

/// Each row of `d` holds a row of `c`: if every row of `c` satisfies `P`,
/// so does every row of `d`, `|c ∧ P| = |c| ⇒ |d ∧ P| = |d|`.
pub fn implied(c: &Int, cp: &Int, d: &Int, dp: &Int) -> Vec<Bool> {
    vec![cp.eq(c).implies(dp.eq(d))]
}

/// Each row has a partner or none: `|K ⋉ O| + |K ▷ O| = |K|`.
pub fn split(semi: &Int, anti: &Int, kept: &Int) -> Vec<Bool> {
    vec![Int::add(&[semi, anti]).eq(kept)]
}

/// Fewer keys have no more combinations: `ndv(K) ≤ ndv(K')` for `K ⊆ K'`.
pub fn fewer_keys(k: &Int, wider: &Int) -> Vec<Bool> {
    vec![k.le(wider)]
}

/// Values of rows each holding a row of `c` are `c`'s: `ndv(K | d) ≤ |c|`.
pub fn values_of_rows(ndv: &Int, c: &Int) -> Vec<Bool> {
    vec![ndv.le(c)]
}
