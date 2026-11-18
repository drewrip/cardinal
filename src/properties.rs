//! Properties: what holds of any rows, as claims on their quantities.
//!
//! Each property is a function of the quantities of the rows it is about
//! (Z3 terms: row counts, distinct counts, ends of ranges), and returns its
//! claims. It asserts nothing, reads no plan and finds nothing: its caller
//! knows how the rows relate, the [rules](crate::rules) from the plan's
//! shape, [`link`](crate::link) from their contexts. This is the one place
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
//!
//! Each claim comes with its [`Role`] in liveness: claims on row counts only
//! are [`Role::Gen`], claims on columns [`Role::Flow`], but
//! [`fewer_keys`]', which bound columns by others of the same rows,
//! [`Role::Local`].

use z3::ast::{Bool, Int};

use crate::postprocess::Role;

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

/// A claim, and its role in liveness.
pub struct Claim {
    pub role: Role,
    pub claim: Bool,
}

/// [`Role::Gen`] for row counts only, [`Role::Flow`] if any of `pairs` is of
/// columns.
fn role(pairs: &[Pair]) -> Role {
    match pairs.iter().all(|p| matches!(p, Pair::Card(..))) {
        true => Role::Gen,
        false => Role::Flow,
    }
}

/// A claim on row counts only.
fn count(claim: Bool) -> Vec<Claim> {
    vec![Claim { role: Role::Gen, claim }]
}

/// `a` and `b` are the same rows: each pair is equal.
pub fn same(pairs: &[Pair]) -> Vec<Claim> {
    pairs
        .iter()
        .map(|p| {
            let (a, b) = p.terms();
            Claim { role: role(&[*p]), claim: a.eq(b) }
        })
        .collect()
}

/// Each of `a`'s rows or values is one of `b`'s: `Card`, `Ndv` and `Max`
/// are `≤`, `Min` `≥`.
pub fn within(pairs: &[Pair]) -> Vec<Claim> {
    pairs
        .iter()
        .map(|p| {
            let claim = match *p {
                Pair::Min(a, b) => a.ge(b),
                Pair::Card(a, b) | Pair::Ndv(a, b) | Pair::Max(a, b) => a.le(b),
            };
            Claim { role: role(&[*p]), claim }
        })
        .collect()
}

/// `a ⊆ b` with as many rows are the same rows: `|a| = |b| ⇒` each pair is
/// equal.
pub fn same_if_as_many(a: &Int, b: &Int, pairs: &[Pair]) -> Vec<Claim> {
    if pairs.is_empty() {
        return vec![];
    }
    let equal: Vec<Bool> = pairs.iter().map(|p| p.terms().0.eq(p.terms().1)).collect();
    vec![Claim { role: role(pairs), claim: a.eq(b).implies(Bool::and(&equal)) }]
}

/// `|a| ≤ |b|`, nothing said of values: an outer join over narrower inputs
/// emits each preserved row once per partner or once padded.
pub fn fewer(a: &Int, b: &Int) -> Vec<Claim> {
    count(a.le(b))
}

/// Rows apart within `whole`: `Σ |part| ≤ |whole|`.
pub fn disjoint(parts: &[&Int], whole: &Int) -> Vec<Claim> {
    count(Int::add(parts).le(whole))
}

/// `d ⊆ c`: `d`'s rows failing `P` are among `c`'s, `|d| − |d ∧ P| ≤ |c| −
/// |c ∧ P|`.
pub fn failing(d: &Int, dp: &Int, c: &Int, cp: &Int) -> Vec<Claim> {
    count(Int::sub(&[d, dp]).le(Int::sub(&[c, cp])))
}

/// Each row of `d` holds a row of `c`: if every row of `c` satisfies `P`,
/// so does every row of `d`, `|c ∧ P| = |c| ⇒ |d ∧ P| = |d|`.
pub fn implied(c: &Int, cp: &Int, d: &Int, dp: &Int) -> Vec<Claim> {
    count(cp.eq(c).implies(dp.eq(d)))
}

/// Each row has a partner or none: `|K ⋉ O| + |K ▷ O| = |K|`.
pub fn split(semi: &Int, anti: &Int, kept: &Int) -> Vec<Claim> {
    count(Int::add(&[semi, anti]).eq(kept))
}

/// Fewer keys have no more combinations: `ndv(K) ≤ ndv(K')` for `K ⊆ K'`.
pub fn fewer_keys(k: &Int, wider: &Int) -> Vec<Claim> {
    vec![Claim { role: Role::Local, claim: k.le(wider) }]
}

/// Values of rows each holding a row of `c` are `c`'s: `ndv(K | d) ≤ |c|`.
pub fn values_of_rows(ndv: &Int, c: &Int) -> Vec<Claim> {
    vec![Claim { role: Role::Flow, claim: ndv.le(c) }]
}
