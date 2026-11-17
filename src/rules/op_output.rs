//! What holds of an operator's output given its input's: the pairs of
//! their quantities a [property](crate::properties) relates.
//!
//! A rule knows from the plan how its output's rows are an input's. It
//! pairs the columns of its output that hold an input column's values (but
//! a float equal to one by a predicate: SQL equality merges values distinct
//! as bits, `-0.0 = 0.0`), and asserts a property of the pairs these
//! functions give:
//!
//! | Relationship | Property | Pairs |
//! |---|---|---|
//! | same rows (projection, alias, sort, ...) | [`same_rows`] | [`with_card`] |
//! | subset (filter, limit, semi join, ...) | [`within`](properties::within) | [`with_card`] |
//! | wider (inner join side, GROUP BY key, ...) | [`within`](properties::within) | [`columns`] |
//! | ranges only (padded side, MIN, MAX) | [`within`](properties::within) | [`ranges`] |

use crate::analysis::Rel;
use crate::properties::{self, Claim, Pair};

/// For each `(j, i)` of `columns`: `o.j`'s and `l.i`'s `Min` and `Max`, if
/// both have them in one unit. A cast of an integer to a decimal keeps the
/// value, not the count.
pub(crate) fn ranges<'a>(o: &'a Rel, l: &'a Rel, columns: &[(usize, usize)]) -> Vec<Pair<'a>> {
    let mut out = vec![];
    for &(j, i) in columns {
        if o.unit[j] != l.unit[i] {
            continue;
        }
        if let (Some(a), Some(b)) = (&o.min[j], &l.min[i]) {
            out.push(Pair::Min(a, b));
        }
        if let (Some(a), Some(b)) = (&o.max[j], &l.max[i]) {
            out.push(Pair::Max(a, b));
        }
    }
    out
}

/// For each `(j, i)` of `columns`: `o.j`'s and `l.i`'s `Ndv`, then their
/// [`ranges`].
pub(crate) fn columns<'a>(o: &'a Rel, l: &'a Rel, columns: &[(usize, usize)]) -> Vec<Pair<'a>> {
    let mut out: Vec<Pair> = columns.iter().map(|&(j, i)| Pair::Ndv(&o.ndv[j], &l.ndv[i])).collect();
    out.extend(ranges(o, l, columns));
    out
}

/// `Card(o.card, l.card)`, then their [`columns`].
pub(crate) fn with_card<'a>(o: &'a Rel, l: &'a Rel, columns: &[(usize, usize)]) -> Vec<Pair<'a>> {
    let mut out = vec![Pair::Card(&o.card, &l.card)];
    out.extend(self::columns(o, l, columns));
    out
}

/// `o`'s rows are `l`'s: their counts are [`same`](properties::same), and
/// their ranges [`within`](properties::within).
pub(crate) fn same_rows(o: &Rel, l: &Rel, columns: &[(usize, usize)]) -> Vec<Claim> {
    let (counts, ranges): (Vec<Pair>, Vec<Pair>) =
        with_card(o, l, columns).into_iter().partition(|p| matches!(p, Pair::Card(..) | Pair::Ndv(..)));
    let mut out = properties::same(&counts);
    out.extend(properties::within(&ranges));
    out
}
