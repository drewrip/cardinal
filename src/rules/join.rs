//! Joins of every kind.

use datafusion::common::{Column, JoinType, NullEquality};
use datafusion::logical_expr::Expr;
use datafusion::logical_expr::logical_plan::{Join, LogicalPlan};
use z3::ast::Int;

use super::op_output::{columns, ranges, with_card};
use super::{aligned, child_column, col, exact_index, key_column, passed_rows, strip_alias};
use crate::analysis::{Analyzer, OpOutput, SubsetBounds, ScanKind, int, min};
use crate::domain::Facts;
use crate::properties::{same, within};

impl<'a> Analyzer<'a> {
    /// `Join` of every kind. Notation as in [the module](super#notation).
    ///
    /// - **Claim**: with `inner` the bound on the matched pairs, `l·r`, or
    ///   `≤ l` if the right key is unique or a foreign key goes from the left
    ///   to the whole right table (and the mirror):
    ///   - inner: `X ≤ inner`; a cross join `X = l·r`; on a foreign key from
    ///     the left `X = l`;
    ///   - left: `X = l` if each left row matches at most once, else `l ≤ X
    ///     ≤ inner + l`; right: the mirror;
    ///   - full: `X ≥ l`, `X ≥ r`, `X ≤ inner + l + r`, and `≤ l + r` with a
    ///     unique key;
    ///   - semi and anti: a [`subset`](super::op_output) of the kept side; on a
    ///     foreign key from it, semi `X =` it and anti `X = 0`;
    ///   - mark: the [`same rows`](super::op_output) as the kept side.
    ///
    ///   Outer and anti joins are also stated in terms of their auxiliary
    ///   joins ([`Self::join_parts`]). Columns ([`Self::join_sides`]): a side
    ///   no row pads [holds](super::op_output) its rows, a preserved side every
    ///   value; a padded side's `ndv ≤` its own `+ 1` (NULL), within its
    ///   range; a semi join's equi-key holds the other side's key. On an
    ///   inner join, the two equi-keys' `ndv` are equal, and a side on a
    ///   foreign key keeps every value ([`Self::join_ndv_kept`]). Keys whose
    ///   values lie among one table's referenced key keep at least the
    ///   values both sides must share ([`Self::join_overlap`]). An inner
    ///   join's equi-keys share their range ([`Self::join_ranges`]).
    /// - **Foreign keys** through joins: a join keeps each of a side's rows
    ///   once if each matches exactly once (inner, on a foreign key from it)
    ///   or at most once (outer, on the other side's unique key), so a
    ///   foreign key to such a side reaches every row of its table.
    pub fn join(&mut self, plan: &LogicalPlan, join: &Join) -> OpOutput {
        let l = self.visit(&join.left);
        let r = self.visit(&join.right);
        let equi = !join.on.is_empty();
        let cross = !equi && join.filter.is_none();
        let (lk, rk): (Vec<&Expr>, Vec<&Expr>) = join.on.iter().map(|(a, b)| (a, b)).unzip();
        let (fk_left, fk_right) = self.foreign_key(join);
        let keys = JoinKeys {
            right_unique: equi && self.key_is_unique(join, &join.right, &rk),
            left_unique: equi && self.key_is_unique(join, &join.left, &lk),
            fk_left,
            fk_right,
        };
        let JoinKeys { right_unique: ru, left_unique: lu, fk_left: fl, fk_right: fr } = keys;
        let kind = format!(
            "{:?}{}Join",
            join.join_type,
            if ru || lu {
                "Key"
            } else if equi {
                "Equi"
            } else if cross {
                "Cross"
            } else {
                "Theta"
            }
        );
        let mut o = self.fresh(&kind, plan);
        let lr = Int::mul(&[&l.card, &r.card]);
        // Bound on the rows the join's matching produces.
        let mut inner = lr.clone();
        if ru || fl {
            inner = min(&inner, &l.card);
        }
        if lu || fr {
            inner = min(&inner, &r.card);
        }
        match join.join_type {
            JoinType::Inner => {
                if cross {
                    self.assert(o.card.eq(&lr));
                } else {
                    self.assert(o.card.le(&inner));
                }
                if fl {
                    self.assert(o.card.eq(&l.card));
                }
                if fr {
                    self.assert(o.card.eq(&r.card));
                }
            }
            // An outer join emits its inner join's rows plus each unmatched row of
            // the preserved side. If each preserved row matches at most once, it
            // appears exactly once.
            JoinType::Left if ru || fl => self.assert(o.card.eq(&l.card)),
            JoinType::Right if lu || fr => self.assert(o.card.eq(&r.card)),
            JoinType::Left | JoinType::Right => {
                let preserved = if join.join_type == JoinType::Left {
                    &l.card
                } else {
                    &r.card
                };
                self.assert(o.card.ge(preserved));
                self.assert(o.card.le(Int::add(&[&inner, preserved])));
            }
            JoinType::Full => {
                self.assert(o.card.ge(&l.card));
                self.assert(o.card.ge(&r.card));
                self.assert(o.card.le(Int::add(&[&inner, &l.card, &r.card])));
                if ru || lu {
                    // One side's rows each appear exactly once, plus the other
                    // side's unmatched rows.
                    self.assert(o.card.le(Int::add(&[&l.card, &r.card])));
                }
            }
            // Every row of the referencing side has a partner.
            JoinType::LeftSemi if fl => self.assert(o.card.eq(&l.card)),
            JoinType::LeftAnti if fl => self.assert(o.card.eq(int(0))),
            JoinType::RightSemi if fr => self.assert(o.card.eq(&r.card)),
            JoinType::RightAnti if fr => self.assert(o.card.eq(int(0))),
            // Their rows are the kept side's (`Self::join_sides`).
            JoinType::LeftSemi
            | JoinType::LeftAnti
            | JoinType::RightSemi
            | JoinType::RightAnti
            | JoinType::LeftMark
            | JoinType::RightMark => {}
        }
        self.join_parts(join, &o, &l, &r, &inner, keys);
        self.join_overlap(join, &o, &l, &r);
        self.join_sides(join, &o, &l, &r);
        self.join_ndv_kept(join, &o, &l, &r, keys);
        self.join_ranges(plan, join, &o);
        o.facts = join_facts(plan, join, &l.facts, &r.facts);
        // Semi, anti and mark joins keep a subset of one side's rows.
        o.subset_bounds = match join.join_type {
            JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => l.subset_bounds.clone(),
            JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => r.subset_bounds.clone(),
            _ => SubsetBounds::default(),
        };
        // On an outer join, a padded-side column that is never NULL on matched
        // rows is NULL exactly on the padded rows: at most the other side's
        // rows. It is non-NULL on the matched rows (and, for a full join, the
        // side's own unmatched rows). A full join also keeps each side's own
        // unmatched rows, whose equi-keys may be NULL, so there only columns
        // never NULL on their side qualify.
        let nl = join.left.schema().fields().len();
        let (pad_left, pad_right) = match join.join_type {
            JoinType::Left => (false, true),
            JoinType::Right => (true, false),
            JoinType::Full => (true, true),
            _ => (false, false),
        };
        let full = join.join_type == JoinType::Full;
        if pad_right {
            let values = if full { Int::add(&[&inner, &r.card]) } else { inner.clone() };
            let keys = if full { &[][..] } else { &rk[..] };
            for c in never_null_when_matched(join, &join.right, &r.facts, keys) {
                o.subset_bounds.nulls.push((col(plan, nl + c), l.card.clone(), values.clone()));
            }
        }
        if pad_left {
            let values = if full { Int::add(&[&inner, &l.card]) } else { inner.clone() };
            let keys = if full { &[][..] } else { &lk[..] };
            for c in never_null_when_matched(join, &join.left, &l.facts, keys) {
                o.subset_bounds.nulls.push((col(plan, c), r.card.clone(), values.clone()));
            }
        }
        let width = plan.schema().fields().len();
        o.origin = match join.join_type {
            JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => l.origin.as_ref(),
            JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => r.origin.as_ref(),
            _ => None,
        }
        .map(|x| x.with_width(width).narrow(&o.facts, plan.schema()));
        o
    }

    /// Part of [`Self::join`]: an outer or anti join's rows, in terms of its
    /// auxiliary joins, which `validate` counts too.
    ///
    /// - **Claim**: with `i ≤ inner` the inner join's rows (`{o}_inner`) and
    ///   `m_l`, `m_r` each side's rows with a partner (`{o}_left`,
    ///   `{o}_right`): `X = i + l − m_l` (left), `i + r − m_r` (right),
    ///   `i + l − m_l + r − m_r` (full), `l − m_l` (left anti, not
    ///   NULL-aware), `r − m_r` (right anti). Each `m ≤` its side and `≤ i`,
    ///   `i ≥ 1 ⇒ m ≥ 1`; `m = i` if the other side's key is unique, and
    ///   `m = i =` its side on a foreign key from it.
    pub fn join_parts(&mut self, join: &Join, o: &OpOutput, l: &OpOutput, r: &OpOutput, inner: &Int, keys: JoinKeys) {
        let parts = auxiliary_joins(join);
        if parts.is_empty() {
            return;
        }
        let JoinKeys { right_unique: ru, left_unique: lu, fk_left: fl, fk_right: fr } = keys;
        let name = self.name_of(&o.card);
        let mut count = |suffix: &str| {
            parts.iter().any(|(s, _)| *s == suffix).then(|| self.new_var(format!("{name}_{suffix}")))
        };
        let (i, ml, mr) = (count("inner"), count("left"), count("right"));
        if let Some(i) = &i {
            self.assert(i.le(inner));
        }
        // Each side's rows with a partner. Each matches at most once if the
        // other side's key is unique, and exactly once on a foreign key.
        for (m, side, unique, foreign) in [(&ml, &l.card, ru, fl), (&mr, &r.card, lu, fr)] {
            if let (Some(i), true) = (&i, foreign) {
                self.assert(i.eq(side));
            }
            let Some(m) = m else { continue };
            self.assert(m.le(side));
            if foreign {
                self.assert(m.eq(side));
            }
            let Some(i) = &i else { continue };
            self.assert(m.le(i));
            // A matched pair has a row on each side.
            self.assert(i.ge(int(1)).implies(m.ge(int(1))));
            if unique {
                self.assert(i.eq(m));
            }
        }
        let unmatched = |side: &Int, m: &Option<Int>| m.as_ref().map(|m| Int::sub(&[side, m]));
        let (ul, ur) = (unmatched(&l.card, &ml), unmatched(&r.card, &mr));
        let rows = match (join.join_type, &i, &ul, &ur) {
            (JoinType::Left, Some(i), Some(ul), _) => Int::add(&[i, ul]),
            (JoinType::Right, Some(i), _, Some(ur)) => Int::add(&[i, ur]),
            (JoinType::Full, Some(i), Some(ul), Some(ur)) => Int::add(&[i, ul, ur]),
            (JoinType::LeftAnti, _, Some(ul), _) => ul.clone(),
            (JoinType::RightAnti, _, _, Some(ur)) => ur.clone(),
            _ => return,
        };
        self.assert(o.card.eq(&rows));
    }

    /// Part of [`Self::join`]: an equi-join on one key keeps the key values
    /// both sides share. Where both sides' non-NULL values lie among one
    /// table's referenced key values (by foreign keys), at most `|T|` of them,
    /// the shared ones number at least `ndv_l + ndv_r − |T|`
    /// (inclusion–exclusion), less one per side whose key may be NULL. An anti
    /// join (not NULL-aware) keeps each row whose key the other side lacks:
    /// `ndv ≥ ndv_l − 1 − ndv_r`.
    pub fn join_overlap(&self, join: &Join, o: &OpOutput, l: &OpOutput, r: &OpOutput) {
        if join.on.len() != 1 || join.null_equality == NullEquality::NullEqualsNull {
            return;
        }
        let (a, b) = &join.on[0];
        let Some((ia, ib)) = exact_pair(join, a, b) else { return };
        let non_null = |side: &LogicalPlan, out: &OpOutput, i: usize| {
            let nullable = !out.facts.dom(&col(side, i), side.schema()).never_null();
            &out.ndv[i] - int(nullable as u64)
        };
        let (vl, vr) = (non_null(&join.left, l, ia), non_null(&join.right, r, ib));
        let out = match join.join_type {
            JoinType::LeftAnti if !join.null_aware => return self.assert(o.ndv[ia].ge(&vl - &r.ndv[ib])),
            JoinType::RightAnti if !join.null_aware => return self.assert(o.ndv[ib].ge(&vr - &l.ndv[ia])),
            JoinType::Inner | JoinType::LeftSemi if join.filter.is_none() => &o.ndv[ia],
            JoinType::RightSemi if join.filter.is_none() => &o.ndv[ib],
            _ => return,
        };
        let (Some((p, lf)), Some((q, rf))) = (self.universe(&join.left, a), self.universe(&join.right, b)) else { return };
        let Some(t) = self.tables.values().find(|t| p == q && t.display == p) else { return };
        // A foreign key's values are never NULL.
        let vl = if lf { l.ndv[ia].clone() } else { vl };
        let vr = if rf { r.ndv[ib].clone() } else { vr };
        self.assert(out.ge(vl + vr - &t.var));
    }

    /// Part of [`Self::join`]: on an inner join, a side whose rows each match
    /// exactly once (a foreign key to all of the other's table) keeps every
    /// value of its columns, `ndv ≥` its own; and each pair of equi-keys
    /// holds equal values on every row, so equal `ndv`.
    pub fn join_ndv_kept(&self, join: &Join, o: &OpOutput, l: &OpOutput, r: &OpOutput, keys: JoinKeys) {
        if join.join_type != JoinType::Inner {
            return;
        }
        let nl = l.ndv.len();
        if keys.fk_left {
            self.kept(o, l, 0);
        }
        if keys.fk_right {
            self.kept(o, r, nl);
        }
        for (ia, ib) in join.on.iter().filter_map(|(a, b)| exact_pair(join, a, b)) {
            self.assert(o.ndv[ia].eq(&o.ndv[nl + ib]));
        }
    }

    /// The table whose referenced key holds every non-NULL value of `side`'s
    /// column `e`, by a single-column foreign key: the referenced table, if
    /// `e` holds the referencing column, and whether it does (so is never
    /// NULL).
    fn universe(&self, side: &LogicalPlan, e: &Expr) -> Option<(String, bool)> {
        let c = key_column(side, e)?;
        let (table, _, column) = self.stored_column(side, &c, String::new())?;
        self.foreign_keys.iter().filter(|fk| fk.columns.len() == 1).find_map(|fk| {
            if fk.table == table && fk.columns[0] == column {
                Some((fk.references.clone(), true))
            } else if fk.references == table && fk.referenced[0] == column {
                Some((table.clone(), false))
            } else {
                None
            }
        })
    }

    /// Whether `join` is on exactly a declared foreign key's columns, from the
    /// left side's values to every row of the table they reference, and from
    /// the right's.
    pub(crate) fn foreign_key(&self, join: &Join) -> (bool, bool) {
        if join.on.is_empty() || join.filter.is_some() {
            return (false, false);
        }
        let from_left = self.references(&join.left, &join.right, join.on.iter().map(|(a, b)| (a, b)));
        let from_right = self.references(&join.right, &join.left, join.on.iter().map(|(a, b)| (b, a)));
        (from_left, from_right)
    }

    /// True if each pair `(f, t)` compares a column of `from` with one of
    /// `to`, together exactly a foreign key's columns: `from`'s hold one row's
    /// values of the referencing columns, and `to` holds every row of the
    /// referenced table once.
    pub(crate) fn references<'e>(
        &self,
        from: &LogicalPlan,
        to: &LogicalPlan,
        pairs: impl Iterator<Item = (&'e Expr, &'e Expr)>,
    ) -> bool {
        let mut source: Option<(String, String)> = None;
        let mut target: Option<String> = None;
        let mut cols = vec![];
        for (f, t) in pairs {
            let (Some(fc), Some(tc)) = (key_column(from, f), key_column(to, t)) else {
                return false;
            };
            let (Some((ft, row, fname)), Some((tt, tname))) =
                (self.stored_column(from, &fc, String::new()), self.every_row(to, &tc))
            else {
                return false;
            };
            if *source.get_or_insert((ft.clone(), row.clone())) != (ft, row)
                || *target.get_or_insert(tt.clone()) != tt
            {
                return false;
            }
            cols.push((fname, tname));
        }
        let (Some((from_table, _)), Some(to_table)) = (source, target) else {
            return false;
        };
        cols.sort();
        cols.dedup();
        self.foreign_keys.iter().any(|fk| {
            let pairs: Vec<(String, String)> =
                fk.pairs().into_iter().map(|(a, b)| (a.to_string(), b.to_string())).collect();
            fk.table == from_table && fk.references == to_table && pairs == cols
        })
    }

    /// The stored column whose values column `c` of `plan` holds on every
    /// row: `(table, row, column)`, where columns with the same `row` hold
    /// values of one row of the table. `path` names the scan by the join
    /// sides leading to it, so two reads of one table stay apart.
    pub(crate) fn stored_column(&self, plan: &LogicalPlan, c: &Column, path: String) -> Option<(String, String, String)> {
        let i = plan.schema().index_of_column(c).ok()?;
        let through = |child: &LogicalPlan, path: String| self.stored_column(child, &child_column(child, i)?, path);
        match plan {
            LogicalPlan::TableScan(scan) => match (self.resolve)(scan) {
                ScanKind::Base { display, .. } => Some((display, path, c.name.clone())),
                ScanKind::NonBase => None,
            },
            LogicalPlan::Projection(p) => self.stored_column(&p.input, &key_column(&p.input, &p.expr[i])?, path),
            LogicalPlan::Aggregate(a) => {
                let key = a.group_expr.get(i)?;
                self.stored_column(&a.input, &key_column(&a.input, key)?, path)
            }
            p if let Some((input, _)) = passed_rows(p) => through(input, path),
            // A padded side's columns may be NULL.
            LogicalPlan::Join(join) => {
                let nl = join.left.schema().fields().len();
                match join.join_type {
                    JoinType::Inner | JoinType::Left if i < nl => through(&join.left, path + "L"),
                    JoinType::Inner | JoinType::Right if i >= nl => {
                        let child = &join.right;
                        self.stored_column(child, &child_column(child, i - nl)?, path + "R")
                    }
                    JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => through(&join.left, path),
                    JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => through(&join.right, path),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The stored table and column, if `plan` holds each of the table's rows
    /// exactly once and column `c` holds that column.
    pub(crate) fn every_row(&self, plan: &LogicalPlan, c: &Column) -> Option<(String, String)> {
        let i = plan.schema().index_of_column(c).ok()?;
        let through = |child: &LogicalPlan| self.every_row(child, &child_column(child, i)?);
        match plan {
            LogicalPlan::TableScan(scan) if scan.filters.is_empty() && scan.fetch.is_none() => {
                match (self.resolve)(scan) {
                    ScanKind::Base { display, .. } => Some((display, c.name.clone())),
                    ScanKind::NonBase => None,
                }
            }
            LogicalPlan::Projection(p) => self.every_row(&p.input, &key_column(&p.input, &p.expr[i])?),
            p if let Some((input, true)) = passed_rows(p) => through(input),
            // A side whose rows each match exactly once (a foreign key to all
            // of the other's table), or on an outer join at most once, keeps
            // each of them once.
            LogicalPlan::Join(join) if join.filter.is_none() && !join.on.is_empty() => {
                let nl = join.left.schema().fields().len();
                let (fl, fr) = self.foreign_key(join);
                let unique = |side: &LogicalPlan, keys: Vec<&Expr>| self.key_is_unique(join, side, &keys);
                let (lk, rk): (Vec<&Expr>, Vec<&Expr>) = join.on.iter().map(|(a, b)| (a, b)).unzip();
                let left = || self.every_row(&join.left, &child_column(&join.left, i)?);
                let right = || self.every_row(&join.right, &child_column(&join.right, i - nl)?);
                match join.join_type {
                    JoinType::Inner if i < nl && fl => left(),
                    JoinType::Inner if i >= nl && fr => right(),
                    JoinType::Left if i < nl && (fl || unique(&join.right, rk)) => left(),
                    JoinType::Right if i >= nl && (fr || unique(&join.left, lk)) => right(),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Part of [`Self::join`]: on an inner join, the two equi-keys' values
    /// are the same, and so are their ranges; its filter orders its columns'
    /// ([`Self::range_pairs`]). Disjoint ranges leave no row with a value, so
    /// none at all.
    pub fn join_ranges(&self, plan: &LogicalPlan, join: &Join, o: &OpOutput) {
        if join.join_type != JoinType::Inner {
            return;
        }
        let nl = join.left.schema().fields().len();
        for (ia, ib) in join.on.iter().filter_map(|(a, b)| exact_pair(join, a, b)) {
            if let (Some(a_lo), Some(a_hi), Some(b_lo), Some(b_hi)) = (&o.min[ia], &o.max[ia], &o.min[nl + ib], &o.max[nl + ib])
                && o.unit[ia] == o.unit[nl + ib]
            {
                self.assert(a_lo.eq(b_lo));
                self.assert(a_hi.eq(b_hi));
            }
        }
        if let Some(f) = &join.filter {
            self.range_pairs(f, plan, o);
        }
    }

    /// Part of [`Self::join`]: what a join's output columns hold of its
    /// inputs'. A side no row pads [holds](super::op_output) its rows, and a
    /// preserved side (left of a left join) every value. A padded side's
    /// rows, or NULL: `ndv ≤` its own `+ 1`, values within its range. A semi
    /// or anti join is a [`subset`](super::op_output) of the kept side, a mark
    /// join the [same rows](super::op_output), and a semi join's equi-key
    /// holds the other side's key (not floats, merged by SQL equality).
    pub fn join_sides(&self, join: &Join, o: &OpOutput, l: &OpOutput, r: &OpOutput) {
        let (nl, nr) = (l.ndv.len(), r.ndv.len());
        match join.join_type {
            JoinType::Inner => {
                self.assert_property("wider", within(&columns(o, l, &aligned(nl, 0))));
                self.assert_property("wider", within(&columns(o, r, &aligned(nr, nl))));
            }
            JoinType::Left => {
                self.assert_property("wider", within(&columns(o, l, &aligned(nl, 0))));
                self.kept(o, l, 0);
                self.padded(o, r, nl);
            }
            JoinType::Right => {
                self.padded(o, l, 0);
                self.assert_property("wider", within(&columns(o, r, &aligned(nr, nl))));
                self.kept(o, r, nl);
            }
            JoinType::Full => {
                self.padded(o, l, 0);
                self.padded(o, r, nl);
            }
            JoinType::LeftSemi | JoinType::LeftAnti => {
                self.assert_property("subset", within(&with_card(o, l, &aligned(nl, 0))))
            }
            JoinType::RightSemi | JoinType::RightAnti => {
                self.assert_property("subset", within(&with_card(o, r, &aligned(nr, 0))))
            }
            JoinType::LeftMark => self.assert_property("same rows", same(&with_card(o, l, &aligned(nl, 0)))),
            JoinType::RightMark => self.assert_property("same rows", same(&with_card(o, r, &aligned(nr, 0)))),
        }
        // Matched equi-key values exist on both sides.
        let semi = match join.join_type {
            JoinType::LeftSemi => true,
            JoinType::RightSemi => false,
            _ => return,
        };
        let keys: Vec<(usize, usize)> = join
            .on
            .iter()
            .filter_map(|(a, b)| exact_pair(join, a, b))
            .map(|(ia, ib)| if semi { (ia, ib) } else { (ib, ia) })
            .collect();
        self.assert_property("wider", within(&columns(o, if semi { r } else { l }, &keys)));
    }

    /// `side`'s columns, from `o`'s position `at` on, keep every value of
    /// `side`'s: each of its rows is one of `o`'s.
    fn kept(&self, o: &OpOutput, side: &OpOutput, at: usize) {
        for (i, v) in side.ndv.iter().enumerate() {
            self.assert(o.ndv[at + i].ge(v));
        }
    }

    /// `side`'s columns, from `o`'s position `at` on, hold a row of `side`
    /// or NULL.
    fn padded(&self, o: &OpOutput, side: &OpOutput, at: usize) {
        for (i, v) in side.ndv.iter().enumerate() {
            self.assert(o.ndv[at + i].le(v + int(1)));
        }
        self.assert_property("within", within(&ranges(o, side, &aligned(side.ndv.len(), at))));
    }
}

/// What a join's keys say of how its rows match.
#[derive(Debug, Clone, Copy)]
pub struct JoinKeys {
    /// The right key is unique: each left row matches at most once.
    pub right_unique: bool,
    /// The left key is unique: each right row matches at most once.
    pub left_unique: bool,
    /// The keys are a foreign key from the left to every row of the right
    /// side's table: each left row matches exactly once.
    pub fk_left: bool,
    /// The mirror: each right row matches exactly once.
    pub fk_right: bool,
}

/// The positions of equi-key pair `a = b` in `join`'s left and right
/// inputs, if both are columns and not floats ([`exact_index`]).
pub(crate) fn exact_pair(join: &Join, a: &Expr, b: &Expr) -> Option<(usize, usize)> {
    Some((exact_index(&join.left, a)?, exact_index(&join.right, b)?))
}

/// Positions of `side`'s columns that are never NULL on a row matched by
/// `join`: those never NULL on `side`, and its equi-key columns `keys`
/// (unless NULL keys match).
pub(crate) fn never_null_when_matched(join: &Join, side: &LogicalPlan, facts: &Facts, keys: &[&Expr]) -> Vec<usize> {
    let schema = side.schema();
    let keys_non_null = join.null_equality != NullEquality::NullEqualsNull;
    (0..schema.fields().len())
        .filter(|&i| {
            let c = super::field_col(schema, i);
            let key = keys_non_null && keys.iter().any(|k| strip_alias(k) == &c);
            key || facts.dom(&c, schema).never_null()
        })
        .collect()
}

/// Facts on a join's output: each side's facts, NULL on a padded side, and
/// matched equi-keys take values both sides have.
pub(crate) fn join_facts(plan: &LogicalPlan, join: &Join, l: &Facts, r: &Facts) -> Facts {
    let schema = plan.schema();
    let nulls_match = join.null_equality == NullEquality::NullEqualsNull;
    // The values a matched pair of keys takes.
    let matched = |a: &Expr, b: &Expr| {
        let d = l
            .dom(a, join.left.schema())
            .intersect(&r.dom(b, join.right.schema()));
        if nulls_match { d } else { d.without_null() }
    };
    let mut out = match join.join_type {
        JoinType::Inner | JoinType::Left | JoinType::Right | JoinType::Full => {
            let pad_left = matches!(join.join_type, JoinType::Right | JoinType::Full);
            let pad_right = matches!(join.join_type, JoinType::Left | JoinType::Full);
            let mut out = if pad_left { l.nullable() } else { l.clone() };
            out.extend(&if pad_right { r.nullable() } else { r.clone() });
            out
        }
        JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => l.clone(),
        JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => r.clone(),
    };
    match join.join_type {
        JoinType::Inner => {
            for (a, b) in &join.on {
                out.add(a, matched(a, b), schema);
                out.add(b, matched(a, b), schema);
            }
            if let Some(f) = &join.filter {
                out.assume(f, schema);
            }
        }
        JoinType::LeftSemi => {
            for (a, b) in &join.on {
                out.add(a, matched(a, b), schema);
            }
        }
        JoinType::RightSemi => {
            for (a, b) in &join.on {
                out.add(b, matched(a, b), schema);
            }
        }
        _ => {}
    }
    out
}

/// The joins whose counts an outer or anti join's rows are stated in terms
/// of, as (suffix of the count's variable, join type).
pub(crate) fn auxiliary_joins(join: &Join) -> Vec<(&'static str, JoinType)> {
    let (inner, left, right) = (
        ("inner", JoinType::Inner),
        ("left", JoinType::LeftSemi),
        ("right", JoinType::RightSemi),
    );
    match join.join_type {
        JoinType::Left => vec![inner, left],
        JoinType::Right => vec![inner, right],
        JoinType::Full => vec![inner, left, right],
        JoinType::LeftAnti if !join.null_aware => vec![left],
        JoinType::RightAnti => vec![right],
        _ => vec![],
    }
}
