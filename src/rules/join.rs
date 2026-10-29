//! Joins of every kind.

use datafusion::common::{Column, JoinType, NullEquality};
use datafusion::logical_expr::Expr;
use datafusion::logical_expr::logical_plan::{Distinct, Join, LogicalPlan};
use z3::ast::Int;

use super::{child_column, col, column_index, key_column, strip_alias};
use crate::analysis::{Analyzer, Rel, Rows, ScanKind, int, min};
use crate::domain::Facts;
use crate::selectivity::auxiliary_joins;

impl<'a> Analyzer<'a> {
    pub(crate) fn join(&mut self, plan: &LogicalPlan, join: &Join) -> Rel {
        let l = self.visit(&join.left);
        let r = self.visit(&join.right);
        let equi = !join.on.is_empty();
        let cross = !equi && join.filter.is_none();
        let (lk, rk): (Vec<&Expr>, Vec<&Expr>) = join.on.iter().map(|(a, b)| (a, b)).unzip();
        // A unique key on one side means each row of the other side matches at
        // most once.
        let ru = equi && self.key_is_unique(join, &join.right, &rk);
        let lu = equi && self.key_is_unique(join, &join.left, &lk);
        // A foreign key from one side to every row of the other's table: each
        // of the first side's rows matches exactly once.
        let (fl, fr) = self.foreign_key(join);
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
            JoinType::LeftSemi | JoinType::LeftAnti => self.assert(o.card.le(&l.card)),
            JoinType::RightSemi | JoinType::RightAnti => self.assert(o.card.le(&r.card)),
            JoinType::LeftMark => self.assert(o.card.eq(&l.card)),
            JoinType::RightMark => self.assert(o.card.eq(&r.card)),
        }
        self.join_parts(join, &o, &l, &r, &inner, (ru, lu, fl, fr));
        self.at_most_once = (ru || fl, lu || fr);
        self.join_ndv(join, &o, &l, &r);
        self.join_ranges(plan, join, &o, &l, &r);
        o.facts = join_facts(plan, join, &l.facts, &r.facts);
        // Semi, anti and mark joins keep a subset of one side's rows.
        o.rows = match join.join_type {
            JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => l.rows.clone(),
            JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => r.rows.clone(),
            _ => Rows::default(),
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
                o.rows.nulls.push((col(plan, nl + c), l.card.clone(), values.clone()));
            }
        }
        if pad_left {
            let values = if full { Int::add(&[&inner, &l.card]) } else { inner.clone() };
            let keys = if full { &[][..] } else { &lk[..] };
            for c in never_null_when_matched(join, &join.left, &l.facts, keys) {
                o.rows.nulls.push((col(plan, c), r.card.clone(), values.clone()));
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

    /// An outer or anti join's rows, in terms of its inner join's rows
    /// (`{o}_inner`) and the rows of each side with a partner (`{o}_left`,
    /// `{o}_right`): the counts `validate` measures its selectivities with
    /// (`selectivity::auxiliary_joins`). `inner` bounds the inner join's rows;
    /// `keys` says whether the right and left keys are unique, and whether a
    /// foreign key goes from the left or the right side to all of the other.
    pub(crate) fn join_parts(&mut self, join: &Join, o: &Rel, l: &Rel, r: &Rel, inner: &Int, keys: (bool, bool, bool, bool)) {
        let parts = auxiliary_joins(join);
        if parts.is_empty() {
            return;
        }
        let (ru, lu, fl, fr) = keys;
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
                (self.values(from, &fc, String::new()), self.every_row(to, &tc))
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
    pub(crate) fn values(&self, plan: &LogicalPlan, c: &Column, path: String) -> Option<(String, String, String)> {
        let i = plan.schema().index_of_column(c).ok()?;
        let through = |child: &LogicalPlan, path: String| self.values(child, &child_column(child, i)?, path);
        match plan {
            LogicalPlan::TableScan(scan) => match (self.resolve)(scan) {
                ScanKind::Base { display, .. } => Some((display, path, c.name.clone())),
                ScanKind::NonBase => None,
            },
            LogicalPlan::Projection(p) => self.values(&p.input, &key_column(&p.input, &p.expr[i])?, path),
            LogicalPlan::Aggregate(a) => {
                let key = a.group_expr.get(i)?;
                self.values(&a.input, &key_column(&a.input, key)?, path)
            }
            LogicalPlan::Filter(_)
            | LogicalPlan::Sort(_)
            | LogicalPlan::Limit(_)
            | LogicalPlan::Repartition(_)
            | LogicalPlan::SubqueryAlias(_)
            | LogicalPlan::Subquery(_)
            | LogicalPlan::Window(_)
            | LogicalPlan::Distinct(Distinct::All(_)) => through(plan.inputs()[0], path),
            // A padded side's columns may be NULL.
            LogicalPlan::Join(join) => {
                let nl = join.left.schema().fields().len();
                match join.join_type {
                    JoinType::Inner | JoinType::Left if i < nl => through(&join.left, path + "L"),
                    JoinType::Inner | JoinType::Right if i >= nl => {
                        let child = &join.right;
                        self.values(child, &child_column(child, i - nl)?, path + "R")
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
            LogicalPlan::Sort(s) if s.fetch.is_none() => through(&s.input),
            LogicalPlan::Repartition(_)
            | LogicalPlan::SubqueryAlias(_)
            | LogicalPlan::Subquery(_)
            | LogicalPlan::Window(_) => through(plan.inputs()[0]),
            _ => None,
        }
    }

    /// A join's output values are its inputs', and matched equi-keys take
    /// values both sides have: on an inner join, the two keys' values are
    /// the same. Disjoint ranges leave no row with a value, so none at all.
    pub(crate) fn join_ranges(&self, plan: &LogicalPlan, join: &Join, o: &Rel, l: &Rel, r: &Rel) {
        let nl = l.min.len();
        let (left, right) = match join.join_type {
            JoinType::Inner | JoinType::Left | JoinType::Right | JoinType::Full => (Some(0), Some(nl)),
            JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => (Some(0), None),
            JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => (None, Some(0)),
        };
        for (side, at) in [(l, left), (r, right)] {
            if let Some(at) = at {
                for i in 0..side.min.len() {
                    self.within(o, at + i, side, i);
                }
            }
        }
        if !matches!(join.join_type, JoinType::Inner | JoinType::LeftSemi | JoinType::RightSemi) {
            return;
        }
        for (a, b) in &join.on {
            let (Some(ia), Some(ib)) = (column_index(&join.left, a), column_index(&join.right, b)) else { continue };
            match join.join_type {
                JoinType::Inner => {
                    self.within(o, ia, r, ib);
                    self.within(o, nl + ib, l, ia);
                    if let (Some(a_lo), Some(a_hi), Some(b_lo), Some(b_hi)) = (&o.min[ia], &o.max[ia], &o.min[nl + ib], &o.max[nl + ib]) {
                        self.assert(a_lo.eq(b_lo));
                        self.assert(a_hi.eq(b_hi));
                    }
                }
                JoinType::LeftSemi => self.within(o, ia, r, ib),
                _ => self.within(o, ib, l, ia),
            }
        }
        if let (JoinType::Inner, Some(f)) = (join.join_type, &join.filter) {
            self.range_pairs(f, plan, o);
        }
    }

    /// NDVs of a join's output columns: values come from the inputs, plus NULL
    /// on a padded side, and equi-key columns only keep values both sides share.
    pub(crate) fn join_ndv(&self, join: &Join, o: &Rel, l: &Rel, r: &Rel) {
        let (nl, nr) = (l.ndv.len(), r.ndv.len());
        // (output position, input rel, input position, padded, exact)
        let mut map: Vec<(usize, &Rel, usize, bool, bool)> = vec![];
        match join.join_type {
            JoinType::Inner | JoinType::Left | JoinType::Right | JoinType::Full => {
                let left_padded = matches!(join.join_type, JoinType::Right | JoinType::Full);
                let right_padded = matches!(join.join_type, JoinType::Left | JoinType::Full);
                let left_exact = join.join_type == JoinType::Left;
                let right_exact = join.join_type == JoinType::Right;
                map.extend((0..nl).map(|i| (i, l, i, left_padded, left_exact)));
                map.extend((0..nr).map(|i| (nl + i, r, i, right_padded, right_exact)));
            }
            JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => {
                map.extend((0..nl).map(|i| (i, l, i, false, join.join_type == JoinType::LeftMark)));
            }
            JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => {
                map.extend(
                    (0..nr).map(|i| (i, r, i, false, join.join_type == JoinType::RightMark)),
                );
            }
        }
        for (out, rel, i, padded, exact) in map {
            let src = &rel.ndv[i];
            if exact {
                // Every row of this side appears (a preserved side, or a mark join).
                self.assert(o.ndv[out].eq(src));
            } else if padded {
                self.assert(o.ndv[out].le(src + int(1)));
            } else {
                self.assert(o.ndv[out].le(src));
            }
        }
        // Matched equi-key values exist on both sides.
        let matches_only = matches!(
            join.join_type,
            JoinType::Inner | JoinType::LeftSemi | JoinType::RightSemi
        );
        if !matches_only {
            return;
        }
        for (a, b) in &join.on {
            let (Some(ca), Some(cb)) = (key_column(&join.left, a), key_column(&join.right, b))
            else {
                continue;
            };
            let (Ok(ia), Ok(ib)) = (
                join.left.schema().index_of_column(&ca),
                join.right.schema().index_of_column(&cb),
            ) else {
                continue;
            };
            if join.left.schema().field(ia).data_type().is_floating()
                || join.right.schema().field(ib).data_type().is_floating()
            {
                continue;
            }
            match join.join_type {
                JoinType::Inner => {
                    self.assert(o.ndv[ia].le(&r.ndv[ib]));
                    self.assert(o.ndv[nl + ib].le(&l.ndv[ia]));
                }
                JoinType::LeftSemi => self.assert(o.ndv[ia].le(&r.ndv[ib])),
                JoinType::RightSemi => self.assert(o.ndv[ib].le(&l.ndv[ia])),
                _ => {}
            }
        }
    }
}

/// Positions of `side`'s columns that are never NULL on a row matched by
/// `join`: those never NULL on `side`, and its equi-key columns `keys`
/// (unless NULL keys match).
pub(crate) fn never_null_when_matched(join: &Join, side: &LogicalPlan, facts: &Facts, keys: &[&Expr]) -> Vec<usize> {
    let schema = side.schema();
    let keys_non_null = join.null_equality != NullEquality::NullEqualsNull;
    (0..schema.fields().len())
        .filter(|&i| {
            let c = Expr::Column(Column::from(schema.qualified_field(i)));
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
