//! Which columns determine a relation's rows: declared keys, followed through
//! the plan, and the functional dependencies they imply.

use std::collections::BTreeSet;

use datafusion::common::{Column, Constraint, JoinType, NullEquality};
use datafusion::logical_expr::Expr;
use datafusion::logical_expr::logical_plan::{Distinct, Join, LogicalPlan};

use crate::analysis::{Analyzer, ScanKind};
use crate::rules::{
    child_column, column_index, determined, equalities, exact_index, key_column, output_indices, pinned, same_positions,
    strip_alias, with_equalities,
};

impl<'a> Analyzer<'a> {
    /// True if each row of the other side of `join` matches at most one row of
    /// `side` on its key expressions `keys` (see `covers_key`): the keys are
    /// columns, possibly under injective casts, unique in `side`'s output. NULL
    /// keys match nothing unless the join compares them as equal.
    pub(crate) fn key_is_unique(&self, join: &Join, side: &LogicalPlan, keys: &[&Expr]) -> bool {
        let Some(cols) = keys
            .iter()
            .map(|e| key_column(side, e))
            .collect::<Option<Vec<Column>>>()
        else {
            return false;
        };
        let nulls = match join.null_equality {
            NullEquality::NullEqualsNothing => Nulls::Distinct,
            NullEquality::NullEqualsNull => Nulls::Equal,
        };
        self.covers_key(side, &cols, nulls)
    }

    /// True if `cols` of `plan`'s output are unique, with NULLs compared as
    /// `nulls` says: they trace back to a declared primary key, a UNIQUE
    /// constraint, a GROUP BY key or a DISTINCT output through operators that
    /// never duplicate rows. A UNIQUE column may hold many NULLs, so it is
    /// unique with NULLs equal only if it is NOT NULL.
    pub(crate) fn covers_key(&self, plan: &LogicalPlan, cols: &[Column], nulls: Nulls) -> bool {
        match plan {
            LogicalPlan::TableScan(scan) => {
                let schema = scan.source.schema();
                let Some(indices) = cols
                    .iter()
                    .map(|c| schema.index_of(&c.name).ok())
                    .collect::<Option<Vec<usize>>>()
                else {
                    return false;
                };
                let unique = |u: &[usize]| {
                    u.iter().all(|i| indices.contains(i))
                        && (nulls == Nulls::Distinct || u.iter().all(|i| !schema.field(*i).is_nullable()))
                };
                let declared = scan.source.constraints().is_some_and(|cs| {
                    cs.iter().any(|c| match c {
                        Constraint::PrimaryKey(pk) => pk.iter().all(|i| indices.contains(i)),
                        Constraint::Unique(u) => unique(u),
                    })
                });
                // A foreign key references a key, so its referenced columns
                // are unique, like a UNIQUE constraint's.
                let ScanKind::Base { display, .. } = (self.resolve)(scan) else {
                    return declared;
                };
                declared
                    || self.foreign_keys.iter().filter(|fk| fk.references == display).any(|fk| {
                        let referenced: Option<Vec<usize>> =
                            fk.referenced.iter().map(|c| schema.index_of(c).ok()).collect();
                        referenced.is_some_and(|r| unique(&r))
                    })
            }
            // A column the filter pins to one value adds nothing to tell its rows
            // apart: if the input is unique on it with `cols`, the filter's rows
            // are unique on `cols` alone, e.g. `rn = 1` over `row_number()`.
            LogicalPlan::Filter(f) => {
                let Some(cs) = same_positions(plan, &f.input, cols) else {
                    return false;
                };
                if self.covers_key(&f.input, &cs, nulls) {
                    return true;
                }
                let mut with = cs.clone();
                for c in pinned(&f.predicate) {
                    if f.input.schema().has_column(&c) && !with.contains(&c) {
                        with.push(c);
                    }
                }
                with.len() > cs.len() && self.covers_key(&f.input, &with, nulls)
            }
            // `row_number()` numbers each partition's rows 1, 2, ...: it is unique
            // with its partition columns. Otherwise the window keeps its input's
            // rows, so the input's keys among `cols` stay unique.
            LogicalPlan::Window(w) => {
                let Some(ix) = output_indices(plan, cols) else {
                    return false;
                };
                let n = w.input.schema().fields().len();
                let numbered = ix.iter().filter(|&&i| i >= n).any(|&i| match strip_alias(&w.window_expr[i - n]) {
                    Expr::WindowFunction(f) if f.fun.name() == "row_number" && f.params.filter.is_none() => {
                        f.params.partition_by.iter().all(|p| match strip_alias(p) {
                            Expr::Column(c) => w.input.schema().index_of_column(c).is_ok_and(|j| ix.contains(&j)),
                            _ => false,
                        })
                    }
                    _ => false,
                });
                let kept: Vec<Column> = ix
                    .iter()
                    .filter(|&&i| i < n)
                    .map(|&i| Column::from(w.input.schema().qualified_field(i)))
                    .collect();
                numbered || (!kept.is_empty() && self.covers_key(&w.input, &kept, nulls))
            }
            // Operators whose output rows are a subset of their input's, with the
            // input's columns first and unchanged.
            LogicalPlan::Sort(_)
            | LogicalPlan::Limit(_)
            | LogicalPlan::Repartition(_)
            | LogicalPlan::SubqueryAlias(_) => {
                let child = plan.inputs()[0];
                same_positions(plan, child, cols).is_some_and(|cs| self.covers_key(child, &cs, nulls))
            }
            // DISTINCT's output is unique on all its columns, and is a subset of its
            // input's rows, so its input's keys stay unique too.
            LogicalPlan::Distinct(Distinct::All(input)) => {
                let all = output_indices(plan, cols)
                    .is_some_and(|ix| (0..plan.schema().fields().len()).all(|i| ix.contains(&i)));
                all || same_positions(plan, input, cols)
                    .is_some_and(|cs| self.covers_key(input, &cs, nulls))
            }
            // DISTINCT ON is unique on its ON expressions, where they are selected
            // as columns; its rows are a subset of its input's.
            LogicalPlan::Distinct(Distinct::On(on)) => {
                let Some(ix) = output_indices(plan, cols) else {
                    return false;
                };
                let on_positions: Option<Vec<usize>> = on
                    .on_expr
                    .iter()
                    .map(|e| {
                        let c = key_column(&on.input, e)?;
                        on.select_expr
                            .iter()
                            .position(|s| key_column(&on.input, s).as_ref() == Some(&c))
                    })
                    .collect();
                let by_on = on_positions.is_some_and(|ps| ps.iter().all(|p| ix.contains(p)));
                let mapped: Option<Vec<Column>> = ix
                    .iter()
                    .map(|&i| key_column(&on.input, &on.select_expr[i]))
                    .collect();
                by_on || mapped.is_some_and(|cs| self.covers_key(&on.input, &cs, nulls))
            }
            // GROUP BY emits one row per distinct combination of its keys (NULLs
            // forming one group), so it is unique on all its key columns, and on any
            // keys that are unique in its input. With no GROUP BY there is exactly
            // one row, unique on anything. ROLLUP / CUBE / GROUPING SETS repeat keys
            // across grouping levels.
            LogicalPlan::Aggregate(agg) => {
                if agg
                    .group_expr
                    .iter()
                    .any(|e| matches!(e, Expr::GroupingSet(_)))
                {
                    return false;
                }
                if agg.group_expr.is_empty() {
                    return true;
                }
                let Some(ix) = output_indices(plan, cols) else {
                    return false;
                };
                let groups = agg.group_expr.len();
                if (0..groups).all(|i| ix.contains(&i)) {
                    return true;
                }
                let mapped: Option<Vec<Column>> = ix
                    .iter()
                    .map(|&i| {
                        if i < groups {
                            key_column(&agg.input, &agg.group_expr[i])
                        } else {
                            None
                        }
                    })
                    .collect();
                if mapped.is_some_and(|cs| self.covers_key(&agg.input, &cs, nulls)) {
                    return true;
                }
                // Columns that determine every key pick out one group.
                let closed = self.fd_closure(plan, &ix);
                (0..groups).all(|i| closed.contains(&i))
            }
            LogicalPlan::Projection(p) => {
                let mapped = cols
                    .iter()
                    .map(|c| {
                        let i = p.schema.index_of_column(c).ok()?;
                        key_column(&p.input, &p.expr[i])
                    })
                    .collect::<Option<Vec<Column>>>();
                mapped.is_some_and(|cs| self.covers_key(&p.input, &cs, nulls))
            }
            LogicalPlan::Join(join) => {
                let left_len = join.left.schema().fields().len();
                let Some(indices) = cols
                    .iter()
                    .map(|c| plan.schema().index_of_column(c).ok())
                    .collect::<Option<Vec<usize>>>()
                else {
                    return false;
                };
                let left_cols = || -> Option<Vec<Column>> {
                    indices
                        .iter()
                        .map(|i| child_column(&join.left, *i))
                        .collect()
                };
                let (lk, rk): (Vec<&Expr>, Vec<&Expr>) = join.on.iter().map(|(a, b)| (a, b)).unzip();
                match join.join_type {
                    // Semi, anti and mark joins emit each row of one side at most once.
                    JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => {
                        left_cols().is_some_and(|cs| self.covers_key(&join.left, &cs, nulls))
                    }
                    // These output the right side's schema (plus a mark column).
                    JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => indices
                        .iter()
                        .map(|i| child_column(&join.right, *i))
                        .collect::<Option<Vec<Column>>>()
                        .is_some_and(|cs| self.covers_key(&join.right, &cs, nulls)),
                    // A row of one side appears at most once if it matches at most one
                    // row of the other side, i.e. the join is on the other side's key.
                    // Rows agreeing on `cols` agree on its columns of that side, so
                    // they are one row if those are unique there. Only the preserved
                    // side of an outer join keeps its key, since the other side gains
                    // NULL-padded rows.
                    JoinType::Inner | JoinType::Left | JoinType::Right => {
                        let mut ix = indices.clone();
                        // An inner join's equi-keys are equal on every row it emits.
                        if join.join_type == JoinType::Inner {
                            for (a, b) in &join.on {
                                let (Some(i), Some(j)) = (column_index(&join.left, a), column_index(&join.right, b))
                                else {
                                    continue;
                                };
                                let j = left_len + j;
                                match (ix.contains(&i), ix.contains(&j)) {
                                    (true, false) => ix.push(j),
                                    (false, true) => ix.push(i),
                                    _ => {}
                                }
                            }
                        }
                        let side = |child: &LogicalPlan, on_side: &dyn Fn(usize) -> Option<usize>| {
                            ix.iter().filter_map(|&i| on_side(i)).map(|i| child_column(child, i)).collect::<Option<Vec<Column>>>()
                        };
                        let left = side(&join.left, &|i| (i < left_len).then_some(i));
                        let right = side(&join.right, &|i| i.checked_sub(left_len));
                        let left_ok = join.join_type != JoinType::Right
                            && left.as_ref().is_some_and(|cs| !cs.is_empty())
                            && self.key_is_unique(join, &join.right, &rk)
                            && left.is_some_and(|cs| self.covers_key(&join.left, &cs, nulls));
                        let right_ok = join.join_type != JoinType::Left
                            && right.as_ref().is_some_and(|cs| !cs.is_empty())
                            && self.key_is_unique(join, &join.left, &lk)
                            && right.is_some_and(|cs| self.covers_key(&join.right, &cs, nulls));
                        left_ok || right_ok
                    }
                    JoinType::Full => false,
                }
            }
            // Unions, scans of non-tables and everything else: no key to rely on.
            _ => false,
        }
    }

    /// Output columns of `plan` that `keys` (output positions) functionally
    /// determine: rows agreeing on `keys`, NULLs equal, agree on them. The
    /// dependencies come from declared keys, and are trusted as they are.
    pub(crate) fn fd_closure(&self, plan: &LogicalPlan, keys: &[usize]) -> BTreeSet<usize> {
        let mut out: BTreeSet<usize> = keys.iter().copied().collect();
        let width = plan.schema().fields().len();
        // The input's closure, for operators whose output columns start with
        // their input's, unchanged.
        let same = |input: &LogicalPlan| {
            let n = input.schema().fields().len();
            let keys: Vec<usize> = keys.iter().copied().filter(|&k| k < n).collect();
            self.fd_closure(input, &keys)
        };
        match plan {
            LogicalPlan::TableScan(_) => {
                let cols: Vec<Column> =
                    keys.iter().map(|&i| Column::from(plan.schema().qualified_field(i))).collect();
                if self.covers_key(plan, &cols, Nulls::Equal) {
                    out.extend(0..width);
                }
            }
            LogicalPlan::Projection(p) => {
                let input: Vec<usize> = keys.iter().filter_map(|&k| column_index(&p.input, &p.expr[k])).collect();
                let closed = self.fd_closure(&p.input, &input);
                out.extend((0..width).filter(|&j| determined(&p.expr[j], &p.input, &closed)));
            }
            // A column the filter pins to one value is the same on every
            // row, and columns it holds equal agree.
            LogicalPlan::Filter(f) => {
                let mut keys = keys.to_vec();
                for c in pinned(&f.predicate) {
                    if let Ok(i) = f.input.schema().index_of_column(&c) {
                        keys.push(i);
                    }
                }
                out.extend(with_equalities(keys, &equalities(&f.predicate, &f.input), |k| self.fd_closure(&f.input, k)));
            }
            // The window's own columns are not determined.
            LogicalPlan::Sort(_)
            | LogicalPlan::Limit(_)
            | LogicalPlan::Repartition(_)
            | LogicalPlan::SubqueryAlias(_)
            | LogicalPlan::Window(_)
            | LogicalPlan::Distinct(Distinct::All(_)) => out.extend(same(plan.inputs()[0])),
            LogicalPlan::Join(join) => {
                let nl = join.left.schema().fields().len();
                // A padded side's columns are NULL on unmatched rows, so its
                // dependencies don't hold on the output: only the preserved
                // side's do.
                let side = |child: &LogicalPlan, keys: &[usize], offset: usize| -> BTreeSet<usize> {
                    let n = child.schema().fields().len();
                    let keys: Vec<usize> =
                        keys.iter().filter_map(|&k| k.checked_sub(offset)).filter(|&k| k < n).collect();
                    self.fd_closure(child, &keys).into_iter().map(|i| i + offset).collect()
                };
                match join.join_type {
                    // Each equi-key pair is equal on every row the join emits.
                    JoinType::Inner => {
                        let pairs: Vec<(usize, usize)> = join
                            .on
                            .iter()
                            .filter_map(|(a, b)| Some((exact_index(&join.left, a)?, nl + exact_index(&join.right, b)?)))
                            .collect();
                        out.extend(with_equalities(keys.to_vec(), &pairs, |k| {
                            let mut closed = side(&join.left, k, 0);
                            closed.extend(side(&join.right, k, nl));
                            closed
                        }));
                    }
                    JoinType::Left | JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => {
                        out.extend(side(&join.left, keys, 0))
                    }
                    JoinType::Right => out.extend(side(&join.right, keys, nl)),
                    // These output the right side's schema (plus a mark column).
                    JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => {
                        out.extend(side(&join.right, keys, 0))
                    }
                    JoinType::Full => {}
                }
            }
            LogicalPlan::Aggregate(agg) if !agg.group_expr.iter().any(|e| matches!(e, Expr::GroupingSet(_))) => {
                let groups = agg.group_expr.len();
                let input: Vec<usize> = keys
                    .iter()
                    .filter(|&&k| k < groups)
                    .filter_map(|&k| column_index(&agg.input, &agg.group_expr[k]))
                    .collect();
                let closed = self.fd_closure(&agg.input, &input);
                out.extend((0..groups).filter(|&j| determined(&agg.group_expr[j], &agg.input, &closed)));
                // The keys pick out one group, aggregates and all.
                if (0..groups).all(|j| out.contains(&j)) {
                    out.extend(0..width);
                }
            }
            _ => {}
        }
        out
    }

    /// A smallest-by-greedy subset of `plan`'s first `n` output positions
    /// that determines all of them ([`Self::fd_closure`]).
    pub(crate) fn determining_keys(&self, plan: &LogicalPlan, n: usize) -> Vec<usize> {
        let mut keys: Vec<usize> = (0..n).collect();
        for k in 0..n {
            let rest: Vec<usize> = keys.iter().copied().filter(|&j| j != k).collect();
            let closed = self.fd_closure(plan, &rest);
            if (0..n).all(|j| closed.contains(&j)) {
                keys = rest;
            }
        }
        keys
    }
}

/// Whether two NULLs count as the same key value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Nulls {
    /// As in a GROUP BY, DISTINCT or NDV, where NULLs form one value.
    Equal,
    /// As in an equi-join, where a NULL key matches nothing.
    Distinct,
}
