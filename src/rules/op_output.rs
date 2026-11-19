//! What holds of op outputs by the plan's shape alone: of each count and
//! output whatever its operator, and of an operator's output given its
//! input's.
//!
//! # Every op output
//!
//! Asserted as each is made or finished, simplest first, one method of
//! [`Analyzer`] each:
//!
//! | When | Rules |
//! |---|---|
//! | a count is made (`Analyzer::new_var`) | [`non_negative`](Analyzer::non_negative) |
//! | an output is made (`Analyzer::fresh`) | [`ndv_within_rows`](Analyzer::ndv_within_rows), [`nonempty_ndv`](Analyzer::nonempty_ndv), [`boolean_ndv`](Analyzer::boolean_ndv) |
//! | a stored table is scanned ([`Analyzer::scan`]) | [`composite_key`](Analyzer::composite_key), [`referenced_size`](Analyzer::referenced_size), with reference plans ([`crate::joint`]) only |
//! | its rule is done (`Analyzer::finish`), by its domains | [`empty_domain`](Analyzer::empty_domain), [`ndv_within_domain`](Analyzer::ndv_within_domain), [`range_within_domain`](Analyzer::range_within_domain) |
//! | 〃, by its subset bounds | [`bounded_sum`](Analyzer::bounded_sum), [`nulls_and_values`](Analyzer::nulls_and_values) |
//! | 〃, by its keys | [`key_ndv`](Analyzer::key_ndv), `unique_columns` |
//!
//! # Given an input
//!
//! A rule knows from the plan how its output's rows are an input's. It
//! pairs the columns of its output that hold an input column's values (but
//! a float equal to one by a predicate: SQL equality merges values distinct
//! as bits, `-0.0 = 0.0`), and asserts a [property](crate::properties) of
//! the pairs these functions give:
//!
//! | Relationship | Property | Pairs |
//! |---|---|---|
//! | same rows (projection, alias, sort, ...) | [`same`](crate::properties::same) | [`with_card`] |
//! | subset (filter, limit, semi join, ...) | [`within`](crate::properties::within) | [`with_card`] |
//! | wider (inner join side, GROUP BY key, ...) | [`within`](crate::properties::within) | [`columns`] |
//! | ranges only (padded side, MIN, MAX) | [`within`](crate::properties::within) | [`ranges`] |

use datafusion::common::{Column, Constraint};
use datafusion::logical_expr::Expr;
use datafusion::logical_expr::logical_plan::{LogicalPlan, TableScan};
use z3::ast::Int;

use super::col;
use crate::analysis::{Analyzer, OpOutput, ScanKind, int, product};
use crate::builder::bare_kind;
use crate::keys::Nulls;
use crate::properties::Pair;

/// For each `(j, i)` of `columns`: `o.j`'s and `l.i`'s `Min` and `Max`, if
/// both have them in one unit. A cast of an integer to a decimal keeps the
/// value, not the count.
pub fn ranges<'a>(o: &'a OpOutput, l: &'a OpOutput, columns: &[(usize, usize)]) -> Vec<Pair<'a>> {
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
pub fn columns<'a>(o: &'a OpOutput, l: &'a OpOutput, columns: &[(usize, usize)]) -> Vec<Pair<'a>> {
    let mut out: Vec<Pair> = columns.iter().map(|&(j, i)| Pair::Ndv(&o.ndv[j], &l.ndv[i])).collect();
    out.extend(ranges(o, l, columns));
    out
}

/// `Card(o.card, l.card)`, then their [`columns`].
pub fn with_card<'a>(o: &'a OpOutput, l: &'a OpOutput, columns: &[(usize, usize)]) -> Vec<Pair<'a>> {
    let mut out = vec![Pair::Card(&o.card, &l.card)];
    out.extend(self::columns(o, l, columns));
    out
}

/// [Rules on every op output](self#every-op-output), one function each, so
/// a trace names the rule a constraint is from.
impl Analyzer<'_> {
    /// `non-negative`.
    ///
    /// - **Claim**: `v ≥ 0` for every row count and `ndv`, and each table's
    ///   size.
    pub fn non_negative(&self, v: &Int) {
        self.assert(v.ge(int(0)));
    }

    /// `ndv within rows`.
    ///
    /// - **Claim**: `ndv ≤ X` for each column.
    pub fn ndv_within_rows(&self, ndv: &Int, rows: &Int) {
        self.assert(ndv.le(rows));
    }

    /// `nonempty ndv`.
    ///
    /// - **Claim**: `X ≥ 1 ⇒ ndv ≥ 1`: a row has a value, NULL counting as
    ///   one.
    pub fn nonempty_ndv(&self, ndv: &Int, rows: &Int) {
        self.assert(rows.ge(int(1)).implies(ndv.ge(int(1))));
    }

    /// `boolean ndv`.
    ///
    /// - **Claim**: `ndv ≤ 3` for a boolean column: true, false and NULL.
    pub fn boolean_ndv(&self, ndv: &Int) {
        self.assert(ndv.le(int(3)));
    }

    /// Every rule on `out`, the output of `plan`, once its rule has found
    /// what is known of its rows: its domains, then its subset bounds, then
    /// its keys.
    pub(crate) fn on_op_output(&self, out: &OpOutput, plan: &LogicalPlan) {
        let schema = plan.schema();
        if out.facts.contradictory() {
            self.empty_domain(&out.card);
        }
        for (j, v) in out.ndv.iter().enumerate() {
            match out.facts.dom(&col(plan, j), schema).size() {
                Some(0) => self.empty_domain(&out.card),
                Some(n) if n <= u64::MAX as u128 => self.ndv_within_domain(v, n as u64),
                _ => {}
            }
        }
        self.range_within_domain(plan, out);
        self.bounded_sum(plan, out);
        self.nulls_and_values(plan, out);
        self.key_ndv(plan, out);
        self.unique_columns(plan, out);
    }

    /// `empty domain`.
    ///
    /// - **Claim**: `X = 0`.
    /// - **When**: the op output's value domains contradict (`x < 1 AND x >
    ///   5`), or a column's domain holds no value.
    /// - **Why**: every row satisfies its domains, so there is none.
    pub fn empty_domain(&self, rows: &Int) {
        self.assert(rows.eq(int(0)));
    }

    /// `ndv within domain`.
    ///
    /// - **Claim**: `ndv ≤ n`, for a column whose domain holds `n` values,
    ///   NULL included if it may occur.
    ///
    /// ```text
    /// WHERE d BETWEEN 1 AND 7  ⇒  ndv(d) ≤ 7
    /// ```
    pub fn ndv_within_domain(&self, ndv: &Int, n: u64) {
        self.assert(ndv.le(int(n)));
    }

    /// `range within domain`.
    ///
    /// - **Claim**: for a column with `min` and `max` variables: they lie
    ///   within its domain's integer range; `X ≥ 1 ⇒ min ≤ max` if it is
    ///   never NULL; and `ndv ≤ max − min + 1`, plus 1 if it may be NULL.
    pub fn range_within_domain(&self, plan: &LogicalPlan, out: &OpOutput) {
        let schema = plan.schema();
        for (j, (lo, hi)) in out.min.iter().zip(&out.max).enumerate() {
            let (Some(lo), Some(hi)) = (lo, hi) else { continue };
            let d = out.facts.dom(&col(plan, j), schema);
            let (from, to) = d.int_range();
            if let Some(from) = from.and_then(|v| i64::try_from(v).ok()) {
                self.assert(lo.ge(Int::from_i64(from)));
            }
            if let Some(to) = to.and_then(|v| i64::try_from(v).ok()) {
                self.assert(hi.le(Int::from_i64(to)));
            }
            if d.never_null() {
                self.assert(out.card.ge(int(1)).implies(lo.le(hi)));
            }
            let width = hi.ge(lo).ite(&(hi - lo + int(1)), &int(0));
            self.assert(out.ndv[j].le(width + int(!d.never_null() as u64)));
        }
    }

    /// `key ndv`.
    ///
    /// - **Claim**: `ndv = X` for a column that traces to a declared primary
    ///   key or NOT NULL UNIQUE column, through every operator that keeps it
    ///   unique.
    /// - **Why**: such a column takes a distinct value on every row.
    pub fn key_ndv(&self, plan: &LogicalPlan, out: &OpOutput) {
        let schema = plan.schema();
        for j in 0..schema.fields().len() {
            let col = Column::from(schema.qualified_field(j));
            if self.covers_key(plan, &[col], Nulls::Equal) {
                self.assert(out.ndv[j].eq(&out.card));
            }
        }
    }

    /// `unique columns`.
    ///
    /// - **Claim**: `X ≤ Π ndv` of a set of columns the rules found unique
    ///   together, or of those of it that determine the rest; a column whose
    ///   domain holds `n` values counts as `n`, which keeps the product
    ///   linear where it can.
    /// - **Why**: each row has its own combination of their values.
    ///
    pub(crate) fn unique_columns(&self, plan: &LogicalPlan, out: &OpOutput) {
        let schema = plan.schema();
        for key in &out.subset_bounds.keys {
            let positions: Option<Vec<usize>> = key
                .iter()
                .map(|e| match e {
                    Expr::Column(c) => schema.index_of_column(c).ok(),
                    _ => None,
                })
                .collect();
            let Some(positions) = positions else { continue };
            let sizes: Vec<Option<u128>> = positions.iter().map(|&i| out.facts.dom(&col(plan, i), schema).size()).collect();
            let determining = self.determining(plan, &positions, &sizes);
            let mut constant: u128 = 1;
            let mut factors: Vec<&Int> = vec![];
            for i in determining {
                match out.facts.dom(&col(plan, i), schema).size() {
                    Some(k) => constant = constant.saturating_mul(k),
                    None => factors.push(&out.ndv[i]),
                }
            }
            if constant > u64::MAX as u128 {
                continue;
            }
            if let Some(p) = product(&factors, self.max_product) {
                self.assert(out.card.le(p * int(constant as u64)));
            }
        }
    }

    /// `bounded sum`.
    ///
    /// - **Claim**: `k·X ≤ b` for a column of non-negative integers summing
    ///   to at most `b` over the rows (a GROUP BY's counts), whose domain
    ///   holds only values `≥ k ≥ 1`.
    /// - **Why**: each row adds at least `k`.
    pub fn bounded_sum(&self, plan: &LogicalPlan, out: &OpOutput) {
        for (c, bound) in &out.subset_bounds.sums {
            if let Some(k) = out.facts.dom(c, plan.schema()).min()
                && k >= 1
                && k <= u64::MAX as i128
            {
                self.assert((&out.card * int(k as u64)).le(bound));
            }
        }
    }

    /// `nulls and values`.
    ///
    /// - **Claim**: `X ≤ n` for a column at most `n` rows have NULL (an outer
    ///   join's padded rows) if its domain holds only NULL; `X ≤ v` for one
    ///   at most `v` rows have non-NULL if it is never NULL.
    /// - **Why**: every row is one of those counted.
    pub fn nulls_and_values(&self, plan: &LogicalPlan, out: &OpOutput) {
        for (c, nulls, values) in &out.subset_bounds.nulls {
            let d = out.facts.dom(c, plan.schema());
            if d.is_null_only() {
                self.assert(out.card.le(nulls));
            } else if d.never_null() {
                self.assert(out.card.le(values));
            }
        }
    }

    /// Creates the size variable of each table `scan`'s table references by
    /// a foreign key, scanned or not, for [`Self::referenced_size`].
    pub(crate) fn referenced_tables(&mut self, scan: &TableScan) {
        let ScanKind::Base { display, .. } = (self.resolve)(scan) else { return };
        let refs: Vec<String> =
            self.foreign_keys.iter().filter(|fk| fk.table == display).map(|fk| fk.references.clone()).collect();
        for t in refs {
            if let ScanKind::Base { key, display } = bare_kind(&t) {
                self.table(&key, &display);
            }
        }
    }

    /// `referenced size`.
    ///
    /// - **Claim**: `ndv(c | R) ≤ |S|` for each column `c` of a foreign key
    ///   `R(cols) → S`, on a scan of `R`.
    /// - **When**: the analysis has reference plans ([`crate::joint`]);
    ///   `S` need not be scanned. Not on a float column.
    /// - **Why**: each row's `cols` equal the key of one row of `S`, so
    ///   they take at most `|S|` combinations, and one column no more.
    pub fn referenced_size(&self, scan: &TableScan, out: &OpOutput) {
        let ScanKind::Base { display, .. } = (self.resolve)(scan) else { return };
        let schema = &scan.projected_schema;
        for fk in self.foreign_keys.iter().filter(|fk| fk.table == display) {
            let ScanKind::Base { key, .. } = bare_kind(&fk.references) else { continue };
            let Some(t) = self.tables.get(&key) else { continue };
            for c in &fk.columns {
                if let Some(j) = schema.fields().iter().position(|f| f.name() == c)
                    && !schema.field(j).data_type().is_floating()
                {
                    self.assert(out.ndv[j].le(&t.var));
                }
            }
        }
    }

    /// `composite key`.
    ///
    /// - **Claim**: `|T| ≤ Π ndv` of a composite primary key's columns, or
    ///   of a composite UNIQUE constraint's on NOT NULL columns.
    /// - **Why**: each row has its own combination of key values.
    pub fn composite_key(&self, scan: &TableScan, out: &OpOutput) {
        let Some(constraints) = scan.source.constraints() else {
            return;
        };
        let schema = scan.source.schema();
        for c in constraints.iter() {
            let pk = match c {
                Constraint::PrimaryKey(pk) => pk,
                Constraint::Unique(u) if u.iter().all(|i| !schema.field(*i).is_nullable()) => u,
                Constraint::Unique(_) => continue,
            };
            if pk.len() < 2 {
                continue;
            }
            let positions: Option<Vec<usize>> = pk
                .iter()
                .map(|src| match &scan.projection {
                    None => Some(*src),
                    Some(proj) => proj.iter().position(|p| p == src),
                })
                .collect();
            if let Some(positions) = positions {
                let factors: Vec<&Int> = positions.iter().map(|i| &out.ndv[*i]).collect();
                if let Some(p) = product(&factors, self.max_product) {
                    self.assert(out.card.le(p));
                }
            }
        }
    }
}
