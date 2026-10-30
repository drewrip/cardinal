//! Rules: the constraints each operator puts on its output, given its inputs.
//!
//! # Spec
//!
//! - **Input**: one operator of a DataFusion [`LogicalPlan`], visited after
//!   its inputs, and its inputs' relations: their variables and what is
//!   known of their rows (value domains, keys, the stored table they are
//!   rows of).
//! - **Output**: the operator's relation. That is fresh variables (`X`, the
//!   output cardinality; per column `ndv`, and `min` and `max` for integer
//!   columns some range or key reads) and Z3 assertions relating them to
//!   the inputs' (`l`, `r`).
//! - **Guarantees**: every assertion holds for every execution of the
//!   operator on any data satisfying the declared keys and foreign keys,
//!   so the constraints admit every real run (`Analysis::validate` checks
//!   this against data).
//! - **Not done**: what holds of every relation whatever its operator is
//!   not here: `ndv ≤ X`, a key's `ndv = X`, value domains bounding `ndv`,
//!   and disjoint filters over one table. Those are axioms.
//!
//! A trace names each constraint's rule by the function that asserted it:
//! `visit_node/<Operator>` for the operators below asserted inline, or
//! the rule's own function (`scan`, `join`, `aggregate`, ...).
//!
//! # Rules
//!
//! `X` is the output's rows, `l` and `r` the inputs' (`l` alone for one
//! input), `ndv(c)` a column's distinct values, NULL counting as one.
//!
//! ## `TableScan`
//!
//! - **Claim**: `X = |T|`, the table's variable, shared by every scan of
//!   it. Pushed-down filters add a filter over the scan (`ScanFilter`), with
//!   `X ≤` the scan's rows and the filters' domains, unless the provider
//!   applies them inexactly. A pushed-down `fetch` bounds nothing.
//! - **Why**: a provider must return at least `fetch` rows and may return
//!   more; DataFusion keeps the limit above.
//!
//! ## `Projection`
//!
//! - **Claim**: `X = l`. Per output column: a column, or an injective cast
//!   of one, has its `ndv`, `min` and `max`; another deterministic
//!   expression has `ndv ≤ Π ndv` of the columns it reads; a literal `≤ 1`.
//!
//! ## `Subquery`, `SubqueryAlias`, `Repartition`
//!
//! - **Claim**: `X = l`, and each column equals its input's (`ndv`, `min`,
//!   `max`).
//!
//! ## `Window`
//!
//! - **Claim**: as `Subquery` for the input's columns. `row_number`, `rank`
//!   and `dense_rank` are `≥ 1`, and `row_number` with its partition columns
//!   is unique.
//!
//! ## `Filter`
//!
//! - **Claim**: `X ≤ l`; each column's `ndv ≤` its input's, its range
//!   within its input's. For `a = b`: `ndv(a) = ndv(b)`, each `≤` the
//!   other's input `ndv`. `a < b` orders their ranges. The predicate's
//!   domains hold above.
//! - **When**: the `a = b` rules skip floats, whose SQL equality merges
//!   values distinct as bits (`-0.0 = 0.0`).
//!
//! ## `Sort`
//!
//! - **Claim**: `X = l` with equal columns; with `fetch n`, `X = min(n, l)`
//!   and columns `≤`.
//!
//! ## `Limit`
//!
//! - **Claim**: literal skip `k` and fetch `n`: `X = min(n, max(l − k, 0))`.
//!   Otherwise `X ≤ l`, and `X ≤ n` for a literal fetch.
//!
//! ## `Distinct`
//!
//! - **Claim**: `X ≤ l`, `l ≥ 1 ⇒ X ≥ 1`, `X ≤ Π ndv` of the input's
//!   columns, or of the columns that determine the rest. Columns keep every
//!   value: `ndv` equal (`≤` for floats). A unique input: `X = l`.
//!
//! ## `DistinctOn`
//!
//! - **Claim**: `X ≤ l`, `l ≥ 1 ⇒ X ≥ 1`, `X ≤ Π ndv` of the `ON`
//!   expressions.
//!
//! ## `aggregate`
//!
//! - **Claim**: without GROUP BY, `X = 1`. With GROUP BY on keys `K`:
//!   `X ≤ l`, `l ≥ 1 ⇒ X ≥ 1`, `X ≤ Π ndv(K)` (or of the keys that
//!   determine the rest, or of one column determining every key), each
//!   key's `ndv` its expression's, and `X = l` if `K` covers a unique key.
//!   `count` columns sum to at most `l`; `min` and `max` take their
//!   argument's range. ROLLUP, CUBE and GROUPING SETS: nothing (they may emit
//!   more rows than they read).
//!
//! ## `join`
//!
//! - **Claim**: with `inner` the bound on the matched pairs, `l·r`, or `≤ l`
//!   if the right key is unique or a foreign key goes from the left to the
//!   whole right table (and the mirror):
//!   - inner: `X ≤ inner`; a cross join `X = l·r`; on a foreign key from
//!     the left `X = l`;
//!   - left: `X = l` if each left row matches at most once, else `l ≤ X ≤
//!     inner + l`; right: the mirror;
//!   - full: `X ≥ l`, `X ≥ r`, `X ≤ inner + l + r`, and `≤ l + r` with a
//!     unique key;
//!   - semi and anti: `X ≤` the kept side; on a foreign key from it, semi
//!     `X =` it and anti `X = 0`;
//!   - mark: `X =` the kept side.
//!
//!   Outer and anti joins also get the counts their selectivities measure
//!   (`join_parts`): the inner join's rows `i` and each side's rows with a
//!   partner `m`, with `X = i + l − m` (left), and so on. Columns: a
//!   preserved side's `ndv` equal, a padded side's `≤ ndv + 1` (NULL), and
//!   an equi-key's `≤` the other side's key `ndv`.
//!
//! ## `Union`
//!
//! - **Claim**: `X = Σ` inputs; `max ndv ≤ ndv ≤ Σ ndv` per column; each
//!   range within the inputs' together.
//!
//! ## `Values`, `EmptyRelation`
//!
//! - **Claim**: `X =` the rows listed, or `0` (`1` if it produces a row).
//!
//! ## Other operators
//!
//! Unnest, recursive CTEs and the rest get no rule: only the axioms on
//! their variables. Their inputs are still visited, so their scans count.

mod aggregate;
mod join;

use std::collections::BTreeSet;

use datafusion::arrow::datatypes::DataType;
use datafusion::common::tree_node::{Transformed, TreeNode};
use datafusion::common::Column;
use datafusion::logical_expr::logical_plan::{Distinct, FetchType, LogicalPlan, SkipType, TableScan};
use datafusion::logical_expr::utils::split_conjunction;
use datafusion::logical_expr::{BinaryExpr, Cast, Expr, ExprSchemable, Operator, TryCast};
use z3::ast::Int;

use crate::analysis::{Analyzer, Rel, ScanKind, inexact_filters, int, max, min, product, range_names};
use crate::domain::{self, Dom, Facts};
use crate::keys::Nulls;
use crate::origin::Origin;

impl<'a> Analyzer<'a> {
    /// Every non-NULL value of `o`'s column `j` is one of `l`'s column `i`.
    pub(crate) fn within(&self, o: &Rel, j: usize, l: &Rel, i: usize) {
        if let (Some(a), Some(b)) = (&o.min[j], &l.min[i]) {
            self.assert(a.ge(b));
        }
        if let (Some(a), Some(b)) = (&o.max[j], &l.max[i]) {
            self.assert(a.le(b));
        }
    }

    /// [`Self::within`], for each of `l`'s columns at the same position.
    pub(crate) fn within_all(&self, o: &Rel, l: &Rel) {
        for j in 0..o.min.len().min(l.min.len()) {
            self.within(o, j, l, j);
        }
    }

    /// The ranges `predicate` holds between two columns on every row of
    /// `o`, the output of `plan` keeping only rows that satisfy it: equal
    /// columns take the same values, and `a < b` puts `b`'s least above
    /// `a`'s least and `a`'s greatest below `b`'s.
    pub(crate) fn range_pairs(&self, predicate: &Expr, plan: &LogicalPlan, o: &Rel) {
        let index = |e: &Expr| column_index(plan, e).filter(|&i| o.min[i].is_some());
        for conj in split_conjunction(predicate) {
            let Expr::BinaryExpr(BinaryExpr { left, op, right }) = conj else { continue };
            let (Some(a), Some(b)) = (index(left), index(right)) else { continue };
            let lo_hi = |i: usize| (o.min[i].as_ref().unwrap(), o.max[i].as_ref().unwrap());
            // Each `x` is below a `y` (by one, `strict`ly).
            let below = |x: usize, y: usize, strict: bool| {
                let ((x_lo, x_hi), (y_lo, y_hi)) = (lo_hi(x), lo_hi(y));
                let gap = int(strict as u64);
                self.assert(y_lo.ge(x_lo + &gap));
                self.assert(x_hi.le(y_hi - &gap));
            };
            match op {
                Operator::Eq => {
                    let ((a_lo, a_hi), (b_lo, b_hi)) = (lo_hi(a), lo_hi(b));
                    self.assert(a_lo.eq(b_lo));
                    self.assert(a_hi.eq(b_hi));
                }
                Operator::Lt => below(a, b, true),
                Operator::LtEq => below(a, b, false),
                Operator::Gt => below(b, a, true),
                Operator::GtEq => below(b, a, false),
                _ => {}
            }
        }
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn visit_node(
        &mut self,
        plan: &LogicalPlan,
    ) -> (Rel, Option<(String, Vec<String>, LogicalPlan)>) {
        if let LogicalPlan::TableScan(scan) = plan {
            return self.scan(plan, scan);
        }
        let out = match plan {
            LogicalPlan::Projection(p) => {
                let l = self.visit(&p.input);
                let mut o = self.fresh("Projection", plan);
                self.assert(o.card.eq(&l.card));
                for (j, e) in p.expr.iter().enumerate() {
                    self.expr_ndv(&o.ndv[j], e, &p.input, &l);
                    // A column, or an integer cast of it, that keeps its value.
                    if let Some(i) = column_index(&p.input, e) {
                        self.within(&o, j, &l, i);
                    }
                }
                o.facts = computed_facts(plan, &p.expr, &p.input, &l.facts);
                o.rows = l.rows.rename(&|c| passed_column(plan, &p.expr, c));
                o.origin = l.origin.as_ref().map(|origin| {
                    origin.project(p.expr.iter().map(|e| match strip_alias(e) {
                        Expr::Column(c) => p.input.schema().index_of_column(c).ok(),
                        _ => None,
                    }))
                });
                o
            }
            LogicalPlan::Subquery(p) => self.same_rows("Subquery", plan, &p.subquery),
            LogicalPlan::SubqueryAlias(p) => self.same_rows("SubqueryAlias", plan, &p.input),
            LogicalPlan::Repartition(p) => self.same_rows("Repartition", plan, &p.input),
            // Window output is the input's columns, then one column per window
            // function, over the same rows.
            LogicalPlan::Window(p) => {
                let mut o = self.same_rows("Window", plan, &p.input);
                self.window_functions(plan, &p.input, &p.window_expr, &mut o);
                o
            }
            LogicalPlan::Filter(f) => {
                let l = self.visit(&f.input);
                let mut o = self.fresh("Filter", plan);
                self.assert(o.card.le(&l.card));
                self.subset_ndv(&o, &l);
                self.filter_ndv(&f.predicate, &f.input, &o, &l);
                self.within_all(&o, &l);
                self.range_pairs(&f.predicate, plan, &o);
                o.facts = l.facts.clone();
                o.rows = l.rows.clone();
                o.facts.assume(&f.predicate, plan.schema());
                o.origin = l.origin.clone().map(|x| x.narrow(&o.facts, plan.schema()));
                o
            }
            LogicalPlan::Distinct(Distinct::All(input)) => {
                let l = self.visit(input);
                let mut o = self.fresh("Distinct", plan);
                o.facts = l.facts.clone();
                o.rows = l.rows.clone();
                o.origin = l.origin.clone();
                self.assert(o.card.le(&l.card));
                self.assert(l.card.ge(int(1)).implies(o.card.ge(int(1))));
                // DISTINCT keeps every value that occurs.
                self.kept_values(plan, &o, &l);
                self.within_all(&o, &l);
                let all: Vec<&Int> = l.ndv.iter().collect();
                if let Some(p) = product(&all, self.max_product) {
                    self.assert(o.card.le(p));
                }
                // Columns the others determine add no distinct rows.
                let determining = self.determining_keys(input, all.len());
                if determining.len() < all.len() {
                    let factors: Vec<&Int> = determining.iter().map(|&j| &l.ndv[j]).collect();
                    if let Some(p) = product(&factors, self.max_product) {
                        self.assert(o.card.le(p));
                    }
                }
                let cols: Vec<Column> = (0..input.schema().fields().len())
                    .map(|i| Column::from(input.schema().qualified_field(i)))
                    .collect();
                if self.covers_key(input, &cols, Nulls::Equal) {
                    self.assert(o.card.eq(&l.card));
                }
                o
            }
            LogicalPlan::Distinct(Distinct::On(on)) => {
                let l = self.visit(&on.input);
                let mut o = self.fresh("DistinctOn", plan);
                o.facts = computed_facts(plan, &on.select_expr, &on.input, &l.facts);
                self.assert(o.card.le(&l.card));
                self.assert(l.card.ge(int(1)).implies(o.card.ge(int(1))));
                let bounds: Option<Vec<Int>> = on
                    .on_expr
                    .iter()
                    .map(|e| expr_bound(e, &on.input, &l, self.max_product))
                    .collect();
                if let Some(bounds) = bounds
                    && let Some(p) = product(&bounds.iter().collect::<Vec<_>>(), self.max_product)
                {
                    self.assert(o.card.le(p));
                }
                o
            }
            LogicalPlan::Sort(s) => {
                let l = self.visit(&s.input);
                let mut o = self.fresh("Sort", plan);
                self.within_all(&o, &l);
                o.facts = l.facts.clone();
                o.rows = l.rows.clone();
                o.origin = l.origin.clone();
                match s.fetch {
                    None => {
                        self.assert(o.card.eq(&l.card));
                        self.equal_ndv(&o, &l);
                    }
                    // Top-k: exactly the first n rows.
                    Some(n) => {
                        self.assert(o.card.eq(min(&int(n as u64), &l.card)));
                        self.subset_ndv(&o, &l);
                    }
                }
                o
            }
            LogicalPlan::Limit(lim) => {
                let l = self.visit(&lim.input);
                let mut o = self.fresh("Limit", plan);
                self.within_all(&o, &l);
                o.facts = l.facts.clone();
                o.rows = l.rows.clone();
                o.origin = l.origin.clone();
                self.subset_ndv(&o, &l);
                let skip = match lim.get_skip_type() {
                    Ok(SkipType::Literal(k)) => Some(k as u64),
                    _ => None,
                };
                let fetch = match lim.get_fetch_type() {
                    Ok(FetchType::Literal(n)) => Some(n.map(|n| n as u64)),
                    _ => None,
                };
                match (skip, fetch) {
                    // Exactly min(n, max(l - k, 0)) rows.
                    (Some(k), Some(n)) => {
                        let after_skip = max(&(&l.card - int(k)), &int(0));
                        let rows = match n {
                            Some(n) => min(&int(n), &after_skip),
                            None => after_skip,
                        };
                        self.assert(o.card.eq(rows));
                    }
                    (_, fetch) => {
                        self.assert(o.card.le(&l.card));
                        if let Some(Some(n)) = fetch {
                            self.assert(o.card.le(int(n)));
                        }
                    }
                }
                o
            }
            LogicalPlan::Aggregate(agg) => self.aggregate(plan, agg),
            LogicalPlan::Join(join) => self.join(plan, join),
            LogicalPlan::Union(u) => {
                let inputs: Vec<Rel> = u.inputs.iter().map(|i| self.visit(i)).collect();
                let mut o = self.fresh("Union", plan);
                for j in 0..plan.schema().fields().len() {
                    let dom = u.inputs.iter().zip(&inputs).fold(
                        Dom::nothing(),
                        |acc, (input, rel)| {
                            let col = Expr::Column(Column::from(input.schema().qualified_field(j)));
                            acc.union(&rel.facts.dom(&col, input.schema()))
                        },
                    );
                    let col = Expr::Column(Column::from(plan.schema().qualified_field(j)));
                    o.facts.add(&col, dom, plan.schema());
                }
                let cards: Vec<&Int> = inputs.iter().map(|r| &r.card).collect();
                self.assert(o.card.eq(Int::add(&cards)));
                for (j, v) in o.ndv.iter().enumerate() {
                    let parts: Vec<&Int> = inputs.iter().map(|r| &r.ndv[j]).collect();
                    self.assert(v.le(Int::add(&parts)));
                    for part in parts {
                        self.assert(v.ge(part));
                    }
                }
                // Each value is one of some input's.
                for j in 0..o.min.len() {
                    let ends = |ends: fn(&Rel) -> &Vec<Option<Int>>| -> Option<Vec<Int>> {
                        inputs.iter().map(|r| ends(r).get(j).cloned().flatten()).collect()
                    };
                    if let (Some(lo), Some(los)) = (&o.min[j], ends(|r| &r.min)) {
                        self.assert(lo.ge(los.iter().skip(1).fold(los[0].clone(), |a, b| min(&a, b))));
                    }
                    if let (Some(hi), Some(his)) = (&o.max[j], ends(|r| &r.max)) {
                        self.assert(hi.le(his.iter().skip(1).fold(his[0].clone(), |a, b| max(&a, b))));
                    }
                }
                o
            }
            LogicalPlan::Values(v) => {
                let mut o = self.fresh("Values", plan);
                self.assert(o.card.eq(int(v.values.len() as u64)));
                for j in 0..plan.schema().fields().len() {
                    let dom = v.values.iter().fold(Dom::nothing(), |acc, row| {
                        acc.union(&Facts::default().dom(&row[j], plan.schema()))
                    });
                    let col = Expr::Column(Column::from(plan.schema().qualified_field(j)));
                    o.facts.add(&col, dom, plan.schema());
                }
                o
            }
            LogicalPlan::EmptyRelation(e) => {
                let o = self.fresh("EmptyRelation", plan);
                self.assert(o.card.eq(int(e.produce_one_row as u64)));
                o
            }
            other => {
                // Unsupported operator: visit children so their scans still count,
                // but say nothing about this operator's output beyond the basics.
                for input in other.inputs() {
                    self.visit(input);
                }
                self.fresh(&format!("Unknown_{}", variant_name(other)), plan)
            }
        };
        (out, None)
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn scan(
        &mut self,
        plan: &LogicalPlan,
        scan: &TableScan,
    ) -> (Rel, Option<(String, Vec<String>, LogicalPlan)>) {
        let mut raw_scan = None;
        let mut out = match (self.resolve)(scan) {
            ScanKind::Base { key, display } => {
                let t = self.table(&key, &display);
                let mut s = self.fresh(&format!("Scan_{display}"), plan);
                self.assert(s.card.eq(&t));
                // Stored tables enforce their columns' nullability.
                let schema = plan.schema();
                for (j, field) in schema.fields().iter().enumerate() {
                    if !field.is_nullable() {
                        let col = Expr::Column(Column::from(schema.qualified_field(j)));
                        s.facts.add(&col, Dom::non_null(), schema);
                    }
                }
                self.composite_key(scan, &s);
                let name = self.name_of(&s.card);
                self.scans.push((name.clone(), display, s.card.clone()));
                s.origin = Some(Origin::scan(&key, schema).narrow(&s.facts, schema));
                if !scan.filters.is_empty() {
                    // The raw scan, before pushed-down filters and fetch.
                    let mut raw = scan.clone();
                    raw.filters.clear();
                    raw.fetch = None;
                    raw_scan = Some((name, self.names_of(&s), LogicalPlan::TableScan(raw)));
                    self.raw_ranges = (range_names(&s.min), range_names(&s.max));
                    self.range_within_domain(plan, &s);
                }
                s
            }
            ScanKind::NonBase => self.fresh(&format!("NonBaseScan_{}", scan.table_name), plan),
        };
        // Pushed-down filters behave like a Filter wrapping the scan: whether the
        // provider applies them exactly or not, it cannot add rows. A pushed-down
        // `fetch` is only a hint: providers must return *at least* that many rows
        // and may return more (DataFusion keeps the Limit above), so it bounds
        // nothing.
        if !scan.filters.is_empty() {
            let mut f = self.fresh("ScanFilter", plan);
            self.assert(f.card.le(&out.card));
            self.subset_ndv(&f, &out);
            self.within_all(&f, &out);
            f.facts = out.facts.clone();
            // Filters applied inexactly may let through rows that fail them.
            if !inexact_filters(scan) {
                for filter in &scan.filters {
                    f.facts.assume(filter, plan.schema());
                    self.range_pairs(filter, plan, &f);
                }
            }
            f.origin = out.origin.clone().map(|x| x.narrow(&f.facts, plan.schema()));
            out = f;
        }
        (out, raw_scan)
    }

    /// Ranking functions number rows from 1, and `row_number()` numbers each
    /// partition's rows 1, 2, 3, ...: with the partition keys, it is unique.
    pub(crate) fn window_functions(&self, plan: &LogicalPlan, input: &LogicalPlan, exprs: &[Expr], o: &mut Rel) {
        let n = input.schema().fields().len();
        for (i, e) in exprs.iter().enumerate() {
            let Expr::WindowFunction(w) = strip_alias(e) else {
                continue;
            };
            let name = w.fun.name();
            if !matches!(name, "row_number" | "rank" | "dense_rank") || w.params.filter.is_some() {
                continue;
            }
            let c = col(plan, n + i);
            o.facts.add(&c, Dom::at_least(1), plan.schema());
            if name != "row_number" {
                continue;
            }
            let partition: Option<Vec<Expr>> = w
                .params
                .partition_by
                .iter()
                .map(|p| match strip_alias(p) {
                    Expr::Column(_) => Some(strip_alias(p).clone()),
                    _ => None,
                })
                .collect();
            if let Some(mut key) = partition {
                key.push(c);
                o.rows.keys.push(key);
            }
        }
    }

    /// Same rows as the input, whose columns come first and unchanged.
    pub(crate) fn same_rows(&mut self, kind: &str, plan: &LogicalPlan, input: &LogicalPlan) -> Rel {
        let l = self.visit(input);
        let mut o = self.fresh(kind, plan);
        self.assert(o.card.eq(&l.card));
        self.equal_ndv(&o, &l);
        self.within_all(&o, &l);
        o.facts = l.facts.by_position(input.schema(), plan.schema());
        let by_position = |c: &Column| {
            let i = input.schema().index_of_column(c).ok()?;
            child_column(plan, i)
        };
        o.rows = l.rows.rename(&by_position);
        o.origin = l.origin.as_ref().map(|x| x.with_width(plan.schema().fields().len()));
        o
    }

    /// The first columns of `o` hold exactly the values of `l`'s columns.
    pub(crate) fn equal_ndv(&self, o: &Rel, l: &Rel) {
        for (a, b) in o.ndv.iter().zip(&l.ndv) {
            self.assert(a.eq(b));
        }
    }

    /// `o` keeps every distinct value of `l`'s columns, but deduplicates by SQL
    /// equality. For floats that can merge values that are distinct as bits
    /// (`-0.0` and `0.0`), so only `<=` is asserted there.
    pub(crate) fn kept_values(&self, plan: &LogicalPlan, o: &Rel, l: &Rel) {
        for (j, (a, b)) in o.ndv.iter().zip(&l.ndv).enumerate() {
            if plan.schema().field(j).data_type().is_floating() {
                self.assert(a.le(b));
            } else {
                self.assert(a.eq(b));
            }
        }
    }

    /// `o`'s rows are a subset of `l`'s.
    pub(crate) fn subset_ndv(&self, o: &Rel, l: &Rel) {
        for (a, b) in o.ndv.iter().zip(&l.ndv) {
            self.assert(a.le(b));
        }
    }

    /// Bounds output column `v`, computed by `e` over the rows of `input`.
    pub(crate) fn expr_ndv(&self, v: &Int, e: &Expr, input: &LogicalPlan, l: &Rel) {
        if let Some(c) = key_column(input, e)
            && let Ok(i) = input.schema().index_of_column(&c)
        {
            // The same values, or an injective image of them.
            self.assert(v.eq(&l.ndv[i]));
        } else if let Some(bound) = expr_bound(e, input, l, self.max_product) {
            self.assert(v.le(bound));
        }
    }

    /// Tightens the NDVs of `o`, the output of filtering `l` by `predicate`.
    pub(crate) fn filter_ndv(&self, predicate: &Expr, input: &LogicalPlan, o: &Rel, l: &Rel) {
        // SQL equality on floats identifies values that are distinct as bits
        // (`-0.0 = 0.0`), so these rules skip float columns.
        let index = |e: &Expr| {
            let i = key_column(input, e).and_then(|c| input.schema().index_of_column(&c).ok())?;
            (!input.schema().field(i).data_type().is_floating()).then_some(i)
        };
        for conj in split_conjunction(predicate) {
            if let Expr::BinaryExpr(BinaryExpr {
                left,
                op: Operator::Eq,
                right,
            }) = conj
                && let (Some(a), Some(b)) = (index(left), index(right))
            {
                // Every surviving row has a = b (neither NULL).
                self.assert(o.ndv[a].eq(&o.ndv[b]));
                self.assert(o.ndv[a].le(&l.ndv[b]));
                self.assert(o.ndv[b].le(&l.ndv[a]));
            }
        }
    }
}

/// `e`, over the output of projection `plan` computing `exprs`, as an
/// expression over its input. `None` if it reads what it can't rewrite.
pub(crate) fn unproject(e: &Expr, plan: &LogicalPlan, exprs: &[Expr]) -> Option<Expr> {
    let mut ok = true;
    let out = e
        .clone()
        .transform_up(|x| match &x {
            Expr::Column(c) => match plan.schema().index_of_column(c) {
                Ok(j) => Ok(Transformed::yes(strip_alias(&exprs[j]).clone())),
                Err(_) => {
                    ok = false;
                    Ok(Transformed::no(x))
                }
            },
            _ => Ok(Transformed::no(x)),
        })
        .ok()?
        .data;
    ok.then_some(out)
}

/// Output column `j` of `plan`, as an expression.
pub(crate) fn col(plan: &LogicalPlan, j: usize) -> Expr {
    Expr::Column(Column::from(plan.schema().qualified_field(j)))
}

/// Facts on the output of an operator computing `exprs` over the rows of
/// `input`: each output column takes its expression's values, and facts on
/// input columns passed through unchanged still hold.
pub(crate) fn computed_facts(plan: &LogicalPlan, exprs: &[Expr], input: &LogicalPlan, facts: &Facts) -> Facts {
    let passed = |c: &Column| passed_column(plan, exprs, c);
    let mut out = facts.rename(&passed);
    for (j, e) in exprs.iter().enumerate() {
        if let Some(e) = domain::rename(e, &passed) {
            out.define(&col(plan, j), &e, plan.schema());
        }
        out.add(&col(plan, j), facts.dom(e, input.schema()), plan.schema());
    }
    out
}

/// The output column of `plan`, computing `exprs`, that passes input column
/// `c` through unchanged.
pub(crate) fn passed_column(plan: &LogicalPlan, exprs: &[Expr], c: &Column) -> Option<Column> {
    let j = exprs
        .iter()
        .position(|e| matches!(strip_alias(e), Expr::Column(x) if x == c))?;
    Some(Column::from(plan.schema().qualified_field(j)))
}

pub(crate) fn strip_alias(e: &Expr) -> &Expr {
    match e {
        Expr::Alias(a) => strip_alias(&a.expr),
        e => e,
    }
}

/// True unless `e` is a deterministic function of the columns it reads: it
/// is volatile, or reads a subquery, an outer query or a parameter.
pub(crate) fn opaque(e: &Expr) -> bool {
    e.is_volatile()
        || e.exists(|x| {
            Ok(matches!(
                x,
                Expr::ScalarSubquery(_)
                    | Expr::Exists(_)
                    | Expr::InSubquery(_)
                    | Expr::SetComparison(_)
                    | Expr::OuterReferenceColumn(..)
                    | Expr::Placeholder(_)
            ))
        })
        .unwrap_or(true)
}

/// True if `e`, over the rows of `input`, takes one value on rows that agree
/// on the columns `determined` (positions in `input`'s output).
pub(crate) fn determined(e: &Expr, input: &LogicalPlan, determined: &BTreeSet<usize>) -> bool {
    !opaque(e)
        && e.column_refs()
            .into_iter()
            .all(|c| input.schema().index_of_column(c).is_ok_and(|i| determined.contains(&i)))
}

/// Pairs of `input`'s output positions that `predicate` holds equal on every
/// row it keeps. Floats are left out: SQL equality identifies values that
/// are distinct as bits (`-0.0 = 0.0`).
pub(crate) fn equalities(predicate: &Expr, input: &LogicalPlan) -> Vec<(usize, usize)> {
    split_conjunction(predicate)
        .into_iter()
        .filter_map(|conj| match conj {
            Expr::BinaryExpr(BinaryExpr { left, op: Operator::Eq, right }) => {
                Some((exact_index(input, left)?, exact_index(input, right)?))
            }
            _ => None,
        })
        .collect()
}

/// [`column_index`], of a column whose type is not a float.
pub(crate) fn exact_index(input: &LogicalPlan, e: &Expr) -> Option<usize> {
    let i = column_index(input, e)?;
    (!input.schema().field(i).data_type().is_floating()).then_some(i)
}

/// The closure `close` gives of `keys`, where each of `pairs` holds two
/// columns equal on every row: a column equal to a determined one is
/// determined too.
pub(crate) fn with_equalities(
    mut keys: Vec<usize>,
    pairs: &[(usize, usize)],
    close: impl Fn(&[usize]) -> BTreeSet<usize>,
) -> BTreeSet<usize> {
    loop {
        let closed = close(&keys);
        let before = keys.len();
        for &(a, b) in pairs {
            for (x, y) in [(a, b), (b, a)] {
                if closed.contains(&x) && !closed.contains(&y) && !keys.contains(&y) {
                    keys.push(y);
                }
            }
        }
        if keys.len() == before {
            return closed;
        }
    }
}

/// An upper bound on the number of distinct values `e` takes over the rows of
/// `input`, or `None` if nothing better than the row count is known. A
/// deterministic function of some columns takes at most as many values as
/// there are combinations of theirs.
pub(crate) fn expr_bound(e: &Expr, input: &LogicalPlan, l: &Rel, cap: usize) -> Option<Int> {
    if let Some(c) = key_column(input, e) {
        let i = input.schema().index_of_column(&c).ok()?;
        return Some(l.ndv[i].clone());
    }
    if opaque(e) {
        return None;
    }
    let factors: Option<Vec<&Int>> = e
        .column_refs()
        .into_iter()
        .map(|c| input.schema().index_of_column(c).ok().map(|i| &l.ndv[i]))
        .collect();
    product(&factors?, cap)
}

/// The column `e` reads from `input`, if `e` is that column possibly wrapped in
/// casts that cannot make two distinct values equal.
pub(crate) fn key_column(input: &LogicalPlan, e: &Expr) -> Option<Column> {
    match e {
        Expr::Column(c) => Some(c.clone()),
        Expr::Alias(a) => key_column(input, &a.expr),
        Expr::Cast(Cast { expr, field }) | Expr::TryCast(TryCast { expr, field }) => {
            let from = expr.get_type(input.schema()).ok()?;
            injective_cast(&from, field.data_type()).then(|| key_column(input, expr))?
        }
        _ => None,
    }
}

/// The position in `input`'s output of the column `e` reads (see
/// [`key_column`]).
pub(crate) fn column_index(input: &LogicalPlan, e: &Expr) -> Option<usize> {
    input.schema().index_of_column(&key_column(input, e)?).ok()
}

/// True if casting `from` to `to` maps distinct values to distinct values.
pub(crate) fn injective_cast(from: &DataType, to: &DataType) -> bool {
    use DataType::*;
    // Decimal digits an integer type's values need.
    let digits = match from {
        Int8 | UInt8 => Some(3),
        Int16 | UInt16 => Some(5),
        Int32 | UInt32 => Some(10),
        Int64 => Some(19),
        UInt64 => Some(20),
        _ => None,
    };
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
                // Floats hold integers exactly up to 2^24 and 2^53.
                | (Int8 | Int16 | UInt8 | UInt16, Float32)
                | (Int8 | Int16 | Int32 | UInt8 | UInt16 | UInt32, Float64)
        )
        || match (digits, to) {
            (Some(d), Decimal128(p, s) | Decimal256(p, s)) => i16::from(*p) - i16::from(*s) >= d,
            _ => false,
        }
}

/// The column of `child` feeding output position `i`, for operators whose output
/// columns start with their child's columns unchanged.
pub(crate) fn child_column(child: &LogicalPlan, i: usize) -> Option<Column> {
    let schema = child.schema();
    (i < schema.fields().len()).then(|| Column::from(schema.qualified_field(i)))
}

/// Maps `cols` of `plan`'s output to the child columns at the same positions.
pub(crate) fn same_positions(plan: &LogicalPlan, child: &LogicalPlan, cols: &[Column]) -> Option<Vec<Column>> {
    cols.iter()
        .map(|c| {
            let i = plan.schema().index_of_column(c).ok()?;
            child_column(child, i)
        })
        .collect()
}

/// Columns `predicate` holds equal to a non-NULL constant on every row it keeps.
pub(crate) fn pinned(predicate: &Expr) -> Vec<Column> {
    split_conjunction(predicate)
        .into_iter()
        .filter_map(|e| match e {
            Expr::BinaryExpr(BinaryExpr { left, op: Operator::Eq, right }) => {
                match (strip_alias(left), strip_alias(right)) {
                    (Expr::Column(c), Expr::Literal(v, _)) | (Expr::Literal(v, _), Expr::Column(c)) if !v.is_null() => {
                        Some(c.clone())
                    }
                    _ => None,
                }
            }
            _ => None,
        })
        .collect()
}

/// Positions of `cols` in `plan`'s output.
pub(crate) fn output_indices(plan: &LogicalPlan, cols: &[Column]) -> Option<Vec<usize>> {
    cols.iter()
        .map(|c| plan.schema().index_of_column(c).ok())
        .collect()
}

pub(crate) fn variant_name(plan: &LogicalPlan) -> &'static str {
    match plan {
        LogicalPlan::Unnest(_) => "Unnest",
        LogicalPlan::RecursiveQuery(_) => "RecursiveQuery",
        LogicalPlan::Extension(_) => "Extension",
        LogicalPlan::Explain(_) => "Explain",
        LogicalPlan::Analyze(_) => "Analyze",
        LogicalPlan::Statement(_) => "Statement",
        LogicalPlan::Dml(_) => "Dml",
        LogicalPlan::Ddl(_) => "Ddl",
        LogicalPlan::Copy(_) => "Copy",
        LogicalPlan::DescribeTable(_) => "DescribeTable",
        _ => "Other",
    }
}
