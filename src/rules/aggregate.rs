//! GROUP BY and aggregates.

use datafusion::common::Column;
use datafusion::logical_expr::Expr;
use datafusion::logical_expr::logical_plan::{Aggregate, LogicalPlan};
use z3::ast::Int;

use super::{col, column_index, determined, expr_bound, key_column, strip_alias, unproject};
use crate::analysis::{Analyzer, Rel, int, product};
use crate::domain::{Dom, Facts};
use crate::keys::Nulls;

impl<'a> Analyzer<'a> {
    pub(crate) fn aggregate(&mut self, plan: &LogicalPlan, agg: &Aggregate) -> Rel {
        let l = self.visit(&agg.input);
        if agg
            .group_expr
            .iter()
            .any(|e| matches!(e, Expr::GroupingSet(_)))
        {
            // ROLLUP / CUBE / GROUPING SETS can emit more rows than they read.
            return self.fresh("GroupingSets", plan);
        }
        if agg.group_expr.is_empty() {
            let mut o = self.fresh("ScalarAggregate", plan);
            self.assert(o.card.eq(int(1)));
            self.aggregate_ranges(agg, &o, &l);
            o.facts = aggregate_facts(plan, agg, &l.facts);
            return o;
        }
        let mut o = self.fresh("GroupBy", plan);
        o.facts = aggregate_facts(plan, agg, &l.facts);
        self.aggregate_ranges(agg, &o, &l);
        // Groups split the input's rows, so their counts sum to at most its
        // row count.
        for (i, e) in agg.aggr_expr.iter().enumerate() {
            if let Expr::AggregateFunction(f) = strip_alias(e)
                && f.func.name() == "count"
            {
                o.rows.sums.push((col(plan, agg.group_expr.len() + i), l.card.clone()));
            }
        }
        self.assert(o.card.le(&l.card));
        self.assert(l.card.ge(int(1)).implies(o.card.ge(int(1))));
        // One group per distinct combination of group values; every value of a
        // group expression shows up in some group.
        let mut factors = vec![];
        for (j, e) in agg.group_expr.iter().enumerate() {
            if plan.schema().field(j).data_type().is_floating() {
                if let Some(bound) = expr_bound(e, &agg.input, &l, self.max_product) {
                    self.assert(o.ndv[j].le(bound));
                }
            } else {
                self.expr_ndv(&o.ndv[j], e, &agg.input, &l);
            }
            factors.push(&o.ndv[j]);
        }
        if let Some(p) = product(&factors, self.max_product) {
            self.assert(o.card.le(p));
        }
        // Keys the others determine add no groups.
        let determining = self.determining_keys(plan, agg.group_expr.len());
        if determining.len() < factors.len() {
            let factors: Vec<&Int> = determining.iter().map(|&j| &o.ndv[j]).collect();
            if let Some(p) = product(&factors, self.max_product) {
                self.assert(o.card.le(p));
            }
        }
        self.determining_column(agg, &o);
        // Grouping by a unique key leaves every row its own group.
        let cols: Option<Vec<Column>> = agg
            .group_expr
            .iter()
            .map(|e| key_column(&agg.input, e))
            .collect();
        if cols.is_some_and(|cols| self.covers_key(&agg.input, &cols, Nulls::Equal)) {
            self.assert(o.card.eq(&l.card));
        }
        o
    }

    /// A column that determines every key, as a key of `nation` does its
    /// name, has at least as many values as there are groups. It may be one
    /// of the input's, or of the rows the projections and filters below it
    /// read: those keep fewer rows, each computed from one of them. The
    /// first of at most 64 columns tried bounds the groups.
    pub(crate) fn determining_column(&self, agg: &Aggregate, o: &Rel) {
        let (mut node, mut keys) = (self.nodes.len() - 1, agg.group_expr.clone());
        let mut tries = 64;
        loop {
            let plan = &self.nodes[node].plan;
            for c in 0..plan.schema().fields().len() {
                if tries == 0 {
                    return;
                }
                tries -= 1;
                let closed = self.fd_closure(plan, &[c]);
                if keys.iter().all(|e| determined(e, plan, &closed)) {
                    self.assert(o.card.le(Int::new_const(self.nodes[node].ndv_vars[c].as_str())));
                    return;
                }
            }
            // The keys over the operator's input.
            keys = match plan {
                LogicalPlan::Projection(p) => {
                    let unprojected: Option<Vec<Expr>> = keys.iter().map(|e| unproject(e, plan, &p.expr)).collect();
                    match unprojected {
                        Some(k) => k,
                        None => return,
                    }
                }
                LogicalPlan::Filter(_) => keys,
                _ => return,
            };
            node = self.nodes[node].inputs[0];
        }
    }

    /// A grouping key's values, and a MIN's or MAX's, are its input's.
    pub(crate) fn aggregate_ranges(&self, agg: &Aggregate, o: &Rel, l: &Rel) {
        let groups = agg.group_expr.len();
        for (j, e) in agg.group_expr.iter().chain(&agg.aggr_expr).enumerate() {
            let arg = match strip_alias(e) {
                e if j < groups => e,
                Expr::AggregateFunction(f) if matches!(f.func.name(), "min" | "max") && f.params.args.len() == 1 => &f.params.args[0],
                _ => continue,
            };
            if let Some(i) = column_index(&agg.input, arg) {
                self.within(o, j, l, i);
            }
        }
    }
}

/// Facts on an aggregate's output: each group key takes its expression's
/// values, and MIN or MAX takes one of its argument's values, or NULL.
pub(crate) fn aggregate_facts(plan: &LogicalPlan, agg: &Aggregate, input: &Facts) -> Facts {
    let in_schema = agg.input.schema();
    let groups = agg.group_expr.len();
    let mut out = Facts::default();
    for (j, e) in agg.group_expr.iter().chain(&agg.aggr_expr).enumerate() {
        let dom = if j < groups {
            input.dom(e, in_schema)
        } else {
            match strip_alias(e) {
                Expr::AggregateFunction(f)
                    if matches!(f.func.name(), "min" | "max") && f.params.args.len() == 1 =>
                {
                    input.dom(&f.params.args[0], in_schema).with_null()
                }
                // A group has at least one row, and `count(*)` counts it.
                Expr::AggregateFunction(f) if f.func.name() == "count" => {
                    let counts_all = f.params.filter.is_none()
                        && !f.params.distinct
                        && f.params.args.iter().all(|a| input.dom(a, in_schema).never_null());
                    Dom::at_least(if groups > 0 && counts_all { 1 } else { 0 })
                }
                _ => continue,
            }
        };
        out.add(&col(plan, j), dom, plan.schema());
    }
    out
}
