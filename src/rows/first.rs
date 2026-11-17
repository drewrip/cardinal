//! The first row of each partition: `rn = 1` over `row_number() OVER
//! (PARTITION BY p ...)`.
//!
//! Such a filter keeps one row per distinct value of `p` among the window's
//! input rows, so it keeps as many rows as `GROUP BY p` would: its share is
//! the distinct count of `p`. Which row of each partition it keeps depends
//! on the window's order, but how many does not. Joined on exactly `p`, each
//! row of the other side has one partner if any row of the window's input
//! has its key, and none otherwise: the join keeps the rows of a semi join
//! with the window's input.

use datafusion::common::{Column, ScalarValue};
use datafusion::logical_expr::logical_plan::{Filter, LogicalPlan};
use datafusion::logical_expr::utils::split_conjunction;
use datafusion::logical_expr::{BinaryExpr, Expr, Operator};

use crate::rules::{child_column, passed_rows, row_number, strip_alias};

/// A filter keeping the first row of each partition of a `row_number()`.
#[derive(Debug, Clone)]
pub(crate) struct FirstRows {
    /// The partition columns, of the window's input.
    pub partition: Vec<Column>,
    /// The nodes from the filter's input down to the window: 0 if the input
    /// is the window.
    pub depth: usize,
}

/// `filter` as a [`FirstRows`]: its predicate is only `rn = 1` (or `rn <=
/// 1`), and `rn` is a `row_number()` partitioned by columns, computed over
/// the filter's input rows: only operators that keep every row in order
/// (projections, aliases, sorts, other windows) are in between.
pub(crate) fn first_rows(filter: &Filter) -> Option<FirstRows> {
    let [conjunct] = split_conjunction(&filter.predicate)[..] else {
        return None;
    };
    let Expr::BinaryExpr(BinaryExpr { left, op, right }) = conjunct else {
        return None;
    };
    let rn = match (op, strip_alias(left), strip_alias(right)) {
        (Operator::Eq | Operator::LtEq, Expr::Column(c), Expr::Literal(v, _)) if one(v) => c,
        (Operator::Eq | Operator::GtEq, Expr::Literal(v, _), Expr::Column(c)) if one(v) => c,
        _ => return None,
    };
    let (mut plan, mut col, mut depth) = (filter.input.as_ref(), rn.clone(), 0);
    loop {
        if let LogicalPlan::Window(w) = plan {
            let i = plan.schema().index_of_column(&col).ok()?;
            let n = w.input.schema().fields().len();
            if i >= n {
                let partition = row_number(&w.window_expr[i - n]).filter(|p| !p.is_empty())?;
                let partition = partition
                    .iter()
                    .map(|p| match strip_alias(p) {
                        Expr::Column(c) => Some(c.clone()),
                        _ => None,
                    })
                    .collect::<Option<Vec<Column>>>()?;
                return Some(FirstRows { partition, depth });
            }
        }
        let (child, c) = step(plan, &col)?;
        (plan, col, depth) = (child, c, depth + 1);
    }
}

/// True if `side`, through operators that keep every row, is a
/// [`FirstRows`] filter, and `keys`, columns of `side`, are its partition
/// columns, together exactly.
pub(crate) fn on_partition(side: &LogicalPlan, keys: &[&Expr]) -> bool {
    let Some(mut cols) = keys
        .iter()
        .map(|k| match strip_alias(k) {
            Expr::Column(c) => Some(c.clone()),
            _ => None,
        })
        .collect::<Option<Vec<Column>>>()
    else {
        return false;
    };
    if cols.is_empty() {
        return false;
    }
    let mut plan = side;
    loop {
        if let LogicalPlan::Filter(f) = plan {
            let Some(first) = first_rows(f) else { return false };
            let mut plan = f.input.as_ref();
            for _ in 0..first.depth {
                let Some(next) = down(plan, &cols) else { return false };
                (plan, cols) = next;
            }
            let mut cols = cols;
            cols.sort_by_key(|c| c.flat_name());
            cols.dedup();
            let mut partition = first.partition;
            partition.sort_by_key(|c| c.flat_name());
            partition.dedup();
            return cols == partition;
        }
        let Some(next) = down(plan, &cols) else { return false };
        (plan, cols) = next;
    }
}

/// `cols` of `plan`, as columns of its input, through an operator that
/// keeps every row.
fn down<'a>(plan: &'a LogicalPlan, cols: &[Column]) -> Option<(&'a LogicalPlan, Vec<Column>)> {
    let mut child = None;
    let mut out = vec![];
    for c in cols {
        let (p, c) = step(plan, c)?;
        child = Some(p);
        out.push(c);
    }
    Some((child?, out))
}

/// Column `col` of `plan` as a column of its one input, where `plan` keeps
/// every row of it, in order, and passes the column through.
fn step<'a>(plan: &'a LogicalPlan, col: &Column) -> Option<(&'a LogicalPlan, Column)> {
    let i = plan.schema().index_of_column(col).ok()?;
    if let LogicalPlan::Projection(p) = plan {
        return match strip_alias(&p.expr[i]) {
            Expr::Column(c) => Some((p.input.as_ref(), c.clone())),
            _ => None,
        };
    }
    let (input, true) = passed_rows(plan)? else { return None };
    Some((input, child_column(input, i)?))
}

/// True if `v` is the number 1.
pub(crate) fn one(v: &ScalarValue) -> bool {
    v.cast_to(&datafusion::arrow::datatypes::DataType::Int64)
        .is_ok_and(|v| v == ScalarValue::Int64(Some(1)))
}
