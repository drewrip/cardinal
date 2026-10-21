//! The contexts of a DataFusion plan's operators, named as facts name them.
//!
//! Facts are read off plans an engine ran; a query to bound is a DataFusion
//! [`LogicalPlan`]. To look up what is known about an operator, its rows are
//! named the way [`super::context::state`] names an executed operator's: each
//! scan is a table instance (`lineitem#4`, by node), predicates are written
//! over instance columns through every projection and alias, and the rules
//! for building contexts are the same, so the same rows read the same from
//! either side. Expressions go through the same [`normalize`] facts' do.

use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

use datafusion::arrow::datatypes::{Field, Schema, SchemaRef};
use datafusion::common::tree_node::{Transformed, TreeNode};
use datafusion::common::{DataFusionError, JoinType, NullEquality};
use datafusion::datasource::source_as_provider;
use datafusion::logical_expr::logical_plan::{Distinct, LogicalPlan};
use datafusion::logical_expr::utils::split_conjunction_owned;
use datafusion::logical_expr::{BinaryExpr, Expr, Operator};

use super::context::{Context, ExistsKind, Taint, Term};
use super::FactKind;
use crate::analyzer::{self, Node};
use crate::first;
use crate::observed::{base_table, normalize, qualified};

/// Every node's context, and what it is computed from.
pub(crate) struct Logical {
    /// Each node's rows, or why they are no context's.
    pub contexts: Vec<Result<Context, Taint>>,
    /// Each node's own terms: a scan's or filter's predicates, a join's
    /// condition, or a grouping's keys. `None` if they did not resolve.
    pub args: Vec<Option<BTreeSet<Term>>>,
    /// Each base-table scan's instance, by node.
    pub instances: Vec<Option<String>>,
    /// Each node's output columns, over instance columns.
    pub lineage: Vec<Vec<Option<Expr>>>,
    /// The schema of every table scanned, by name.
    tables: HashMap<String, SchemaRef>,
    /// Every aggregate value's column, with its type.
    values: Vec<Field>,
}

impl Logical {
    /// The contexts of `nodes` (children before parents). `scans` maps each
    /// base-table scan's variable to its table.
    pub(crate) fn new(nodes: &[Node], scans: &[(String, String)]) -> Logical {
        Logical::reduced(nodes, scans, &[])
    }

    /// [`Logical::new`], with each node `i` that `same[i]` says outputs
    /// input `k`'s rows one for one (`Some(k)`) given input `k`'s context.
    /// A filter or a scan's filters keep every row; a join keeps side `k`'s
    /// rows each once, and the other side's columns read as nothing, so that
    /// what reads them is unresolved. Contexts so named count the same rows,
    /// but name them differently from facts.
    pub(crate) fn reduced(nodes: &[Node], scans: &[(String, String)], same: &[Option<usize>]) -> Logical {
        let mut l = Logical {
            contexts: vec![],
            args: vec![],
            instances: vec![],
            lineage: vec![],
            tables: HashMap::new(),
            values: vec![],
        };
        for (i, node) in nodes.iter().enumerate() {
            let (mut ctx, args, mut lineage) = l.node(nodes, scans, i);
            if let Some(k) = same.get(i).copied().flatten() {
                (ctx, lineage) = l.same(nodes, i, k, lineage);
            }
            let width = node.plan.schema().fields().len();
            lineage.resize(width, None);
            l.contexts.push(ctx);
            l.args.push(args);
            l.lineage.push(lineage);
        }
        l
    }

    #[allow(clippy::type_complexity)]
    fn node(
        &mut self,
        nodes: &[Node],
        scans: &[(String, String)],
        i: usize,
    ) -> (Result<Context, Taint>, Option<BTreeSet<Term>>, Vec<Option<Expr>>) {
        self.instances.push(None);
        let node = &nodes[i];
        let input = |k: usize| self.contexts[node.inputs[k]].clone();
        let pass = |k: usize| self.lineage[node.inputs[k]].clone();
        let unsupported = || Err(Taint::Unsupported(plan_name(&node.plan)));
        match &node.plan {
            LogicalPlan::TableScan(scan) => {
                let var = node.raw_scan.as_ref().map_or(&node.var, |(v, _, _)| v);
                let Some((_, table)) = scans.iter().find(|(s, _)| s == var) else {
                    return (unsupported(), None, vec![]);
                };
                let instance = format!("{table}#{i}");
                if let Ok(p) = source_as_provider(&scan.source) {
                    self.tables.insert(table.clone(), p.schema());
                }
                self.instances[i] = Some(instance.clone());
                let lineage = scan.projected_schema.fields().iter().map(|f| Some(qualified(&instance, f.name()))).collect();
                let column = |c: &datafusion::common::Column| Some(qualified(&instance, &c.name));
                let preds = self.terms(scan.filters.iter().cloned(), &column);
                let ctx = match (&preds, scan.fetch) {
                    (Err(t), _) => Err(t.clone()),
                    // A pushed-down fetch may cut the scan short.
                    (_, Some(_)) => Err(Taint::EarlyStop),
                    // Filters applied inexactly may let through rows that
                    // fail them, until a filter above checks them.
                    (Ok(p), None) if analyzer::inexact_filters(scan) => {
                        Err(Taint::Pruned(p.iter().map(|t| t.to_string()).collect::<Vec<_>>().join(" and ")))
                    }
                    (Ok(p), None) => Ok(Context::table(&instance).filter(p)),
                };
                (ctx, preds.ok(), lineage)
            }
            LogicalPlan::Projection(p) => {
                let lineage = p.expr.iter().map(|e| self.resolve(nodes, i, e).ok()).collect();
                (input(0), None, lineage)
            }
            LogicalPlan::SubqueryAlias(_) | LogicalPlan::Subquery(_) | LogicalPlan::Repartition(_) => {
                (input(0), None, pass(0))
            }
            LogicalPlan::Window(_) => (input(0), None, pass(0)),
            LogicalPlan::Sort(s) => {
                let ctx = match s.fetch {
                    None => input(0),
                    Some(n) => input(0).map(|c| Context::Derived { op: format!("top {n}"), args: vec![], inputs: vec![c] }),
                };
                (ctx, None, pass(0))
            }
            LogicalPlan::Limit(_) => (Err(Taint::EarlyStop), None, pass(0)),
            // The first row of each partition: as many rows as a GROUP BY on
            // the partition, which is all that is named of them. Which row
            // of a partition was kept depends on the window's order, so its
            // other columns read as nothing.
            LogicalPlan::Filter(f) if first::first_rows(f).is_some() => {
                let first = first::first_rows(f).unwrap();
                let mut w = node.inputs[0];
                for _ in 0..first.depth {
                    w = nodes[w].inputs[0];
                }
                let keys: Option<Vec<Expr>> = first
                    .partition
                    .iter()
                    .map(|c| self.rewrite(&Expr::Column(c.clone()), &|c| self.column(nodes, w, c)).ok())
                    .collect();
                let lineage = match &keys {
                    Some(ks) => pass(0).into_iter().map(|e| e.filter(|e| ks.contains(e))).collect(),
                    None => vec![],
                };
                let keys: Option<BTreeSet<Term>> = keys.map(|ks| ks.into_iter().map(Term::new).collect());
                (group(input(0), keys.clone()), keys, lineage)
            }
            LogicalPlan::Filter(f) => {
                let preds = self.terms(split_conjunction_owned(f.predicate.clone()), &|c| self.column(nodes, i, c));
                // Re-checking a scan's inexact filters, its rows are the
                // table's satisfying it.
                let below = match analyzer::rechecked_scan(nodes, i) {
                    Some(k) => self.instances[k].as_deref().map(Context::table).ok_or(Taint::Unsupported("TableScan".into())),
                    None => input(0),
                };
                let ctx = match (&preds, below) {
                    (Err(t), _) => Err(t.clone()),
                    (_, Err(t)) => Err(t),
                    (Ok(p), Ok(c)) => Ok(c.filter(p)),
                };
                (ctx, preds.ok(), pass(0))
            }
            LogicalPlan::Distinct(Distinct::All(_)) => {
                let keys: Option<BTreeSet<Term>> = pass(0).into_iter().map(|e| e.map(Term::new)).collect();
                let ctx = group(input(0), keys.clone());
                (ctx, keys, pass(0))
            }
            LogicalPlan::Aggregate(agg) => {
                if agg.group_expr.iter().any(|e| matches!(e, Expr::GroupingSet(_))) {
                    return (unsupported(), None, vec![]);
                }
                let keys: Option<Vec<Expr>> = agg.group_expr.iter().map(|e| self.resolve(nodes, i, e).ok()).collect();
                let ctx = group(input(0), keys.as_ref().map(|ks| ks.iter().cloned().map(Term::new).collect()));
                let mut lineage: Vec<Option<Expr>> = match &keys {
                    Some(ks) => ks.iter().cloned().map(Some).collect(),
                    None => vec![None; agg.group_expr.len()],
                };
                // Values read as opaque columns, named for the aggregate and
                // the rows it ran over, as `Values::value` names them.
                let fields = node.plan.schema().fields().iter().skip(agg.group_expr.len());
                for (e, field) in agg.aggr_expr.iter().zip(fields) {
                    let value = match (&ctx, self.resolve(nodes, i, e)) {
                        (Ok(over), Ok(v)) => value_column(v, over),
                        _ => None,
                    };
                    if let Some(Expr::Column(c)) = &value {
                        self.values.push(Field::new(&c.name, field.data_type().clone(), true));
                    }
                    lineage.push(value);
                }
                (ctx, keys.map(|ks| ks.into_iter().map(Term::new).collect()), lineage)
            }
            LogicalPlan::Join(join) => {
                let (l, r) = (node.inputs[0], node.inputs[1]);
                let mut on = vec![];
                for (a, b) in &join.on {
                    let (Ok(a), Ok(b)) = (self.resolve_in(nodes, l, a), self.resolve_in(nodes, r, b)) else {
                        on.clear();
                        on.push(None);
                        break;
                    };
                    on.push(Some(match join.null_equality {
                        NullEquality::NullEqualsNothing => a.eq(b),
                        NullEquality::NullEqualsNull => Expr::BinaryExpr(BinaryExpr::new(Box::new(a), Operator::IsNotDistinctFrom, Box::new(b))),
                    }));
                }
                let pairs: Vec<(Expr, Expr)> = join
                    .on
                    .iter()
                    .filter_map(|(a, b)| Some((self.resolve_in(nodes, l, a).ok()?, self.resolve_in(nodes, r, b).ok()?)))
                    .collect();
                let filter = join.filter.iter().cloned().flat_map(split_conjunction_owned);
                let filter: Vec<Option<Expr>> = filter.map(|e| self.resolve(nodes, i, &e).ok()).collect();
                let on: Option<BTreeSet<Term>> =
                    on.into_iter().chain(filter).map(|e| e.map(Term::new)).collect();
                let mut lineage = match join.join_type {
                    JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => pass(0),
                    JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => pass(1),
                    _ => pass(0).into_iter().chain(pass(1)).collect(),
                };
                // On exactly the partition of a side's first rows: the rows
                // of a semi join with the window's input, whose key columns
                // read as their partners'.
                let (lk, rk): (Vec<&Expr>, Vec<&Expr>) = join.on.iter().map(|(a, b)| (a, b)).unzip();
                let plain = join.join_type == JoinType::Inner
                    && join.filter.is_none()
                    && join.null_equality == NullEquality::NullEqualsNothing
                    && pairs.len() == join.on.len();
                let semi = if plain && first::on_partition(&join.right, &rk) {
                    Some(JoinType::LeftSemi)
                } else if plain && first::on_partition(&join.left, &lk) {
                    Some(JoinType::RightSemi)
                } else {
                    None
                };
                if let Some(kind) = semi {
                    let left = pass(0).len();
                    for (j, e) in lineage.iter_mut().enumerate() {
                        let grouped = (kind == JoinType::LeftSemi) == (j >= left);
                        if grouped {
                            let partner = e.as_ref().and_then(|e| {
                                pairs.iter().find_map(|(a, b)| match kind {
                                    JoinType::LeftSemi => (b == e).then(|| a.clone()),
                                    _ => (a == e).then(|| b.clone()),
                                })
                            });
                            *e = partner;
                        }
                    }
                }
                let ctx = match (input(0), input(1), &on) {
                    (Err(t), _, _) | (_, Err(t), _) => Err(t),
                    (_, _, None) => Err(Taint::Unresolved("join condition".into())),
                    (Ok(lc), Ok(rc), Some(on)) => join_context(semi.unwrap_or(join.join_type), join.null_aware, lc, rc, on),
                };
                (ctx, on, lineage)
            }
            LogicalPlan::Union(_) => {
                let inputs: Result<Vec<Context>, Taint> = (0..node.inputs.len()).map(input).collect();
                let ctx = inputs.map(|inputs| Context::Derived { op: "union".into(), args: vec![], inputs });
                (ctx, None, vec![])
            }
            _ => (unsupported(), None, vec![]),
        }
    }

    /// The context and lineage of node `i`, whose rows are input `k`'s one
    /// for one, given its own `lineage`.
    fn same(&self, nodes: &[Node], i: usize, k: usize, lineage: Vec<Option<Expr>>) -> (Result<Context, Taint>, Vec<Option<Expr>>) {
        let node = &nodes[i];
        match &node.plan {
            LogicalPlan::TableScan(_) => {
                let ctx = match &self.instances[i] {
                    Some(instance) => Ok(Context::table(instance)),
                    None => Err(Taint::Unsupported("TableScan".into())),
                };
                (ctx, lineage)
            }
            LogicalPlan::Join(join) => {
                let left = join.left.schema().fields().len();
                let lineage = lineage.into_iter().enumerate().map(|(j, e)| e.filter(|_| (j >= left) == (k == 1))).collect();
                (self.contexts[node.inputs[k]].clone(), lineage)
            }
            _ => (self.contexts[node.inputs[k]].clone(), lineage),
        }
    }

    /// Canonical terms of `exprs`, with columns given by `column`, or why not.
    fn terms(
        &self,
        exprs: impl IntoIterator<Item = Expr>,
        column: &dyn Fn(&datafusion::common::Column) -> Option<Expr>,
    ) -> Result<BTreeSet<Term>, Taint> {
        let mut out = BTreeSet::new();
        for e in exprs {
            for e in split_conjunction_owned(self.rewrite(&e, column)?) {
                out.insert(Term::new(e));
            }
        }
        Ok(out)
    }

    /// `e`, evaluated over the inputs of node `i`, as an expression over
    /// instance columns.
    fn resolve(&self, nodes: &[Node], i: usize, e: &Expr) -> Result<Expr, Taint> {
        self.rewrite(e, &|c| self.column(nodes, i, c))
    }

    /// `e`, evaluated over the output of node `i`.
    fn resolve_in(&self, nodes: &[Node], i: usize, e: &Expr) -> Result<Expr, Taint> {
        self.rewrite(e, &|c| self.output(nodes, i, c))
    }

    fn rewrite(&self, e: &Expr, column: &dyn Fn(&datafusion::common::Column) -> Option<Expr>) -> Result<Expr, Taint> {
        let unresolved = || Taint::Unresolved(e.to_string());
        let out = e
            .clone()
            .transform_up(|e| match e {
                Expr::Column(c) => column(&c).map(Transformed::yes).ok_or_else(|| plan_error("column")),
                Expr::Alias(a) => Ok(Transformed::yes(*a.expr)),
                Expr::ScalarSubquery(_)
                | Expr::Exists(_)
                | Expr::InSubquery(_)
                | Expr::OuterReferenceColumn(..)
                | Expr::Placeholder(_) => Err(plan_error("subquery")),
                e => Ok(Transformed::no(e)),
            })
            .map_err(|_| unresolved())?
            .data;
        if out.is_volatile() {
            return Err(Taint::Volatile(e.to_string()));
        }
        Ok(normalize(out, &|r| match base_table(r) {
            Some(t) => self.tables.get(t).cloned(),
            None if r == "value" => Some(Arc::new(Schema::new(self.values.clone()))),
            None => None,
        }))
    }

    /// The lineage of column `c` of node `i`'s inputs.
    fn column(&self, nodes: &[Node], i: usize, c: &datafusion::common::Column) -> Option<Expr> {
        nodes[i].inputs.iter().find_map(|&k| self.output(nodes, k, c))
    }

    /// The lineage of column `c` of node `i`'s output.
    fn output(&self, nodes: &[Node], i: usize, c: &datafusion::common::Column) -> Option<Expr> {
        let j = nodes[i].plan.schema().maybe_index_of_column(c)?;
        self.lineage[i].get(j).cloned().flatten()
    }
}

/// A GROUP BY or DISTINCT on `keys` over `input`, as `context::state` names it.
fn group(input: Result<Context, Taint>, keys: Option<BTreeSet<Term>>) -> Result<Context, Taint> {
    let input = input?;
    let keys = keys.ok_or_else(|| Taint::Unresolved("grouping key".into()))?;
    let op = if keys.is_empty() { "aggregate" } else { "group" };
    Ok(Context::Derived { op: op.into(), args: keys.into_iter().collect(), inputs: vec![input] })
}

/// A join's rows, as `context::state` names them. A null-aware anti join is
/// `NOT IN`, which an executed plan shows as a mark join filtered on its mark.
fn join_context(kind: JoinType, null_aware: bool, l: Context, r: Context, on: &BTreeSet<Term>) -> Result<Context, Taint> {
    if !l.tables().is_disjoint(&r.tables()) {
        return Err(Taint::SelfJoin);
    }
    Ok(match kind {
        JoinType::Inner => l.cross(&r).unwrap().filter(on),
        JoinType::LeftAnti if null_aware => l.exists(ExistsKind::NotIn, on.clone(), r),
        kind => Context::join(kind, on.clone(), l, r),
    })
}

/// The opaque column for aggregate `value` over the rows of `over`, named as
/// `Values::value` names it.
fn value_column(value: Expr, over: &Context) -> Option<Expr> {
    let kind = FactKind::Distinct { keys: [Term::new(value)].into(), over: over.clone() }.canonical();
    let FactKind::Distinct { keys, over } = kind else { unreachable!() };
    Some(qualified("value", &format!("{} of {over}", keys.first()?)))
}

fn plan_name(plan: &LogicalPlan) -> String {
    plan.display().to_string().split(':').next().unwrap_or_default().to_string()
}

fn plan_error(what: &str) -> DataFusionError {
    DataFusionError::Plan(format!("unresolved {what}"))
}
