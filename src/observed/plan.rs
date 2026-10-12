//! An observed plan as a DataFusion [`LogicalPlan`] of the same shape, so
//! that a query can be analyzed as an engine planned it.
//!
//! Facts name the rows an engine's operators computed. A query planned by
//! DataFusion asks about the rows of DataFusion's operators, which may join
//! in another order or push other filters into scans, and so asks about rows
//! no engine counted. Read from the engine's own plan, the query asks about
//! the rows its profiles count.
//!
//! The plan is built as written, never optimized. Every operator outputs the
//! base-table instance columns of its input (`lineitem#3.l_orderkey`), which
//! is what an observed plan's predicates and keys read, so projections, sorts
//! and windows, which keep every row, are left out. What does not translate
//! (an operator without a model, a predicate that did not resolve, a plan
//! DataFusion rejects) becomes an opaque operator or predicate, which bounds
//! nothing and names no rows: the analysis stays sound, only weaker.

use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;
use std::sync::Arc;

use datafusion::arrow::datatypes::DataType;
use datafusion::common::tree_node::{Transformed, TreeNode};
use datafusion::common::{Column, DFSchema, DFSchemaRef, DataFusionError, JoinConstraint, JoinType, NullEquality};
use datafusion::datasource::provider_as_source;
use datafusion::logical_expr::logical_plan::{Extension, Join, LogicalPlan, LogicalPlanBuilder, TableScanBuilder};
use datafusion::functions_aggregate::count::count_all;
use datafusion::logical_expr::utils::conjunction;
use datafusion::logical_expr::{
    BinaryExpr, ColumnarValue, Expr, Operator, ScalarFunctionArgs, ScalarUDF, ScalarUDFImpl, Signature,
    UserDefinedLogicalNodeCore, Volatility, lit,
};

use super::{Catalog, Lineage, ObservedPlan, Op, Pred, base_table, qualified, requalify};
use datafusion::common::Result;

impl Catalog {
    /// `plan`'s operators as a [`LogicalPlan`] over this catalog's tables, in
    /// the engine's order. Scans are aliased by instance (`lineitem#3`).
    pub fn to_logical(&self, plan: &ObservedPlan) -> crate::Result<LogicalPlan> {
        Ok(Translator { catalog: self, plan }.build(plan.root, "").plan)
    }
}

/// A translated operator.
#[derive(Clone)]
struct Built {
    plan: LogicalPlan,
    /// Expressions the operator outputs as a column of its own: a GROUP BY's
    /// keys that are not columns, and aggregate values of a copy.
    subst: HashMap<Expr, Expr>,
}

impl Built {
    fn new(plan: LogicalPlan) -> Built {
        Built { plan, subst: HashMap::new() }
    }
}

struct Translator<'a> {
    catalog: &'a Catalog,
    plan: &'a ObservedPlan,
}

impl Translator<'_> {
    /// Node `i`, with each of its instances renamed with `suffix`: the copy a
    /// [`Op::Reuse`] reads.
    fn build(&self, i: usize, suffix: &str) -> Built {
        let node = &self.plan.nodes[i];
        match &node.op {
            Op::Reuse { suffix: s, .. } => return self.build(node.children[0], &format!("{s}{suffix}")),
            // A filter on a mark join's mark reads its join's inputs.
            Op::MarkFilter { negated } => {
                let mark = &self.plan.nodes[node.children[0]];
                if let Op::Join { kind: JoinType::LeftMark, on } = &mark.op {
                    let kids: Vec<Built> = mark.children.iter().map(|&c| self.build(c, suffix)).collect();
                    let kind = if *negated { JoinType::LeftAnti } else { JoinType::LeftSemi };
                    return self
                        .join(kind, *negated, on, &kids, suffix)
                        .unwrap_or_else(|e| opaque(&node.engine_op, &e, &kids));
                }
            }
            Op::Join { .. } => {
                if let Some(b) = self.late_materialization(i, suffix) {
                    return b;
                }
            }
            _ => {}
        }
        let kids: Vec<Built> = node.children.iter().map(|&c| self.build(c, suffix)).collect();
        self.convert(i, &kids, suffix).unwrap_or_else(|e| opaque(&node.engine_op, &e, &kids))
    }

    /// DuckDB's late materialization: a limit or top-n picks rows of a scan
    /// of `T`, and a semi join on `rowid = rowid` reads their columns from
    /// another, unfiltered scan of `T`. Its rows are exactly the ones picked,
    /// which carry the same values, so it reads as the picking side, with
    /// the other scan's columns read as the picking scan's.
    fn late_materialization(&self, i: usize, suffix: &str) -> Option<Built> {
        let node = &self.plan.nodes[i];
        let Op::Join { kind: JoinType::LeftSemi, on } = &node.op else { return None };
        let ([cond], [probe, pick]) = (&on[..], &node.children[..]) else { return None };
        if cond.text.split_whitespace().collect::<Vec<_>>() != ["rowid", "=", "rowid"] {
            return None;
        }
        let Op::Scan { table, instance: read, filters, .. } = &self.plan.nodes[*probe].op else { return None };
        if filters.iter().any(|f| !f.optional) {
            return None;
        }
        // The picked rows are some of one scan's, each once.
        let mut j = *pick;
        let picked = loop {
            let n = &self.plan.nodes[j];
            match &n.op {
                Op::Scan { table: t, instance, .. } if t == table => break instance,
                Op::Filter { .. } | Op::Project | Op::Sort | Op::Window | Op::Limit { .. } | Op::TopN { .. } => j = n.children[0],
                _ => return None,
            }
        };
        let mut b = self.build(*pick, suffix);
        for c in self.catalog.columns(table)? {
            b.subst.insert(qualified(&format!("{read}{suffix}"), &c), qualified(&format!("{picked}{suffix}"), &c));
        }
        Some(b)
    }

    fn convert(&self, i: usize, kids: &[Built], suffix: &str) -> Result<Built> {
        let node = &self.plan.nodes[i];
        let input = || kids[0].clone();
        Ok(match (&node.op, kids) {
            (Op::Scan { table, instance, filters, .. }, []) => self.scan(table, &format!("{instance}{suffix}"), filters)?,
            (Op::Filter { predicate }, [k]) => {
                // A filter that printed no predicate still filters.
                let preds: Vec<Expr> = predicate.iter().map(|p| pred(p, k, suffix)).collect();
                let p = conjunction(preds).unwrap_or_else(|| opaque_pred(&node.engine_op));
                Built { plan: LogicalPlanBuilder::from(k.plan.clone()).filter(p)?.build()?, subst: k.subst.clone() }
            }
            (Op::Project | Op::Sort, [_]) => input(),
            // Its window functions, each read above as its column.
            (Op::Window, [k]) => {
                let windows: Vec<Expr> = node
                    .columns
                    .iter()
                    .filter_map(|c| match &c.lineage {
                        Lineage::Exact(e @ Expr::WindowFunction(_)) => substitute(e, k, suffix),
                        _ => None,
                    })
                    .filter(|w| w.column_refs().into_iter().all(|c| k.plan.schema().has_column(c)))
                    .collect();
                if windows.is_empty() {
                    return Ok(input());
                }
                let plan = LogicalPlanBuilder::from(k.plan.clone()).window(windows.clone())?.build()?;
                let mut subst = k.subst.clone();
                for (w, field) in windows.iter().zip(plan.schema().fields().iter().skip(k.plan.schema().fields().len())) {
                    subst.insert(w.clone(), Expr::Column(Column::new_unqualified(field.name())));
                }
                Built { plan, subst }
            }
            // Only a cross product joins on nothing: a join that printed no
            // condition has one.
            (Op::Join { kind, on }, [_, _]) if on.is_empty() && node.engine_op != "CROSS_PRODUCT" => {
                let on = [Pred { expr: None, text: node.engine_op.clone(), optional: false }];
                self.join(*kind, false, &on, kids, suffix)?
            }
            (Op::Join { kind, on }, [_, _]) => self.join(*kind, false, on, kids, suffix)?,
            (Op::Aggregate { keys, values }, [k]) => self.aggregate(i, keys, values, k, suffix)?,
            // A sort keeping the first `offset + fetch` rows, then a limit
            // skipping `offset`.
            (Op::TopN { fetch, offset }, [k]) => {
                let Some(first) = k.plan.schema().columns().into_iter().next() else {
                    return Err(plan_error("top n over no columns"));
                };
                let sort = Expr::Column(first).sort(true, true);
                let b = LogicalPlanBuilder::from(k.plan.clone()).sort_with_limit(vec![sort], Some((fetch + offset) as usize))?;
                let b = match offset {
                    0 => b,
                    skip => b.limit(*skip as usize, Some(*fetch as usize))?,
                };
                Built { plan: b.build()?, subst: k.subst.clone() }
            }
            // A limit keeps some of its input's rows, at most `at_most`: a
            // filter on what is unknown, then a limit of what is known.
            (Op::Limit { at_most }, [k]) => {
                let b = LogicalPlanBuilder::from(k.plan.clone()).filter(opaque_pred(&node.engine_op))?;
                let b = match at_most {
                    Some(n) => b.limit(0, Some(*n as usize))?,
                    None => b,
                };
                Built { plan: b.build()?, subst: k.subst.clone() }
            }
            // Each input, as one column: nothing above reads a union's
            // columns, which an observed plan does not trace.
            (Op::Union, [first, rest @ ..]) if !rest.is_empty() => {
                let one = |k: &Built| LogicalPlanBuilder::from(k.plan.clone()).project([lit(0i64).alias("union")])?.build();
                let mut b = LogicalPlanBuilder::from(one(first)?);
                for k in rest {
                    b = b.union(one(k)?)?;
                }
                Built::new(b.build()?)
            }
            _ => return Err(plan_error("no model")),
        })
    }

    /// A scan of `table`, with its pushed filters, aliased as `instance`.
    /// Optional filters may not have been applied, and runtime filters drop
    /// only rows the join above drops: neither changes the rows above.
    fn scan(&self, table: &str, instance: &str, filters: &[Pred]) -> Result<Built> {
        let provider = self.catalog.providers.get(table).ok_or_else(|| plan_error("unknown table"))?;
        let source = provider_as_source(provider.clone());
        // Pushed filters read the scan's own columns, under the table's name.
        let raw = Built::new(LogicalPlanBuilder::scan(table, source.clone(), None)?.build()?);
        let to_table = |r: &str| base_table(r).map(|_| table.to_string());
        let filters: Vec<Expr> = filters
            .iter()
            .filter(|p| !p.optional)
            .map(|p| match &p.expr {
                Some(e) => Some(requalify(e, &to_table)).filter(|e| resolves(e, &raw)),
                None => None,
            }.unwrap_or_else(|| opaque_pred(&p.text)))
            .collect();
        let scan = TableScanBuilder::new(table, source).with_filters(filters).build()?;
        let plan = LogicalPlanBuilder::from(LogicalPlan::TableScan(scan)).alias(instance)?.build()?;
        Ok(Built::new(plan))
    }

    /// A join of `kids` on `on`: equalities between one side and the other
    /// are its keys, and the rest its filter.
    fn join(&self, kind: JoinType, null_aware: bool, on: &[Pred], kids: &[Built], suffix: &str) -> Result<Built> {
        let [l, r] = kids else { return Err(plan_error("join of other than two inputs")) };
        let mut both = l.clone();
        both.subst.extend(r.subst.clone());
        let both_schema = l.plan.schema().join(r.plan.schema())?;
        both.plan = LogicalPlan::EmptyRelation(datafusion::logical_expr::EmptyRelation {
            produce_one_row: false,
            schema: Arc::new(both_schema),
        });
        let preds: Vec<Expr> = on.iter().map(|p| pred(p, &both, suffix)).collect();
        // Keys compare with `=`, or all with `IS NOT DISTINCT FROM`, as
        // DuckDB joins a decorrelated subquery to its input.
        let distinct = |e: &Expr| matches!(e, Expr::BinaryExpr(BinaryExpr { op: Operator::IsNotDistinctFrom, .. }));
        let (key_op, null_equality) = match !preds.is_empty() && preds.iter().all(distinct) {
            true => (Operator::IsNotDistinctFrom, NullEquality::NullEqualsNull),
            false => (Operator::Eq, NullEquality::NullEqualsNothing),
        };
        let (mut keys, mut filter) = (vec![], vec![]);
        for e in preds {
            if let Expr::BinaryExpr(BinaryExpr { left: a, op, right: b }) = &e
                && *op == key_op
            {
                if resolves(a, l) && resolves(b, r) {
                    keys.push((*a.clone(), *b.clone()));
                    continue;
                }
                if resolves(b, l) && resolves(a, r) {
                    keys.push((*b.clone(), *a.clone()));
                    continue;
                }
            }
            filter.push(e);
        }
        let join = Join::try_new(
            Arc::new(l.plan.clone()),
            Arc::new(r.plan.clone()),
            keys,
            conjunction(filter),
            kind,
            JoinConstraint::On,
            null_equality,
            null_aware,
        )?;
        let subst = match kind {
            JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => l.subst.clone(),
            JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => r.subst.clone(),
            _ => both.subst,
        };
        Ok(Built { plan: LogicalPlan::Join(join), subst })
    }

    /// A GROUP BY `keys` with `values`, node `i`. Keys that are not columns,
    /// and values, are columns of relation `@i` (renamed in a copy), as the
    /// observed plan names its values.
    fn aggregate(&self, i: usize, keys: &[Option<Expr>], values: &[Option<Expr>], k: &Built, suffix: &str) -> Result<Built> {
        let relation = format!("@{i}{suffix}");
        let mut subst = HashMap::new();
        let mut group = vec![];
        let columns = &self.plan.nodes[i].columns;
        for (j, key) in keys.iter().enumerate() {
            // A key that did not resolve groups by some value of the row.
            let e = key.as_ref().and_then(|key| expr(key, k, suffix)).unwrap_or_else(|| opaque_value(&format!("{} (key {j})", columns[j].name)));
            let g = match &e {
                Expr::Column(_) => e.clone(),
                _ => {
                    let name = format!("key{j}");
                    subst.insert(e.clone(), Expr::Column(Column::new(Some(relation.as_str()), &name)));
                    e.clone().alias_qualified(Some(relation.as_str()), name)
                }
            };
            if !group.contains(&g) {
                group.push(g);
            }
        }
        let names = &columns[keys.len()..];
        let mut aggs = vec![];
        for (v, col) in values.iter().zip(names) {
            let (Some(v), Lineage::Exact(Expr::Column(c))) = (v, &col.lineage) else { continue };
            let Some(v) = expr(v, k, suffix) else { continue };
            let out = Column::new(Some(relation.as_str()), &c.name);
            if out != *c {
                subst.insert(Expr::Column(c.clone()), Expr::Column(out));
            }
            if !aggs.iter().any(|a: &Expr| a.schema_name().to_string() == c.name) {
                aggs.push(v.alias_qualified(Some(relation.as_str()), &c.name));
            }
        }
        // An aggregate with no value read still has its rows: one, ungrouped.
        if group.is_empty() && aggs.is_empty() {
            aggs.push(count_all().alias_qualified(Some(relation.as_str()), "count_star()"));
        }
        let plan = LogicalPlanBuilder::from(k.plan.clone()).aggregate(group, aggs)?.build()?;
        Ok(Built { plan, subst })
    }
}

/// Renames each instance with `suffix`.
fn rename(suffix: &str) -> impl Fn(&str) -> Option<String> + '_ {
    move |r| base_table(r).map(|_| format!("{r}{suffix}"))
}

/// `e`, an expression of the observed plan, over `input`'s output: its
/// instances renamed with `suffix`, and what `input` computes read from its
/// columns. `None` if it reads anything else.
fn expr(e: &Expr, input: &Built, suffix: &str) -> Option<Expr> {
    let e = substitute(e, input, suffix)?;
    resolves(&e, input).then_some(e)
}

/// `e` with its instances renamed with `suffix`, and what `input` computes
/// read from its columns.
fn substitute(e: &Expr, input: &Built, suffix: &str) -> Option<Expr> {
    let e = if suffix.is_empty() { e.clone() } else { requalify(e, &rename(suffix)) };
    let e = e
        .transform_down(|e| match input.subst.get(&e) {
            Some(c) => Ok(Transformed::new(c.clone(), true, datafusion::common::tree_node::TreeNodeRecursion::Jump)),
            None => Ok(Transformed::no(e)),
        })
        .ok()?
        .data;
    Some(e)
}

/// A predicate over `input`, or an opaque one if it did not resolve.
fn pred(p: &Pred, input: &Built, suffix: &str) -> Expr {
    p.expr.as_ref().and_then(|e| expr(e, input, suffix)).unwrap_or_else(|| opaque_pred(&p.text))
}

/// Whether every column `e` reads is one of `input`'s, and every window
/// function's value it reads one `input` computed.
fn resolves(e: &Expr, input: &Built) -> bool {
    let schema = input.plan.schema();
    e.column_refs().into_iter().all(|c| schema.has_column(c))
        && !e.exists(|x| Ok(matches!(x, Expr::WindowFunction(_)))).unwrap_or(true)
}

fn plan_error(what: &str) -> DataFusionError {
    DataFusionError::Plan(format!("cannot translate: {what}"))
}

/// An operator without a model, over `kids`, and why: it outputs what its
/// one input does, or the columns of all of them.
fn opaque(engine_op: &str, why: &DataFusionError, kids: &[Built]) -> Built {
    let mut schema = DFSchema::empty();
    for k in kids {
        schema.merge(k.plan.schema());
    }
    let subst = match kids {
        [k] => k.subst.clone(),
        _ => HashMap::new(),
    };
    let node = Opaque {
        name: format!("{engine_op} ({})", why.strip_backtrace()),
        inputs: kids.iter().map(|k| k.plan.clone()).collect(),
        schema: Arc::new(schema),
    };
    Built { plan: LogicalPlan::Extension(Extension { node: Arc::new(node) }), subst }
}

/// An operator the analysis has no model for, so bounds nothing about.
#[derive(Debug, PartialEq, Eq, Hash)]
struct Opaque {
    name: String,
    inputs: Vec<LogicalPlan>,
    schema: DFSchemaRef,
}

impl PartialOrd for Opaque {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.name.cmp(&other.name) {
            Ordering::Equal => self.inputs.partial_cmp(&other.inputs),
            o => Some(o),
        }
    }
}

impl UserDefinedLogicalNodeCore for Opaque {
    fn name(&self) -> &str {
        "Opaque"
    }

    fn inputs(&self) -> Vec<&LogicalPlan> {
        self.inputs.iter().collect()
    }

    fn schema(&self) -> &DFSchemaRef {
        &self.schema
    }

    fn expressions(&self) -> Vec<Expr> {
        vec![]
    }

    fn fmt_for_explain(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Opaque: {}", self.name)
    }

    fn with_exprs_and_inputs(&self, _exprs: Vec<Expr>, inputs: Vec<LogicalPlan>) -> Result<Self> {
        Ok(Opaque { name: self.name.clone(), inputs, schema: self.schema.clone() })
    }
}

/// A predicate that did not resolve: `opaque('<text>')`, volatile, so that
/// it bounds nothing and no fact names the rows it keeps.
fn opaque_pred(text: &str) -> Expr {
    opaque_fn(text, DataType::Boolean)
}

/// A value that did not resolve, as [`opaque_pred`]. A string: a boolean
/// would take at most three values.
fn opaque_value(text: &str) -> Expr {
    opaque_fn(text, DataType::Utf8)
}

fn opaque_fn(text: &str, ty: DataType) -> Expr {
    let f = OpaqueFn { signature: Signature::any(1, Volatility::Volatile), ty };
    ScalarUDF::new_from_impl(f).call(vec![lit(text.to_string())])
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct OpaqueFn {
    signature: Signature,
    ty: DataType,
}

impl ScalarUDFImpl for OpaqueFn {
    fn name(&self) -> &str {
        "opaque"
    }

    fn signature(&self) -> &Signature {
        &self.signature
    }

    fn return_type(&self, _: &[DataType]) -> Result<DataType> {
        Ok(self.ty.clone())
    }

    fn invoke_with_args(&self, _: ScalarFunctionArgs) -> Result<ColumnarValue> {
        Err(plan_error("an opaque expression has no value"))
    }
}
