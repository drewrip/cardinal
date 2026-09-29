//! Checks a real execution of an analyzed plan against its constraints.

use std::collections::HashMap;
use std::sync::Arc;

use datafusion::arrow::datatypes::{Field, Schema};
use datafusion::arrow::record_batch::{RecordBatch, RecordBatchOptions};
use datafusion::common::TableReference;
use datafusion::common::tree_node::TreeNode;
use datafusion::datasource::{MemTable, provider_as_source};
use datafusion::execution::context::SessionState;
use datafusion::logical_expr::LogicalPlan;
use datafusion::logical_expr::logical_plan::TableScanBuilder;
use datafusion::physical_plan::collect;
use datafusion::physical_planner::{DefaultPhysicalPlanner, PhysicalPlanner};
use datafusion::prelude::SessionContext;
use z3::SatResult;
use z3::ast::Int;

use crate::analyzer::{Node, new_solver};
use crate::{Error, Result, Validation};

/// Evaluates `nodes` bottom-up and returns the actual row count of every node
/// that could be evaluated, as (variable, rows), children before parents.
///
/// Each node runs over scans of its children's materialized output rather than
/// over its original subtree, so a parent sees exactly the rows its children's
/// counts describe.
pub(crate) async fn evaluate(nodes: &[Node], ctx: &SessionContext) -> Vec<(String, u64)> {
    let state = ctx.state();
    let mut counts = vec![];
    // For each node, a scan over its materialized output, if it was evaluated.
    let mut outputs: Vec<Option<LogicalPlan>> = Vec::with_capacity(nodes.len());
    // Whether each node's count was recorded.
    let mut counted = vec![false; nodes.len()];
    for (id, node) in nodes.iter().enumerate() {
        if has_side_effects(&node.plan) {
            outputs.push(None);
            continue;
        }
        if let Some((var, raw)) = &node.raw_scan
            && let Some(batches) = run(&state, raw).await
        {
            counts.push((var.clone(), rows(&batches)));
        }
        // A subquery's result is its plan's result; the wrapper has no physical
        // form of its own.
        if let LogicalPlan::Subquery(_) = node.plan
            && let [input] = node.inputs[..]
            && counted[input]
            && let Some(inner) = counts.iter().rev().find(|(v, _)| *v == nodes[input].var)
        {
            counts.push((node.var.clone(), inner.1));
            counted[id] = true;
            outputs.push(outputs[input].clone());
            continue;
        }
        let inputs: Option<Vec<LogicalPlan>> =
            node.inputs.iter().map(|i| outputs[*i].clone()).collect();
        let batches = match inputs {
            Some(inputs) if inputs.is_empty() => run(&state, &node.plan).await,
            Some(inputs) => match node.plan.with_new_exprs(node.plan.expressions(), inputs) {
                Ok(plan) => run(&state, &plan).await,
                Err(_) => None,
            },
            // An input could not be evaluated on its own (e.g. a recursive CTE's
            // work table), so try the whole subtree. That re-executes the inputs,
            // so it is only consistent if none of the missing inputs was counted.
            None if node
                .inputs
                .iter()
                .all(|i| outputs[*i].is_some() || !counted[*i]) =>
            {
                run(&state, &node.plan).await
            }
            None => None,
        };
        let output = batches.and_then(|batches| {
            counts.push((node.var.clone(), rows(&batches)));
            counted[id] = true;
            materialize(id, &node.plan, batches)
        });
        outputs.push(output);
    }
    counts
}

/// Pins each count, in order, onto the constraints and reports the first one
/// that makes them unsatisfiable.
pub(crate) fn check(
    constraints: &str,
    assertions: usize,
    counts: &[(String, u64)],
) -> Result<Validation> {
    let solver = new_solver();
    solver.from_string(constraints);
    let parsed = solver.get_assertions().len();
    if parsed != assertions {
        return Err(Error::Internal(format!(
            "constraints parsed back to {parsed} assertions, expected {assertions}"
        )));
    }
    let mut rows = HashMap::new();
    let mut undecided = false;
    for (var, n) in counts {
        rows.insert(var.clone(), *n);
        solver.assert(Int::new_const(var.as_str()).eq(Int::from_u64(*n)));
        match solver.check() {
            SatResult::Sat => {}
            SatResult::Unknown => undecided = true,
            SatResult::Unsat => {
                return Ok(Validation {
                    rows,
                    violation: Some(var.clone()),
                    undecided,
                });
            }
        }
    }
    Ok(Validation {
        rows,
        violation: None,
        undecided,
    })
}

fn rows(batches: &[RecordBatch]) -> u64 {
    batches.iter().map(|b| b.num_rows() as u64).sum()
}

/// True if `plan` contains an operator that is not a read-only query.
fn has_side_effects(plan: &LogicalPlan) -> bool {
    plan.exists(|p| {
        Ok(matches!(
            p,
            LogicalPlan::Dml(_)
                | LogicalPlan::Ddl(_)
                | LogicalPlan::Copy(_)
                | LogicalPlan::Statement(_)
                | LogicalPlan::Explain(_)
                | LogicalPlan::Analyze(_)
                | LogicalPlan::Extension(_)
        ))
    })
    .unwrap_or(true)
}

/// Executes `plan` exactly as given: physical planning only, no logical
/// re-optimization.
async fn run(state: &SessionState, plan: &LogicalPlan) -> Option<Vec<RecordBatch>> {
    let physical = DefaultPhysicalPlanner::default()
        .create_physical_plan(plan, state)
        .await
        .ok()?;
    collect(physical, state.task_ctx()).await.ok()
}

/// A scan over `batches` that carries `plan`'s output schema, qualifiers
/// included, so it can stand in for `plan` as an input of its parent.
fn materialize(id: usize, plan: &LogicalPlan, batches: Vec<RecordBatch>) -> Option<LogicalPlan> {
    let schema = plan.schema();
    let arrow = Arc::clone(schema.inner());
    let batches = batches
        .into_iter()
        .map(|b| {
            let options = RecordBatchOptions::new().with_row_count(Some(b.num_rows()));
            RecordBatch::try_new_with_options(Arc::clone(&arrow), b.columns().to_vec(), &options)
        })
        .collect::<std::result::Result<Vec<_>, _>>()
        .ok()?;
    let mem = MemTable::try_new(Arc::clone(&arrow), vec![batches]).ok()?;
    // The builder derives the scan's schema by qualifying every field with the
    // table name, which fails when `plan`'s output repeats a column name (e.g.
    // `a.id` and `b.id` after a join). So build it over a placeholder with unique
    // names, then swap in the real source and `plan`'s own schema.
    let placeholder = Schema::new(
        arrow
            .fields()
            .iter()
            .enumerate()
            .map(|(i, f)| Field::new(format!("c{i}"), f.data_type().clone(), true))
            .collect::<Vec<_>>(),
    );
    let placeholder = MemTable::try_new(Arc::new(placeholder), vec![vec![]]).ok()?;
    let mut scan = TableScanBuilder::new(
        TableReference::bare(format!("__cardinal_{id}")),
        provider_as_source(Arc::new(placeholder)),
    )
    .build()
    .ok()?;
    scan.source = provider_as_source(Arc::new(mem));
    scan.projected_schema = Arc::clone(schema);
    Some(LogicalPlan::TableScan(scan))
}
