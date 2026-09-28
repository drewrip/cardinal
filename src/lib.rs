//! Static claims about SQL output cardinality.
//!
//! A query is parsed and optimized into a DataFusion `LogicalPlan`, every operator
//! gets a Z3 integer for its output cardinality, and each operator contributes
//! constraints relating its output to its inputs. We then ask Z3 whether the root's
//! cardinality must be at most the sum of all table scan cardinalities.

mod analyzer;

use std::collections::HashMap;

use datafusion::logical_expr::LogicalPlan;
use datafusion::prelude::SessionContext;
use z3::SatResult;
use z3::ast::Int;

use analyzer::Analyzer;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    DataFusion(#[from] datafusion::error::DataFusionError),
}

pub type Result<T> = std::result::Result<T, Error>;

/// Outcome of checking `O_root <= Σ scans`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// The claim holds for every assignment satisfying the constraints.
    Proven,
    /// A counterexample: values for every table, scan and operator variable.
    Refuted(HashMap<String, i64>),
    /// Z3 could not decide (e.g. nonlinear `l * r` terms); holds its reason.
    Unknown(String),
}

#[derive(Debug, Clone)]
pub struct Analysis {
    pub verdict: Verdict,
    /// The constraint set `S` plus the negated claim, in SMT-LIB form.
    pub smtlib: String,
    /// Name of the root operator's variable.
    pub root: String,
    /// Each scan as (scan variable, table name), in visit order.
    pub scans: Vec<(String, String)>,
    /// The optimized plan that was analyzed, for display.
    pub plan: String,
}

/// Parses and optimizes `sql` with `ctx`, then analyzes the resulting plan.
pub async fn analyze_sql(ctx: &SessionContext, sql: &str) -> Result<Analysis> {
    let state = ctx.state();
    let plan = state.create_logical_plan(sql).await?;
    let plan = state.optimize(&plan)?;
    Ok(analyze_plan(&plan))
}

/// Analyzes an already-built logical plan.
pub fn analyze_plan(plan: &LogicalPlan) -> Analysis {
    let mut a = Analyzer::new();
    let root = a.visit(plan);

    let scan_vars: Vec<&Int> = a.scans.iter().map(|(_, _, v)| v).collect();
    let total = if scan_vars.is_empty() {
        Int::from_i64(0)
    } else {
        Int::add(&scan_vars)
    };
    // Prove the claim by showing its negation is unsatisfiable.
    a.solver.assert(root.le(&total).not());
    let smtlib = a.solver.to_string();

    let verdict = match a.solver.check() {
        SatResult::Unsat => Verdict::Proven,
        SatResult::Unknown => Verdict::Unknown(
            a.solver
                .get_reason_unknown()
                .unwrap_or_else(|| "unknown".to_string()),
        ),
        SatResult::Sat => {
            let model = a.solver.get_model().expect("sat result has a model");
            let named = a
                .tables
                .iter()
                .map(|(name, v)| (name.clone(), v.clone()))
                .chain(a.vars.iter().cloned());
            let values = named
                .filter_map(|(name, v)| {
                    model
                        .eval(&v, true)
                        .and_then(|x| x.as_i64())
                        .map(|x| (name, x))
                })
                .collect();
            Verdict::Refuted(values)
        }
    };

    Analysis {
        verdict,
        smtlib,
        root: root.to_string(),
        scans: a
            .scans
            .iter()
            .map(|(s, t, _)| (s.clone(), t.clone()))
            .collect(),
        plan: plan.display_indent().to_string(),
    }
}
