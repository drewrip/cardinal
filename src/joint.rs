//! Reference plans: a query analyzed together with the executed plans of
//! other queries ([`Builder::with_plans`](crate::Builder::with_plans)),
//! each counted operator pinned to its rows.
//!
//! No rules read facts off the plans, combine them, or match them to the
//! query's operators: the plans' operators get the constraints any
//! operator does, [link](crate::link) relates them to the query's by their
//! contexts, and Z3 finds what follows.
//!
//! ```text
//!  query ──────────┐
//!                  ├─ rules ─ link ─ pins ─ solve-eqs ─ dedup ─▶ Analysis
//!  plans ─ select ─┘               X = rows
//! ```
//!
//! # Spec
//!
//! - **Input**: the query's plan, executed plans of other queries over the
//!   same data, translated with a [`Catalog`], and the options.
//! - **Selection**: of each plan, the maximal subtrees that scan only
//!   tables the query scans or those reference by foreign keys,
//!   transitively (`maximal`). Subtrees over a referenced table bound its
//!   size, which the `referenced size` rule
//!   ([`Analyzer::referenced_size`]) bounds the referencing columns'
//!   distinct counts by. Other subtrees share no context with the query's.
//! - **Pins**: each operator the engine counted, and that did not stop
//!   early, holds its node's rows: `X = rows`, or `X ≥ rows` where a
//!   runtime filter pruned them (`counts`). Plans that were not run, or
//!   do not translate, are left out.
//! - **Reduction**: each variable but the query's and the tables' that an
//!   assertion defines by others is substituted away (Z3's `solve-eqs`),
//!   and the assertions that then repeat are kept once. The query's
//!   variables and the tables' sizes all stay, with exactly the values they
//!   had, so every bound and claim on them is as before.
//! - **Trace**: with [`Options::trace`], every constraint before the
//!   reduction, the plans' nodes named by their plan
//!   ([`TraceNode::plan`](crate::TraceNode::plan)) and each pin as a fact
//!   (`observed rows`, `observed floor`).
//! - **Not done**: no check that the pins are consistent with the
//!   constraints. Plans of other data, or a wrong rule, make the set
//!   unsatisfiable, and an unsatisfiable set proves any bound.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::ops::Range;
use std::panic::Location;

use datafusion::common::tree_node::TreeNodeRecursion;
use datafusion::logical_expr::LogicalPlan;
use z3::ast::{Ast, Bool, Int};
use z3::{FuncDecl, Goal, Solver, Sort, Tactic};

use crate::analysis::{Analyzer, Node, ranged_columns};
use crate::facts::State;
use crate::facts::state::{states, stopped};
use crate::observed::{Catalog, ObservedPlan, Op};
use crate::trace::{FactClaim, FactInfo, FactRef};
use crate::Options;

/// A reference plan, translated: its root, and each operator with the
/// subplans it became.
pub(crate) struct Translated<'p> {
    plan: &'p ObservedPlan,
    root: LogicalPlan,
    built: Vec<(usize, LogicalPlan)>,
}

/// The plans of `plans` that ran and translate with `catalog`.
pub(crate) fn translate<'p>(catalog: &Catalog, plans: &[&'p ObservedPlan]) -> Vec<Translated<'p>> {
    plans
        .iter()
        .filter(|p| p.counted)
        .filter_map(|p| {
            let (root, built) = catalog.to_logical_mapped(p).ok()?;
            Some(Translated { plan: p, root, built })
        })
        .collect()
}

/// The columns of `plans` that get min and max variables, as the query's
/// do ([`ranged_columns`]).
pub(crate) fn ranged(plans: &[Translated]) -> BTreeSet<String> {
    plans.iter().flat_map(|t| ranged_columns(&t.root)).collect()
}

/// One operator of a reference plan held to the rows it was counted with.
pub(crate) struct Pin {
    /// The analyzer node it became, and its variable.
    node: usize,
    var: String,
    /// The plan, and the operator.
    plan: String,
    op: usize,
    engine_op: String,
    rows: u64,
    /// Whether the rows are only a floor (a runtime filter pruned them).
    floor: bool,
}

/// Visits each of `plans`' subtrees `query` could share rows with
/// (`maximal`), after the query's own nodes. Returns each counted
/// operator's pin, and the nodes each plan became, by its name.
pub(crate) fn visit(
    a: &mut Analyzer,
    query: &LogicalPlan,
    plans: &[Translated],
    options: &Options,
) -> (Vec<Pin>, Vec<(Range<usize>, String)>) {
    let within = reachable(&tables_of(query), options);
    let (mut pins, mut owners) = (vec![], vec![]);
    for t in plans {
        let mut parts = vec![];
        maximal(&t.root, &within, &mut parts);
        let first = a.nodes.len();
        for part in parts {
            let start = a.nodes.len();
            a.visit(part);
            for (m, j, floor) in counts(t.plan, &a.nodes[start..], &t.built) {
                let n = &t.plan.nodes[j];
                pins.push(Pin {
                    node: start + m,
                    var: a.nodes[start + m].var.clone(),
                    plan: t.plan.name.clone(),
                    op: j,
                    engine_op: n.engine_op.clone(),
                    rows: n.rows,
                    floor,
                });
            }
        }
        if a.nodes.len() > first {
            owners.push((first..a.nodes.len(), t.plan.name.clone()));
        }
    }
    (pins, owners)
}

/// Asserts each pin, and gives it as a fact for the trace.
pub(crate) fn assert_pins(a: &Analyzer, pins: &[Pin]) -> Vec<FactClaim> {
    let mut out = vec![];
    for p in pins {
        let (v, n) = (Int::new_const(p.var.as_str()), Int::from_u64(p.rows));
        let (claim, source, op) = if p.floor { (v.ge(&n), "observed floor", ">=") } else { (v.eq(&n), "observed rows", "=") };
        a.assert_untraced(claim.clone());
        let fact = FactRef { text: format!("|{}#{} {}|", p.plan, p.op, p.engine_op), origins: vec![format!("{}#{}", p.plan, p.op)] };
        out.push(FactClaim {
            claim,
            node: Some(p.node),
            info: FactInfo { source: source.to_string(), facts: vec![fact], value: format!("{op} {}", p.rows) },
            at: Location::caller(),
        });
    }
    out
}

/// The variables the reduction keeps: those that may be read once the
/// analysis is made, the query's (the first `own_vars`), and the tables'
/// sizes, which the `referenced size` rule may have made after the
/// query's visit.
pub(crate) fn kept(a: &Analyzer, own_vars: usize) -> Vec<String> {
    a.vars[..own_vars]
        .iter()
        .map(|(n, _)| n.clone())
        .chain(a.tables.values().map(|t| t.symbol.clone()))
        .collect()
}

/// The SMT-LIB `script` reduced (see the [spec](self#spec)): `solve-eqs`
/// keeping the variables `kept` names, then each assertion kept once.
/// Returns the reduced script and how many assertions it holds.
pub(crate) fn reduce(script: &str, kept: &[String]) -> (String, usize) {
    let parsed = Solver::new();
    parsed.from_string(script);
    let kept: Vec<Int> = kept.iter().map(|v| Int::new_const(v.as_str())).collect();
    // Substituted, a plan's copy of an operator the query has (a table's
    // scan, most often) asserts what the query's does: each assertion
    // once, the first kept in place.
    let solver = Solver::new();
    let mut seen = HashSet::new();
    for f in solve_eqs(&parsed.get_assertions(), &kept) {
        if seen.insert(f.clone()) {
            solver.assert(&f);
        }
    }
    (solver.to_string(), solver.get_assertions().len())
}

/// Each analyzer node of `nodes` an operator of `plan` became, by `built`
/// (each operator and the subplans it became), with the operator and
/// whether its count is only a floor for the node's rows.
///
/// An operator counts if the engine counted it and it did not stop early.
/// Its count is the node's rows if no runtime or optional filter pruned at
/// or below it (the translation leaves both out), or its state is clean; a
/// floor if only runtime filters did ([`State::lower`]).
fn counts(plan: &ObservedPlan, nodes: &[Node], built: &[(usize, LogicalPlan)]) -> Vec<(usize, usize, bool)> {
    let states = states(plan);
    let stopped = stopped(plan);
    let mut pruned = vec![false; plan.nodes.len()];
    for (j, n) in plan.nodes.iter().enumerate() {
        let own = match &n.op {
            Op::Scan { runtime_filters, filters, .. } => !runtime_filters.is_empty() || filters.iter().any(|f| f.optional),
            _ => false,
        };
        pruned[j] = own || n.children.iter().any(|&c| pruned[c]);
    }
    let mut by_plan: HashMap<&LogicalPlan, Vec<usize>> = HashMap::new();
    for (j, p) in built {
        by_plan.entry(p).or_default().push(*j);
    }
    let mut out = vec![];
    let mut done = BTreeSet::new();
    for (m, node) in nodes.iter().enumerate() {
        for &j in by_plan.get(&node.plan).into_iter().flatten() {
            if !plan.nodes[j].counted || stopped[j] || !done.insert((m, j)) {
                continue;
            }
            let floor = match &states[j] {
                _ if !pruned[j] => false,
                State::Clean(_) => false,
                s if s.lower().is_some() => true,
                _ => continue,
            };
            out.push((m, j, floor));
        }
    }
    out
}

/// `assertions` with Z3's `solve-eqs` applied: each variable but `kept`
/// that an assertion defines as a term of others (`y = t`, `y` not in
/// `t`) is replaced by that term, and the definition dropped.
///
/// Lossless on `kept`: the result admits exactly the values of `kept`
/// that `assertions` admit, since each such value extends to the
/// eliminated variables by their definitions. `solve-eqs` eliminates only
/// constants, so each kept variable is a function's application while it
/// runs. If it fails, `assertions` are returned as they are.
fn solve_eqs(assertions: &[Bool], kept: &[Int]) -> Vec<Bool> {
    if assertions.is_empty() {
        return vec![];
    }
    let hidden: Vec<Int> = kept
        .iter()
        .map(|v| {
            let f = FuncDecl::new(format!("{v}!kept"), &[&Sort::int()], &Sort::int());
            f.apply(&[&Int::from_i64(0)]).as_int().expect("an Int function")
        })
        .collect();
    let hide: Vec<(&Int, &Int)> = kept.iter().zip(&hidden).collect();
    let show: Vec<(&Int, &Int)> = hidden.iter().zip(kept).collect();
    // One conjunction, so each substitution is one pass.
    let goal = Goal::new(true, false, false);
    goal.assert(&Bool::and(assertions).substitute(&hide));
    let Ok(result) = Tactic::new("solve-eqs").apply(&goal, None) else {
        return assertions.to_vec();
    };
    let goals: Vec<Goal> = result.list_subgoals().collect();
    let [goal] = &goals[..] else {
        return assertions.to_vec();
    };
    match &goal.get_formulas()[..] {
        [] => vec![],
        [f] => vec![f.substitute(&show)],
        fs => {
            let back: Vec<Bool> = Bool::and(fs).substitute(&show).children().iter().filter_map(|f| f.as_bool()).collect();
            match back.len() == fs.len() {
                true => back,
                false => fs.iter().map(|f| f.substitute(&show)).collect(),
            }
        }
    }
}

/// The base tables `plan` scans, subqueries included.
fn tables_of(plan: &LogicalPlan) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let _ = plan.apply_with_subqueries(|p| {
        if let LogicalPlan::TableScan(s) = p {
            out.insert(s.table_name.table().to_string());
        }
        Ok(TreeNodeRecursion::Continue)
    });
    out
}

/// `tables`, and every table one of them references by a foreign key,
/// transitively.
fn reachable(tables: &BTreeSet<String>, options: &Options) -> BTreeSet<String> {
    let mut out = tables.clone();
    loop {
        let more: Vec<String> = options
            .foreign_keys
            .iter()
            .filter(|fk| out.contains(&fk.table) && !out.contains(&fk.references))
            .map(|fk| fk.references.clone())
            .collect();
        if more.is_empty() {
            return out;
        }
        out.extend(more);
    }
}

/// Into `out`: the maximal subtrees of `plan` that scan only tables of
/// `within` (and some). Going up a plan, the tables scanned only grow, so
/// a subtree's are within if its parent's are.
fn maximal<'p>(plan: &'p LogicalPlan, within: &BTreeSet<String>, out: &mut Vec<&'p LogicalPlan>) {
    let l = tables_of(plan);
    if !l.is_empty() && l.is_subset(within) {
        out.push(plan);
        return;
    }
    for c in plan.inputs() {
        maximal(c, within, out);
    }
}
