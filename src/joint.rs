//! Facts as plans: a query analyzed together with the executed plans of
//! other queries, each counted operator pinned to its rows.
//!
//! An alternative to [`Analysis::with_facts`](crate::Analysis::with_facts),
//! and an experiment. No rules read facts off the plans, combine them, or
//! match them to the query's operators: the profiles' operators get the
//! constraints any operator does, the axioms between contexts
//! ([`crate::axioms`]) relate them to the query's, and Z3 finds what
//! follows.
//!
//! ```text
//!  query ───────────┐
//!                   ├─ rules ─ axioms ─ pins ─ dead columns ─ solve-eqs ─ dedup ─▶ Analysis
//!  profiles ─ select┘                 X = rows  (if asked)
//! ```
//!
//! # Spec
//!
//! - **Input**: the query's plan, executed plans of other queries over the
//!   same data (their counts read as [`observe`](crate::facts::observe)
//!   reads a translated plan's), and the options.
//! - **Output**: an [`Analysis`] of the query, without a trace.
//! - **Selection**: of each profile, the maximal subtrees that scan only
//!   tables the query scans or those reference by foreign keys,
//!   transitively (`maximal`). Subtrees over a referenced table bound its
//!   size, which the `referenced size` axiom
//!   ([`Analyzer::referenced_size`]) bounds the referencing columns'
//!   distinct counts by. Other subtrees share no context with the query's.
//! - **Reduction**: if [`Options::postprocess`] asks, the assertions over
//!   dead columns are left out first ([`crate::postprocess`]), the pins
//!   counting as [`Role::Gen`]. Then each variable of the profiles' or the axioms' that an
//!   assertion defines by others is substituted away (Z3's `solve-eqs`),
//!   and the assertions that then repeat are kept once. The query's
//!   variables and the tables' sizes all stay, with exactly the values
//!   they had, so every bound and claim on them is as before.
//! - **Not done**: no check that the pins are consistent with the
//!   constraints. Facts of other data, or a wrong rule, make the set
//!   unsatisfiable, and an unsatisfiable set proves any bound.
//!   Slower than [`Analysis::with_facts`](crate::Analysis::with_facts):
//!   the 46 DuckDB fixtures take about 11× as long in all, nearly all of
//!   it proving the bounds.

use std::collections::{BTreeSet, HashSet};

use datafusion::common::tree_node::TreeNodeRecursion;
use datafusion::logical_expr::LogicalPlan;
use datafusion::logical_expr::logical_plan::TableScan;
use z3::ast::{Ast, Bool, Int};
use z3::{FuncDecl, Goal, Solver, Sort, Tactic};

use crate::analysis::{Analyzer, ranged_columns};
use crate::postprocess::{self, Role};
use crate::observed::{Catalog, ObservedPlan};
use crate::{Analysis, Options, Result, axioms, base_kind};

/// `plan` analyzed together with the parts of `profiles` it could share
/// rows with, each of their counted operators pinned to its rows (or, a
/// runtime filter pruned its rows, bounded below by them).
///
/// The profiles must have run on the data the bounds are for. Plans that
/// were not run, or do not translate, are left out.
pub fn analyze_joint(
    catalog: &Catalog,
    plan: &ObservedPlan,
    profiles: &[ObservedPlan],
    options: Options,
) -> Result<Analysis> {
    let query = catalog.to_logical(plan)?;
    let translated: Vec<_> = profiles
        .iter()
        .filter(|p| p.counted)
        .filter_map(|p| Some((p, catalog.to_logical_mapped(p).ok()?)))
        .collect();
    let resolve = |scan: &TableScan| base_kind(&scan.table_name, "datafusion", "public");
    let mut a = Analyzer::new(&resolve, options.max_product, &options.foreign_keys, false)
        .with_ranges(&query);
    a.referenced_sizes = true;
    for (_, (root, _)) in &translated {
        a.ranged.extend(ranged_columns(root));
    }
    let root = a.visit(&query).card;
    let (own, own_scans, own_vars) = (a.nodes.len(), a.scans.len(), a.vars.len());

    let tables = tables_of(&query);
    let within = reachable(&tables, &options);
    let mut pins = vec![];
    for (p, (root, built)) in &translated {
        let mut parts = vec![];
        maximal(root, &within, &mut parts);
        for t in parts {
            let start = a.nodes.len();
            a.visit(t);
            for (m, j, floor) in crate::facts::observe::counts(p, &a.nodes[start..], built) {
                pins.push((a.nodes[start + m].var.clone(), p.nodes[j].rows, floor));
            }
        }
    }
    axioms::assert_all(&mut a);
    for (var, rows, floor) in pins {
        let (v, n) = (Int::new_const(var.as_str()), Int::from_u64(rows));
        a.assert_as(Role::Gen, if floor { v.ge(&n) } else { v.eq(&n) });
    }
    let mut assertions = a.solver.get_assertions();
    if options.postprocess.dead_columns {
        let kept = postprocess::Assertions::new(&a, &a.solver.to_string()).kept();
        assertions = assertions.into_iter().zip(kept).filter_map(|(b, k)| k.then_some(b)).collect();
    }
    // What may be read once the analysis is made: the query's variables,
    // and the tables' sizes, which the referenced-size axiom may have
    // made after the query's visit.
    let kept: Vec<Int> = a.vars[..own_vars]
        .iter()
        .map(|(_, v)| v.clone())
        .chain(a.tables.values().map(|t| t.var.clone()))
        .collect();
    // Substituted, a profile's copy of an operator the query has (a
    // table's scan, most often) asserts what the query's does: each
    // assertion once, the first kept in place.
    let solver = Solver::new();
    let mut seen = HashSet::new();
    for f in solve_eqs(&assertions, &kept) {
        if seen.insert(f.clone()) {
            solver.assert(&f);
        }
    }

    let root = a.name_of(&root);
    let scans = a.scans[..own_scans]
        .iter()
        .map(|(s, t, _)| (s.clone(), t.clone()))
        .collect();
    let mut nodes = a.nodes;
    nodes.truncate(own);
    Ok(Analysis {
        root,
        scans,
        plan: query.display_indent().to_string(),
        trace: None,
        constraints: solver.to_string(),
        assertions: solver.get_assertions().len(),
        nodes,
        check_facts: options.check_facts,
        postprocess: options.postprocess.clone(),
        // `solve-eqs` rewrote the assertions: their roles no longer apply.
        parts: None,
    })
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
