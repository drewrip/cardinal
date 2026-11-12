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
//!                   ├─ rules ─ axioms ─ pins ─▶ Analysis
//!  profiles ─ select┘                 X = rows
//! ```
//!
//! # Spec
//!
//! - **Input**: the query's plan, executed plans of other queries over the
//!   same data (their counts read as [`observe`](crate::facts::observe)
//!   reads a translated plan's), and the options.
//! - **Output**: an [`Analysis`] of the query, without a trace.
//! - **Selection**: of each profile, the maximal subtrees that scan only
//!   tables the query scans (`maximal`), and its unfiltered scans of the
//!   tables those reference by foreign keys, transitively: those pin the
//!   tables' sizes, which the `referenced size` axiom
//!   ([`Analyzer::referenced_size`]) bounds the referencing columns'
//!   distinct counts by. Other subtrees share no context with the query's.
//! - **Not done**: no check that the pins are consistent with the
//!   constraints. Facts of other data, or a wrong rule, make the set
//!   unsatisfiable, and an unsatisfiable set proves any bound.
//!   Slower than [`Analysis::with_facts`](crate::Analysis::with_facts):
//!   the 46 DuckDB fixtures take about 8× as long in all.

use std::collections::BTreeSet;

use datafusion::common::tree_node::TreeNodeRecursion;
use datafusion::logical_expr::LogicalPlan;
use datafusion::logical_expr::logical_plan::TableScan;
use z3::ast::Int;

use crate::analysis::{Analyzer, ranged_columns};
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
    let (own, own_scans) = (a.nodes.len(), a.scans.len());

    let tables = tables_of(&query);
    let referenced: BTreeSet<String> = reachable(&tables, &options)
        .difference(&tables)
        .cloned()
        .collect();
    let mut pins = vec![];
    for (p, (root, built)) in &translated {
        let mut parts = vec![];
        maximal(root, &tables, &referenced, &mut parts);
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
        a.solver.assert(&if floor { v.ge(&n) } else { v.eq(&n) });
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
        constraints: a.solver.to_string(),
        assertions: a.solver.get_assertions().len(),
        nodes,
        check_facts: options.check_facts,
    })
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
/// `within` (and some), and its unfiltered scans of a table of `bare`.
/// Going up a plan, the tables scanned only grow, so a subtree's are
/// within if its parent's are.
fn maximal<'p>(
    plan: &'p LogicalPlan,
    within: &BTreeSet<String>,
    bare: &BTreeSet<String>,
    out: &mut Vec<&'p LogicalPlan>,
) {
    // Translated, a scan is aliased by its instance.
    let scan = match plan {
        LogicalPlan::SubqueryAlias(a) => a.input.as_ref(),
        p => p,
    };
    if let LogicalPlan::TableScan(s) = scan
        && s.filters.is_empty()
        && bare.contains(s.table_name.table())
    {
        out.push(plan);
        return;
    }
    let l = tables_of(plan);
    if !l.is_empty() && l.is_subset(within) {
        out.push(plan);
        return;
    }
    for c in plan.inputs() {
        maximal(c, within, bare, out);
    }
}
