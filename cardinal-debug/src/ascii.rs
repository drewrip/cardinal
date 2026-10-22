//! A dump as text: the plan tree with each node's constraints under it, then
//! each proof and the constraints it needs.

use std::collections::BTreeSet;
use std::fmt::Write;

use cardinal::{Constraint, ProofStatus};

use crate::{Dump, readable, roots};

/// What to show.
#[derive(Debug, Clone, Default)]
pub struct View {
    /// Only the constraints of this proof, by name, with its nodes marked.
    pub proof: Option<String>,
    /// Only this node's constraints, in full.
    pub node: Option<usize>,
    /// Hide constraints in the tree; show how many each node has.
    pub brief: bool,
}

pub fn render(dump: &Dump, view: &View) -> Result<String, String> {
    let t = &dump.trace;
    let mut out = String::new();
    let w = &mut out;
    let _ = writeln!(w, "Query:   {}", dump.query.trim());
    let _ = writeln!(w, "Verdict: {}", dump.verdict);
    if let Some(b) = &dump.bounds {
        let _ = writeln!(w, "Bounds:  {b}");
    }
    let _ = writeln!(w, "Root:    {}   ({} nodes, {} constraints)", t.root, t.nodes.len(), t.constraints.len());

    if let Some(id) = view.node {
        let n = t.nodes.get(id).ok_or_else(|| format!("no node {id}: there are {}", t.nodes.len()))?;
        let _ = writeln!(w, "\nNode [{id}] {}", n.label.replace('\n', " "));
        let _ = writeln!(w, "  rows: {}{}", n.var, n.raw_var.as_ref().map(|r| format!("   unfiltered scan: {r}")).unwrap_or_default());
        for (col, var) in &n.columns {
            let _ = writeln!(w, "  ndv:  {var:<24} {col}");
        }
        let _ = writeln!(w, "  inputs: {:?}", n.inputs);
        for c in t.of_node(id) {
            detail(w, dump, c);
        }
        return Ok(out);
    }

    let proof = match &view.proof {
        Some(name) => Some(dump.proofs.iter().find(|p| p.name == *name).ok_or_else(|| {
            let names: Vec<&str> = dump.proofs.iter().map(|p| p.name.as_str()).collect();
            format!("no proof {name:?}; there are: {}", names.join(", "))
        })?),
        None => None,
    };
    let core: Option<BTreeSet<usize>> = proof.map(|p| p.core.iter().copied().collect());
    let marked: BTreeSet<usize> = core
        .iter()
        .flatten()
        .filter_map(|&c| t.constraints[c].node)
        .collect();
    let shown = |c: &Constraint| core.as_ref().is_none_or(|k| k.contains(&c.id));

    if let Some(p) = proof {
        let _ = writeln!(w, "\nProof {}: {}  [{}]  {} constraints", p.name, p.claim, status(&p.status), p.core.len());
    }
    let _ = writeln!(w, "\nPlan and constraints:");
    let rs = roots(t);
    for (i, &r) in rs.iter().enumerate() {
        if i + 1 < rs.len() {
            let _ = writeln!(w, "(subquery)");
        }
        tree(w, dump, r, "", true, &marked, &shown, view.brief);
    }
    let partitions: Vec<&Constraint> = t.constraints.iter().filter(|c| c.node.is_none() && shown(c)).collect();
    if !partitions.is_empty() {
        let _ = writeln!(w, "\nPartitions (over several relations of a table):");
        for c in partitions {
            line(w, dump, c, "  ");
        }
    }
    if proof.is_none() {
        let _ = writeln!(w, "\nProofs:");
        for p in &dump.proofs {
            let mut nodes: Vec<usize> = p.core.iter().filter_map(|&c| t.constraints[c].node).collect();
            nodes.sort();
            nodes.dedup();
            let _ = writeln!(
                w,
                "  {:<8} {:<16} {:<24} {:>3} constraints, nodes {:?}",
                status(&p.status),
                p.name,
                p.claim,
                p.core.len(),
                nodes
            );
        }
        let _ = writeln!(w, "  (--proof NAME shows one proof's constraints)");
    }
    if let Some(ce) = &dump.counterexample {
        let _ = writeln!(w, "\nCounterexample:");
        for (k, v) in ce {
            let _ = writeln!(w, "  {k:<28} {v}");
        }
    }
    Ok(out)
}

fn status(s: &ProofStatus) -> String {
    match s {
        ProofStatus::Proven => "proven".into(),
        ProofStatus::Refuted => "refuted".into(),
        ProofStatus::Unknown(r) => format!("unknown ({r})"),
    }
}

#[allow(clippy::too_many_arguments)]
fn tree(
    w: &mut String,
    dump: &Dump,
    id: usize,
    prefix: &str,
    last: bool,
    marked: &BTreeSet<usize>,
    shown: &dyn Fn(&Constraint) -> bool,
    brief: bool,
) {
    let t = &dump.trace;
    let n = &t.nodes[id];
    let branch = if prefix.is_empty() { "" } else if last { "└─ " } else { "├─ " };
    let mark = if marked.contains(&id) { "● " } else { "" };
    let label = n.label.lines().next().unwrap_or("");
    let constraints: Vec<&Constraint> = t.of_node(id).filter(|c| shown(c)).collect();
    let count = if brief { format!("  ({} constraints)", constraints.len()) } else { String::new() };
    let _ = writeln!(w, "{prefix}{branch}{mark}[{id}] {label}   {}{count}", n.var);
    let child_prefix = if prefix.is_empty() {
        "   ".to_string()
    } else {
        format!("{prefix}{}", if last { "   " } else { "│  " })
    };
    if !brief {
        let bar = if n.inputs.is_empty() { "   " } else { "│  " };
        for c in constraints {
            line(w, dump, c, &format!("{child_prefix}{bar}"));
        }
    }
    for (i, &input) in n.inputs.iter().enumerate() {
        tree(w, dump, input, &child_prefix, i + 1 == n.inputs.len(), marked, shown, brief);
    }
}

/// One constraint on a line: id, formula, and the rule that made it.
fn line(w: &mut String, dump: &Dump, c: &Constraint, prefix: &str) {
    let formula = readable(&dump.trace, &c.infix);
    let file = c.source.rsplit('/').next().unwrap_or(&c.source);
    let _ = writeln!(w, "{prefix}c{:<4} {formula:<48}  {} {file}", c.id, c.function);
}

fn detail(w: &mut String, dump: &Dump, c: &Constraint) {
    let _ = writeln!(w, "\n  c{}  {}", c.id, readable(&dump.trace, &c.infix));
    let _ = writeln!(w, "      smt:  {}", c.smt.split_whitespace().collect::<Vec<_>>().join(" "));
    let _ = writeln!(w, "      rule: {} at {}", c.function, c.source);
    let _ = writeln!(w, "            {}", c.code);
}
