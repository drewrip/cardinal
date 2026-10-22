//! A dump as text: the plan tree with each node's constraints under it, then
//! each proof and the constraints it needs, and with facts, which were used
//! and which not.

use std::collections::BTreeSet;
use std::fmt::Write;

use cardinal::{Constraint, Proof, ProofStatus, Trace};

use crate::{Dump, FactsDump, readable, roots};

/// What to show.
#[derive(Debug, Clone, Default)]
pub struct View {
    /// Only the constraints of this proof, by name, with its nodes marked.
    pub proof: Option<String>,
    /// Only this node's constraints, in full.
    pub node: Option<usize>,
    /// Hide constraints in the tree; show how many each node has.
    pub brief: bool,
    /// Show the analysis without its facts, as if none were given.
    pub without_facts: bool,
}

pub fn render(dump: &Dump, view: &View) -> Result<String, String> {
    let facts = dump.facts.as_ref().filter(|_| !view.without_facts);
    let t = facts.map_or(&dump.trace, |f| &f.trace);
    // Without the proofs with facts, the base ones: their constraints come
    // first in the trace with facts too.
    let proofs: &[Proof] = match facts {
        Some(f) if f.explained => &f.proofs,
        _ => &dump.proofs,
    };
    let mut out = String::new();
    let w = &mut out;
    let _ = writeln!(w, "Query:   {}", dump.query.trim());
    let _ = writeln!(w, "Verdict: {}", dump.verdict);
    if let Some(b) = &dump.bounds {
        let _ = writeln!(w, "Bounds:  {b}");
    }
    if let Some(f) = facts {
        let n = t.constraints.iter().filter(|c| c.fact.is_some()).count();
        let _ = writeln!(w, "With facts: {}", f.bounds.as_deref().unwrap_or("not computed"));
        let _ = writeln!(w, "Facts:   {}, {n} fact constraints, X = {}", f.mode, f.report.output);
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
            detail(w, t, c);
        }
        return Ok(out);
    }

    let proof = match &view.proof {
        Some(name) => Some(proofs.iter().find(|p| p.name == *name).ok_or_else(|| {
            let names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
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
        tree(w, t, facts, r, "", true, &marked, &shown, view.brief);
    }
    let partitions: Vec<&Constraint> = t.constraints.iter().filter(|c| c.node.is_none() && shown(c)).collect();
    if !partitions.is_empty() {
        let _ = writeln!(w, "\nPartitions (over several relations of a table):");
        for c in partitions {
            line(w, t, c, "  ");
        }
    }
    if proof.is_none()
        && let Some(f) = facts.filter(|f| f.explained)
    {
        let _ = writeln!(w, "\nProofs (without facts / with facts):");
        for (i, p) in f.proofs.iter().enumerate() {
            let without = f.base_proofs.get(i).map_or("—".to_string(), needs);
            let k = p.core.iter().filter(|&&c| t.constraints[c].fact.is_some()).count();
            let with = match p.status {
                ProofStatus::Proven => format!("{} ({k} fact{})", needs(p), if k == 1 { "" } else { "s" }),
                _ => needs(p),
            };
            let _ = writeln!(w, "  {:<16} {:<24} {:<26} {}", p.name, p.claim, without, with);
        }
        let _ = writeln!(w, "  (--proof NAME shows one proof's constraints; --without-facts the analysis without facts)");
    } else if proof.is_none() {
        let _ = writeln!(w, "\nProofs:");
        if facts.is_some() {
            let _ = writeln!(w, "  (without facts: the proofs with facts were skipped)");
        }
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
    if let Some(f) = facts {
        facts_sections(w, f);
    }
    if let Some(ce) = &dump.counterexample {
        let _ = writeln!(w, "\nCounterexample:");
        for (k, v) in ce {
            let _ = writeln!(w, "  {k:<28} {v}");
        }
    }
    Ok(out)
}

/// A proof's status and how many constraints it needs, e.g. `proven, 4 needed`.
fn needs(p: &Proof) -> String {
    match p.status {
        ProofStatus::Proven => format!("proven, {} needed", p.core.len()),
        _ => status(&p.status),
    }
}

/// Which facts were used, which not and why, and which conflict.
fn facts_sections(w: &mut String, f: &FactsDump) {
    let r = &f.report;
    let _ = writeln!(w, "\nFacts used:");
    for m in &r.matched {
        let from: Vec<String> = m
            .facts
            .iter()
            .map(|x| match x.origins.is_empty() {
                true => x.text.clone(),
                false => format!("{} [{}]", x.text, x.origins.join(", ")),
            })
            .collect();
        let _ = writeln!(w, "  {:<6} = {:<12} from {}", m.name, m.value, from.join(", "));
    }
    let counts = [("pinned", r.pinned.len()), ("capped", r.capped.len()), ("ndv", r.pinned_ndv.len()), ("floors", r.floors.len())];
    let counts: Vec<String> = counts.iter().filter(|(_, n)| *n > 0).map(|(k, n)| format!("{n} {k}")).collect();
    if !counts.is_empty() {
        let _ = writeln!(w, "  row counts: {} (marked ◆ in the tree)", counts.join(", "));
    }
    let _ = writeln!(w, "\nFacts not used:");
    if r.rejected.is_empty() && r.unchecked.is_empty() && r.unmatched.is_empty() {
        let _ = writeln!(w, "  (none)");
    }
    for (s, why) in &r.rejected {
        let _ = writeln!(w, "  rejected   {s}: {why}");
    }
    for s in &r.unchecked {
        let _ = writeln!(w, "  unchecked  {s}: not decided in time");
    }
    for (s, why) in &r.unmatched {
        let _ = writeln!(w, "  unmatched  {s}: {why}");
    }
    if !f.conflicts.is_empty() {
        let _ = writeln!(w, "\nConflicts (left out):");
        for c in &f.conflicts {
            let _ = writeln!(w, "  {c}");
        }
    }
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
    t: &Trace,
    facts: Option<&FactsDump>,
    id: usize,
    prefix: &str,
    last: bool,
    marked: &BTreeSet<usize>,
    shown: &dyn Fn(&Constraint) -> bool,
    brief: bool,
) {
    let n = &t.nodes[id];
    let branch = if prefix.is_empty() { "" } else if last { "└─ " } else { "├─ " };
    let mut mark = if marked.contains(&id) { "● " } else { "" }.to_string();
    if t.of_node(id).any(|c| c.fact.is_some()) {
        mark.push_str("◆ ");
    }
    let label = n.label.lines().next().unwrap_or("");
    let constraints: Vec<&Constraint> = t.of_node(id).filter(|c| shown(c)).collect();
    let count = if brief { format!("  ({} constraints)", constraints.len()) } else { String::new() };
    let _ = writeln!(w, "{prefix}{branch}{mark}[{id}] {label}   {}{}{count}", n.var, values(n, facts));
    let child_prefix = if prefix.is_empty() {
        "   ".to_string()
    } else {
        format!("{prefix}{}", if last { "   " } else { "│  " })
    };
    if !brief {
        let bar = if n.inputs.is_empty() { "   " } else { "│  " };
        for c in constraints {
            line(w, t, c, &format!("{child_prefix}{bar}"));
        }
    }
    for (i, &input) in n.inputs.iter().enumerate() {
        tree(w, t, facts, input, &child_prefix, i + 1 == n.inputs.len(), marked, shown, brief);
    }
}

/// The row counts facts pin or cap node `n`'s variables to, e.g.
/// `  = 6001215`.
fn values(n: &cardinal::TraceNode, facts: Option<&FactsDump>) -> String {
    let Some(f) = facts else { return String::new() };
    let vars: Vec<&str> = std::iter::once(n.var.as_str()).chain(n.raw_var.as_deref()).collect();
    let mut out = String::new();
    for (list, op) in [(&f.report.pinned, "="), (&f.report.capped, "<=")] {
        for (v, k) in list.iter().filter(|(v, _)| vars.contains(&v.as_str())) {
            let _ = write!(out, "  {v} {op} {k}");
        }
    }
    out
}

/// One constraint on a line: id, formula, and the rule that made it, or
/// for a fact's, the facts it is read from.
fn line(w: &mut String, t: &Trace, c: &Constraint, prefix: &str) {
    let formula = readable(t, &c.infix);
    let from = match &c.fact {
        Some(_) => c.code.clone(),
        None => c.source.rsplit('/').next().unwrap_or(&c.source).to_string(),
    };
    let _ = writeln!(w, "{prefix}c{:<4} {formula:<48}  {} {from}", c.id, c.function);
}

fn detail(w: &mut String, t: &Trace, c: &Constraint) {
    let _ = writeln!(w, "\n  c{}  {}", c.id, readable(t, &c.infix));
    let _ = writeln!(w, "      smt:  {}", c.smt.split_whitespace().collect::<Vec<_>>().join(" "));
    let _ = writeln!(w, "      rule: {} at {}", c.function, c.source);
    let _ = writeln!(w, "            {}", c.code);
    if let Some(f) = &c.fact {
        for x in &f.facts {
            let _ = writeln!(w, "      fact: {}  {}", x.text, x.origins.join(", "));
        }
    }
}
