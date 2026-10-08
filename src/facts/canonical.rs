//! Facts written the same whichever plan they came from.
//!
//! Plans name table instances by operator (`lineitem#7`), so the same rows
//! read in two plans would differ by name. A fact's instances are renamed:
//! a table's only instance to the table's name, and several instances of one
//! table to `lineitem@1`, `lineitem@2`, ..., in the order that makes the fact
//! least. Any renaming of instances of one table keeps a fact's meaning, so
//! the least is a canonical form.

use std::collections::{BTreeMap, HashMap};

use super::{Context, FactKind, Term};
use crate::observed::base_table;

/// More orders than this are not tried: instances are then numbered as they
/// first appear, which is deterministic but may keep equal facts apart.
const MAX_ORDERS: usize = 5040;

impl FactKind {
    /// This fact with its table instances canonically renamed.
    pub fn canonical(&self) -> FactKind {
        let instances = self.instances();
        let mut groups: BTreeMap<&str, Vec<&String>> = BTreeMap::new();
        for i in &instances {
            groups.entry(base_table(i).unwrap()).or_default().push(i);
        }
        let groups: Vec<(&str, Vec<&String>)> = groups.into_iter().collect();
        let orders = groups.iter().try_fold(1usize, |n, (_, g)| (1..=g.len()).try_fold(n, |n, k| n.checked_mul(k)));
        if orders.is_none_or(|n| n > MAX_ORDERS) {
            let names = groups.iter().map(|(_, g)| g.clone()).collect::<Vec<_>>();
            return self.rename(&labels(&groups, &names));
        }
        let mut best: Option<FactKind> = None;
        let mut choice = vec![];
        each_order(&groups, 0, &mut choice, &mut |order| {
            let candidate = self.rename(&labels(&groups, order));
            if best.as_ref().is_none_or(|b| candidate < *b) {
                best = Some(candidate);
            }
        });
        best.unwrap_or_else(|| self.clone())
    }

    fn rename(&self, names: &HashMap<String, String>) -> FactKind {
        let f = |r: &str| names.get(r).cloned();
        let terms = |s: &std::collections::BTreeSet<Term>| s.iter().map(|t| t.rename(&f)).collect();
        match self {
            FactKind::Cardinality(c) => FactKind::Cardinality(c.rename(&f)),
            FactKind::Selectivity { pred, over } => FactKind::Selectivity { pred: terms(pred), over: over.rename(&f) },
            FactKind::Match { on, kept, other } => {
                FactKind::Match { on: terms(on), kept: kept.rename(&f), other: other.rename(&f) }
            }
            FactKind::Distinct { keys, over } => FactKind::Distinct { keys: terms(keys), over: over.rename(&f) },
            FactKind::Unique { keys, over } => FactKind::Unique { keys: terms(keys), over: over.rename(&f) },
        }
    }

    /// Every table instance named, in order of first appearance.
    fn instances(&self) -> Vec<String> {
        let mut out = vec![];
        let terms = |ts: &mut dyn Iterator<Item = &Term>, out: &mut Vec<String>| {
            for t in ts {
                term_instances(t, out);
            }
        };
        match self {
            FactKind::Cardinality(c) => context_instances(c, &mut out),
            FactKind::Selectivity { pred, over } => {
                context_instances(over, &mut out);
                terms(&mut pred.iter(), &mut out);
            }
            FactKind::Match { on, kept, other } => {
                context_instances(kept, &mut out);
                context_instances(other, &mut out);
                terms(&mut on.iter(), &mut out);
            }
            FactKind::Distinct { keys, over } | FactKind::Unique { keys, over } => {
                context_instances(over, &mut out);
                terms(&mut keys.iter(), &mut out);
            }
        }
        out
    }

    /// A query counting what this fact counts, if it is the size of, or the
    /// distinct keys in, a context over base tables, to check it against
    /// the engine.
    pub fn count_sql(&self) -> Option<String> {
        let (keys, over) = match self {
            FactKind::Cardinality(c) => (None, c),
            FactKind::Distinct { keys, over } => (Some(keys), over),
            _ => return None,
        };
        let Context::Spj { tables, preds } = over else { return None };
        let opaque = |t: &Term| t.expr.column_refs().iter().any(|c| c.relation.as_ref().is_some_and(|r| r.table() == "value"));
        if preds.iter().chain(keys.into_iter().flatten()).any(opaque) {
            return None;
        }
        let from = tables
            .iter()
            .map(|t| format!("{} AS \"{t}\"", t.split('@').next().unwrap()))
            .collect::<Vec<_>>()
            .join(", ");
        let filter = match preds.is_empty() {
            true => String::new(),
            false => format!(" WHERE {}", preds.iter().map(|p| format!("({p})")).collect::<Vec<_>>().join(" AND ")),
        };
        Some(match keys {
            None => format!("SELECT count(*) FROM {from}{filter}"),
            Some(keys) => {
                let keys = keys.iter().map(ToString::to_string).collect::<Vec<_>>().join(", ");
                format!("SELECT count(*) FROM (SELECT DISTINCT {keys} FROM {from}{filter})")
            }
        })
    }
}

impl Context {
    /// This context with its table instances canonically renamed.
    pub fn canonical(&self) -> Context {
        match FactKind::Cardinality(self.clone()).canonical() {
            FactKind::Cardinality(c) => c,
            _ => unreachable!(),
        }
    }
}

fn context_instances(c: &Context, out: &mut Vec<String>) {
    match c {
        Context::Spj { tables, preds } => {
            for t in tables {
                push(t, out);
            }
            for p in preds {
                term_instances(p, out);
            }
        }
        Context::Derived { args, inputs, .. } => {
            for i in inputs {
                context_instances(i, out);
            }
            for a in args {
                term_instances(a, out);
            }
        }
    }
}

fn term_instances(t: &Term, out: &mut Vec<String>) {
    for c in t.expr.column_refs() {
        if let Some(r) = c.relation.as_ref() {
            push(r.table(), out);
        }
    }
}

fn push(r: &str, out: &mut Vec<String>) {
    if base_table(r).is_some() && !out.iter().any(|o| o == r) {
        out.push(r.to_string());
    }
}

/// Instance names: the table's for its only instance, else numbered in the
/// order given for each table.
fn labels(groups: &[(&str, Vec<&String>)], order: &[Vec<&String>]) -> HashMap<String, String> {
    let mut out = HashMap::new();
    for ((table, _), order) in groups.iter().zip(order) {
        for (k, i) in order.iter().enumerate() {
            let label = if order.len() == 1 { table.to_string() } else { format!("{table}@{}", k + 1) };
            out.insert((*i).clone(), label);
        }
    }
    out
}

/// Calls `f` with every choice of an order for each group's instances.
fn each_order<'a>(
    groups: &[(&str, Vec<&'a String>)],
    at: usize,
    choice: &mut Vec<Vec<&'a String>>,
    f: &mut dyn FnMut(&[Vec<&'a String>]),
) {
    if at == groups.len() {
        f(choice);
        return;
    }
    for p in permutations(&groups[at].1) {
        choice.push(p);
        each_order(groups, at + 1, choice, f);
        choice.pop();
    }
}

fn permutations<'a>(items: &[&'a String]) -> Vec<Vec<&'a String>> {
    if items.len() <= 1 {
        return vec![items.to_vec()];
    }
    let mut out = vec![];
    for i in 0..items.len() {
        let mut rest = items.to_vec();
        let first = rest.remove(i);
        for mut p in permutations(&rest) {
            p.insert(0, first);
            out.push(p);
        }
    }
    out
}
