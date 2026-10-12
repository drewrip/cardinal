//! Facts written the same whichever plan they came from.
//!
//! Plans name table instances by operator (`lineitem#7`), so the same rows
//! read in two plans would differ by name. A fact's instances are renamed:
//! a table's only instance to the table's name, and several instances of one
//! table to `lineitem@1`, `lineitem@2`, ..., in the order that makes the fact
//! least. Any renaming of instances of one table keeps a fact's meaning, so
//! the least is a canonical form.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use super::{Context, Exists, ExistsKind, FactKind, Term, rewrite};
use crate::observed::base_table;

/// More orders than this are not tried: instances are then numbered as they
/// first appear, which is deterministic but may keep equal facts apart.
const MAX_ORDERS: usize = 5040;

impl FactKind {
    /// This fact with its table instances canonically renamed.
    pub fn canonical(&self) -> FactKind {
        // Lookups no term reads taken out, and decorrelated first: what they
        // take out is no instance to name.
        let unpadded = self.unpadded();
        let this = unpadded.as_ref().unwrap_or(self);
        let decorrelated = this.decorrelated();
        let this = decorrelated.as_ref().unwrap_or(this);
        let instances = this.instances();
        let mut groups: BTreeMap<&str, Vec<&String>> = BTreeMap::new();
        for i in &instances {
            groups.entry(base_table(i).unwrap()).or_default().push(i);
        }
        let groups: Vec<(&str, Vec<&String>)> = groups.into_iter().collect();
        let orders = groups.iter().try_fold(1usize, |n, (_, g)| (1..=g.len()).try_fold(n, |n, k| n.checked_mul(k)));
        if orders.is_none_or(|n| n > MAX_ORDERS) {
            let names = groups.iter().map(|(_, g)| g.clone()).collect::<Vec<_>>();
            return this.rename(&labels(&groups, &names));
        }
        let mut best: Option<FactKind> = None;
        let mut choice = vec![];
        each_order(&groups, 0, &mut choice, &mut |order| {
            let candidate = this.rename(&labels(&groups, order));
            if best.as_ref().is_none_or(|b| candidate < *b) {
                best = Some(candidate);
            }
        });
        best.unwrap_or_else(|| this.clone())
    }

    /// This fact with its left joins that only look up groups nothing
    /// reads, and its inner joins on groups nothing else reads, taken out
    /// (see [`rewrite::unpadded`]), until none is left: taking one out may
    /// leave another that only it read. `None` if there are none, or if any
    /// term reads an aggregate's value, which may be a group's.
    fn unpadded(&self) -> Option<FactKind> {
        let mut this = self.clone();
        loop {
            let next = this.unpadded_once()?;
            if next == this {
                return (this != *self).then_some(this);
            }
            this = next;
        }
    }

    fn unpadded_once(&self) -> Option<FactKind> {
        let (mut read, mut values) = (BTreeMap::new(), false);
        let terms = |ts: &BTreeSet<Term>, read: &mut BTreeMap<String, usize>, values: &mut bool| {
            for t in ts {
                for c in t.expr.column_refs() {
                    match c.relation.as_ref().map(|r| r.table()) {
                        Some("value") | None => *values = true,
                        Some(r) => *read.entry(r.to_string()).or_default() += 1,
                    }
                }
            }
        };
        let contexts: Vec<&Context> = match self {
            FactKind::Cardinality(c) => vec![c],
            FactKind::Selectivity { pred, over } => {
                terms(pred, &mut read, &mut values);
                vec![over]
            }
            FactKind::Match { on, kept, other } => {
                terms(on, &mut read, &mut values);
                vec![kept, other]
            }
            FactKind::Distinct { keys, over } | FactKind::Unique { keys, over } => {
                terms(keys, &mut read, &mut values);
                vec![over]
            }
        };
        for c in &contexts {
            rewrite::reads(c, &mut read, &mut values);
        }
        if values {
            return None;
        }
        let f = |c: &Context| rewrite::unpadded(c, &read);
        Some(match self {
            FactKind::Cardinality(c) => FactKind::Cardinality(f(c)),
            FactKind::Selectivity { pred, over } => FactKind::Selectivity { pred: pred.clone(), over: f(over) },
            FactKind::Match { on, kept, other } => FactKind::Match { on: on.clone(), kept: f(kept), other: f(other) },
            FactKind::Distinct { keys, over } => FactKind::Distinct { keys: keys.clone(), over: f(over) },
            FactKind::Unique { keys, over } => FactKind::Unique { keys: keys.clone(), over: f(over) },
        })
    }

    /// A match share on a copy of its kept side grouped on the correlated
    /// columns, as a semi join of the kept side itself (see
    /// [`rewrite::decorrelate`]). `None` if it is not one.
    fn decorrelated(&self) -> Option<FactKind> {
        let FactKind::Match { on, kept, other: before } = self else { return None };
        let e = Exists { kind: ExistsKind::Semi, on: on.clone(), other: before.clone() };
        let Exists { on, other, .. } = rewrite::decorrelate(kept, e);
        (other != *before).then(|| FactKind::Match { on, kept: kept.clone(), other })
    }

    /// This fact with its instances renamed by `names`, in normal form:
    /// contexts as [`rewrite`] builds them, a selectivity's predicates as its
    /// rows with them write them, and keys and conditions with columns
    /// written as the least column equal to them.
    fn rename(&self, names: &HashMap<String, String>) -> FactKind {
        let f = |r: &str| names.get(r).cloned();
        let terms = |s: &BTreeSet<Term>| s.iter().map(|t| t.rename(&f)).collect::<BTreeSet<_>>();
        match self {
            FactKind::Cardinality(c) => FactKind::Cardinality(c.rename(&f)),
            FactKind::Selectivity { pred, over } => {
                let (pred, over) = (terms(pred), over.rename(&f));
                let delta = rewrite::delta(&over, &pred);
                FactKind::Selectivity { pred: if delta.is_empty() { pred } else { delta }, over }
            }
            FactKind::Match { on, kept, other } => {
                let (kept, other) = (kept.rename(&f), other.rename(&f));
                let on = rewrite::on(&other, &rewrite::on(&kept, &terms(on)));
                FactKind::Match { on, kept, other }
            }
            FactKind::Distinct { keys, over } => {
                let over = over.rename(&f);
                FactKind::Distinct { keys: rewrite::keys(&over, &terms(keys)), over }
            }
            FactKind::Unique { keys, over } => {
                let over = over.rename(&f);
                FactKind::Unique { keys: rewrite::keys(&over, &terms(keys)), over }
            }
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
        Context::Spj { tables, atoms, preds, exists } => {
            for t in tables {
                push(t, out);
            }
            for a in atoms {
                context_instances(a, out);
            }
            for p in preds {
                term_instances(p, out);
            }
            for e in exists {
                context_instances(&e.other, out);
                for t in &e.on {
                    term_instances(t, out);
                }
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
