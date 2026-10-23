//! Facts that follow from other facts.
//!
//! Rows counted in one plan and a filter measured in another combine: a
//! filtered size over a base size is a selectivity, a selectivity times its
//! input's size is a size, a join's size over the sizes of its inputs is a
//! join selectivity, and a semi join's over its kept side's is a match share.
//! These are applied until nothing new follows. Every fact is exact, so this
//! terminates: the contexts it can reach are combinations of ones already
//! known.

use std::collections::{BTreeSet, HashMap};

use super::rewrite::Spj;
use super::{Context, Exists, ExistsKind, Fact, FactKind, FactSet, Origin, Ratio, Term};

pub(super) fn close(set: &mut FactSet) {
    loop {
        let mut added = false;
        for (kind, value, rule) in step(set) {
            added |= set.insert(Fact { kind, value, origins: vec![Origin::Derived { rule: rule.into() }] });
        }
        if !added {
            break;
        }
    }
}

/// An SPJ's parts: its tables, atoms, predicates and conditions.
type Parts<'a> = (&'a BTreeSet<String>, &'a BTreeSet<Context>, &'a BTreeSet<Term>, &'a BTreeSet<Exists>);

fn parts(c: &Context) -> Option<Parts<'_>> {
    match c {
        Context::Spj { tables, atoms, preds, exists } => Some((tables, atoms, preds, exists)),
        _ => None,
    }
}

fn step(set: &FactSet) -> Vec<(FactKind, Ratio, &'static str)> {
    let mut out = vec![];
    let cards: HashMap<&Context, Ratio> = set
        .iter()
        .filter_map(|f| match &f.kind {
            FactKind::Cardinality(c) => Some((c, f.value)),
            _ => None,
        })
        .collect();
    let spj: Vec<(Parts, &Context, Ratio)> = cards.iter().filter_map(|(c, v)| Some((parts(c)?, *c, *v))).collect();
    // By inputs: tables and atoms.
    let mut by_inputs: HashMap<(&BTreeSet<String>, &BTreeSet<Context>), Vec<usize>> = HashMap::new();
    for (i, ((tables, atoms, ..), ..)) in spj.iter().enumerate() {
        by_inputs.entry((*tables, *atoms)).or_default().push(i);
    }

    // Ratio: |C ∧ p| / |C| = s(p | C), where C ∧ p has C's inputs and
    // conditions, and predicates that are C's with p.
    for group in by_inputs.values() {
        for &i in group {
            for &j in group {
                let (((_, _, p1, e1), c1, v1), ((_, _, p2, e2), c2, v2)) = (&spj[i], &spj[j]);
                if i == j || e1 != e2 || p1.len() > p2.len() || c1.filter(p2) != **c2 {
                    continue;
                }
                let pred: BTreeSet<Term> = p2.difference(p1).cloned().collect();
                if let (false, Some(s)) = (pred.is_empty(), v2.over(*v1)) {
                    out.push((FactKind::Selectivity { pred, over: (*c1).clone() }, s, "ratio"));
                }
            }
        }
    }
    // A filter over one atom: |σp(G)| / |G|.
    for &((tables, atoms, preds, exists), _, v) in &spj {
        if tables.is_empty() && atoms.len() == 1 && exists.is_empty() && !preds.is_empty() {
            let atom = atoms.first().unwrap();
            if let Some(s) = cards.get(atom).and_then(|n| v.over(*n)) {
                out.push((FactKind::Selectivity { pred: preds.clone(), over: atom.clone() }, s, "ratio"));
            }
        }
    }

    // Product: s(p | C) · |C| = |C ∧ p|, and back. Not back to a cross
    // product, whose size is just the product of its inputs'.
    for f in set.iter() {
        let FactKind::Selectivity { pred, over } = &f.kind else { continue };
        let target = over.filter(pred);
        if let Some(n) = cards.get(over).and_then(|n| n.times(f.value)).filter(|n| n.as_int().is_some()) {
            out.push((FactKind::Cardinality(target.clone()), n, "product"));
        }
        let cross = matches!(parts(over), Some((tables, atoms, ..)) if tables.len() + atoms.len() > 1);
        if let (false, Some(n)) = (cross, cards.get(&target).and_then(|n| n.over(f.value)))
            && n.as_int().is_some()
        {
            out.push((FactKind::Cardinality(over.clone()), n, "product"));
        }
    }

    // Join: s(rest | L × R) = |C| / (|L| · |R|), where C's inputs are L's
    // and R's, C is L × R with more predicates, `rest`, and at least one of
    // them relates the two sides.
    for &((tables, atoms, preds, exists), c, cv) in &spj {
        if tables.len() + atoms.len() < 2 {
            continue;
        }
        for &((lt, la, _, le), l, lv) in &spj {
            if lt.len() + la.len() >= tables.len() + atoms.len()
                || !lt.is_subset(tables)
                || !la.is_subset(atoms)
                || !le.is_subset(exists)
            {
                continue;
            }
            let rt: BTreeSet<String> = tables.difference(lt).cloned().collect();
            let ra: BTreeSet<Context> = atoms.difference(la).cloned().collect();
            for &k in by_inputs.get(&(&rt, &ra)).into_iter().flatten() {
                let ((_, _, _, re), r, rv) = spj[k];
                if !re.is_subset(exists) || l > r {
                    continue;
                }
                let Some(over) = l.cross(r) else { continue };
                if over.filter(preds) != *c {
                    continue;
                }
                let Some((_, _, op, _)) = parts(&over) else { continue };
                let rest: BTreeSet<Term> = preds.difference(op).cloned().collect();
                let (ls, rs) = (l.tables(), r.tables());
                let relates = rest.iter().any(|p| {
                    let used: BTreeSet<String> = p.expr.column_refs().iter().filter_map(|c| c.relation.as_ref().map(|r| r.table().to_string())).collect();
                    !used.is_disjoint(&ls) && !used.is_disjoint(&rs)
                });
                if let (true, Some(s)) = (relates, lv.times(rv).and_then(|lr| cv.over(lr))) {
                    out.push((FactKind::Selectivity { pred: rest, over }, s, "join"));
                }
            }
        }
    }

    // Match: a context with a semi or anti condition, over the same without
    // it, is the share of its rows with a partner.
    for &((tables, atoms, preds, exists), _, v) in &spj {
        for e in exists {
            let semi = match e.kind {
                ExistsKind::Semi => true,
                ExistsKind::Anti => false,
                ExistsKind::NotIn => continue,
            };
            let mut rest = exists.clone();
            rest.remove(e);
            let kept = Spj { tables: tables.clone(), atoms: atoms.clone(), preds: preds.clone(), exists: rest }.build();
            // Named as a fact of its own, kept may read differently.
            let Some(n) = cards.get(&kept.canonical()).and_then(|k| k.as_int()) else { continue };
            let Some(rows) = v.as_int() else { continue };
            let matched = if semi { Some(rows) } else { n.checked_sub(rows) };
            if let Some(m) = matched.and_then(|m| Ratio::new(m, n)) {
                let kind = FactKind::Match { on: e.on.clone(), kept, other: e.other.clone() };
                out.push((kind.canonical(), m, "match"));
            }
        }
    }

    // Redundant: s(P | C) = 1 says every row of C satisfies each term of P,
    // so a context with C's inputs and conditions names the same rows with
    // or without it. Engines add such terms (DuckDB filters a join's side by
    // the other's key range), and a query that does not spell them out
    // finds the facts without them. One term goes at a time: which can go
    // next may depend on which went first.
    let always: Vec<(Parts, &Term)> = set
        .iter()
        .filter(|f| f.value == Ratio::int(1))
        .filter_map(|f| match &f.kind {
            FactKind::Selectivity { pred, over } => Some((parts(over)?, pred)),
            _ => None,
        })
        .flat_map(|(parts, pred)| pred.iter().map(move |p| (parts, p)))
        .collect();
    if !always.is_empty() {
        // Whether `p` holds on every row of a context with these parts. A
        // row of it is, on C's inputs, a row of C.
        let implied = |p: &Term, (tables, atoms, preds, exists): Parts| {
            always.iter().any(|((t, a, c, e), q)| {
                *q == p && t.is_subset(tables) && a.is_subset(atoms) && c.is_subset(preds) && e.is_subset(exists) && !c.contains(p)
            })
        };
        // `c` without each term it implies otherwise.
        let reduced = |c: &Context| -> Vec<Context> {
            let Some((tables, atoms, preds, exists)) = parts(c) else { return vec![] };
            preds
                .iter()
                .filter_map(|p| {
                    let mut rest = preds.clone();
                    rest.remove(p);
                    implied(p, (tables, atoms, &rest, exists)).then(|| {
                        Spj { tables: tables.clone(), atoms: atoms.clone(), preds: rest, exists: exists.clone() }.build()
                    })
                })
                .collect()
        };
        for f in set.iter() {
            let kinds: Vec<FactKind> = match &f.kind {
                FactKind::Cardinality(c) => reduced(c).into_iter().map(FactKind::Cardinality).collect(),
                FactKind::Selectivity { pred, over } => {
                    let mut out: Vec<FactKind> = reduced(over)
                        .into_iter()
                        .map(|over| FactKind::Selectivity { pred: pred.clone(), over })
                        .collect();
                    if let Some(p_over) = parts(over) {
                        for p in pred.iter().filter(|p| pred.len() > 1 && implied(p, p_over)) {
                            let mut rest = pred.clone();
                            rest.remove(p);
                            out.push(FactKind::Selectivity { pred: rest, over: over.clone() });
                        }
                    }
                    out
                }
                FactKind::Distinct { keys, over } => {
                    reduced(over).into_iter().map(|over| FactKind::Distinct { keys: keys.clone(), over }).collect()
                }
                FactKind::Unique { keys, over } => {
                    reduced(over).into_iter().map(|over| FactKind::Unique { keys: keys.clone(), over }).collect()
                }
                FactKind::Min { key, over } => {
                    reduced(over).into_iter().map(|over| FactKind::Min { key: key.clone(), over }).collect()
                }
                FactKind::Max { key, over } => {
                    reduced(over).into_iter().map(|over| FactKind::Max { key: key.clone(), over }).collect()
                }
                FactKind::Match { on, kept, other } => {
                    let kept_side = reduced(kept)
                        .into_iter()
                        .map(|kept| FactKind::Match { on: on.clone(), kept, other: other.clone() });
                    let other_side = reduced(other)
                        .into_iter()
                        .map(|other| FactKind::Match { on: on.clone(), kept: kept.clone(), other });
                    kept_side.chain(other_side).collect()
                }
            };
            out.extend(kinds.into_iter().map(|k| (k.canonical(), f.value, "redundant")));
        }
    }

    // Unique: ndv(keys | C) = |C|.
    for f in set.iter() {
        if let FactKind::Distinct { keys, over } = &f.kind
            && cards.get(over) == Some(&f.value)
        {
            out.push((FactKind::Unique { keys: keys.clone(), over: over.clone() }, Ratio::int(1), "unique"));
        }
    }
    out
}
