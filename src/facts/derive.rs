//! Facts that follow from other facts.
//!
//! Rows counted in one plan and a filter measured in another combine: a
//! filtered size over a base size is a selectivity, a selectivity times its
//! input's size is a size, a join's size over the sizes of its inputs is a
//! join selectivity, and a semi join's over its kept side's is a match share. These are applied
//! until nothing new follows. Every fact is exact, so this terminates: the
//! contexts it can reach are combinations of ones already known.

use std::collections::{BTreeSet, HashMap};

use super::{Context, Fact, FactKind, FactSet, Origin, Ratio, Term};

pub(super) fn close(set: &mut FactSet) {
    loop {
        let mut added = false;
        for (kind, value, rule) in step(set) {
            added |= set.insert(Fact { kind, value, origins: vec![Origin::Derived { rule }] });
        }
        if !added {
            break;
        }
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
    let spj: Vec<(&BTreeSet<String>, &BTreeSet<_>, &Context, Ratio)> = cards
        .iter()
        .filter_map(|(c, v)| match c {
            Context::Spj { tables, preds } => Some((tables, preds, *c, *v)),
            _ => None,
        })
        .collect();
    let mut by_tables: HashMap<&BTreeSet<String>, Vec<usize>> = HashMap::new();
    for (i, (tables, ..)) in spj.iter().enumerate() {
        by_tables.entry(*tables).or_default().push(i);
    }

    // Ratio: |C ∧ p| / |C| = s(p | C).
    for group in by_tables.values() {
        for &i in group {
            for &j in group {
                let ((_, p1, c1, v1), (_, p2, _, v2)) = (spj[i], spj[j]);
                if p1.len() < p2.len() && p1.is_subset(p2) {
                    let pred = p2.difference(p1).cloned().collect();
                    if let Some(s) = v2.over(v1) {
                        out.push((FactKind::Selectivity { pred, over: c1.clone() }, s, "ratio"));
                    }
                }
            }
        }
    }
    for (c, v) in &cards {
        if let Context::Derived { op, args, inputs } = c
            && op == "σ"
            && let Some(input) = cards.get(&inputs[0])
            && let Some(s) = v.over(*input)
        {
            let pred = args.iter().cloned().collect();
            out.push((FactKind::Selectivity { pred, over: inputs[0].clone() }, s, "ratio"));
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
        let cross = matches!(over, Context::Spj { tables, .. } if tables.len() > 1);
        if let (false, Some(n)) = (cross, cards.get(&target).and_then(|n| n.over(f.value)))
            && n.as_int().is_some()
        {
            out.push((FactKind::Cardinality(over.clone()), n, "product"));
        }
    }

    // Join: s(rest | L × R) = |C| / (|L| · |R|), where C draws on the tables
    // of L and R and satisfies their predicates, and `rest` are its other
    // predicates, at least one of which relates the two sides.
    for &(tables, preds, _, cv) in &spj {
        if tables.len() < 2 {
            continue;
        }
        for &(lt, lp, l, lv) in &spj {
            if lt.len() >= tables.len() || !lt.is_subset(tables) || !lp.is_subset(preds) {
                continue;
            }
            let rt: BTreeSet<String> = tables.difference(lt).cloned().collect();
            for &k in by_tables.get(&rt).into_iter().flatten() {
                let (_, rp, r, rv) = spj[k];
                if !rp.is_subset(preds) || l > r {
                    continue;
                }
                let rest: BTreeSet<Term> = preds.iter().filter(|p| !lp.contains(p) && !rp.contains(p)).cloned().collect();
                let relates = rest.iter().any(|p| {
                    let used: BTreeSet<String> = p.expr.column_refs().iter().filter_map(|c| c.relation.as_ref().map(|r| r.table().to_string())).collect();
                    !used.is_disjoint(lt) && !used.is_disjoint(&rt)
                });
                if let (true, Some(over), Some(s)) = (relates, l.cross(r), lv.times(rv).and_then(|lr| cv.over(lr))) {
                    out.push((FactKind::Selectivity { pred: rest, over }, s, "join"));
                }
            }
        }
    }

    // Match: a semi or anti join's size over its kept side's, the first
    // (`Context::join` names a right one as a left one).
    for (c, v) in &cards {
        let Context::Derived { op, args, inputs } = c else { continue };
        let semi = match op.as_str() {
            "LeftSemi join" => true,
            "LeftAnti join" => false,
            _ => continue,
        };
        let (kept, other) = (&inputs[0], &inputs[1]);
        // Named as a fact of its own, kept may read differently.
        let Some(n) = cards.get(&kept.canonical()).and_then(|k| k.as_int()) else { continue };
        let Some(rows) = v.as_int() else { continue };
        let matched = if semi { Some(rows) } else { n.checked_sub(rows) };
        if let Some(m) = matched.and_then(|m| Ratio::new(m, n)) {
            let on = args.iter().cloned().collect();
            out.push((FactKind::Match { on, kept: kept.clone(), other: other.clone() }, m, "match"));
        }
    }

    // Redundant: s(P | C) = 1 says every row of C satisfies each term of P,
    // so a context with C's tables and predicates names the same rows with
    // or without it. Engines add such terms (DuckDB filters a join's side by
    // the other's key range), and a query that does not spell them out
    // finds the facts without them. One term goes at a time: which can go
    // next may depend on which went first.
    let always: Vec<(&BTreeSet<String>, &BTreeSet<Term>, &Term)> = set
        .iter()
        .filter(|f| f.value == Ratio::int(1))
        .filter_map(|f| match &f.kind {
            FactKind::Selectivity { pred, over: Context::Spj { tables, preds } } => Some((tables, preds, pred)),
            _ => None,
        })
        .flat_map(|(tables, preds, pred)| pred.iter().map(move |p| (tables, preds, p)))
        .collect();
    if !always.is_empty() {
        // Whether `p` holds on every row of the cross product of `tables`
        // satisfying `preds`.
        let implied = |p: &Term, tables: &BTreeSet<String>, preds: &BTreeSet<Term>| {
            always.iter().any(|(t, c, q)| *q == p && t.is_subset(tables) && c.is_subset(preds) && !c.contains(p))
        };
        // `c` without each term it implies otherwise.
        let reduced = |c: &Context| -> Vec<Context> {
            let Context::Spj { tables, preds } = c else { return vec![] };
            preds
                .iter()
                .filter_map(|p| {
                    let mut rest = preds.clone();
                    rest.remove(p);
                    implied(p, tables, &rest).then(|| Context::Spj { tables: tables.clone(), preds: rest })
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
                    if let Context::Spj { tables, preds } = over {
                        for p in pred.iter().filter(|p| pred.len() > 1 && implied(p, tables, preds)) {
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
