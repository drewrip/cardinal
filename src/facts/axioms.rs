//! What any data satisfies, relating the quantities of named rows.
//!
//! Stage 3 of the [pipeline](super#pipeline), run by
//! [`Analysis::with_store`](crate::Analysis::with_store); notation as in
//! [the module](super#notation).
//!
//! # Spec
//!
//! - **Input**: every quantity (`|C|`, `ndv(K | C)`, `min(k | C)`,
//!   `max(k | C)`, canonical) with the Z3 terms known to equal it: the
//!   query's operator variables for the rows they name, and a variable of
//!   its own for each fact's quantity that no operator has.
//! - **Output**: ground Z3 assertions over those terms, each tagged with
//!   its rule ([`Grounded::axioms`](crate::Grounded::axioms) counts them).
//!   No quantifiers: Rust decides which contexts relate, Z3 does the
//!   arithmetic.
//! - **Guarantees**: each axiom holds for any data, so it is asserted
//!   untracked, and only the facts' claims can be rejected. The tests on
//!   contexts are conservative: missing a relation loses an axiom, never
//!   adds a wrong one.
//! - **Not done**: selectivities and match shares get no axioms (the store
//!   claims only quantities); contexts outside the relevant set are not
//!   related.
//!
//! # Relevant contexts
//!
//! Only contexts near the query's are related. Starting from the contexts
//! of the query's operators, add each context two contexts relate to (one
//! is ⊆ or has fewer rows than the other, or both are SPJs with the same
//! inputs and conditions) among those over the same base tables, twice;
//! then each context any of these [joins](#relations-between-contexts).
//!
//! # Relations between contexts
//!
//! Each test holds up to renaming the instances of one table among
//! themselves (`t@1`, `t@2`).
//!
//! - `A ⊆ B`: `A`'s rows are among `B`'s. `A = B`; or `B` is an outer join
//!   and `A ⊆` its inner join; or both have the same tables and atoms, `A`
//!   has all of `B`'s predicates, and for each condition of `B` a stricter
//!   one: a semi join against fewer rows, an anti join against more.
//! - `fewer(A, B)`: `|A| ≤ |B|`. `A ⊆ B`; or both are left joins on the same
//!   condition with inputs pairwise `⊆`; or `A` is a left or full join and
//!   `B` a full join on the same condition, inputs pairwise `⊆` either way.
//! - `D` joins `C`: both SPJs, `D` with more inputs, and all of `C`'s
//!   tables, atoms, conditions and predicates.
//!
//! # Axioms
//!
//! ## `same rows`
//!
//! - **Claim**: `t = t'` for any two terms of one quantity. And for `A ⊆ B`:
//!   `|A| = |B| ⇒` each key quantity of `A` equals `B`'s of the same keys.
//! - **Why**: one quantity has one value; `A ⊆ B` with as many rows makes
//!   them the same rows.
//!
//! ## `ndv within rows`
//!
//! - **Claim**: `ndv(K | C) ≤ |C|`.
//!
//! ## `subset`
//!
//! - **Claim**: for `A ⊆ B`, `A ≠ B`: `|A| ≤ |B|`; `ndv(K | A) ≤ ndv(K' |
//!   B)` for `K ⊆ K'`; `min(k | A) ≥ min(k | B)`; `max(k | A) ≤ max(k | B)`.
//! - **Why**: fewer rows have fewer values, within the same range.
//!
//! ## `fewer`
//!
//! - **Claim**: `|A| ≤ |B|` for `fewer(A, B)` but not `A ⊆ B`.
//! - **Why**: an outer join emits each preserved row once per partner or
//!   once padded, so narrowing an input never adds rows. Its rows need not
//!   be among the other's (a row may lose its partner and be padded), so
//!   nothing is said of their values.
//!
//! ## `failing rows`
//!
//! - **Claim**: `|D| − |D ∧ P| ≤ |C| − |C ∧ P|`.
//! - **When**: `D ⊆ C` as named, `C` an SPJ, `C ∧ P` a relevant SPJ with
//!   `C`'s inputs and conditions, and `D ∧ P ≠ D`.
//! - **Why**: `D`'s rows failing `P` are among `C`'s.
//!
//! ```text
//! D = orders ∧ o_status = 'F' ⊆ C = orders, P = {o_price > 100}
//! ⇒ |D| − |D ∧ P| ≤ |orders| − |orders ∧ P|
//! ```
//!
//! ## `implied`
//!
//! - **Claim**: `|C ∧ P| = |C| ⇒ |D ∧ P| = |D|`.
//! - **When**: `C` an SPJ, `C ∧ P` a relevant SPJ with `C`'s inputs and
//!   conditions, `D` joins `C` and does not already have all of `P`.
//! - **Why**: if every row of `C` satisfies `P`, so does every row of `D`,
//!   which is, on `C`'s inputs, a row of `C`.
//!
//! ```text
//! C = lineitem, P = {l_quantity >= 1}, D = lineitem ⋈ orders
//! ⇒ |lineitem ∧ P| = |lineitem| ⇒ |D ∧ P| = |D|
//! ```
//!
//! ## `semi and anti`
//!
//! - **Claim**: `|K ⋉ O| + |K ▷ O| = |K|`, for `K ⋉ O` an SPJ with a semi
//!   condition, `K` it without it, and `K ▷ O` it with the anti condition on
//!   the same `on` and `O` instead.
//! - **Why**: each row of `K` has a partner or has none.
//!
//! ## `fewer keys`
//!
//! - **Claim**: `ndv(K | C) ≤ ndv(K' | C)` for `K ⊊ K'`.
//! - **Why**: fewer keys have no more combinations.
//!
//! ## `wider rows`
//!
//! - **Claim**: for `D` joining `C`, and keys `K` (or `k`) whose columns are
//!   all of `C`'s tables: `ndv(K | D) ≤ |C|`; `ndv(K | D) ≤ ndv(K' | C)` for
//!   `K ⊆ K'`; `min(k | D) ≥ min(k | C)`; `max(k | D) ≤ max(k | C)`.
//! - **Why**: each row of `D` holds a row of `C`, so `C`'s columns take in
//!   `D` only values they take in `C`.
//!
//! ```text
//! D = orders ⋈ lineitem on o_orderkey = l_orderkey
//! ⇒ ndv(o_custkey | D) ≤ ndv(o_custkey | orders) and ≤ |orders|
//! ```
//!
//! ## `disjoint`
//!
//! - **Claim**: `|X| + |Y| ≤ |Z|`.
//! - **When**: `X`, `Y` and `Z` are SPJs with the same inputs and
//!   conditions; `X` and `Y` compare some expression with literals in
//!   ranges that do not meet (values of different types are taken to
//!   meet); `Z`'s predicates are among both's, and no such `Z` has more.
//! - **Why**: no row satisfies both, so `X`'s and `Y`'s rows are apart
//!   among `Z`'s.
//!
//! ```text
//! |orders ∧ o_orderdate < 10| + |orders ∧ o_orderdate > 20| ≤ |orders|
//! ```
//!
//! ## `non-negative`
//!
//! - **Claim**: `t ≥ 0` for a fact's own variable on a size or distinct
//!   count. The query's variables have this among their constraints.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use datafusion::common::ScalarValue;
use datafusion::logical_expr::{BinaryExpr, Expr, Operator};
use z3::ast::{Bool, Int};

use crate::rows::contain::{fewer, renamed, renamed_kind, subset};
use crate::rows::rewrite::Spj;
use crate::rows::{Context, Exists, ExistsKind, Term};
use super::FactKind;

/// An assertion every data satisfies, and the rule it is from.
pub(crate) struct Axiom {
    pub claim: Bool,
    pub rule: &'static str,
}

/// The terms each quantity equals.
#[derive(Default)]
pub(crate) struct Space {
    terms: BTreeMap<FactKind, Vec<Int>>,
}

impl Space {
    /// Records that `term` equals quantity `q`, a canonical kind.
    pub fn add(&mut self, q: FactKind, term: Int) {
        let terms = self.terms.entry(q).or_default();
        if !terms.contains(&term) {
            terms.push(term);
        }
    }

    /// The term standing for `q`, if any has been added.
    pub fn term(&self, q: &FactKind) -> Option<&Int> {
        self.terms.get(q).and_then(|t| t.first())
    }

    /// The contexts of `seeds`, those related to one ([`related`]), those
    /// related to one of them, and those any of these is a join of
    /// ([`joins`]).
    pub fn relevant(&self, seeds: &BTreeSet<Context>) -> BTreeSet<Context> {
        let buckets = self.buckets();
        let mut out: BTreeSet<Context> = seeds.clone();
        let mut frontier: Vec<Context> = seeds.iter().cloned().collect();
        for _ in 0..2 {
            let mut next = vec![];
            for a in &frontier {
                for b in buckets.get(&bases(a)).into_iter().flatten() {
                    if !out.contains(*b) && related(a, b) {
                        next.push((*b).clone());
                    }
                }
            }
            out.extend(next.iter().cloned());
            frontier = next;
        }
        let contexts: BTreeSet<&Context> = self.terms.keys().map(over).collect();
        let narrower: Vec<&Context> =
            contexts.into_iter().filter(|c| !out.contains(*c) && out.iter().any(|d| joins(d, c))).collect();
        out.extend(narrower.into_iter().cloned());
        out
    }

    /// Every axiom over the quantities of `relevant` contexts.
    pub fn axioms(&self, relevant: &BTreeSet<Context>) -> Vec<Axiom> {
        let mut out = vec![];
        let card = |c: &Context| self.term(&FactKind::Cardinality(c.clone()));
        // Each relevant context's key quantities.
        let mut keys: BTreeMap<&Context, Vec<&FactKind>> = BTreeMap::new();
        for q in self.terms.keys() {
            if relevant.contains(over(q)) && !matches!(q, FactKind::Cardinality(_)) {
                keys.entry(over(q)).or_default().push(q);
            }
        }
        for (q, terms) in &self.terms {
            if !relevant.contains(over(q)) {
                continue;
            }
            // Every term of one quantity is one value.
            for t in &terms[1..] {
                out.push(Axiom { claim: t.eq(&terms[0]), rule: "same rows" });
            }
            if let FactKind::Distinct { over, .. } = q
                && let Some(n) = card(over)
            {
                out.push(Axiom { claim: terms[0].le(n), rule: "ndv within rows" });
            }
        }

        let buckets = self.buckets();
        for a in relevant {
            let Some(ca) = card(a) else { continue };
            for b in buckets.get(&bases(a)).into_iter().flatten().filter(|b| relevant.contains(**b) && **b != a) {
                let Some(cb) = card(b) else { continue };
                if renamed(a, b, subset) {
                    out.push(Axiom { claim: ca.le(cb), rule: "subset" });
                    // Each key of `a` that is one of `b`'s, over rows among
                    // `b`'s, and the same once there are as many rows.
                    let mut same = vec![];
                    for qa in keys.get(a).into_iter().flatten() {
                        for qb in keys.get(*b).into_iter().flatten() {
                            if !renamed_kind(qa, qb, key_within) {
                                continue;
                            }
                            let (ta, tb) = (self.term(qa).unwrap(), self.term(qb).unwrap());
                            let claim = match qa {
                                FactKind::Min { .. } => ta.ge(tb),
                                _ => ta.le(tb),
                            };
                            out.push(Axiom { claim, rule: "subset" });
                            if width(qa) == width(qb) {
                                same.push(ta.eq(tb));
                            }
                        }
                    }
                    if !same.is_empty() {
                        let all = Bool::and(&same);
                        out.push(Axiom { claim: ca.eq(cb).implies(&all), rule: "same rows" });
                    }
                    out.extend(failing(self, relevant, a, b));
                } else if renamed(a, b, fewer) {
                    out.push(Axiom { claim: ca.le(cb), rule: "fewer" });
                }
            }
            out.extend(split(self, a));
            out.extend(fewer_keys(self, &keys, a));
        }
        out.extend(implied(self, relevant));
        out.extend(wider(self, &keys, relevant));
        out.extend(disjoint(self, relevant));
        out
    }

    /// The contexts of every quantity, by the tables they draw on: only
    /// contexts with the same are related.
    fn buckets(&self) -> BTreeMap<Vec<String>, Vec<&Context>> {
        let mut out: BTreeMap<Vec<String>, Vec<&Context>> = BTreeMap::new();
        let contexts: BTreeSet<&Context> = self.terms.keys().map(over).collect();
        for c in contexts {
            out.entry(bases(c)).or_default().push(c);
        }
        out
    }
}

/// The rows `q` is a quantity of.
pub(crate) fn over(q: &FactKind) -> &Context {
    match q {
        FactKind::Cardinality(c) => c,
        FactKind::Selectivity { over, .. }
        | FactKind::Distinct { over, .. }
        | FactKind::Unique { over, .. }
        | FactKind::Min { over, .. }
        | FactKind::Max { over, .. } => over,
        FactKind::Match { kept, .. } => kept,
    }
}

/// True if `a` and `b` name rows one bounds the other's: either is among
/// the other's, has fewer, or is the other with other predicates.
fn related(a: &Context, b: &Context) -> bool {
    renamed(a, b, fewer) || renamed(b, a, fewer) || renamed(a, b, same_inputs)
}

/// True if `a` and `b` are SPJs over the same inputs and conditions.
fn same_inputs(a: &Context, b: &Context) -> bool {
    let (Context::Spj { tables: ta, atoms: aa, exists: ea, .. }, Context::Spj { tables: tb, atoms: ab, exists: eb, .. }) = (a, b)
    else {
        return false;
    };
    ta == tb && aa == ab && ea == eb
}

/// True if `a` is `b`'s quantity of the same key, or for a distinct count of
/// some of its keys, over rows among `b`'s.
fn key_within(a: &FactKind, b: &FactKind) -> bool {
    match (a, b) {
        (FactKind::Distinct { keys: ka, over: oa }, FactKind::Distinct { keys: kb, over: ob }) => {
            ka.is_subset(kb) && subset(oa, ob)
        }
        (FactKind::Min { key: ka, over: oa }, FactKind::Min { key: kb, over: ob })
        | (FactKind::Max { key: ka, over: oa }, FactKind::Max { key: kb, over: ob }) => ka == kb && subset(oa, ob),
        _ => false,
    }
}

/// For `d` among `c`'s rows as named, each `c ∧ P` with a term and `d ∧ P`
/// too: the rows of `d` failing `P` are among those of `c` failing it.
fn failing(space: &Space, relevant: &BTreeSet<Context>, d: &Context, c: &Context) -> Vec<Axiom> {
    let card = |x: &Context| space.term(&FactKind::Cardinality(x.clone()));
    let (Some(cd), Some(cc), true) = (card(d), card(c), subset(d, c)) else { return vec![] };
    let Context::Spj { preds: pc, .. } = c else { return vec![] };
    let mut out = vec![];
    for cp in relevant {
        let Context::Spj { preds, .. } = cp else { continue };
        if cp == c || !same_inputs(cp, c) || !preds.is_superset(pc) {
            continue;
        }
        let p: BTreeSet<_> = preds.difference(pc).cloned().collect();
        let dp = d.filter(&p).canonical();
        if dp == *d {
            continue;
        }
        if let (Some(ccp), Some(cdp)) = (card(cp), card(&dp)) {
            let claim = Int::sub(&[cd, cdp]).le(Int::sub(&[cc, ccp]));
            out.push(Axiom { claim, rule: "failing rows" });
        }
    }
    out
}

/// For each `c ∧ P` with a term, and each `d` over more inputs than `c`
/// and at least its conditions and predicates, with `d ∧ P` a term too: if
/// every row of `c` satisfies `P`, every row of `d` does. Contexts over the
/// same inputs are left to [`failing`].
fn implied(space: &Space, relevant: &BTreeSet<Context>) -> Vec<Axiom> {
    let card = |x: &Context| space.term(&FactKind::Cardinality(x.clone()));
    let mut out = vec![];
    for c in relevant {
        let (Context::Spj { tables: tc, atoms: ac, preds: pc, exists: ec }, Some(cc)) = (c, card(c)) else { continue };
        for cp in relevant {
            let Context::Spj { preds, .. } = cp else { continue };
            if cp == c || !same_inputs(cp, c) || !preds.is_superset(pc) {
                continue;
            }
            let Some(ccp) = card(cp) else { continue };
            let p: BTreeSet<_> = preds.difference(pc).cloned().collect();
            for d in relevant {
                let Context::Spj { tables: td, atoms: ad, preds: pd, exists: ed } = d else { continue };
                let wider = td.len() + ad.len() > tc.len() + ac.len();
                if !wider || !td.is_superset(tc) || !ad.is_superset(ac) || !ed.is_superset(ec) || !pd.is_superset(pc) || pd.is_superset(&p) {
                    continue;
                }
                let dp = d.filter(&p).canonical();
                if let (Some(cd), Some(cdp)) = (card(d), card(&dp)) {
                    out.push(Axiom { claim: ccp.eq(cc).implies(cdp.eq(cd)), rule: "implied" });
                }
            }
        }
    }
    out
}

/// For `s` with a semi join condition, its rows with and without a partner
/// split the rows without the condition, where all three have terms.
fn split(space: &Space, s: &Context) -> Vec<Axiom> {
    let card = |x: &Context| space.term(&FactKind::Cardinality(x.clone()));
    let Context::Spj { tables, atoms, preds, exists } = s else { return vec![] };
    let Some(semi) = card(s) else { return vec![] };
    let mut out = vec![];
    for e in exists.iter().filter(|e| e.kind == ExistsKind::Semi) {
        let mut rest = exists.clone();
        rest.remove(e);
        let spj = |exists: BTreeSet<Exists>| Spj { tables: tables.clone(), atoms: atoms.clone(), preds: preds.clone(), exists }.build();
        let kept = spj(rest.clone()).canonical();
        let mut with_anti = rest;
        with_anti.insert(Exists { kind: ExistsKind::Anti, on: e.on.clone(), other: e.other.clone() });
        let anti = spj(with_anti).canonical();
        if let (Some(k), Some(a)) = (card(&kept), card(&anti)) {
            out.push(Axiom { claim: Int::add(&[semi, a]).eq(k), rule: "semi and anti" });
        }
    }
    out
}

/// How many keys `q` is of.
fn width(q: &FactKind) -> usize {
    match q {
        FactKind::Distinct { keys, .. } | FactKind::Unique { keys, .. } => keys.len(),
        _ => 1,
    }
}

/// For each distinct count over `c` of keys among another's over `c`, the
/// fewer keys' count is at most the other's.
fn fewer_keys(space: &Space, keys: &BTreeMap<&Context, Vec<&FactKind>>, c: &Context) -> Vec<Axiom> {
    let mut out = vec![];
    for qa in keys.get(c).into_iter().flatten() {
        let FactKind::Distinct { keys: ka, .. } = qa else { continue };
        for qb in keys.get(c).into_iter().flatten() {
            let FactKind::Distinct { keys: kb, .. } = qb else { continue };
            if ka.len() < kb.len() && ka.is_subset(kb) {
                let (ta, tb) = (space.term(qa).unwrap(), space.term(qb).unwrap());
                out.push(Axiom { claim: ta.le(tb), rule: "fewer keys" });
            }
        }
    }
    out
}

/// True if `d` is `c` joined to more tables or atoms: an SPJ over at least
/// `c`'s inputs, conditions and predicates, so each row of `d` holds a row
/// of `c` in `c`'s tables' columns.
fn joins(d: &Context, c: &Context) -> bool {
    let (Context::Spj { tables: td, atoms: ad, preds: pd, exists: ed }, Context::Spj { tables: tc, atoms: ac, preds: pc, exists: ec }) =
        (d, c)
    else {
        return false;
    };
    td.len() + ad.len() > tc.len() + ac.len()
        && td.is_superset(tc)
        && ad.is_superset(ac)
        && ed.is_superset(ec)
        && pd.is_superset(pc)
}

/// True if every column `keys` read is of one of `tables`.
fn of_tables(keys: &BTreeSet<Term>, tables: &BTreeSet<String>) -> bool {
    !keys.is_empty()
        && keys.iter().all(|k| {
            let columns = k.expr.column_refs();
            !columns.is_empty() && columns.iter().all(|c| c.relation.as_ref().is_some_and(|r| tables.contains(r.table())))
        })
}

/// For each `d` a join of `c` ([`joins`]), each key quantity of `d` over
/// `c`'s tables' columns is within `c`'s: its distinct count at most `|c|`
/// and at most that of any keys of `c` it is among, and its min and max
/// within `c`'s.
fn wider(space: &Space, keys: &BTreeMap<&Context, Vec<&FactKind>>, relevant: &BTreeSet<Context>) -> Vec<Axiom> {
    let card = |x: &Context| space.term(&FactKind::Cardinality(x.clone()));
    let mut out = vec![];
    for d in relevant {
        let Some(qds) = keys.get(d) else { continue };
        for c in relevant {
            let Context::Spj { tables: tc, .. } = c else { continue };
            if !joins(d, c) {
                continue;
            }
            for qd in qds {
                let td = space.term(qd).unwrap();
                match qd {
                    FactKind::Distinct { keys: kd, .. } if of_tables(kd, tc) => {
                        if let Some(n) = card(c) {
                            out.push(Axiom { claim: td.le(n), rule: "wider rows" });
                        }
                        for qc in keys.get(c).into_iter().flatten() {
                            if let FactKind::Distinct { keys: kc, .. } = qc
                                && kd.is_subset(kc)
                            {
                                out.push(Axiom { claim: td.le(space.term(qc).unwrap()), rule: "wider rows" });
                            }
                        }
                    }
                    FactKind::Min { key, .. } | FactKind::Max { key, .. } if of_tables(&[key.clone()].into(), tc) => {
                        let at_c = match qd {
                            FactKind::Min { .. } => FactKind::Min { key: key.clone(), over: c.clone() },
                            _ => FactKind::Max { key: key.clone(), over: c.clone() },
                        };
                        if let Some(tc) = space.term(&at_c) {
                            let claim = if matches!(qd, FactKind::Min { .. }) { td.ge(tc) } else { td.le(tc) };
                            out.push(Axiom { claim, rule: "wider rows" });
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    out
}

/// For each two SPJs over the same inputs and conditions whose predicates
/// cannot hold together, their rows are apart among those of any SPJ over
/// the same with only predicates both have: `|x| + |y| <= |z|`. Of such
/// `z`, only those with the most predicates are used.
fn disjoint(space: &Space, relevant: &BTreeSet<Context>) -> Vec<Axiom> {
    let card = |x: &Context| space.term(&FactKind::Cardinality(x.clone()));
    let mut groups: BTreeMap<_, Vec<(&BTreeSet<Term>, &Int)>> = BTreeMap::new();
    for c in relevant {
        if let (Context::Spj { tables, atoms, preds, exists }, Some(n)) = (c, card(c)) {
            groups.entry((tables, atoms, exists)).or_default().push((preds, n));
        }
    }
    let mut out = vec![];
    for group in groups.values() {
        for (i, (px, x)) in group.iter().enumerate() {
            for (py, y) in &group[i + 1..] {
                if !contradict(px, py) {
                    continue;
                }
                let within: Vec<&(&BTreeSet<Term>, &Int)> =
                    group.iter().filter(|(pz, _)| pz.is_subset(px) && pz.is_subset(py)).collect();
                for (pz, z) in &within {
                    if within.iter().any(|(pw, _)| pw.len() > pz.len() && pw.is_superset(pz)) {
                        continue;
                    }
                    out.push(Axiom { claim: Int::add(&[*x, *y]).le(*z), rule: "disjoint" });
                }
            }
        }
    }
    out
}

/// True if no row satisfies both `a` and `b`: some expression is compared
/// with literals into ranges that do not meet. Comparisons of values of
/// different types are taken to meet.
fn contradict(a: &BTreeSet<Term>, b: &BTreeSet<Term>) -> bool {
    let ranges = |preds: &BTreeSet<Term>| {
        let mut out: BTreeMap<String, Vec<(Operator, ScalarValue)>> = BTreeMap::new();
        for p in preds {
            if let Some((e, op, v)) = comparison(&p.expr) {
                out.entry(e.to_string()).or_default().push((op, v));
            }
        }
        out
    };
    let (ra, rb) = (ranges(a), ranges(b));
    ra.iter().any(|(e, xs)| rb.get(e).is_some_and(|ys| xs.iter().any(|x| ys.iter().any(|y| apart(x, y)))))
}

/// `e op v`, for a comparison of an expression with a non-NULL literal, the
/// literal on the right as [`Term`] writes it.
fn comparison(e: &Expr) -> Option<(&Expr, Operator, ScalarValue)> {
    let Expr::BinaryExpr(BinaryExpr { left, op, right }) = e else { return None };
    if !matches!(op, Operator::Eq | Operator::Lt | Operator::LtEq | Operator::Gt | Operator::GtEq) {
        return None;
    }
    let v = match right.as_ref() {
        Expr::Literal(v, _) => v.clone(),
        Expr::Cast(c) => match c.expr.as_ref() {
            Expr::Literal(v, _) => v.cast_to(c.field.data_type()).ok()?,
            _ => return None,
        },
        _ => return None,
    };
    (!v.is_null() && !matches!(left.as_ref(), Expr::Literal(..))).then_some((left.as_ref(), *op, v))
}

/// True if no value satisfies both `_ x.0 x.1` and `_ y.0 y.1`.
fn apart(x: &(Operator, ScalarValue), y: &(Operator, ScalarValue)) -> bool {
    // Each as the least and greatest value it lets through, and whether
    // that end is let through itself.
    type End = Option<(ScalarValue, bool)>;
    let ends = |(op, v): &(Operator, ScalarValue)| -> (End, End) {
        match op {
            Operator::Eq => (Some((v.clone(), true)), Some((v.clone(), true))),
            Operator::Lt => (None, Some((v.clone(), false))),
            Operator::LtEq => (None, Some((v.clone(), true))),
            Operator::Gt => (Some((v.clone(), false)), None),
            _ => (Some((v.clone(), true)), None),
        }
    };
    let below = |hi: &End, lo: &End| match (hi, lo) {
        (Some((h, hin)), Some((l, lin))) => match h.partial_cmp(l) {
            Some(Ordering::Less) => true,
            Some(Ordering::Equal) => !(*hin && *lin),
            _ => false,
        },
        _ => false,
    };
    let ((xlo, xhi), (ylo, yhi)) = (ends(x), ends(y));
    below(&xhi, &ylo) || below(&yhi, &xlo)
}

/// The tables `ctx` draws on, by base table, each as often as it does.
pub(crate) fn bases(ctx: &Context) -> Vec<String> {
    let mut out: Vec<String> = ctx.tables().iter().map(|t| crate::observed::base_table(t).unwrap_or(t).to_string()).collect();
    out.sort();
    out
}

#[cfg(test)]
mod tests {
    use datafusion::prelude::{cast, col, lit};
    use datafusion::arrow::datatypes::DataType;

    use super::*;
    use crate::rows::terms;

    fn t(name: &str) -> Context {
        Context::table(name)
    }

    #[test]
    fn ranges_apart_contradict() {
        let date = |s: &str| cast(lit(s), DataType::Date32);
        let q04 = terms([col("orders.o_orderdate").gt_eq(date("1993-07-01")), col("orders.o_orderdate").lt(date("1993-10-01"))]);
        let later = terms([col("orders.o_orderdate").gt_eq(date("1995-01-01"))]);
        assert!(contradict(&q04, &later));
        assert!(!contradict(&q04, &terms([col("orders.o_orderdate").lt(date("1993-08-01"))])));
        // Touching ends meet only if both let the end through.
        let x = terms([col("t.a").lt_eq(lit(5))]);
        assert!(!contradict(&x, &terms([col("t.a").gt_eq(lit(5))])));
        assert!(contradict(&x, &terms([col("t.a").gt(lit(5))])));
        assert!(contradict(&terms([col("t.a").eq(lit(1))]), &terms([col("t.a").eq(lit(2))])));
        // Other columns, or literals of other types, say nothing.
        assert!(!contradict(&x, &terms([col("t.b").gt(lit(5))])));
        assert!(!contradict(&x, &terms([col("t.a").gt(lit(5.5))])));
    }

    #[test]
    fn disjoint_filters_split_their_input() {
        let mut space = Space::default();
        let orders = t("orders");
        let early = orders.filter(&terms([col("orders.o_orderdate").lt(lit(10))]));
        let late = orders.filter(&terms([col("orders.o_orderdate").gt(lit(20))]));
        for (c, v) in [(&orders, "n"), (&early, "x"), (&late, "y")] {
            space.add(FactKind::Cardinality(c.clone()), Int::new_const(v));
        }
        let relevant: BTreeSet<Context> = [orders, early, late].into();
        let axioms = disjoint(&space, &relevant);
        assert_eq!(axioms.len(), 1);
        assert_eq!(axioms[0].claim.to_string(), "(<= (+ x y) n)");
    }

    #[test]
    fn keys_of_a_join_stay_within_its_inputs() {
        let orders = t("orders");
        let joined = orders.cross(&t("customer")).unwrap().filter(&terms([col("orders.o_custkey").eq(col("customer.c_custkey"))]));
        assert!(joins(&joined, &orders));
        assert!(!joins(&orders, &joined));
        let key = |c: &Context| FactKind::Distinct { keys: terms([col("orders.o_orderkey")]), over: c.clone() };
        let mut space = Space::default();
        space.add(FactKind::Cardinality(orders.clone()), Int::new_const("n"));
        space.add(key(&joined), Int::new_const("k"));
        let relevant: BTreeSet<Context> = [orders, joined.clone()].into();
        let mut keys: BTreeMap<&Context, Vec<&FactKind>> = BTreeMap::new();
        let q = key(&joined);
        keys.entry(&joined).or_default().push(&q);
        let axioms: Vec<String> = wider(&space, &keys, &relevant).iter().map(|a| a.claim.to_string()).collect();
        assert_eq!(axioms, ["(<= k n)"]);
    }
}
