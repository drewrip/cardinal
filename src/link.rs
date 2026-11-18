//! Link: properties between rows that only their contexts relate.
//!
//! The [rules](crate::rules) apply [properties] where the
//! plan's shape makes the relationship plain: an operator and its input,
//! one op output, one table's origins. Link finds the rest: properties
//! between the rows of operators whose canonical [`Context`]s are equal or
//! contain one another, though no path of the plan relates them. Notation
//! as in [`crate::facts`](crate::facts#notation).
//!
//! ```text
//!  operators ──context──▶ Space: |C|, ndv(K | C), min, max ──finders──▶ Z3
//!                         of the relevant contexts
//! ```
//!
//! [`link_all`] gives each operator's rows its context, canonicalized, and
//! collects the quantities of those contexts in a [`Space`], each with the
//! terms (variables) that stand for it. Each finder below decides where a
//! property applies, and the property gives the claims. No quantifiers:
//! Rust decides where a property applies, Z3 does the arithmetic.
//!
//! # Soundness
//!
//! Each claim holds for any data (satisfying the declared keys) if its
//! premise does. The premises rest on:
//!
//! - equal canonical contexts being the same rows on every run: how plans
//!   name their rows (`rows::logical`, `facts::state`) and canonicalize
//!   the names (`rows::canonical`);
//! - `contain::subset`, `contain::fewer` and `joins` holding for any data;
//! - renamings of a table's instances (`contain::renamed_in`,
//!   `renamed_kind`) renaming keys with their contexts.
//!
//! Missing a case loses a claim, never adds a wrong one.
//!
//! # Scope: off one path
//!
//! Link relates the terms of nodes off one root-to-leaf path: of different
//! plans (the query, each subquery visited from an expression, each
//! reference plan's part) or of different branches of one. Along one path
//! the rules relate each node to its inputs, and so to all below it.
//! [`eq_context`] equates two terms of one quantity only off one path, and
//! every other finder picks terms not all on one path, or skips. But the
//! rules relate only one column's values along a path, never a
//! combination's: quantities of several keys (a grouping's rows) are
//! related on any path.
//!
//! This bears on tightness only: a claim left out never makes the
//! constraints unsound. It rests on the rules stating along one path what
//! link would. Two known exceptions: a `Filter(p)` over a `Filter(p)`, one
//! context of which the rules give only `X ≤ l`; and `implied` or
//! `failing` with every context on one join path.
//!
//! # Finders
//!
//! | Finder | Property | Rule name |
//! |---|---|---|
//! | [`eq_context`] | [`same`](properties::same), one pair per quantity | `eq context` |
//! | [`subset_context`] | [`within`](properties::within), [`same_if_as_many`](properties::same_if_as_many) | `subset` |
//! | [`fewer`] | [`fewer`](properties::fewer) | `fewer` |
//! | [`failing`] | [`failing`](properties::failing) | `failing rows` |
//! | [`implied`] | [`implied`](properties::implied) | `implied` |
//! | [`split`] | [`split`](properties::split) | `semi and anti` |
//! | [`fewer_keys`] | [`fewer_keys`](properties::fewer_keys) | `fewer keys` |
//! | [`wider_context`] | [`values_of_rows`](properties::values_of_rows), [`within`](properties::within) | `wider rows` |
//! | [`disjoint_context`] | [`disjoint`](properties::disjoint) | `disjoint` |
//!
//! ## Relevant contexts
//!
//! Only contexts near the operators' are related. Starting from the
//! contexts of the operators' rows, add each context two contexts relate to (one
//! is ⊆ or has fewer rows than the other, or both are SPJs with the same
//! inputs and conditions) among those over the same base tables, twice;
//! then each context any of these [joins](#relations-between-contexts).
//!
//! ## Relations between contexts
//!
//! Each test holds up to renaming the instances of one table among
//! themselves (`t@1`, `t@2`), by `rows::contain`.
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
//! # Known gaps
//!
//! `contain::apart` orders strings by their bytes, which is sound only for
//! byte-order collations. Only plans or facts from engines with other
//! collations reach it.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use datafusion::common::ScalarValue;
use datafusion::logical_expr::{Expr, Operator};

use z3::ast::{Bool, Int};

use crate::analysis::{Analyzer, Ancestors, Node};
use crate::facts::FactKind;
use crate::rows::canonical::Canonicals;
use crate::rows::contain::{self, renamed_kind};
use crate::rows::logical::Logical;
use crate::rows::rewrite::Spj;
use crate::rows::{Context, Exists, ExistsKind, Term, bases};
use crate::properties::{self, Pair};

/// Asserts every property link finds between the rows of `a`'s operators,
/// once its rules have visited every plan: each operator's rows given the
/// context facts give them, among the
/// [relevant contexts](self#relevant-contexts).
pub fn link_all(a: &Analyzer) {
    let scans: Vec<(String, String)> = a.scans.iter().map(|(s, t, _)| (s.clone(), t.clone())).collect();
    let logical = Logical::new(&a.nodes, &scans);
    let mut space = Space { ancestors: a.ancestors(), ..Space::default() };
    let seeds = add_nodes(&mut space, &a.nodes, &logical);
    let relevant = space.relevant(&seeds);
    for p in space.applied(&relevant) {
        a.assert_property(p.rule, p.claims);
    }
}

/// Adds the quantities of `nodes`' rows, named by `logical`, to `space`.
/// Returns the contexts of the nodes' rows.
fn add_nodes(space: &mut Space, nodes: &[Node], logical: &Logical) -> BTreeSet<Context> {
    let mut contexts = BTreeSet::new();
    let mut canonicals = Canonicals::default();
    for (i, node) in nodes.iter().enumerate() {
        let mut add = |space: &mut Space, q: FactKind, var: &str, contexts: &mut BTreeSet<Context>| {
            let q = q.canonical_in(&mut canonicals);
            contexts.insert(over(&q).clone());
            space.add(q, Int::new_const(var), i);
        };
        let schema = node.plan.schema();
        // A column `j` of the rows, if it is a column of a table and not a
        // float: the constraints count a float's values by bits, facts by
        // SQL equality.
        let column = |j: usize| -> Option<Term> {
            let Some(Some(e @ Expr::Column(_))) = logical.lineage[i].get(j) else { return None };
            (j < schema.fields().len() && !schema.field(j).data_type().is_floating()).then(|| Term::new(e.clone()))
        };
        let mut rows = vec![];
        if let (Some(raw), Some(instance)) = (&node.raw_scan, &logical.instances[i]) {
            rows.push((Context::table(instance), &raw.var, &raw.ndv_vars, &raw.min_vars, &raw.max_vars));
        }
        if let Ok(ctx) = &logical.contexts[i] {
            rows.push((ctx.clone(), &node.var, &node.ndv_vars, &node.min_vars, &node.max_vars));
            // A grouping's rows are its keys' distinct values.
            if let Context::Derived { op, args, inputs } = ctx
                && op == "group"
            {
                let keys = args.iter().cloned().collect();
                add(space, FactKind::Distinct { keys, over: inputs[0].clone() }, &node.var, &mut contexts);
            }
        }
        for (ctx, card, ndvs, mins, maxs) in rows {
            add(space, FactKind::Cardinality(ctx.clone()), card, &mut contexts);
            for (j, ndv) in ndvs.iter().enumerate() {
                if let Some(key) = column(j) {
                    add(space, FactKind::Distinct { keys: [key].into(), over: ctx.clone() }, ndv, &mut contexts);
                }
            }
            for (j, (lo, hi)) in mins.iter().zip(maxs).enumerate() {
                let Some(key) = column(j) else { continue };
                if let Some(lo) = lo {
                    add(space, FactKind::Min { key: key.clone(), over: ctx.clone() }, lo, &mut contexts);
                }
                if let Some(hi) = hi {
                    add(space, FactKind::Max { key, over: ctx.clone() }, hi, &mut contexts);
                }
            }
        }
    }
    contexts
}

/// The claims of a property where a finder found it applies, and the
/// finder's rule name.
pub struct Applied {
    pub rule: &'static str,
    pub claims: Vec<Bool>,
}

impl Applied {
    fn new(rule: &'static str, claims: Vec<Bool>) -> Applied {
        Applied { rule, claims }
    }
}

/// The quantities of contexts (`|C|`, `ndv(K | C)`, `min`, `max`), each
/// with the Z3 terms it equals: the variables of the operators whose rows
/// it is of, with their nodes.
#[derive(Default)]
pub struct Space {
    terms: BTreeMap<FactKind, Vec<(Int, usize)>>,
    /// Which nodes are on one path ([scope](self#scope-off-one-path)).
    ancestors: Ancestors,
    /// The canonical forms of the parts of contexts renamed to relate
    /// them ([`contain::candidates`]).
    canonicals: RefCell<Canonicals>,
}

impl Space {
    /// `a ⊆ b`, up to renaming `a`'s instances
    /// ([relations](self#relations-between-contexts)).
    fn subset(&self, a: &Context, b: &Context) -> bool {
        self.renamed(a, b, contain::subset)
    }

    /// `fewer(a, b)`, up to renaming.
    fn fewer(&self, a: &Context, b: &Context) -> bool {
        self.renamed(a, b, contain::fewer)
    }

    /// True if `a` and `b` name rows one bounds the other's: either has
    /// fewer than the other, or is the other with other predicates.
    fn related(&self, a: &Context, b: &Context) -> bool {
        self.fewer(a, b) || self.fewer(b, a) || self.renamed(a, b, same_inputs)
    }

    /// `test(a, b)` up to renaming `a`'s instances ([`contain::renamed_in`]).
    fn renamed(&self, a: &Context, b: &Context, test: impl Fn(&Context, &Context) -> bool) -> bool {
        contain::renamed_in(a, b, test, &mut self.canonicals.borrow_mut())
    }

    /// Records that `term`, of node `node`, equals quantity `q`, a
    /// canonical kind.
    fn add(&mut self, q: FactKind, term: Int, node: usize) {
        let terms = self.terms.entry(q).or_default();
        if !terms.iter().any(|(t, _)| *t == term) {
            terms.push((term, node));
        }
    }

    /// True if a term stands for `|c|`.
    fn has_card(&self, c: &Context) -> bool {
        self.terms.contains_key(&card(c))
    }

    /// A term for each of `qs`, whose nodes are not all on one path: the
    /// first of each, but for two quantities whose terms are off one path.
    /// `None` if a quantity has no term, or every choice is on one path:
    /// the rules relate those ([scope](self#scope-off-one-path)). Any
    /// choice if one is of several keys.
    fn off_path(&self, qs: &[&FactKind]) -> Option<Vec<&Int>> {
        let terms: Vec<&Vec<(Int, usize)>> = qs.iter().map(|q| self.terms.get(*q)).collect::<Option<_>>()?;
        if qs.iter().any(|q| width(q) > 1) {
            return Some(terms.iter().map(|t| &t[0].0).collect());
        }
        for i in 0..terms.len() {
            for j in i + 1..terms.len() {
                for (a, m) in terms[i] {
                    if let Some((b, _)) = terms[j].iter().find(|(_, n)| !self.ancestors.on_one_path(*m, *n)) {
                        let mut out: Vec<&Int> = terms.iter().map(|t| &t[0].0).collect();
                        (out[i], out[j]) = (a, b);
                        return Some(out);
                    }
                }
            }
        }
        None
    }

    /// [`Self::off_path`] of two quantities.
    fn off_path2(&self, a: &FactKind, b: &FactKind) -> Option<(&Int, &Int)> {
        self.off_path(&[a, b]).map(|t| (t[0], t[1]))
    }

    /// The [relevant contexts](self#relevant-contexts): `seeds`, those
    /// related to one ([`Self::related`]), those related to one of them,
    /// and those any of these is a join of ([`joins`]).
    fn relevant(&self, seeds: &BTreeSet<Context>) -> BTreeSet<Context> {
        let buckets = self.buckets();
        let mut out: BTreeSet<Context> = seeds.clone();
        let mut frontier: Vec<Context> = seeds.iter().cloned().collect();
        for _ in 0..2 {
            let mut next = vec![];
            for a in &frontier {
                for b in buckets.get(&bases(a)).into_iter().flatten() {
                    if !out.contains(*b) && self.related(a, b) {
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

    /// Every property the finders apply over the quantities of `relevant`
    /// contexts.
    fn applied(&self, relevant: &BTreeSet<Context>) -> Vec<Applied> {
        // Each relevant context's key quantities.
        let mut keys: BTreeMap<&Context, Vec<&FactKind>> = BTreeMap::new();
        for q in self.terms.keys() {
            if relevant.contains(over(q)) && !matches!(q, FactKind::Cardinality(_)) {
                keys.entry(over(q)).or_default().push(q);
            }
        }
        let mut out = eq_context(self, relevant);
        let buckets = self.buckets();
        for a in relevant {
            if !self.has_card(a) {
                continue;
            }
            for b in buckets.get(&bases(a)).into_iter().flatten().filter(|b| relevant.contains(**b) && **b != a) {
                if self.subset(a, b) {
                    out.extend(subset_context(self, &keys, a, b));
                    out.extend(failing(self, relevant, a, b));
                } else {
                    out.extend(fewer(self, a, b));
                }
            }
            out.extend(split(self, a));
            out.extend(fewer_keys(self, &keys, a));
        }
        out.extend(implied(self, relevant));
        out.extend(wider_context(self, &keys, relevant));
        out.extend(disjoint_context(self, relevant));
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
fn over(q: &FactKind) -> &Context {
    q.over()
}

/// `|c|`.
fn card(c: &Context) -> FactKind {
    FactKind::Cardinality(c.clone())
}

/// `eq context`, between the terms of one quantity.
///
/// - **Claim**: `t = t'` for two terms of one quantity, of nodes off one
///   path. The terms fall in chains of nodes on one path, which the rules
///   relate; each chain but the first gets one claim, joining it to the
///   first. Every term of a quantity of several keys is its own chain.
/// - **Why**: they count the same rows, of one context.
pub fn eq_context(space: &Space, relevant: &BTreeSet<Context>) -> Vec<Applied> {
    let mut out = vec![];
    for (q, terms) in space.terms.iter().filter(|(q, _)| relevant.contains(over(q))) {
        let on_path = |a: usize, b: usize| width(q) == 1 && space.ancestors.on_one_path(a, b);
        let mut chains: Vec<Vec<&(Int, usize)>> = vec![];
        for t in terms {
            match chains.iter_mut().find(|c| c.iter().all(|u| on_path(t.1, u.1))) {
                Some(c) => c.push(t),
                None => chains.push(vec![t]),
            }
        }
        for c in chains.iter().skip(1) {
            // Off one path from some term of the first chain, as it could
            // not join it.
            let (t, u) = (c[0], chains[0].iter().find(|u| !on_path(c[0].1, u.1)).unwrap());
            out.push(Applied::new("eq context", properties::same(&[pair(q, &t.0, &u.0)])));
        }
    }
    out
}

/// Terms `a` and `b` of the kind of quantity `q` is.
fn pair<'a>(q: &FactKind, a: &'a Int, b: &'a Int) -> Pair<'a> {
    match q {
        FactKind::Cardinality(_) => Pair::Card(a, b),
        FactKind::Min { .. } => Pair::Min(a, b),
        FactKind::Max { .. } => Pair::Max(a, b),
        _ => Pair::Ndv(a, b),
    }
}

/// `subset`, for `A ⊆ B` ([relations](self#relations-between-contexts)),
/// with `keys` each context's key quantities.
///
/// - **Claim**: for `A ⊆ B`, `A ≠ B`: `|A| ≤ |B|`; `ndv(K | A) ≤ ndv(K' |
///   B)` for `K ⊆ K'`; `min(k | A) ≥ min(k | B)`; `max(k | A) ≤ max(k |
///   B)`. And `|A| = |B| ⇒` each key quantity of `A` equals `B`'s of the
///   same keys.
/// - **Why**: fewer rows have fewer values, within the same range; as many
///   are the same rows.
pub fn subset_context(space: &Space, keys: &BTreeMap<&Context, Vec<&FactKind>>, a: &Context, b: &Context) -> Vec<Applied> {
    let (ca, cb) = (card(a), card(b));
    if !space.has_card(a) || !space.has_card(b) {
        return vec![];
    }
    // Each key of `a` that is one of `b`'s, over rows among `b`'s, and the
    // same once there are as many rows.
    let (mut within, mut same) = (vec![(&ca, &cb)], vec![]);
    for qa in keys.get(a).into_iter().flatten() {
        for qb in keys.get(b).into_iter().flatten() {
            if renamed_kind(qa, qb, key_within) {
                within.push((*qa, *qb));
                if width(qa) == width(qb) {
                    same.push((*qa, *qb));
                }
            }
        }
    }
    let within: Vec<Pair> =
        within.iter().filter_map(|(qa, qb)| space.off_path2(qa, qb).map(|(ta, tb)| pair(qa, ta, tb))).collect();
    let mut out = vec![Applied::new("subset", properties::within(&within))];
    let qs: Vec<&FactKind> = [&ca, &cb].into_iter().chain(same.iter().flat_map(|(qa, qb)| [*qa, *qb])).collect();
    if let (false, Some(t)) = (same.is_empty(), space.off_path(&qs)) {
        let same: Vec<Pair> = same.iter().enumerate().map(|(k, (qa, _))| pair(qa, t[2 + 2 * k], t[3 + 2 * k])).collect();
        out.push(Applied::new("subset", properties::same_if_as_many(t[0], t[1], &same)));
    }
    out
}

/// `fewer`, for `fewer(A, B)` ([relations](self#relations-between-contexts)).
///
/// - **Claim**: `|A| ≤ |B|` for `fewer(A, B)` but not `A ⊆ B`.
/// - **Why**: an outer join emits each preserved row once per partner or
///   once padded, so narrowing an input never adds rows. Its rows need not
///   be among the other's (a row may lose its partner and be padded), so
///   nothing is said of their values.
pub fn fewer(space: &Space, a: &Context, b: &Context) -> Vec<Applied> {
    match space.off_path2(&card(a), &card(b)) {
        Some((ca, cb)) if space.fewer(a, b) => vec![Applied::new("fewer", properties::fewer(ca, cb))],
        _ => vec![],
    }
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
            ka.is_subset(kb) && contain::subset(oa, ob)
        }
        (FactKind::Min { key: ka, over: oa }, FactKind::Min { key: kb, over: ob })
        | (FactKind::Max { key: ka, over: oa }, FactKind::Max { key: kb, over: ob }) => ka == kb && contain::subset(oa, ob),
        _ => false,
    }
}

/// `failing rows`, for `d ⊆ c`.
///
/// - **Claim**: `|D| − |D ∧ P| ≤ |C| − |C ∧ P|`.
/// - **When**: `D ⊆ C` as named, `C` an SPJ, `C ∧ P` a relevant SPJ with
///   `C`'s inputs and conditions, and `D ∧ P ≠ D`.
/// - **Why**: `D`'s rows failing `P` are among `C`'s.
///
/// ```text
/// D = orders ∧ o_status = 'F' ⊆ C = orders, P = {o_price > 100}
/// ⇒ |D| − |D ∧ P| ≤ |orders| − |orders ∧ P|
/// ```
pub fn failing(space: &Space, relevant: &BTreeSet<Context>, d: &Context, c: &Context) -> Vec<Applied> {
    let (Context::Spj { preds: pc, .. }, true) = (c, space.has_card(d) && space.has_card(c) && contain::subset(d, c)) else {
        return vec![];
    };
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
        if let Some(t) = space.off_path(&[&card(d), &card(&dp), &card(c), &card(cp)]) {
            out.push(Applied::new("failing rows", properties::failing(t[0], t[1], t[2], t[3])));
        }
    }
    out
}

/// `implied`.
///
/// - **Claim**: `|C ∧ P| = |C| ⇒ |D ∧ P| = |D|`.
/// - **When**: `C` an SPJ, `C ∧ P` a relevant SPJ with `C`'s inputs and
///   conditions, `D` joins `C` and does not already have all of `P`.
///   Contexts over the same inputs are left to [`failing`].
/// - **Why**: if every row of `C` satisfies `P`, so does every row of `D`,
///   which is, on `C`'s inputs, a row of `C`.
///
/// ```text
/// C = lineitem, P = {l_quantity >= 1}, D = lineitem ⋈ orders
/// ⇒ |lineitem ∧ P| = |lineitem| ⇒ |D ∧ P| = |D|
/// ```
pub fn implied(space: &Space, relevant: &BTreeSet<Context>) -> Vec<Applied> {
    let mut out = vec![];
    for c in relevant {
        let (Context::Spj { preds: pc, .. }, true) = (c, space.has_card(c)) else { continue };
        for cp in relevant {
            let Context::Spj { preds, .. } = cp else { continue };
            if cp == c || !same_inputs(cp, c) || !preds.is_superset(pc) {
                continue;
            }
            if !space.has_card(cp) {
                continue;
            }
            let p: BTreeSet<_> = preds.difference(pc).cloned().collect();
            for d in relevant {
                let Context::Spj { preds: pd, .. } = d else { continue };
                if !joins(d, c) || pd.is_superset(&p) {
                    continue;
                }
                let dp = d.filter(&p).canonical();
                if let Some(t) = space.off_path(&[&card(c), &card(cp), &card(d), &card(&dp)]) {
                    out.push(Applied::new("implied", properties::implied(t[0], t[1], t[2], t[3])));
                }
            }
        }
    }
    out
}

/// `semi and anti`, for `s` with a semi join condition.
///
/// - **Claim**: `|K ⋉ O| + |K ▷ O| = |K|`, for `K ⋉ O` an SPJ with a semi
///   condition, `K` it without it, and `K ▷ O` it with the anti condition
///   on the same `on` and `O` instead.
/// - **Why**: each row of `K` has a partner or has none.
pub fn split(space: &Space, s: &Context) -> Vec<Applied> {
    let (Context::Spj { tables, atoms, preds, exists }, true) = (s, space.has_card(s)) else { return vec![] };
    let mut out = vec![];
    for e in exists.iter().filter(|e| e.kind == ExistsKind::Semi) {
        let mut rest = exists.clone();
        rest.remove(e);
        let spj = |exists: BTreeSet<Exists>| Spj { tables: tables.clone(), atoms: atoms.clone(), preds: preds.clone(), exists }.build();
        let kept = spj(rest.clone()).canonical();
        let mut with_anti = rest;
        with_anti.insert(Exists { kind: ExistsKind::Anti, on: e.on.clone(), other: e.other.clone() });
        let anti = spj(with_anti).canonical();
        if let Some(t) = space.off_path(&[&card(s), &card(&anti), &card(&kept)]) {
            out.push(Applied::new("semi and anti", properties::split(t[0], t[1], t[2])));
        }
    }
    out
}

/// How many keys `q` is of.
fn width(q: &FactKind) -> usize {
    match q {
        FactKind::Distinct { keys, .. } => keys.len(),
        _ => 1,
    }
}

/// `fewer keys`, over `c`, with `keys` each context's key quantities.
///
/// - **Claim**: `ndv(K | C) ≤ ndv(K' | C)` for `K ⊊ K'`.
/// - **Why**: fewer keys have no more combinations.
pub fn fewer_keys(space: &Space, keys: &BTreeMap<&Context, Vec<&FactKind>>, c: &Context) -> Vec<Applied> {
    let mut out = vec![];
    for qa in keys.get(c).into_iter().flatten() {
        let FactKind::Distinct { keys: ka, .. } = qa else { continue };
        for qb in keys.get(c).into_iter().flatten() {
            let FactKind::Distinct { keys: kb, .. } = qb else { continue };
            if let (true, Some((ta, tb))) = (ka.len() < kb.len() && ka.is_subset(kb), space.off_path2(qa, qb)) {
                out.push(Applied::new("fewer keys", properties::fewer_keys(ta, tb)));
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

/// `wider rows`, with `keys` each context's key quantities.
///
/// - **Claim**: for `D` joining `C`, and keys `K` (or `k`) whose columns are
///   all of `C`'s tables: `ndv(K | D) ≤ |C|`; `ndv(K | D) ≤ ndv(K' | C)` for
///   `K ⊆ K'`; `min(k | D) ≥ min(k | C)`; `max(k | D) ≤ max(k | C)`.
/// - **Why**: each row of `D` holds a row of `C`, so `C`'s columns take in
///   `D` only values they take in `C`.
///
/// ```text
/// D = orders ⋈ lineitem on o_orderkey = l_orderkey
/// ⇒ ndv(o_custkey | D) ≤ ndv(o_custkey | orders) and ≤ |orders|
/// ```
pub fn wider_context(space: &Space, keys: &BTreeMap<&Context, Vec<&FactKind>>, relevant: &BTreeSet<Context>) -> Vec<Applied> {
    let mut out = vec![];
    for d in relevant {
        let Some(qds) = keys.get(d) else { continue };
        for c in relevant {
            let Context::Spj { tables: tc, .. } = c else { continue };
            if !joins(d, c) {
                continue;
            }
            for qd in qds {
                match qd {
                    FactKind::Distinct { keys: kd, .. } if of_tables(kd, tc) => {
                        if let Some((td, n)) = space.off_path2(qd, &card(c)) {
                            out.push(Applied::new("wider rows", properties::values_of_rows(td, n)));
                        }
                        for qc in keys.get(c).into_iter().flatten() {
                            if let FactKind::Distinct { keys: kc, .. } = qc
                                && kd.is_subset(kc)
                                && let Some((td, tc)) = space.off_path2(qd, qc)
                            {
                                out.push(Applied::new("wider rows", properties::within(&[Pair::Ndv(td, tc)])));
                            }
                        }
                    }
                    FactKind::Min { key, .. } | FactKind::Max { key, .. } if of_tables(&[key.clone()].into(), tc) => {
                        let at_c = match qd {
                            FactKind::Min { .. } => FactKind::Min { key: key.clone(), over: c.clone() },
                            _ => FactKind::Max { key: key.clone(), over: c.clone() },
                        };
                        if let Some((td, tc)) = space.off_path2(qd, &at_c) {
                            out.push(Applied::new("wider rows", properties::within(&[pair(qd, td, tc)])));
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    out
}

/// `disjoint`, between contexts. [`Analyzer::disjoint_origins`] finds it
/// between op outputs of one table.
///
/// - **Claim**: rows that no row satisfies the conditions of both are apart
///   among any rows holding both: `|X| + |Y| ≤ |Z|`.
/// - **When**: `X`, `Y` and `Z` are SPJs with the same inputs and
///   conditions; `X` and `Y` compare some expression with literals in
///   ranges that do not meet (values of different types are taken to
///   meet); `Z`'s predicates are among both's, and no such `Z` has more.
///
/// ```text
/// |orders ∧ o_orderdate < 10| + |orders ∧ o_orderdate > 20| ≤ |orders|
/// ```
pub fn disjoint_context(space: &Space, relevant: &BTreeSet<Context>) -> Vec<Applied> {
    let mut groups: BTreeMap<_, Vec<(&BTreeSet<Term>, FactKind)>> = BTreeMap::new();
    for c in relevant {
        if let (Context::Spj { tables, atoms, preds, exists }, true) = (c, space.has_card(c)) {
            groups.entry((tables, atoms, exists)).or_default().push((preds, card(c)));
        }
    }
    let mut out = vec![];
    for group in groups.values() {
        for (i, (px, x)) in group.iter().enumerate() {
            for (py, y) in &group[i + 1..] {
                if !contradict(px, py) {
                    continue;
                }
                let within: Vec<&(&BTreeSet<Term>, FactKind)> =
                    group.iter().filter(|(pz, _)| pz.is_subset(px) && pz.is_subset(py)).collect();
                for (pz, z) in &within {
                    if within.iter().any(|(pw, _)| pw.len() > pz.len() && pw.is_superset(pz)) {
                        continue;
                    }
                    if let Some(t) = space.off_path(&[x, y, z]) {
                        out.push(Applied::new("disjoint", properties::disjoint(&[t[0], t[1]], t[2])));
                    }
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
            if let Some((e, op, v)) = contain::comparison(&p.expr) {
                out.entry(e.to_string()).or_default().push((op, v));
            }
        }
        out
    };
    let (ra, rb) = (ranges(a), ranges(b));
    ra.iter().any(|(e, xs)| rb.get(e).is_some_and(|ys| xs.iter().any(|x| ys.iter().any(|y| contain::apart(x, y)))))
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
        for (node, (c, v)) in [(&orders, "n"), (&early, "x"), (&late, "y")].into_iter().enumerate() {
            space.add(card(c), Int::new_const(v), node);
        }
        let relevant: BTreeSet<Context> = [orders, early, late].into();
        let applied = disjoint_context(&space, &relevant);
        assert_eq!(applied.len(), 1);
        assert_eq!(applied[0].claims[0].to_string(), "(<= (+ x y) n)");
    }

    #[test]
    fn keys_of_a_join_stay_within_its_inputs() {
        let orders = t("orders");
        let joined = orders.cross(&t("customer")).unwrap().filter(&terms([col("orders.o_custkey").eq(col("customer.c_custkey"))]));
        assert!(joins(&joined, &orders));
        assert!(!joins(&orders, &joined));
        let key = |c: &Context| FactKind::Distinct { keys: terms([col("orders.o_orderkey")]), over: c.clone() };
        let mut space = Space::default();
        space.add(card(&orders), Int::new_const("n"), 0);
        space.add(key(&joined), Int::new_const("k"), 1);
        let relevant: BTreeSet<Context> = [orders, joined.clone()].into();
        let mut keys: BTreeMap<&Context, Vec<&FactKind>> = BTreeMap::new();
        let q = key(&joined);
        keys.entry(&joined).or_default().push(&q);
        let claims: Vec<String> = wider_context(&space, &keys, &relevant).iter().flat_map(|a| &a.claims).map(|c| c.to_string()).collect();
        assert_eq!(claims, ["(<= k n)"]);
    }

    #[test]
    fn terms_on_one_path_are_left_to_the_rules() {
        // Node 1 is above node 0; node 2 is in another plan.
        let ancestors = Ancestors(vec![vec![false, true, false], vec![false; 3], vec![false; 3]]);
        let mut space = Space { ancestors, ..Space::default() };
        let (orders, early) = (t("orders"), t("orders").filter(&terms([col("orders.o_orderdate").lt(lit(10))])));
        for (node, v) in ["a", "b", "c"].into_iter().enumerate() {
            space.add(card(&orders), Int::new_const(v), node);
        }
        let relevant: BTreeSet<Context> = [orders.clone(), early.clone()].into();
        let claims = |applied: Vec<Applied>| -> Vec<String> {
            applied.iter().flat_map(|a| &a.claims).map(|c| c.to_string()).collect()
        };
        assert_eq!(claims(eq_context(&space, &relevant)), ["(= c a)"]);
        // The filter's rows are node 0's: only another plan's relates them.
        space.add(card(&early), Int::new_const("x"), 0);
        assert_eq!(claims(subset_context(&space, &BTreeMap::new(), &early, &orders)), ["(<= x c)"]);
        // A grouping's rows, of several keys, are related on any path: here
        // grouped at node 1 over a join at node 0.
        let joined = orders.cross(&t("customer")).unwrap().filter(&terms([col("orders.o_custkey").eq(col("customer.c_custkey"))]));
        let group = FactKind::Distinct { keys: terms([col("orders.o_orderkey"), col("orders.o_custkey")]), over: joined.clone() };
        space.add(group.clone(), Int::new_const("g"), 1);
        let keys: BTreeMap<&Context, Vec<&FactKind>> = [(&joined, vec![&group])].into();
        let relevant: BTreeSet<Context> = [orders, joined.clone()].into();
        assert_eq!(claims(wider_context(&space, &keys, &relevant)), ["(<= g a)"]);
    }
}
