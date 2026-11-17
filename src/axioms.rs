//! Axioms: what holds of any data, relating the quantities of rows.
//!
//! A rule ([`crate::rules`]) relates one operator to its inputs. An axiom
//! holds of rows whatever operator made them: rows among another's are
//! fewer, two filters that cannot both hold split their input. Notation as
//! in [`crate::facts`](crate::facts#notation).
//!
//! # Spec
//!
//! - **Input**: what the [rules](crate::rules) recorded as they visited the
//!   plan: each relation, with its rows, `ndv`, `min` and `max` variables
//!   and the value domains, keys and origin found of its rows; the nodes;
//!   and the declared keys.
//! - **Output**: ground Z3 assertions, each tagged by its axiom: a trace
//!   names the function that asserted it, or the axiom's name, and the node
//!   it is about. No quantifiers: Rust decides where an axiom applies, Z3
//!   does the arithmetic.
//! - **Guarantees**: each axiom holds for any data; a schema axiom for any
//!   data satisfying the declared keys. The tests deciding where an
//!   axiom applies are conservative: missing a case loses an axiom, never
//!   adds a wrong one.
//! - **Not done**: contexts outside the relevant set are not related.
//!
//! [`assert_all`] asserts every axiom, once the rules are done, before any
//! fact. They are grouped by what they range over.
//!
//! # Axioms on each scan
//!
//! One method of [`Analyzer`] each:
//!
//! | Axiom | Claim |
//! |---|---|
//! | `composite key` | [`Analyzer::composite_key`] |
//! | `referenced size` | [`Analyzer::referenced_size`], with reference plans ([`crate::joint`]) only |
//!
//! # Axioms on one table's rows
//!
//! | Axiom | Claim |
//! |---|---|
//! | `disjoint` | [`Analyzer::disjoint`] |
//!
//! # Axioms between contexts
//!
//! [`Analyzer::between_contexts`] gives each operator's rows its
//! [`Context`], canonicalized, and collects the quantities of those
//! contexts in a [`Space`]. The functions below relate them, wherever terms
//! for them exist, and each [`Axiom`] carries its name.
//!
//! ```text
//!  operators ──context──▶ Space: |C|, ndv(K | C), min, max ──axioms──▶ Z3
//!                         of the relevant contexts
//! ```
//!
//! | Axiom | Claim |
//! |---|---|
//! | `same rows` | [`same_rows`], [`subset`] |
//! | `subset` | [`subset`] |
//! | `fewer` | [`fewer`] |
//! | `failing rows` | [`failing`] |
//! | `implied` | [`implied`] |
//! | `semi and anti` | [`split`] |
//! | `fewer keys` | [`fewer_keys`] |
//! | `wider rows` | [`wider`] |
//! | `disjoint` | [`disjoint`] |
//!
//! ## Relevant contexts
//!
//! Only contexts near the query's are related. Starting from the contexts
//! of the query's operators, add each context two contexts relate to (one
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

use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::{BTreeMap, BTreeSet, HashMap};

use datafusion::common::{Constraint, ScalarValue};
use datafusion::logical_expr::logical_plan::TableScan;
use datafusion::logical_expr::{Expr, Operator};

use z3::ast::Int;

use crate::builder::bare_kind;
use crate::analysis::{Analyzer, Node, Rel, ScanKind, product};
use crate::facts::FactKind;
use crate::origin::{self, Origin};
use crate::rows::canonical::Canonicals;
use crate::rows::contain::{self, renamed_kind};
use crate::rows::logical::Logical;
use crate::rows::rewrite::Spj;
use crate::rows::{Context, Exists, ExistsKind, Term};
use crate::properties::{self, Claim, Pair};

/// [Axioms on each scan](self#axioms-on-each-scan) and on
/// [one table's rows](self#axioms-on-one-tables-rows), one function each, so
/// a trace names the axiom a constraint is from.
impl<'a> Analyzer<'a> {
    /// Creates the size variable of each table `scan`'s table references by
    /// a foreign key, scanned or not, for [`Self::referenced_size`].
    fn referenced_tables(&mut self, scan: &TableScan) {
        let ScanKind::Base { display, .. } = (self.resolve)(scan) else { return };
        let refs: Vec<String> =
            self.foreign_keys.iter().filter(|fk| fk.table == display).map(|fk| fk.references.clone()).collect();
        for t in refs {
            if let ScanKind::Base { key, display } = bare_kind(&t) {
                self.table(&key, &display);
            }
        }
    }

    /// `referenced size`.
    ///
    /// - **Claim**: `ndv(c | R) ≤ |S|` for each column `c` of a foreign key
    ///   `R(cols) → S`, on a scan of `R`.
    /// - **When**: the analysis has reference plans ([`crate::joint`]);
    ///   `S` need not be scanned. Not on a float column.
    /// - **Why**: each row's `cols` equal the key of one row of `S`, so
    ///   they take at most `|S|` combinations, and one column no more.
    pub fn referenced_size(&self, scan: &TableScan, rel: &Rel) {
        let ScanKind::Base { display, .. } = (self.resolve)(scan) else { return };
        let schema = &scan.projected_schema;
        for fk in self.foreign_keys.iter().filter(|fk| fk.table == display) {
            let ScanKind::Base { key, .. } = bare_kind(&fk.references) else { continue };
            let Some(t) = self.tables.get(&key) else { continue };
            for c in &fk.columns {
                if let Some(j) = schema.fields().iter().position(|f| f.name() == c)
                    && !schema.field(j).data_type().is_floating()
                {
                    self.assert(rel.ndv[j].le(&t.var));
                }
            }
        }
    }

    /// `composite key`.
    ///
    /// - **Claim**: `|T| ≤ Π ndv` of a composite primary key's columns, or
    ///   of a composite UNIQUE constraint's on NOT NULL columns.
    /// - **Why**: each row has its own combination of key values.
    pub fn composite_key(&self, scan: &TableScan, rel: &Rel) {
        let Some(constraints) = scan.source.constraints() else {
            return;
        };
        let schema = scan.source.schema();
        for c in constraints.iter() {
            let pk = match c {
                Constraint::PrimaryKey(pk) => pk,
                Constraint::Unique(u) if u.iter().all(|i| !schema.field(*i).is_nullable()) => u,
                Constraint::Unique(_) => continue,
            };
            if pk.len() < 2 {
                continue;
            }
            let positions: Option<Vec<usize>> = pk
                .iter()
                .map(|src| match &scan.projection {
                    None => Some(*src),
                    Some(proj) => proj.iter().position(|p| p == src),
                })
                .collect();
            if let Some(positions) = positions {
                let factors: Vec<&Int> = positions.iter().map(|i| &rel.ndv[*i]).collect();
                if let Some(p) = product(&factors, self.max_product) {
                    self.assert(rel.card.le(p));
                }
            }
        }
    }

    /// `disjoint`, between relations. [`disjoint`](fn@disjoint) finds it
    /// between contexts.
    ///
    /// - **Claim**: relations whose rows no row of the table is in both of
    ///   are apart: `|X| + |Y| ≤ |T|`.
    /// - **When**: relations made of distinct rows of one stored table `T`,
    ///   reached through operators that never repeat a row (filter,
    ///   projection, sort, limit, distinct, semi and anti joins), whose value
    ///   domains on some column do not meet. Relations with the same domains
    ///   form a class bounded by one variable, and each set of pairwise
    ///   disjoint classes sums to at most `|T|`; at most 64 classes per
    ///   table.
    ///
    /// ```text
    /// |orders ∧ o_orderdate < 10| + |orders ∧ o_orderdate > 20| ≤ |orders|
    /// ```
    pub fn disjoint(&mut self) {
        // Nodes' outputs of distinct rows of one stored table, in node order.
        let mut of: Vec<(usize, Int, Origin)> = self
            .relations
            .iter()
            .filter_map(|r| {
                let o = r.rel.origin.as_ref().filter(|o| o.informative())?;
                Some((r.node?, r.rel.card.clone(), o.clone()))
            })
            .collect();
        of.sort_by_key(|(node, _, _)| *node);
        let (cards, origins): (Vec<Int>, Vec<Origin>) = of.into_iter().map(|(_, c, o)| (c, o)).unzip();
        let (classes, cliques) = origin::disjoint_classes(&origins, 64);
        let mut part: HashMap<usize, Int> = HashMap::new();
        for clique in cliques {
            let table = self.tables[&origins[classes[clique[0]][0]].table].var.clone();
            let mut sum = vec![];
            for c in clique {
                let v = match part.entry(c) {
                    Entry::Occupied(e) => e.get().clone(),
                    Entry::Vacant(e) => {
                        let v = self.new_var(format!("part{c}"));
                        for &m in &classes[c] {
                            self.assert(cards[m].le(&v));
                        }
                        self.assert(v.le(&table));
                        e.insert(v).clone()
                    }
                };
                sum.push(v);
            }
            self.assert(Int::add(&sum).le(&table));
        }
    }

    /// Every [axiom between contexts](self#axioms-between-contexts)
    /// over the quantities of this analysis's own operators, each
    /// operator's rows given the context facts give them, among the
    /// [relevant contexts](self#relevant-contexts).
    pub fn between_contexts(&mut self) {
        let scans: Vec<(String, String)> = self.scans.iter().map(|(s, t, _)| (s.clone(), t.clone())).collect();
        let logical = Logical::new(&self.nodes, &scans);
        let mut space = Space::default();
        let seeds = add_nodes(&mut space, &self.nodes, &logical);
        let relevant = space.relevant(&seeds);
        for a in space.axioms(&relevant) {
            self.assert_property(a.rule, a.claims);
        }
    }

    /// Runs `f` with `frame` as the node being visited, so a trace gives
    /// what it asserts to that node.
    fn in_frame<T>(&mut self, frame: Option<usize>, f: impl FnOnce(&Self) -> T) -> T {
        let n = self.owners.len();
        self.owners.extend(frame);
        let out = f(self);
        self.owners.truncate(n);
        out
    }
}

/// Asserts every axiom of `a`, once its rules have visited the plan: those
/// on each relation the rules made, on the rows of one table, and between
/// contexts.
pub fn assert_all(a: &mut Analyzer) {
    let relations = std::mem::take(&mut a.relations);
    // The sizes of the tables scans' foreign keys reference.
    if a.referenced_sizes {
        for r in &relations {
            if let Some(scan) = &r.scan {
                a.referenced_tables(scan);
            }
        }
    }
    // The keys of each scan's table.
    for r in &relations {
        if let Some(scan) = &r.scan {
            a.in_frame(r.frame, |a| {
                a.composite_key(scan, &r.rel);
                if a.referenced_sizes {
                    a.referenced_size(scan, &r.rel);
                }
            });
        }
    }
    a.relations = relations;
    // The rows of one table.
    a.disjoint();
    // Between the contexts of the operators' rows.
    a.between_contexts();
}

/// Adds the quantities of `nodes`' rows, named by `logical`, to `space`.
/// Returns the contexts of the nodes' rows.
fn add_nodes(space: &mut Space, nodes: &[Node], logical: &Logical) -> BTreeSet<Context> {
    let mut contexts = BTreeSet::new();
    let mut canonicals = Canonicals::default();
    let mut add = |space: &mut Space, q: FactKind, var: &str, contexts: &mut BTreeSet<Context>| {
        let q = q.canonical_in(&mut canonicals);
        contexts.insert(over(&q).clone());
        space.add(q, Int::new_const(var));
    };
    for (i, node) in nodes.iter().enumerate() {
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

/// The claims of a property, where an axiom found it applies, and the
/// axiom's name.
pub(crate) struct Axiom {
    pub rule: &'static str,
    pub claims: Vec<Claim>,
}

impl Axiom {
    fn new(rule: &'static str, claims: Vec<Claim>) -> Axiom {
        Axiom { rule, claims }
    }
}

/// The quantities of contexts (`|C|`, `ndv(K | C)`, `min`, `max`), each
/// with the Z3 terms it equals: the variables of the operators whose rows
/// it is of.
#[derive(Default)]
pub struct Space {
    terms: BTreeMap<FactKind, Vec<Int>>,
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

    /// Records that `term` equals quantity `q`, a canonical kind.
    fn add(&mut self, q: FactKind, term: Int) {
        let terms = self.terms.entry(q).or_default();
        if !terms.contains(&term) {
            terms.push(term);
        }
    }

    /// The term standing for `q`, if any has been added.
    fn term(&self, q: &FactKind) -> Option<&Int> {
        self.terms.get(q).and_then(|t| t.first())
    }

    /// The term standing for `|c|`, if any has been added.
    fn card(&self, c: &Context) -> Option<&Int> {
        self.term(&FactKind::Cardinality(c.clone()))
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

    /// Every axiom over the quantities of `relevant` contexts.
    fn axioms(&self, relevant: &BTreeSet<Context>) -> Vec<Axiom> {
        // Each relevant context's key quantities.
        let mut keys: BTreeMap<&Context, Vec<&FactKind>> = BTreeMap::new();
        for q in self.terms.keys() {
            if relevant.contains(over(q)) && !matches!(q, FactKind::Cardinality(_)) {
                keys.entry(over(q)).or_default().push(q);
            }
        }
        let mut out = same_rows(self, relevant);
        let buckets = self.buckets();
        for a in relevant {
            if self.card(a).is_none() {
                continue;
            }
            for b in buckets.get(&bases(a)).into_iter().flatten().filter(|b| relevant.contains(**b) && **b != a) {
                if self.subset(a, b) {
                    out.extend(subset(self, &keys, a, b));
                    out.extend(failing(self, relevant, a, b));
                } else {
                    out.extend(fewer(self, a, b));
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
fn over(q: &FactKind) -> &Context {
    q.over()
}

/// `same rows`, between the terms of one quantity. [`subset`] states it
/// between rows among others' too.
///
/// - **Claim**: `t = t'` for any two terms of one quantity. And for `A ⊆ B`:
///   `|A| = |B| ⇒` each key quantity of `A` equals `B`'s of the same keys.
/// - **Why**: one quantity has one value; `A ⊆ B` with as many rows makes
///   them the same rows.
pub(crate) fn same_rows(space: &Space, relevant: &BTreeSet<Context>) -> Vec<Axiom> {
    let mut out = vec![];
    for (q, terms) in &space.terms {
        if relevant.contains(over(q)) {
            for t in &terms[1..] {
                out.push(Axiom::new("same rows", properties::same(&[pair(q, t, &terms[0])])));
            }
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
/// with `keys` each context's key quantities. Also the `same rows` claim
/// between them ([`same_rows`]).
///
/// - **Claim**: for `A ⊆ B`, `A ≠ B`: `|A| ≤ |B|`; `ndv(K | A) ≤ ndv(K' |
///   B)` for `K ⊆ K'`; `min(k | A) ≥ min(k | B)`; `max(k | A) ≤ max(k |
///   B)`.
/// - **Why**: fewer rows have fewer values, within the same range.
pub(crate) fn subset(space: &Space, keys: &BTreeMap<&Context, Vec<&FactKind>>, a: &Context, b: &Context) -> Vec<Axiom> {
    let (Some(ca), Some(cb)) = (space.card(a), space.card(b)) else { return vec![] };
    // Each key of `a` that is one of `b`'s, over rows among `b`'s, and the
    // same once there are as many rows.
    let (mut within, mut same) = (vec![Pair::Card(ca, cb)], vec![]);
    for qa in keys.get(a).into_iter().flatten() {
        for qb in keys.get(b).into_iter().flatten() {
            if !renamed_kind(qa, qb, key_within) {
                continue;
            }
            let p = pair(qa, space.term(qa).unwrap(), space.term(qb).unwrap());
            within.push(p);
            if width(qa) == width(qb) {
                same.push(p);
            }
        }
    }
    vec![
        Axiom::new("subset", properties::within(&within)),
        Axiom::new("same rows", properties::same_if_as_many(ca, cb, &same)),
    ]
}

/// `fewer`, for `fewer(A, B)` ([relations](self#relations-between-contexts)).
///
/// - **Claim**: `|A| ≤ |B|` for `fewer(A, B)` but not `A ⊆ B`.
/// - **Why**: an outer join emits each preserved row once per partner or
///   once padded, so narrowing an input never adds rows. Its rows need not
///   be among the other's (a row may lose its partner and be padded), so
///   nothing is said of their values.
pub(crate) fn fewer(space: &Space, a: &Context, b: &Context) -> Vec<Axiom> {
    match (space.card(a), space.card(b)) {
        (Some(ca), Some(cb)) if space.fewer(a, b) => vec![Axiom::new("fewer", properties::fewer(ca, cb))],
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
pub(crate) fn failing(space: &Space, relevant: &BTreeSet<Context>, d: &Context, c: &Context) -> Vec<Axiom> {
    let (Some(cd), Some(cc), true) = (space.card(d), space.card(c), contain::subset(d, c)) else { return vec![] };
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
        if let (Some(ccp), Some(cdp)) = (space.card(cp), space.card(&dp)) {
            out.push(Axiom::new("failing rows", properties::failing(cd, cdp, cc, ccp)));
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
pub(crate) fn implied(space: &Space, relevant: &BTreeSet<Context>) -> Vec<Axiom> {
    let mut out = vec![];
    for c in relevant {
        let (Context::Spj { preds: pc, .. }, Some(cc)) = (c, space.card(c)) else { continue };
        for cp in relevant {
            let Context::Spj { preds, .. } = cp else { continue };
            if cp == c || !same_inputs(cp, c) || !preds.is_superset(pc) {
                continue;
            }
            let Some(ccp) = space.card(cp) else { continue };
            let p: BTreeSet<_> = preds.difference(pc).cloned().collect();
            for d in relevant {
                let Context::Spj { preds: pd, .. } = d else { continue };
                if !joins(d, c) || pd.is_superset(&p) {
                    continue;
                }
                let dp = d.filter(&p).canonical();
                if let (Some(cd), Some(cdp)) = (space.card(d), space.card(&dp)) {
                    out.push(Axiom::new("implied", properties::implied(cc, ccp, cd, cdp)));
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
pub(crate) fn split(space: &Space, s: &Context) -> Vec<Axiom> {
    let Context::Spj { tables, atoms, preds, exists } = s else { return vec![] };
    let Some(semi) = space.card(s) else { return vec![] };
    let mut out = vec![];
    for e in exists.iter().filter(|e| e.kind == ExistsKind::Semi) {
        let mut rest = exists.clone();
        rest.remove(e);
        let spj = |exists: BTreeSet<Exists>| Spj { tables: tables.clone(), atoms: atoms.clone(), preds: preds.clone(), exists }.build();
        let kept = spj(rest.clone()).canonical();
        let mut with_anti = rest;
        with_anti.insert(Exists { kind: ExistsKind::Anti, on: e.on.clone(), other: e.other.clone() });
        let anti = spj(with_anti).canonical();
        if let (Some(k), Some(a)) = (space.card(&kept), space.card(&anti)) {
            out.push(Axiom::new("semi and anti", properties::split(semi, a, k)));
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
pub(crate) fn fewer_keys(space: &Space, keys: &BTreeMap<&Context, Vec<&FactKind>>, c: &Context) -> Vec<Axiom> {
    let mut out = vec![];
    for qa in keys.get(c).into_iter().flatten() {
        let FactKind::Distinct { keys: ka, .. } = qa else { continue };
        for qb in keys.get(c).into_iter().flatten() {
            let FactKind::Distinct { keys: kb, .. } = qb else { continue };
            if ka.len() < kb.len() && ka.is_subset(kb) {
                let (ta, tb) = (space.term(qa).unwrap(), space.term(qb).unwrap());
                out.push(Axiom::new("fewer keys", properties::fewer_keys(ta, tb)));
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
pub(crate) fn wider(space: &Space, keys: &BTreeMap<&Context, Vec<&FactKind>>, relevant: &BTreeSet<Context>) -> Vec<Axiom> {
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
                        if let Some(n) = space.card(c) {
                            out.push(Axiom::new("wider rows", properties::values_of_rows(td, n)));
                        }
                        for qc in keys.get(c).into_iter().flatten() {
                            if let FactKind::Distinct { keys: kc, .. } = qc
                                && kd.is_subset(kc)
                            {
                                let p = Pair::Ndv(td, space.term(qc).unwrap());
                                out.push(Axiom::new("wider rows", properties::within(&[p])));
                            }
                        }
                    }
                    FactKind::Min { key, .. } | FactKind::Max { key, .. } if of_tables(&[key.clone()].into(), tc) => {
                        let at_c = match qd {
                            FactKind::Min { .. } => FactKind::Min { key: key.clone(), over: c.clone() },
                            _ => FactKind::Max { key: key.clone(), over: c.clone() },
                        };
                        if let Some(tc) = space.term(&at_c) {
                            out.push(Axiom::new("wider rows", properties::within(&[pair(qd, td, tc)])));
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    out
}

/// `disjoint`, between contexts. [`Analyzer::disjoint`] finds it between
/// relations.
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
pub(crate) fn disjoint(space: &Space, relevant: &BTreeSet<Context>) -> Vec<Axiom> {
    let mut groups: BTreeMap<_, Vec<(&BTreeSet<Term>, &Int)>> = BTreeMap::new();
    for c in relevant {
        if let (Context::Spj { tables, atoms, preds, exists }, Some(n)) = (c, space.card(c)) {
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
                    out.push(Axiom::new("disjoint", properties::disjoint(&[x, y], z)));
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
        assert_eq!(axioms[0].claims[0].claim.to_string(), "(<= (+ x y) n)");
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
        let axioms: Vec<String> = wider(&space, &keys, &relevant).iter().flat_map(|a| &a.claims).map(|c| c.claim.to_string()).collect();
        assert_eq!(axioms, ["(<= k n)"]);
    }
}
