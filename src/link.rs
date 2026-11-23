//! Link: properties between the rows of operators, whatever the plans'
//! shapes, through an e-graph of every plan the analyzer visited.
//!
//! The [rules](crate::rules) apply [properties](crate::properties) where
//! the plan's shape makes the relationship plain: an operator and its
//! input, one op output. Link relates the rest.
//!
//! # E-nodes
//!
//! Each analyzer node gets at most one [`ENode`], over the classes of the
//! e-nodes below it. Only e-nodes of one kind share a class.
//!
//! - **`Spj`**: a select-project-join subtree (scans, inner joins, filters,
//!   projections, aliases, repartitions, sorts without fetch), flattened
//!   down to its [`Input`]s: tables, or the classes of the nearest other
//!   e-nodes below. Its rows are those of its inputs' cross product on
//!   which every predicate is TRUE, some columns projected. Predicates and
//!   columns are over base columns, `i{k}.name` for input `k`. There is
//!   none if a predicate is volatile or opaque (`rules::opaque`), a scan
//!   applies its filters inexactly or has a `fetch`, or an input is a
//!   count-only class.
//! - **`Agg`**: `GROUP BY` or `DISTINCT` (every column a key), without
//!   grouping sets.
//! - **`Join`**: semi, anti and outer joins, `Right*` swapped to `Left*`.
//! - **`Limit`**: `LIMIT`, or a sort with fetch: count-only, as which rows
//!   it keeps hangs on order and ties.
//!
//! An `Agg`'s or `Join`'s expressions are over its inputs' classes' base
//! columns, as an `Spj`'s predicates: projections below are absorbed, so a
//! `GROUP BY extract(year …)` groups by that expression of a scan's column.
//! A `Join`'s right side reads past its left's inputs.
//!
//! # Classes
//!
//! A class's columns are its base columns: an `Spj` class's are its root's
//! inputs', any other's are named by the canonical text of their
//! expression, `i0.l_returnflag` or `sum(i0.l_quantity)`. An `Spj` reading
//! such a class as input `k` reads its column `e` as `i{k}."e"`.
//!
//! # Worklist
//!
//! [`link_all`] keeps one union-find over every analyzer node, each `Spj`
//! with the mapping of its inputs onto its root's. Each node, children
//! first, is placed:
//!
//! - an `Spj` in the partition of its sorted inputs (a multiset), where it
//!   is compared with one member of each other class under each mapping of
//!   its like inputs onto the other's: by their sets of conjuncts (interned
//!   once per node) or, where those don't nest, by a solver of link's own
//!   deciding from the predicates `P1` and `P2`, encoded in three-valued
//!   logic (`predicates`), whether `¬(P1 ∧ P2)`, `P1 ⇒ P2` or `P2 ⇒ P1` is
//!   valid. Equivalent predicates are a union; nested ones a subset edge,
//!   disjoint ones a disjoint pair, both related once classes are final.
//!   The predicates' variables never reach the analysis's solver.
//! - any other e-node by its key over its inputs' current roots
//!   (hash-consing): an equal key is a union.
//!
//! A union changes its classes' roots, so the e-nodes above them: these
//! are rebuilt at once, bottom-up, and any that changed is placed again.
//! A node in a partition thus always reads its inputs' current classes and
//! column names, and two nodes are compared only over the same ones. It
//! ends as classes only merge.
//!
//! # Relations
//!
//! Once classes are final, in one pass (so relations never merge classes):
//!
//! | kind | relation | premise | claims | label |
//! |---|---|---|---|---|
//! | any | same rows | one class | card, each column's ndv, min, max equal; count-only: card | `eq link` |
//! | `Spj` | subset | `P1 ⇒ P2` | card, each base column's within | `subset link` |
//! | `Spj` | disjoint | `¬(P1 ∧ P2)` | cards' sum within the inputs' product | `disjoint link` |
//! | `Agg` | fewer keys | same input, `∅ ≠ K ⊊ K'` | card `≤`; `K`'s columns equal | `fewer link` |
//! | `Agg` | subset input | input `⊆` (σ), `∅ ≠ σ(K) ⊆ K'` | card `≤`; `K`'s columns within | `fewer link` |
//! | semi | subset | left `⊆` (σ), right `⊆` (ρ), `on` equal under σ, ρ | card, the left's columns within | `subset link` |
//! | anti | subset | left `⊆` (σ), right `⊇` (ρ), `on` equal under σ, ρ | as semi | `subset link` |
//! | semi, anti | split | same left, right, `on`; anti not null-aware | `\|semi\| + \|anti\| = \|left\|` | `split link` |
//!
//! `⊆` includes the same class. Without keys an aggregate has a row even
//! over none, so relates to nothing. Only the transitive reduction of the
//! subset edges is asserted: an edge is left out if a path implies all its
//! claims, Z3 deriving them.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use datafusion::arrow::datatypes::{Field, Schema, SchemaRef};
use datafusion::common::tree_node::{Transformed, TreeNode};
use datafusion::common::{Column, DFSchema, DataFusionError, NullEquality, TableReference};
use datafusion::logical_expr::logical_plan::{Distinct, FetchType, JoinType, LogicalPlan, SkipType};
use datafusion::logical_expr::utils::split_conjunction_owned;
use datafusion::logical_expr::{BinaryExpr, Expr, ExprSchemable, Operator, binary_expr};
use z3::ast::{Bool, Int};
use z3::{SatResult, Solver};

use crate::analysis::{Analyzer, inexact_filters, product, solver_with_limits};
use crate::observed;
use crate::predicates::Encoder;
use crate::properties::{self, Pair};
use crate::rules::{grouping_sets, opaque};

/// What an e-node reads: a table (by its display name), or the class of
/// another e-node (by its root).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Input {
    Table(String),
    Class(usize),
}

/// A select-project-join subtree: the rows of its inputs' cross product
/// that satisfy every predicate, with some columns projected.
#[derive(Clone, PartialEq)]
struct SpjNode {
    /// Each input, in the subtree's order, and its schema: the table's, or
    /// the columns of the class it reads. Base columns name input `k` by
    /// the relation `i{k}`.
    scans: Vec<(Input, SchemaRef)>,
    /// The conjuncts, over base columns, canonical: sorted, deduplicated.
    preds: Vec<Expr>,
    /// Each root output column as an expression over base columns,
    /// `None` if opaque.
    columns: Vec<Option<Expr>>,
}

/// The rows an analyzer node outputs, over its inputs' classes.
#[derive(Clone, PartialEq)]
enum ENode {
    Spj(SpjNode),
    /// One row per distinct value of `keys` (in output order) over the
    /// rows of class `input`, and an aggregate per `aggs` (`None` if
    /// opaque).
    Agg { input: usize, keys: Vec<Expr>, aggs: Vec<Option<Expr>> },
    /// `left`'s rows kept by (semi), without (anti) or padded with (outer)
    /// a partner in `right` on `on`. `columns` are its output's.
    Join { kind: JoinType, null_aware: bool, left: usize, right: usize, on: Vec<Expr>, columns: Vec<Option<Expr>> },
    /// The rows of class `input` after skipping `skip`, at most `fetch`.
    Limit { input: usize, skip: usize, fetch: Option<usize> },
}

/// What an e-node other than `Spj` is equal by: its rows'.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Key {
    /// Its input and keys, sorted.
    Agg(usize, Vec<Expr>),
    Join(JoinType, bool, usize, usize, Vec<Expr>),
    Limit(usize, usize, Option<usize>),
}

impl ENode {
    fn key(&self) -> Option<Key> {
        Some(match self {
            ENode::Spj(_) => return None,
            ENode::Agg { input, keys, .. } => Key::Agg(*input, sorted(keys.clone())),
            ENode::Join { kind, null_aware, left, right, on, .. } => Key::Join(*kind, *null_aware, *left, *right, on.clone()),
            ENode::Limit { input, skip, fetch } => Key::Limit(*input, *skip, *fetch),
        })
    }

    /// Its output columns' expressions: an `Spj`'s over its base columns,
    /// any other's over its inputs' (none for a count-only `Limit`).
    fn columns(&self) -> Vec<Option<Expr>> {
        match self {
            ENode::Spj(c) => c.columns.clone(),
            ENode::Agg { keys, aggs, .. } => keys.iter().cloned().map(Some).chain(aggs.iter().cloned()).collect(),
            ENode::Join { columns, .. } => columns.clone(),
            ENode::Limit { .. } => vec![],
        }
    }

    /// The classes it reads.
    fn inputs(&self) -> Vec<usize> {
        match self {
            ENode::Spj(c) => c.scans.iter().filter_map(|(t, _)| if let Input::Class(c) = t { Some(*c) } else { None }).collect(),
            ENode::Agg { input, .. } | ENode::Limit { input, .. } => vec![*input],
            ENode::Join { left, right, .. } => vec![*left, *right],
        }
    }
}

/// A mapping of an `Spj`'s inputs onto another's like inputs: input `k`
/// becomes `σ[k]`.
type Mapping = Vec<usize>;

/// Asserts every property link finds between the rows of `a`'s operators,
/// once its rules have visited every plan.
pub fn link_all(a: &Analyzer) {
    let mut link = Link::new(a);
    link.run();
    link.relate();
}

/// Where an `Spj` is placed: its partition, and what is computed of it
/// once there.
struct Placed {
    /// Its inputs, sorted: the partition's key.
    inputs: Vec<Input>,
    /// Its input `k` is the sorted `π[k]`.
    pi: Mapping,
    /// Sorted, under each of the partition's mappings, the identity first.
    variants: Vec<SpjNode>,
    /// The interned conjuncts of each variant, sorted.
    keys: Vec<Vec<u32>>,
}

/// The `Spj`s over one multiset of inputs.
struct Partition {
    /// Each mapping of the sorted inputs onto themselves, within like ones.
    mappings: Vec<Mapping>,
    members: Vec<usize>,
}

/// A class's quantities: its card, and per column ndv, min and max.
struct Class {
    card: Int,
    columns: BTreeMap<Column, Column3>,
    /// For a class other than `Spj`'s: each column's expression over its
    /// inputs, which a mapping of its inputs relabels.
    exprs: HashMap<Column, Expr>,
}

struct Column3 {
    ndv: Int,
    min: Option<Int>,
    max: Option<Int>,
}

impl Class {
    /// Column `c` of this class, its inputs mapped by `sigma`.
    fn image(&self, c: &Column, sigma: &[usize]) -> Column {
        match self.exprs.get(c) {
            Some(e) => base_column(0, &relabel(e, sigma).to_string()),
            None => relabeled(c, sigma),
        }
    }
}

/// A subset edge between nodes, or classes: `sub`'s rows are among
/// `sup`'s, `sub`'s input `k` mapped to `sup`'s `σ[k]`.
#[derive(Clone, PartialEq, Eq, Hash)]
struct Edge {
    sub: usize,
    sup: usize,
    sigma: Mapping,
}

/// The state of [`link_all`].
struct Link<'a, 'b> {
    a: &'a Analyzer<'b>,
    decide: Decide,
    /// Each conjunct seen, by id.
    interned: HashMap<Expr, u32>,
    /// Classes given synthetic variables so far.
    synthetic: usize,
    uf: UnionFind,
    /// Each node's e-node over the current roots, once built.
    enodes: Vec<Option<ENode>>,
    built: Vec<bool>,
    /// Each node's parents: the nodes whose e-nodes read it.
    users: Vec<Vec<usize>>,
    /// Each root's class's members.
    members: Vec<Vec<usize>>,
    partitions: HashMap<Vec<Input>, Partition>,
    placed: Vec<Option<Placed>>,
    /// Each key of an e-node other than `Spj` seen, and a node of it. A
    /// key over roots names the same rows while they are roots, and none
    /// once one is not: an entry is never wrong.
    memo: HashMap<Key, usize>,
    /// Subset edges and disjoint pairs between `Spj` nodes.
    edges: Vec<Edge>,
    disjoint: Vec<(usize, usize)>,
    /// Nodes to place, children first.
    work: BTreeSet<usize>,
}

impl<'a, 'b> Link<'a, 'b> {
    fn new(a: &'a Analyzer<'b>) -> Self {
        Link::with_decide(a, Decide::new())
    }

    fn with_decide(a: &'a Analyzer<'b>, decide: Decide) -> Self {
        let n = a.nodes.len();
        let mut users = vec![vec![]; n];
        for (i, node) in a.nodes.iter().enumerate() {
            for &c in &node.inputs {
                users[c].push(i);
            }
        }
        Link {
            a,
            decide,
            interned: HashMap::new(),
            synthetic: 0,
            uf: UnionFind::new(n),
            enodes: vec![None; n],
            built: vec![false; n],
            users,
            members: (0..n).map(|i| vec![i]).collect(),
            partitions: HashMap::new(),
            placed: (0..n).map(|_| None).collect(),
            memo: HashMap::new(),
            edges: vec![],
            disjoint: vec![],
            work: (0..n).collect(),
        }
    }

    /// Places every node, until no union changes one.
    fn run(&mut self) {
        while let Some(i) = self.work.pop_first() {
            if !self.built[i] {
                self.built[i] = true;
                self.enodes[i] = self.enode(i);
                if let Some(ENode::Spj(c)) = &self.enodes[i] {
                    self.uf.to_parent[i] = (0..c.scans.len()).collect();
                }
            }
            match &self.enodes[i] {
                None => {}
                Some(ENode::Spj(_)) => self.place(i),
                Some(e) => {
                    let key = e.key().expect("not an Spj");
                    match self.memo.get(&key) {
                        Some(&j) => self.union(i, j, &[]),
                        None => {
                            self.memo.insert(key, i);
                        }
                    }
                }
            }
        }
    }

    /// Unions the classes of `x` and `y`, `x`'s input `k` being `y`'s
    /// `σ[k]`, and rebuilds what reads them.
    fn union(&mut self, x: usize, y: usize, sigma: &[usize]) {
        let Some((from, to)) = self.uf.union(x, y, sigma) else { return };
        let moved = std::mem::take(&mut self.members[from]);
        self.members[to].extend(moved);
        let mut queue: BTreeSet<usize> = self.members[to].iter().flat_map(|&m| self.users[m].iter().copied()).collect();
        while let Some(u) = queue.pop_first() {
            if !self.built[u] {
                continue;
            }
            let e = self.enode(u);
            if e == self.enodes[u] {
                continue;
            }
            self.unplace(u);
            self.enodes[u] = e;
            self.work.insert(u);
            queue.extend(self.users[u].iter().copied());
        }
    }

    fn unplace(&mut self, i: usize) {
        if let Some(p) = self.placed[i].take() {
            self.partitions.get_mut(&p.inputs).expect("placed in it").members.retain(|&m| m != i);
        }
    }

    /// Places `Spj` node `i` in its partition: equal conjuncts under a
    /// mapping are a union; else, against one member of each other class,
    /// equivalent predicates are a union, nested ones an edge, disjoint
    /// ones a disjoint pair.
    fn place(&mut self, i: usize) {
        let Some(ENode::Spj(c)) = &self.enodes[i] else { unreachable!("an Spj") };
        let mut order: Vec<usize> = (0..c.scans.len()).collect();
        order.sort_by(|&x, &y| c.scans[x].0.cmp(&c.scans[y].0));
        let mut pi = vec![0; order.len()];
        for (p, &k) in order.iter().enumerate() {
            pi[k] = p;
        }
        let scans: Vec<_> = order.iter().map(|&k| c.scans[k].clone()).collect();
        let node = c.mapped(&pi, &scans);
        let inputs: Vec<Input> = scans.iter().map(|(t, _)| t.clone()).collect();
        let part = self
            .partitions
            .entry(inputs.clone())
            .or_insert_with(|| Partition { mappings: mappings(&inputs), members: vec![] });
        let variants: Vec<SpjNode> = part.mappings.iter().map(|m| node.mapped(m, &[])).collect();
        let others = part.members.clone();
        let mappings = part.mappings.clone();
        let keys: Vec<Vec<u32>> = variants.iter().map(|v| self.key(&v.preds)).collect();
        let x = Placed { inputs: inputs.clone(), pi, variants, keys };

        // `y`'s sorted `σ`: from `x`'s inputs to `y`'s, in their own orders.
        let natural = |x: &Placed, y: &Placed, m: &[usize]| -> Mapping {
            let y_inv = inverse(&y.pi);
            x.pi.iter().map(|&p| y_inv[m[p]]).collect()
        };
        // Same conjuncts, up to a mapping: the same class, and what it is
        // related to is known.
        let same = others.iter().find_map(|&y| {
            let py = self.placed[y].as_ref()?;
            let v = x.keys.iter().position(|k| *k == py.keys[0])?;
            Some((y, natural(&x, py, &mappings[v])))
        });
        if let Some((y, sigma)) = same {
            self.union(i, y, &sigma);
        } else {
            let mut seen = HashSet::new();
            for y in others {
                let root = self.uf.find(y).0;
                if root == self.uf.find(i).0 || !seen.insert(root) {
                    continue;
                }
                let Some(py) = self.placed[y].as_ref() else { continue };
                let quick = (0..mappings.len()).find_map(|v| {
                    let (k1, k2) = (&x.keys[v], &py.keys[0]);
                    match (subset(k2, k1), subset(k1, k2)) {
                        (false, false) => None,
                        (sub, sup) => Some((v, sub, sup, false)),
                    }
                });
                let relations: Vec<(usize, bool, bool, bool)> = match quick {
                    Some(q) => vec![q],
                    None => (0..mappings.len())
                        .filter_map(|v| {
                            let key = (inputs.clone(), x.keys[v].clone(), py.keys[0].clone());
                            let r = self.decide.relation(key, &x.variants[v], &py.variants[0])?;
                            Some((v, r.sub, r.sup, r.disjoint))
                        })
                        .collect(),
                };
                let found: Vec<(Mapping, bool, bool, bool)> =
                    relations.into_iter().map(|(v, sub, sup, apart)| (natural(&x, py, &mappings[v]), sub, sup, apart)).collect();
                for (sigma, sub, sup, apart) in found {
                    if apart {
                        self.disjoint.push((i, y));
                    }
                    match (sub, sup) {
                        (true, true) => self.union(i, y, &sigma),
                        (true, false) => self.edges.push(Edge { sub: i, sup: y, sigma }),
                        (false, true) => self.edges.push(Edge { sub: y, sup: i, sigma: inverse(&sigma) }),
                        (false, false) => {}
                    }
                }
            }
        }
        self.partitions.get_mut(&inputs).expect("made above").members.push(i);
        self.placed[i] = Some(x);
    }

    /// The sorted ids of `preds`.
    fn key(&mut self, preds: &[Expr]) -> Vec<u32> {
        let mut k: Vec<u32> = preds
            .iter()
            .map(|p| {
                let n = self.interned.len() as u32;
                *self.interned.entry(p.clone()).or_insert(n)
            })
            .collect();
        k.sort_unstable();
        k.dedup();
        k
    }

    /// Node `i`'s e-node over its inputs' current roots, given its
    /// children's.
    fn enode(&mut self, i: usize) -> Option<ENode> {
        let a = self.a;
        let node = &a.nodes[i];
        let e = match &node.plan {
            LogicalPlan::TableScan(_)
            | LogicalPlan::Filter(_)
            | LogicalPlan::Projection(_)
            | LogicalPlan::SubqueryAlias(_)
            | LogicalPlan::Repartition(_) => ENode::Spj(self.spj(i)?),
            LogicalPlan::Join(j) if j.join_type == JoinType::Inner => ENode::Spj(self.spj(i)?),
            LogicalPlan::Sort(s) if s.fetch.is_none() => ENode::Spj(self.spj(i)?),
            LogicalPlan::Aggregate(agg) if !grouping_sets(agg) => {
                let (input, _, columns) = self.rows(node.inputs[0])?;
                let over = |e: &Expr| substitute(e, agg.input.schema(), &columns).map(ordered);
                let keys = agg.group_expr.iter().map(over).collect::<Option<Vec<Expr>>>()?;
                match self.regrouped(node.inputs[0], &keys, agg.aggr_expr.len()) {
                    Some(e) => e,
                    None => ENode::Agg { input, keys, aggs: agg.aggr_expr.iter().map(over).collect() },
                }
            }
            LogicalPlan::Distinct(Distinct::All(_)) => {
                let (input, _, columns) = self.rows(node.inputs[0])?;
                ENode::Agg { input, keys: columns.into_iter().collect::<Option<_>>()?, aggs: vec![] }
            }
            LogicalPlan::Join(j) if STAGE >= 3 => self.join(i, j)?,
            LogicalPlan::Sort(s) if STAGE >= 4 => ENode::Limit { input: self.class(node.inputs[0])?, skip: 0, fetch: s.fetch },
            LogicalPlan::Limit(l) if STAGE >= 4 => {
                let (Ok(SkipType::Literal(skip)), Ok(FetchType::Literal(fetch))) = (l.get_skip_type(), l.get_fetch_type()) else {
                    return None;
                };
                ENode::Limit { input: self.class(node.inputs[0])?, skip, fetch }
            }
            _ => return None,
        };
        let width = match &e {
            ENode::Limit { .. } => node.ndv_vars.len(),
            e => e.columns().len(),
        };
        (width == node.ndv_vars.len()).then_some(e)
    }

    /// A `GROUP BY` of `keys` over node `c`, as a `GROUP BY` of `c`'s input
    /// if `c` is a `GROUP BY` and `keys` some of its keys: its groups'
    /// values of them are its input's. Its aggregates, over groups, are
    /// opaque.
    fn regrouped(&self, c: usize, keys: &[Expr], aggs: usize) -> Option<ENode> {
        let Some(ENode::Agg { input, keys: inner, .. }) = &self.enodes[c] else { return None };
        let keys: Vec<Expr> = keys
            .iter()
            .map(|k| match k {
                Expr::Column(k) if instance(k) == Some(0) => inner.iter().find(|i| i.to_string() == k.name).cloned(),
                _ => None,
            })
            .collect::<Option<_>>()?;
        Some(ENode::Agg { input: *input, keys, aggs: vec![None; aggs] })
    }

    /// Node `c`'s class, if it has an e-node.
    fn class(&mut self, c: usize) -> Option<usize> {
        self.enodes[c].as_ref()?;
        Some(self.uf.find(c).0)
    }

    /// Node `c`'s rows as an input: its class, the class's width (its
    /// base columns' inputs), and `c`'s output columns over them. None for
    /// a count-only class.
    fn rows(&mut self, c: usize) -> Option<(usize, usize, Vec<Option<Expr>>)> {
        let (root, tau) = self.uf.find(c);
        match self.enodes[c].as_ref()? {
            ENode::Spj(s) => Some((root, s.scans.len(), s.columns.iter().map(|e| e.as_ref().map(|e| relabel(e, &tau))).collect())),
            ENode::Limit { .. } => None,
            e => Some((root, 1, e.columns().iter().map(|e| e.as_ref().map(|e| Expr::Column(base_column(0, &e.to_string())))).collect())),
        }
    }

    /// The [`SpjNode`] of node `i`, given its children's e-nodes: a child
    /// of another kind is an input, its class.
    fn spj(&mut self, i: usize) -> Option<SpjNode> {
        let a = self.a;
        let node = &a.nodes[i];
        let mut out = match &node.plan {
            LogicalPlan::TableScan(scan) => {
                if scan.fetch.is_some() || inexact_filters(scan) {
                    return None;
                }
                let var = node.raw_scan.as_ref().map_or(&node.var, |r| &r.var);
                let (_, display, _) = a.scans.iter().find(|(s, _, _)| s == var)?;
                let base = |e: &Expr| -> Option<Expr> {
                    if opaque(e) {
                        return None;
                    }
                    let e = e.clone().transform_up(|x| match x {
                        Expr::Column(c) => Ok(Transformed::yes(Expr::Column(base_column(0, &c.name)))),
                        x => Ok(Transformed::no(x)),
                    });
                    Some(e.ok()?.data)
                };
                SpjNode {
                    scans: vec![(Input::Table(display.clone()), scan.source.schema())],
                    preds: scan.filters.iter().map(base).collect::<Option<_>>()?,
                    columns: scan
                        .projected_schema
                        .fields()
                        .iter()
                        .map(|f| Some(Expr::Column(base_column(0, f.name()))))
                        .collect(),
                }
            }
            LogicalPlan::Filter(f) => {
                let mut c = self.spj_input(node.inputs[0])?;
                c.preds.push(substitute(&f.predicate, f.input.schema(), &c.columns)?);
                c
            }
            LogicalPlan::Projection(p) => {
                let mut c = self.spj_input(node.inputs[0])?;
                c.columns = p.expr.iter().map(|e| substitute(e, p.input.schema(), &c.columns)).collect();
                c
            }
            LogicalPlan::Join(j) => {
                let (mut l, r) = (self.spj_input(node.inputs[0])?, self.spj_input(node.inputs[1])?);
                let r = r.mapped(&shift(r.scans.len(), l.scans.len()), &[]);
                let op = key_op(j.null_equality);
                for (le, re) in &j.on {
                    let le = substitute(le, j.left.schema(), &l.columns)?;
                    let re = substitute(re, j.right.schema(), &r.columns)?;
                    l.preds.push(binary_expr(le, op, re));
                }
                l.scans.extend(r.scans);
                l.preds.extend(r.preds);
                l.columns.extend(r.columns);
                if let Some(f) = &j.filter {
                    l.preds.push(substitute(f, &j.schema, &l.columns)?);
                }
                l
            }
            _ => self.spj_input(node.inputs[0])?,
        };
        out.preds = canonical(out.preds);
        (out.columns.len() == node.ndv_vars.len()).then_some(out)
    }

    /// Node `c`'s rows as an `Spj`'s: its own, or one input reading its
    /// class.
    fn spj_input(&mut self, c: usize) -> Option<SpjNode> {
        match self.enodes[c].as_ref()? {
            ENode::Spj(s) => Some(s.clone()),
            ENode::Limit { .. } => None,
            e => {
                let columns = e.columns();
                let types = self.a.nodes[c].plan.schema();
                let mut fields: Vec<Field> = vec![];
                for (j, e) in columns.iter().enumerate() {
                    let Some(e) = e else { continue };
                    let name = e.to_string();
                    if !fields.iter().any(|f| *f.name() == name) {
                        fields.push(Field::new(name, types.field(j).data_type().clone(), true));
                    }
                }
                let schema = Arc::new(Schema::new(fields));
                Some(SpjNode {
                    scans: vec![(Input::Class(self.uf.find(c).0), schema)],
                    preds: vec![],
                    columns: columns.iter().map(|e| e.as_ref().map(|e| Expr::Column(base_column(0, &e.to_string())))).collect(),
                })
            }
        }
    }

    /// The e-node of join `j`, node `i`, other than inner or mark: its
    /// sides' columns over the left's base columns, then the right's past
    /// them.
    fn join(&mut self, i: usize, j: &datafusion::logical_expr::Join) -> Option<ENode> {
        use JoinType::*;
        let (kind, swap) = match j.join_type {
            Left => (Left, false),
            Right => (Left, true),
            Full => (Full, false),
            LeftSemi => (LeftSemi, false),
            RightSemi => (LeftSemi, true),
            LeftAnti => (LeftAnti, false),
            RightAnti => (LeftAnti, true),
            Inner | LeftMark | RightMark => return None,
        };
        let a = self.a;
        let inputs = &a.nodes[i].inputs;
        let (l, r) = (self.rows(inputs[0])?, self.rows(inputs[1])?);
        // A full join's sides are unordered: the lesser class first.
        let swap = swap || (kind == Full && r.0 < l.0);
        let (first, second) = if swap { (r, l) } else { (l, r) };
        let past = shift(second.1, first.1);
        let second_columns: Vec<Option<Expr>> = second.2.iter().map(|e| e.as_ref().map(|e| relabel(e, &past))).collect();
        let (lc, rc) = if swap { (second_columns, first.2) } else { (first.2, second_columns) };
        let op = key_op(j.null_equality);
        let mut on = vec![];
        for (le, re) in &j.on {
            on.push(binary_expr(substitute(le, j.left.schema(), &lc)?, op, substitute(re, j.right.schema(), &rc)?));
        }
        let both: Vec<Option<Expr>> = lc.iter().chain(&rc).cloned().collect();
        if let Some(f) = &j.filter {
            on.push(substitute(f, &j.left.schema().join(j.right.schema()).ok()?, &both)?);
        }
        let columns = match j.join_type {
            LeftSemi | LeftAnti => lc,
            RightSemi | RightAnti => rc,
            _ => both,
        };
        // NULL-aware only where a key may be NULL: else as any anti join.
        let nullable = |e: &Expr, s: &DFSchema| e.nullable(s).unwrap_or(true);
        let null_aware = j.null_aware
            && (j.filter.is_some() || j.on.iter().any(|(l, r)| nullable(l, j.left.schema()) || nullable(r, j.right.schema())));
        Some(ENode::Join { kind, null_aware, left: first.0, right: second.0, on: canonical(on), columns })
    }

    /// Asserts each class's `eq link`s, then what relates the classes.
    fn relate(&mut self) {
        let mut groups: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        for i in 0..self.enodes.len() {
            if self.enodes[i].is_some() {
                let root = self.uf.find(i).0;
                groups.entry(root).or_default().push(i);
            }
        }
        let mut classes: HashMap<usize, Class> = HashMap::new();
        for (&root, ms) in &groups {
            let ms: Vec<(usize, Vec<Option<Column>>)> = ms.iter().map(|&x| (x, self.columns_of(x))).collect();
            let mut class = match &ms[..] {
                [(x, columns)] => own(self.a, *x, columns),
                _ => {
                    let class = self.synthetic(&ms);
                    for (x, columns) in &ms {
                        self.a.assert_property("eq link", eq_link(self.a, *x, columns, &class));
                    }
                    class
                }
            };
            if !matches!(self.enodes[root], Some(ENode::Spj(_))) {
                for (x, _) in &ms {
                    for e in self.enodes[*x].as_ref().expect("a member").columns().into_iter().flatten() {
                        class.exprs.insert(base_column(0, &e.to_string()), e);
                    }
                }
            }
            classes.insert(root, class);
        }

        // `Spj` edges between classes, and the mappings under which each
        // pair nests: pairwise in a partition, so closed.
        let mut seen = HashSet::new();
        let mut edges: Vec<Edge> = vec![];
        for e in std::mem::take(&mut self.edges) {
            let ((sub, ts), (sup, tp)) = (self.uf.find(e.sub), self.uf.find(e.sup));
            let ts_inv = inverse(&ts);
            let sigma = (0..e.sigma.len()).map(|k| tp[e.sigma[ts_inv[k]]]).collect();
            let e = Edge { sub, sup, sigma };
            if sub != sup && seen.insert(e.clone()) {
                edges.push(e);
            }
        }
        let mut subsets: HashMap<(usize, usize), Vec<Mapping>> = HashMap::new();
        for e in &edges {
            subsets.entry((e.sub, e.sup)).or_default().push(e.sigma.clone());
        }

        // A disjoint pair's claim reads only cards: one per pair of classes.
        let mut pairs: BTreeSet<(usize, usize)> = BTreeSet::new();
        for (x, y) in std::mem::take(&mut self.disjoint) {
            let (x, y) = (self.uf.find(x).0, self.uf.find(y).0);
            if x != y {
                pairs.insert((x.min(y), x.max(y)));
            }
        }
        for (x, y) in pairs {
            let Some(ENode::Spj(c)) = &self.enodes[x] else { unreachable!("an Spj") };
            let claims = disjoint_link(self.a, &classes, &classes[&x], &classes[&y], &c.scans);
            self.a.assert_property("disjoint link", claims);
        }

        let roots: Vec<usize> = groups.keys().copied().collect();
        edges.extend(self.joins(&roots, &classes, &mut subsets));
        self.aggregates(&roots, &classes, &subsets);
        for e in reduced(&edges, &classes) {
            self.a.assert_property("subset link", subset_link(&classes[&e.sub], &classes[&e.sup], &e.sigma));
        }
    }

    /// Node `x`'s output columns, over its class's columns.
    fn columns_of(&mut self, x: usize) -> Vec<Option<Column>> {
        let tau = self.uf.find(x).1;
        match self.enodes[x].as_ref().expect("a member") {
            ENode::Spj(c) => c.keyed(&tau),
            ENode::Limit { .. } => vec![None; self.a.nodes[x].ndv_vars.len()],
            e => e.columns().iter().map(|e| e.as_ref().map(|e| base_column(0, &e.to_string()))).collect(),
        }
    }

    /// The subset edges between semi joins, and between anti joins, of
    /// nested inputs, bottom-up, each pair's mappings added to `subsets`;
    /// and asserts each `split link`.
    fn joins(&self, roots: &[usize], classes: &HashMap<usize, Class>, subsets: &mut HashMap<(usize, usize), Vec<Mapping>>) -> Vec<Edge> {
        use JoinType::*;
        let mut joins: Vec<(usize, &ENode)> = roots
            .iter()
            .filter_map(|&r| match &self.enodes[r] {
                Some(e @ ENode::Join { kind: LeftSemi | LeftAnti, .. }) => Some((r, e)),
                _ => None,
            })
            .collect();
        let mut rank = HashMap::new();
        joins.sort_by_key(|(r, _)| (self.rank(*r, &mut rank), *r));

        let mut out = vec![];
        for (n, &(x, ex)) in joins.iter().enumerate() {
            let ENode::Join { kind, null_aware, left, right, on, .. } = ex else { unreachable!("a join") };
            for &(y, ey) in &joins[..n] {
                let ENode::Join { kind: k2, null_aware: n2, left: l2, right: r2, on: on2, .. } = ey else { unreachable!("a join") };
                if (kind, null_aware) != (k2, n2) {
                    continue;
                }
                // Mappings under which `a`'s rows are among `b`'s, a join's
                // as its left's.
                for (a, b, (la, ra, oa), (lb, rb, ob)) in [(x, y, (left, right, on), (l2, r2, on2)), (y, x, (l2, r2, on2), (left, right, on))] {
                    let rights = match kind {
                        LeftAnti => self.maps(*rb, *ra, subsets).into_iter().map(|s| inverse(&s)).collect(),
                        _ => self.maps(*ra, *rb, subsets),
                    };
                    let width = self.width(*la);
                    'found: for sl in self.maps(*la, *lb, subsets) {
                        for sr in &rights {
                            let both: Mapping = sl.iter().copied().chain(sr.iter().map(|&k| k + width)).collect();
                            if canonical(oa.iter().map(|e| relabel(e, &both)).collect()) == *ob {
                                subsets.entry((a, b)).or_default().push(sl.clone());
                                out.push(Edge { sub: a, sup: b, sigma: sl });
                                break 'found;
                            }
                        }
                    }
                }
            }
        }

        // Each row of the left has a partner or none.
        let semis: HashMap<(usize, usize, &Vec<Expr>), usize> = joins
            .iter()
            .filter_map(|(r, e)| match e {
                ENode::Join { kind: LeftSemi, left, right, on, .. } => Some(((*left, *right, on), *r)),
                _ => None,
            })
            .collect();
        for (r, e) in &joins {
            let ENode::Join { kind: LeftAnti, null_aware: false, left, right, on, .. } = e else { continue };
            if let Some(s) = semis.get(&(*left, *right, on)) {
                let claims = properties::split(&classes[s].card, &classes[r].card, &classes[left].card);
                self.a.assert_property("split link", claims);
            }
        }
        out
    }

    /// Asserts each `fewer link` between `GROUP BY`s: of fewer keys over the
    /// same rows, or of the same keys or fewer over fewer rows.
    fn aggregates(&self, roots: &[usize], classes: &HashMap<usize, Class>, subsets: &HashMap<(usize, usize), Vec<Mapping>>) {
        let aggs: Vec<(usize, usize, Vec<Expr>)> = roots
            .iter()
            .filter_map(|&r| match &self.enodes[r] {
                Some(ENode::Agg { input, keys, .. }) => Some((r, *input, sorted(keys.clone()))),
                _ => None,
            })
            .collect();
        for (x, ix, kx) in &aggs {
            if kx.is_empty() {
                continue;
            }
            for (y, iy, ky) in &aggs {
                if x == y {
                    continue;
                }
                let ky: HashSet<String> = ky.iter().map(|k| k.to_string()).collect();
                let found = self.maps(*ix, *iy, subsets).into_iter().find_map(|sigma| {
                    let pairs: Vec<(String, String)> = kx.iter().map(|k| (k.to_string(), relabel(k, &sigma).to_string())).collect();
                    let within = pairs.iter().all(|(_, m)| ky.contains(m));
                    // The same keys over the same rows are one class.
                    (within && (ix != iy || pairs.len() < ky.len())).then_some(pairs)
                });
                let Some(pairs) = found else { continue };
                let (cx, cy) = (&classes[x], &classes[y]);
                let mut claims = properties::fewer(&cx.card, &cy.card);
                for (k, m) in pairs {
                    let (Some(p), Some(q)) = (cx.columns.get(&base_column(0, &k)), cy.columns.get(&base_column(0, &m))) else { continue };
                    let pairs = column3_pairs(p, q);
                    claims.extend(if ix == iy { properties::same(&pairs) } else { properties::within(&pairs) });
                }
                self.a.assert_property("fewer link", claims);
            }
        }
    }

    /// The mappings under which class `x`'s rows are among class `y`'s:
    /// the identity for one class.
    fn maps(&self, x: usize, y: usize, subsets: &HashMap<(usize, usize), Vec<Mapping>>) -> Vec<Mapping> {
        match x == y {
            true => vec![(0..self.width(x)).collect()],
            false => subsets.get(&(x, y)).cloned().unwrap_or_default(),
        }
    }

    /// How many inputs class `root`'s base columns are over.
    fn width(&self, root: usize) -> usize {
        match &self.enodes[root] {
            Some(ENode::Spj(c)) => c.scans.len(),
            _ => 1,
        }
    }

    /// Class `root`'s height above tables.
    fn rank(&self, root: usize, known: &mut HashMap<usize, usize>) -> usize {
        if let Some(&r) = known.get(&root) {
            return r;
        }
        known.insert(root, 0);
        let inputs = self.enodes[root].as_ref().map(|e| e.inputs()).unwrap_or_default();
        let r = 1 + inputs.iter().map(|&c| self.rank(c, known)).max().unwrap_or(0);
        known.insert(root, r);
        r
    }

    /// Synthetic variables for the class of `members` (each with its
    /// columns over the class's): card, and per column any member has,
    /// ndv, and min and max if any member has them.
    fn synthetic(&mut self, members: &[(usize, Vec<Option<Column>>)]) -> Class {
        let base = format!("eq{}", self.synthetic);
        self.synthetic += 1;
        let mut columns: BTreeMap<Column, Column3> = BTreeMap::new();
        for (x, cols) in members {
            let q = Quantities::of(self.a, *x);
            for (j, c) in cols.iter().enumerate() {
                let Some(c) = c else { continue };
                let n = columns.len();
                let q3 = columns.entry(c.clone()).or_insert_with(|| Column3 { ndv: Int::new_const(format!("{base}_c{n}")), min: None, max: None });
                let name = q3.ndv.to_string();
                if q.min[j].is_some() && q3.min.is_none() {
                    q3.min = Some(Int::new_const(format!("{name}_min")));
                }
                if q.max[j].is_some() && q3.max.is_none() {
                    q3.max = Some(Int::new_const(format!("{name}_max")));
                }
            }
        }
        Class { card: Int::new_const(base.as_str()), columns, exprs: HashMap::new() }
    }
}

/// The kinds [`Link::enode`] builds: 2 aggregates, 3 joins, 4 limits.
const STAGE: u8 = 3;

/// A union-find over every analyzer node, each `Spj` with the mapping of
/// its inputs onto its parent's (none for other kinds).
struct UnionFind {
    parent: Vec<usize>,
    to_parent: Vec<Mapping>,
}

impl UnionFind {
    /// `n` nodes, each its own class. A node's mapping is set to the
    /// identity once its width is known.
    fn new(n: usize) -> UnionFind {
        UnionFind { parent: (0..n).collect(), to_parent: vec![vec![]; n] }
    }

    /// `x`'s root, and the mapping of `x`'s inputs onto the root's.
    fn find(&mut self, x: usize) -> (usize, Mapping) {
        let p = self.parent[x];
        if p == x {
            return (x, self.to_parent[x].clone());
        }
        let (root, up) = self.find(p);
        let tau: Mapping = self.to_parent[x].iter().map(|&k| up[k]).collect();
        self.parent[x] = root;
        self.to_parent[x] = tau.clone();
        (root, tau)
    }

    /// Unions `x` and `y`, `x`'s input `k` being `y`'s `σ[k]`: the root
    /// that moved and the one it moved under, if they were apart.
    fn union(&mut self, x: usize, y: usize, sigma: &[usize]) -> Option<(usize, usize)> {
        let ((rx, tx), (ry, ty)) = (self.find(x), self.find(y));
        if rx == ry {
            return None;
        }
        // rx's k is x's tx⁻¹[k], y's σ[…], ry's ty[…].
        let tx_inv = inverse(&tx);
        self.to_parent[rx] = (0..tx.len()).map(|k| ty[sigma[tx_inv[k]]]).collect();
        self.parent[rx] = ry;
        Some((rx, ry))
    }
}

/// The inverse of mapping `s`.
fn inverse(s: &[usize]) -> Mapping {
    let mut out = vec![0; s.len()];
    for (k, &m) in s.iter().enumerate() {
        out[m] = k;
    }
    out
}

/// The mapping of `n` inputs past `by` others.
fn shift(n: usize, by: usize) -> Mapping {
    (0..n).map(|k| k + by).collect()
}

/// True if sorted `a` is a subset of sorted `b`.
fn subset(a: &[u32], b: &[u32]) -> bool {
    let mut b = b.iter();
    a.iter().all(|x| b.any(|y| y == x))
}

/// Base column `c` with its input mapped by `sigma`.
fn relabeled(c: &Column, sigma: &[usize]) -> Column {
    match instance(c) {
        Some(k) => base_column(sigma[k], &c.name),
        None => c.clone(),
    }
}

/// The edges of `edges` whose claims no path of other remaining edges
/// implies: a path implies an edge's claims if it maps the inputs as the
/// edge does, and each class on it has each column the edge pairs, with
/// min and max where the edge pairs them.
fn reduced(edges: &[Edge], classes: &HashMap<usize, Class>) -> Vec<Edge> {
    let mut alive = vec![true; edges.len()];
    for (i, e) in edges.iter().enumerate() {
        alive[i] = false;
        let (sub, sup) = (&classes[&e.sub], &classes[&e.sup]);
        // The columns the edge pairs, as `sub` names them, and whether it
        // pairs their min and max.
        let needed: Vec<(&Column, bool, bool)> = sub
            .columns
            .iter()
            .filter_map(|(c, q)| {
                let p = sup.columns.get(&sub.image(c, &e.sigma))?;
                Some((c, q.min.is_some() && p.min.is_some(), q.max.is_some() && p.max.is_some()))
            })
            .collect();
        let carries = |x: &Class, mu: &[usize]| {
            needed.iter().all(|(c, min, max)| {
                x.columns.get(&sub.image(c, mu)).is_some_and(|q| (!min || q.min.is_some()) && (!max || q.max.is_some()))
            })
        };
        let identity: Mapping = (0..e.sigma.len()).collect();
        let mut stack = vec![(e.sub, identity.clone())];
        let mut visited = HashSet::from([(e.sub, identity)]);
        let mut implied = false;
        'search: while let Some((x, mu)) = stack.pop() {
            for (j, f) in edges.iter().enumerate() {
                if !alive[j] || f.sub != x {
                    continue;
                }
                let mu2: Mapping = mu.iter().map(|&k| f.sigma[k]).collect();
                if f.sup == e.sup && mu2 == e.sigma {
                    implied = true;
                    break 'search;
                }
                if carries(&classes[&f.sup], &mu2) && visited.insert((f.sup, mu2.clone())) {
                    stack.push((f.sup, mu2));
                }
            }
        }
        alive[i] = !implied;
    }
    edges.iter().zip(alive).filter(|(_, a)| *a).map(|(e, _)| e.clone()).collect()
}

/// How the predicates `P1` and `P2` of two nodes over the same inputs
/// relate, each valid for every row.
#[derive(Clone, Copy)]
struct Relation {
    /// `¬(P1 ∧ P2)`.
    disjoint: bool,
    /// `P1 ⇒ P2`.
    sub: bool,
    /// `P2 ⇒ P1`.
    sup: bool,
}

/// Decides [`Relation`]s with a solver of its own, once per pair of
/// predicates. Each check is limited by Z3's resource count
/// ([`DECIDE_RLIMIT`]), not by time, so the links found do not depend on
/// the machine's load.
struct Decide {
    solver: Solver,
    encoders: usize,
    /// By partition and the two nodes' conjuncts' keys.
    known: HashMap<(Vec<Input>, Vec<u32>, Vec<u32>), Option<Relation>>,
}

impl Decide {
    fn new() -> Decide {
        Decide::with_rlimit(DECIDE_RLIMIT)
    }

    fn with_rlimit(rlimit: u32) -> Decide {
        Decide { solver: solver_with_limits(rlimit, DECIDE_TIMEOUT_MS), encoders: 0, known: HashMap::new() }
    }

    /// How `c1`'s predicates relate to `c2`'s, both over the same sorted
    /// inputs, `key` naming the pair. None if the inputs' columns don't
    /// type.
    fn relation(&mut self, key: (Vec<Input>, Vec<u32>, Vec<u32>), c1: &SpjNode, c2: &SpjNode) -> Option<Relation> {
        if let Some(r) = self.known.get(&key) {
            return *r;
        }
        let r = base_schema(&[c1, c2]).map(|schema| {
            let mut e = Encoder::new(&format!("pred{}", self.encoders), &schema);
            self.encoders += 1;
            let (p1, p2) = (e.holds(&c1.preds), e.holds(&c2.preds));
            Relation {
                disjoint: self.valid(&Bool::and(&[p1.clone(), p2.clone()]).not()),
                sub: self.valid(&p1.implies(&p2)),
                sup: self.valid(&p2.implies(&p1)),
            }
        });
        self.known.insert(key, r);
        r
    }

    /// True if `f` holds whatever its variables, as far as the solver
    /// decides within the check's resource limit: undecided is not valid.
    fn valid(&self, f: &Bool) -> bool {
        self.solver.push();
        self.solver.assert(f.not());
        let unsat = self.solver.check() == SatResult::Unsat;
        self.solver.pop(1);
        unsat
    }
}

/// Per-check resource limit of [`Decide`]. Over TPC-H, alone and with the
/// other queries' plans, every check is decided: proofs spend at most
/// about 50, refutations about 700. A hard nonlinear formula spends about
/// 4 million a second on an unloaded core, so this is a fraction of a
/// second's work, as Z3 counts work unevenly: about the 1 s timeout it
/// replaces.
const DECIDE_RLIMIT: u32 = 1_000_000;
/// Wall-clock limit, only against a check that stalls without spending
/// its resources: far beyond what its resource limit takes.
const DECIDE_TIMEOUT_MS: u32 = 10_000;

/// Node `x`, a member of `class` with `columns` over the class's, is the
/// class's rows: its card and each column's quantities equal the class's
/// ([`properties::same`]). A column of one name is one expression of the
/// same rows, so of one type and unit.
fn eq_link(a: &Analyzer, x: usize, columns: &[Option<Column>], class: &Class) -> Vec<Bool> {
    let q = Quantities::of(a, x);
    let mut pairs = vec![Pair::Card(&q.card, &class.card)];
    for (j, col) in columns.iter().enumerate() {
        let Some(q3) = col.as_ref().and_then(|c| class.columns.get(c)) else { continue };
        pairs.extend(column_pairs(&q, j, q3));
    }
    properties::same(&pairs)
}

/// `sub`'s rows are among `sup`'s, `sub`'s input `k` being `sup`'s
/// `σ[k]`: `|sub| ≤ |sup|`, and each column's values within
/// ([`properties::within`]).
fn subset_link(sub: &Class, sup: &Class, sigma: &[usize]) -> Vec<Bool> {
    let mut claims = properties::within(&[Pair::Card(&sub.card, &sup.card)]);
    for (c, q) in &sub.columns {
        let Some(p) = sup.columns.get(&sub.image(c, sigma)) else { continue };
        claims.extend(properties::within(&column3_pairs(q, p)));
    }
    claims
}

/// No row of the cross product of `scans` is both `c1`'s and `c2`'s:
/// `|c1| + |c2| ≤ Π` of the inputs' rows, a table's or a class's
/// ([`properties::disjoint`]). None if the product has more than
/// `max_product` factors.
fn disjoint_link(a: &Analyzer, classes: &HashMap<usize, Class>, c1: &Class, c2: &Class, scans: &[(Input, SchemaRef)]) -> Vec<Bool> {
    let inputs: Option<Vec<Int>> = scans
        .iter()
        .map(|(t, _)| match t {
            Input::Table(t) => {
                let mut vars = a.tables.values().filter(|v| v.display == *t);
                match (vars.next(), vars.next()) {
                    (Some(v), None) => Some(v.var.clone()),
                    _ => None,
                }
            }
            Input::Class(c) => Some(classes[c].card.clone()),
        })
        .collect();
    let Some(inputs) = inputs else { return vec![] };
    let Some(whole) = product(&inputs.iter().collect::<Vec<_>>(), a.max_product) else { return vec![] };
    properties::disjoint(&[&c1.card, &c2.card], &whole)
}

/// An analyzer node's quantities.
struct Quantities {
    card: Int,
    ndv: Vec<Int>,
    min: Vec<Option<Int>>,
    max: Vec<Option<Int>>,
}

impl Quantities {
    fn of(a: &Analyzer, x: usize) -> Quantities {
        let n = &a.nodes[x];
        let int = |v: &String| Int::new_const(v.as_str());
        Quantities {
            card: int(&n.var),
            ndv: n.ndv_vars.iter().map(int).collect(),
            min: n.min_vars.iter().map(|v| v.as_ref().map(int)).collect(),
            max: n.max_vars.iter().map(|v| v.as_ref().map(int)).collect(),
        }
    }
}

/// Column `j` of `q` paired with `p`: `Ndv`, and `Min` and `Max` where
/// both have them.
fn column_pairs<'q>(q: &'q Quantities, j: usize, p: &'q Column3) -> Vec<Pair<'q>> {
    let mut out = vec![Pair::Ndv(&q.ndv[j], &p.ndv)];
    if let (Some(a), Some(b)) = (&q.min[j], &p.min) {
        out.push(Pair::Min(a, b));
    }
    if let (Some(a), Some(b)) = (&q.max[j], &p.max) {
        out.push(Pair::Max(a, b));
    }
    out
}

/// Two classes' columns paired: `Ndv`, and `Min` and `Max` where both have
/// them.
fn column3_pairs<'q>(q: &'q Column3, p: &'q Column3) -> Vec<Pair<'q>> {
    let mut out = vec![Pair::Ndv(&q.ndv, &p.ndv)];
    if let (Some(a), Some(b)) = (&q.min, &p.min) {
        out.push(Pair::Min(a, b));
    }
    if let (Some(a), Some(b)) = (&q.max, &p.max) {
        out.push(Pair::Max(a, b));
    }
    out
}

/// A single node's quantities, as a class: per column, those of the first
/// of its `columns` that is it.
fn own(a: &Analyzer, x: usize, columns: &[Option<Column>]) -> Class {
    let q = Quantities::of(a, x);
    let mut out = BTreeMap::new();
    for (j, col) in columns.iter().enumerate() {
        if let Some(col) = col {
            out.entry(col.clone()).or_insert_with(|| Column3 { ndv: q.ndv[j].clone(), min: q.min[j].clone(), max: q.max[j].clone() });
        }
    }
    Class { card: q.card, columns: out, exprs: HashMap::new() }
}

impl SpjNode {
    /// This node with each input `k` renamed `sigma[k]`, over `scans` (its
    /// own if empty), its predicates canonical again.
    fn mapped(&self, sigma: &[usize], scans: &[(Input, SchemaRef)]) -> SpjNode {
        SpjNode {
            scans: if scans.is_empty() { self.scans.clone() } else { scans.to_vec() },
            preds: canonical(self.preds.iter().map(|e| relabel(e, sigma)).collect()),
            columns: self.columns.iter().map(|c| c.as_ref().map(|e| relabel(e, sigma))).collect(),
        }
    }

    /// Each output column that is a base column, mapped by `tau`.
    fn keyed(&self, tau: &[usize]) -> Vec<Option<Column>> {
        self.columns
            .iter()
            .map(|c| match c {
                Some(Expr::Column(c)) => Some(relabeled(c, tau)),
                _ => None,
            })
            .collect()
    }
}

/// `e` with each base column's input `k` renamed `sigma[k]`.
fn relabel(e: &Expr, sigma: &[usize]) -> Expr {
    e.clone()
        .transform_up(|x| match x {
            Expr::Column(c) => match instance(&c) {
                Some(k) => Ok(Transformed::yes(Expr::Column(base_column(sigma[k], &c.name)))),
                None => Ok(Transformed::no(Expr::Column(c))),
            },
            x => Ok(Transformed::no(x)),
        })
        .map(|t| t.data)
        .unwrap_or_else(|_| e.clone())
}

/// Base column `name` of input `k`.
fn base_column(k: usize, name: &str) -> Column {
    Column::new(Some(TableReference::bare(format!("i{k}"))), name)
}

/// The input a base column names.
fn instance(c: &Column) -> Option<usize> {
    c.relation.as_ref()?.table().strip_prefix('i')?.parse().ok()
}

/// How a join's keys compare.
fn key_op(n: NullEquality) -> Operator {
    match n {
        NullEquality::NullEqualsNull => Operator::IsNotDistinctFrom,
        NullEquality::NullEqualsNothing => Operator::Eq,
    }
}

/// `e`, over the columns of `schema`, rewritten over base columns:
/// `columns` gives each of `schema`'s. None if `e` is opaque or reads an
/// opaque column.
fn substitute(e: &Expr, schema: &DFSchema, columns: &[Option<Expr>]) -> Option<Expr> {
    if opaque(e) {
        return None;
    }
    let e = e
        .clone()
        .transform_up(|x| match x {
            Expr::Column(c) => schema
                .index_of_column(&c)
                .ok()
                .and_then(|j| columns.get(j).cloned().flatten())
                .map(Transformed::yes)
                .ok_or_else(|| DataFusionError::Plan(format!("no base column for {c}"))),
            x => Ok(Transformed::no(x)),
        })
        .ok()?
        .data;
    Some(e.unalias_nested().data)
}

/// The conjuncts of `preds`, without aliases, each comparison's operands
/// in `Display` order and each `LIKE` as observed plans read it
/// ([`observed::like`]), sorted by `Display` and deduplicated.
fn canonical(preds: Vec<Expr>) -> Vec<Expr> {
    let like = |e: Expr| e.transform_up(|x| Ok(observed::like(x))).map(|t| t.data).expect("rewriting LIKE cannot fail");
    let out: Vec<Expr> =
        preds.into_iter().flat_map(split_conjunction_owned).map(|e| ordered(like(e.unalias_nested().data))).collect();
    sorted(out)
}

/// `es` sorted by `Display`, deduplicated.
fn sorted(mut es: Vec<Expr>) -> Vec<Expr> {
    es.sort_by_cached_key(|e| e.to_string());
    let mut seen = HashSet::new();
    es.retain(|e| seen.insert(e.clone()));
    es
}

/// `e` with each comparison's operands, and each `IN` list, in `Display`
/// order.
fn ordered(e: Expr) -> Expr {
    e.transform_up(|x| match x {
        Expr::InList(mut l) => {
            l.list = sorted(l.list);
            Ok(Transformed::yes(Expr::InList(l)))
        }
        Expr::BinaryExpr(BinaryExpr { left, op, right }) => match op.swap() {
            Some(swapped) if left.to_string() > right.to_string() => {
                Ok(Transformed::yes(Expr::BinaryExpr(BinaryExpr { left: right, op: swapped, right: left })))
            }
            _ => Ok(Transformed::no(Expr::BinaryExpr(BinaryExpr { left, op, right }))),
        },
        x => Ok(Transformed::no(x)),
    })
    .map(|t| t.data)
    .expect("reordering cannot fail")
}

/// The base columns of `nodes`, all over the same inputs, each input `k`
/// qualified `i{k}`: a table's columns, or every column any node reads of
/// a class.
fn base_schema(nodes: &[&SpjNode]) -> Option<DFSchema> {
    let mut out = DFSchema::empty();
    for k in 0..nodes[0].scans.len() {
        let mut fields: Vec<Arc<Field>> = vec![];
        for n in nodes {
            for f in n.scans[k].1.fields() {
                if !fields.iter().any(|g| g.name() == f.name()) {
                    fields.push(f.clone());
                }
            }
        }
        let schema = Schema::new(fields);
        out = out.join(&DFSchema::try_from_qualified_schema(format!("i{k}"), &schema).ok()?).ok()?;
    }
    Some(out)
}

/// Each mapping of `inputs` onto themselves, within like ones, the
/// identity first.
fn mappings(inputs: &[Input]) -> Vec<Mapping> {
    let mut out = vec![(0..inputs.len()).collect::<Mapping>()];
    let distinct: BTreeSet<&Input> = inputs.iter().collect();
    for t in distinct {
        let of: Vec<usize> = inputs.iter().enumerate().filter(|(_, u)| *u == t).map(|(k, _)| k).collect();
        let mut next = vec![];
        for perm in permutations(&of) {
            for s in &out {
                let mut s = s.clone();
                for (&k, &m) in of.iter().zip(&perm) {
                    s[k] = m;
                }
                next.push(s);
            }
        }
        out = next;
    }
    out
}

/// Every ordering of `xs`.
fn permutations(xs: &[usize]) -> Vec<Vec<usize>> {
    if xs.is_empty() {
        return vec![vec![]];
    }
    let mut out = vec![];
    for (i, &x) in xs.iter().enumerate() {
        let rest: Vec<usize> = xs.iter().enumerate().filter(|&(j, _)| j != i).map(|(_, &y)| y).collect();
        for mut p in permutations(&rest) {
            p.insert(0, x);
            out.push(p);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `x³ + y³ = z³` has no solution in `x, y, z > 1`, which Z3 cannot
    /// decide: its negation is valid, but checking it spends any limit.
    fn hard() -> Bool {
        let (x, y, z) = (Int::new_const("x"), Int::new_const("y"), Int::new_const("z"));
        let cube = |v: &Int| v * v * v;
        Bool::and(&[x.gt(1), y.gt(1), z.gt(1), (cube(&x) + cube(&y)).eq(cube(&z))]).not()
    }

    /// `x < 5` and `x >= 5` are disjoint.
    fn easy() -> Bool {
        let x = Int::new_const("x");
        Bool::and(&[x.lt(5), x.ge(5)]).not()
    }

    fn spent(d: &Decide) -> u64 {
        match d.solver.get_statistics().value("rlimit count") {
            Some(z3::StatisticsValue::UInt(n)) => n.into(),
            v => panic!("rlimit count: {v:?}"),
        }
    }

    /// The limit is per check: after checks that together spent more, a
    /// simple one is still decided.
    #[test]
    fn decide_limit_is_per_check() {
        let d = Decide::new();
        while spent(&d) <= u64::from(DECIDE_RLIMIT) {
            assert!(!d.valid(&hard()));
        }
        assert!(d.valid(&easy()));
    }

    /// The first check is limited too: a hard formula is not valid within
    /// a small limit.
    #[test]
    fn decide_first_check_is_limited() {
        let d = Decide::with_rlimit(1_000);
        assert!(!d.valid(&hard()));
        assert!(spent(&d) < 100_000, "{}", spent(&d));
        assert!(d.valid(&easy()));
    }

    #[test]
    fn union_find_composes_mappings() {
        // x's inputs 0, 1 are y's 1, 0; y's are z's 1, 0: x's are z's.
        let mut uf = UnionFind::new(3);
        uf.to_parent = vec![vec![0, 1]; 3];
        uf.union(0, 1, &[1, 0]);
        uf.union(1, 2, &[1, 0]);
        assert_eq!(uf.find(0), (2, vec![0, 1]));
        assert_eq!(uf.find(1), (2, vec![1, 0]));
    }

    #[test]
    fn mappings_permute_within_like_inputs() {
        let t = |s: &str| Input::Table(s.to_string());
        assert_eq!(mappings(&[t("a"), t("a"), t("b")]), vec![vec![0, 1, 2], vec![1, 0, 2]]);
        let c = Input::Class;
        assert_eq!(mappings(&[t("a"), c(3), c(3)]), vec![vec![0, 1, 2], vec![0, 2, 1]]);
    }

    #[test]
    fn reduction_keeps_edges_whose_columns_a_path_drops() {
        let col = |n: &str| base_column(0, n);
        let class = |name: &str, cols: &[&str]| Class {
            card: Int::new_const(name),
            columns: cols
                .iter()
                .map(|c| (col(c), Column3 { ndv: Int::new_const(format!("{name}_{c}")), min: None, max: None }))
                .collect(),
            exprs: HashMap::new(),
        };
        let edge = |sub, sup| Edge { sub, sup, sigma: vec![0] };
        // 0 ⊆ 1 ⊆ 2 and 0 ⊆ 2: the path implies the direct edge only if
        // 1 has column x.
        for (middle, kept) in [(vec!["x"], 2), (vec![], 3)] {
            let classes = HashMap::from([(0, class("a", &["x"])), (1, class("b", &middle)), (2, class("c", &["x"]))]);
            assert_eq!(reduced(&[edge(0, 2), edge(0, 1), edge(1, 2)], &classes).len(), kept);
        }
    }
}
