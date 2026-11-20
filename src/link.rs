//! Link: properties between select-project-join subtrees, whatever the
//! plan's shape.
//!
//! The [rules](crate::rules) apply [properties](crate::properties) where
//! the plan's shape makes the relationship plain: an operator and its
//! input, one op output. Link relates the rest, in every plan the analyzer
//! visited.
//!
//! An `SpjNode` is a select-project-join subtree: scans, inner joins,
//! filters, projections, aliases, repartitions and sorts. Its rows are
//! those of its scans' cross product on which every predicate is TRUE,
//! some columns projected. Predicates and columns are over base columns,
//! `i{k}.name` for the scan `k`. A subtree is none if a predicate is
//! volatile or opaque (`rules::opaque`), or a scan applies its filters
//! inexactly or has a `fetch`: its rows are then not its predicates'.
//!
//! [`link_all`] partitions the nodes by their tables (a multiset). Within
//! one, nodes compare under each mapping of one's instances onto the
//! other's, by their sets of conjuncts (interned once per node) or, where
//! those don't nest, by a solver of link's own deciding from the
//! predicates `P1` and `P2`, encoded in three-valued logic
//! (`predicates`), whether `¬(P1 ∧ P2)`, `P1 ⇒ P2` or `P2 ⇒ P1` is valid.
//! The predicates' variables never reach the analysis's solver.
//!
//! - **Same rows**: nodes with equal conjuncts, then representatives
//!   whose predicates imply each other, are unioned into classes. Each
//!   class of several nodes gets synthetic variables (card, and ndv, min,
//!   max per base column) that its members equal (`eq link`).
//! - **Subset**: a superset of conjuncts, or `P1 ⇒ P2`, between classes'
//!   representatives is an edge of a graph. Only its transitive reduction
//!   is asserted (`subset link`): an edge is left out if a path implies
//!   all its claims, Z3 deriving them.
//! - **Disjoint**: each pair of classes whose representatives' conjuncts
//!   don't nest, with `¬(P1 ∧ P2)` valid, on the classes' cards
//!   (`disjoint link`). The members' follow by their `eq link`s.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use datafusion::arrow::datatypes::SchemaRef;
use datafusion::common::tree_node::{Transformed, TreeNode};
use datafusion::common::{Column, DFSchema, DataFusionError, NullEquality, TableReference};
use datafusion::logical_expr::logical_plan::{JoinType, LogicalPlan};
use datafusion::logical_expr::utils::split_conjunction_owned;
use datafusion::logical_expr::{BinaryExpr, Expr, Operator, binary_expr};
use z3::ast::{Bool, Int};
use z3::{SatResult, Solver};

use crate::analysis::{Analyzer, inexact_filters, product, solver_with_limits};
use crate::predicates::Encoder;
use crate::properties::{self, Pair};
use crate::rules::opaque;

/// A select-project-join subtree: the rows of its scans' cross product
/// that satisfy every predicate, with some columns projected.
#[derive(Clone)]
pub(crate) struct SpjNode {
    /// The analyzer node (`Analyzer::nodes`) at the subtree's root.
    node: usize,
    /// Each scan: its table (display name) and the table's schema.
    /// Base columns name scan `k` by the relation `i{k}`.
    scans: Vec<(String, SchemaRef)>,
    /// The conjuncts, over base columns, canonical: sorted, deduplicated.
    preds: Vec<Expr>,
    /// Each root output column as an expression over base columns,
    /// `None` if opaque.
    columns: Vec<Option<Expr>>,
}

/// A mapping of a partition's scans onto themselves, within each table:
/// scan `k` becomes `σ[k]`.
type Mapping = Vec<usize>;

/// Asserts every property link finds between the rows of `a`'s operators,
/// once its rules have visited every plan.
pub fn link_all(a: &Analyzer) {
    let mut partitions: HashMap<Vec<String>, Vec<SpjNode>> = HashMap::new();
    for c in spj_nodes(a).into_iter().flatten() {
        let c = c.sorted();
        partitions.entry(c.scans.iter().map(|(t, _)| t.clone()).collect()).or_default().push(c);
    }
    let mut partitions: Vec<Vec<SpjNode>> = partitions.into_values().collect();
    partitions.sort_by_key(|p| p[0].node);
    let mut link = Link { a, decide: Decide::new(), interned: HashMap::new(), classes: 0 };
    for (id, nodes) in partitions.into_iter().enumerate() {
        link.partition(id, nodes);
    }
}

/// A node of a partition, with what is computed of it once: its variants
/// under each of the partition's mappings, and their conjuncts' keys.
struct Linked {
    /// Under each mapping, the first the identity.
    variants: Vec<SpjNode>,
    /// The interned conjuncts of each variant, sorted.
    keys: Vec<Vec<u32>>,
}

/// An equality class's quantities: its card, and per base column (named
/// as in its root) ndv, min and max.
struct Class {
    card: Int,
    columns: BTreeMap<Column, Column3>,
}

struct Column3 {
    ndv: Int,
    min: Option<Int>,
    max: Option<Int>,
}

/// A subset edge between classes: `sub`'s rows are among `sup`'s, `sub`'s
/// scan `k` mapped to `sup`'s `σ[k]`.
#[derive(Clone, PartialEq, Eq, Hash)]
struct Edge {
    sub: usize,
    sup: usize,
    sigma: Mapping,
}

/// The state of [`link_all`] across partitions.
struct Link<'a, 'b> {
    a: &'a Analyzer<'b>,
    decide: Decide,
    /// Each conjunct seen, by id.
    interned: HashMap<Expr, u32>,
    /// Classes given synthetic variables so far.
    classes: usize,
}

impl Link<'_, '_> {
    /// Links the nodes of one partition, all over the same sorted scans.
    fn partition(&mut self, id: usize, nodes: Vec<SpjNode>) {
        // Tries every mapping of a table's instances, factorial in them;
        // revisit.
        let mappings = mappings(&nodes[0].scans);
        let linked: Vec<Linked> = nodes
            .iter()
            .map(|c| {
                let variants: Vec<SpjNode> = mappings.iter().map(|s| c.mapped(s, &c.scans)).collect();
                let keys = variants.iter().map(|v| self.key(&v.preds)).collect();
                Linked { variants, keys }
            })
            .collect();
        let mut uf = UnionFind::new(linked.len(), nodes[0].scans.len());

        // Same conjuncts, up to a mapping.
        let mut by_key: HashMap<&[u32], usize> = HashMap::new();
        for (x, l) in linked.iter().enumerate() {
            match l.keys.iter().enumerate().find_map(|(v, k)| Some((v, *by_key.get(&k[..])?))) {
                Some((v, y)) => uf.union(x, y, &mappings[v]),
                None => {
                    by_key.insert(&l.keys[0], x);
                }
            }
        }

        // Between representatives: equivalent predicates join a class,
        // nested ones give an edge, disjoint ones a disjoint pair.
        let reps: Vec<usize> = (0..linked.len()).filter(|&x| uf.find(x).0 == x).collect();
        let mut edges: Vec<Edge> = vec![];
        let mut disjoint: Vec<(usize, usize)> = vec![];
        for (i, &r1) in reps.iter().enumerate() {
            for &r2 in &reps[i + 1..] {
                let (l1, l2) = (&linked[r1], &linked[r2]);
                let quick = (0..mappings.len()).find_map(|v| {
                    let (k1, k2) = (&l1.keys[v], &l2.keys[0]);
                    match (subset(k2, k1), subset(k1, k2)) {
                        (true, true) => Some((v, true, true, false)),
                        (true, false) => Some((v, true, false, false)),
                        (false, true) => Some((v, false, true, false)),
                        (false, false) => None,
                    }
                });
                let relations: Vec<(usize, bool, bool, bool)> = match quick {
                    Some(q) => vec![q],
                    None => (0..mappings.len())
                        .filter_map(|v| {
                            let r = self.decide.relation((id, l1.keys[v].clone(), l2.keys[0].clone()), &l1.variants[v], &l2.variants[0])?;
                            Some((v, r.sub, r.sup, r.disjoint))
                        })
                        .collect(),
                };
                for (v, sub, sup, apart) in relations {
                    let sigma = &mappings[v];
                    if apart {
                        disjoint.push((r1, r2));
                    }
                    match (sub, sup) {
                        (true, true) => uf.union(r1, r2, sigma),
                        (true, false) => edges.push(Edge { sub: r1, sup: r2, sigma: sigma.clone() }),
                        (false, true) => edges.push(Edge { sub: r2, sup: r1, sigma: inverse(sigma) }),
                        (false, false) => {}
                    }
                }
            }
        }

        let classes = self.eq_links(&nodes, &mut uf);
        let mut seen = HashSet::new();
        let edges: Vec<Edge> = edges
            .into_iter()
            .filter_map(|e| {
                let ((sub, ts), (sup, tp)) = (uf.find(e.sub), uf.find(e.sup));
                let ts_inv = inverse(&ts);
                let sigma = (0..e.sigma.len()).map(|k| tp[e.sigma[ts_inv[k]]]).collect();
                let e = Edge { sub, sup, sigma };
                (sub != sup && seen.insert(e.clone())).then_some(e)
            })
            .collect();
        for e in reduced(&edges, &classes) {
            self.a.assert_property("subset link", subset_link(&classes[&e.sub], &classes[&e.sup], &e.sigma));
        }

        // A disjoint pair's claim reads only cards: one per pair of classes.
        let mut pairs: BTreeSet<(usize, usize)> = BTreeSet::new();
        for (x, y) in disjoint {
            let (x, y) = (uf.find(x).0, uf.find(y).0);
            if x != y {
                pairs.insert((x.min(y), x.max(y)));
            }
        }
        for (x, y) in pairs {
            self.a.assert_property("disjoint link", disjoint_link(self.a, &classes[&x], &classes[&y], &nodes[0].scans));
        }
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

    /// Each class's quantities, by its root. A class of several nodes gets
    /// synthetic variables, and each member's are asserted equal to them;
    /// a single node's are its own.
    fn eq_links(&mut self, nodes: &[SpjNode], uf: &mut UnionFind) -> HashMap<usize, Class> {
        let mut members: HashMap<usize, Vec<(usize, Mapping)>> = HashMap::new();
        for x in 0..nodes.len() {
            let (root, tau) = uf.find(x);
            members.entry(root).or_default().push((x, tau));
        }
        let mut roots: Vec<usize> = members.keys().copied().collect();
        roots.sort();
        let mut out = HashMap::new();
        for root in roots {
            let ms = &members[&root];
            let class = match &ms[..] {
                [(x, _)] => own(self.a, &nodes[*x]),
                _ => {
                    let class = self.synthetic(nodes, ms);
                    for (x, tau) in ms {
                        self.a.assert_property("eq link", eq_link(self.a, &nodes[*x], tau, &class));
                    }
                    class
                }
            };
            out.insert(root, class);
        }
        out
    }

    /// Synthetic variables for the class of `members` (each with its
    /// mapping onto the root): card, and per base column any member
    /// projects, ndv, and min and max if any member has them.
    fn synthetic(&mut self, nodes: &[SpjNode], members: &[(usize, Mapping)]) -> Class {
        let base = format!("eq{}", self.classes);
        self.classes += 1;
        let mut columns: BTreeMap<Column, Column3> = BTreeMap::new();
        for (x, tau) in members {
            let q = Quantities::of(self.a, &nodes[*x]);
            for (j, c) in nodes[*x].columns.iter().enumerate() {
                let Some(Expr::Column(c)) = c else { continue };
                let c = relabeled(c, tau);
                let n = columns.len();
                let q3 = columns.entry(c).or_insert_with(|| Column3 { ndv: Int::new_const(format!("{base}_c{n}")), min: None, max: None });
                let name = q3.ndv.to_string();
                if q.min[j].is_some() && q3.min.is_none() {
                    q3.min = Some(Int::new_const(format!("{name}_min")));
                }
                if q.max[j].is_some() && q3.max.is_none() {
                    q3.max = Some(Int::new_const(format!("{name}_max")));
                }
            }
        }
        Class { card: Int::new_const(base.as_str()), columns }
    }
}

/// A union-find over a partition's nodes, each with the mapping of its
/// scans onto its parent's.
struct UnionFind {
    parent: Vec<usize>,
    to_parent: Vec<Mapping>,
}

impl UnionFind {
    fn new(n: usize, scans: usize) -> UnionFind {
        UnionFind { parent: (0..n).collect(), to_parent: vec![(0..scans).collect(); n] }
    }

    /// `x`'s root, and the mapping of `x`'s scans onto the root's.
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

    /// Unions `x` and `y`, `x`'s scan `k` being `y`'s `σ[k]`.
    fn union(&mut self, x: usize, y: usize, sigma: &[usize]) {
        let ((rx, tx), (ry, ty)) = (self.find(x), self.find(y));
        if rx == ry {
            return;
        }
        // rx's k is x's tx⁻¹[k], y's σ[…], ry's ty[…].
        let tx_inv = inverse(&tx);
        self.to_parent[rx] = (0..tx.len()).map(|k| ty[sigma[tx_inv[k]]]).collect();
        self.parent[rx] = ry;
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

/// True if sorted `a` is a subset of sorted `b`.
fn subset(a: &[u32], b: &[u32]) -> bool {
    let mut b = b.iter();
    a.iter().all(|x| b.any(|y| y == x))
}

/// Base column `c` with its scan mapped by `sigma`.
fn relabeled(c: &Column, sigma: &[usize]) -> Column {
    match instance(c) {
        Some(k) => base_column(sigma[k], &c.name),
        None => c.clone(),
    }
}

/// The edges of `edges` whose claims no path of other remaining edges
/// implies: a path implies an edge's claims if it maps the scans as the
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
                let p = sup.columns.get(&relabeled(c, &e.sigma))?;
                Some((c, q.min.is_some() && p.min.is_some(), q.max.is_some() && p.max.is_some()))
            })
            .collect();
        let carries = |x: &Class, mu: &[usize]| {
            needed.iter().all(|(c, min, max)| {
                x.columns.get(&relabeled(c, mu)).is_some_and(|q| (!min || q.min.is_some()) && (!max || q.max.is_some()))
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

/// How the predicates `P1` and `P2` of two nodes over the same scans
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
    known: HashMap<(usize, Vec<u32>, Vec<u32>), Option<Relation>>,
}

impl Decide {
    fn new() -> Decide {
        Decide::with_rlimit(DECIDE_RLIMIT)
    }

    fn with_rlimit(rlimit: u32) -> Decide {
        Decide { solver: solver_with_limits(rlimit, DECIDE_TIMEOUT_MS), encoders: 0, known: HashMap::new() }
    }

    /// How `c1`'s predicates relate to `c2`'s, both over `c2`'s scans,
    /// `key` naming the pair. None if the scans' columns don't type.
    fn relation(&mut self, key: (usize, Vec<u32>, Vec<u32>), c1: &SpjNode, c2: &SpjNode) -> Option<Relation> {
        if let Some(r) = self.known.get(&key) {
            return *r;
        }
        let r = base_schema(&c2.scans).map(|schema| {
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

/// `c`, a member of `class` mapped onto its root by `tau`, is the class's
/// rows: its card and each base column's quantities equal the class's
/// ([`properties::same`]).
fn eq_link(a: &Analyzer, c: &SpjNode, tau: &[usize], class: &Class) -> Vec<Bool> {
    let q = Quantities::of(a, c);
    let mut pairs = vec![Pair::Card(&q.card, &class.card)];
    for (j, col) in c.columns.iter().enumerate() {
        let Some(Expr::Column(col)) = col else { continue };
        let Some(q3) = class.columns.get(&relabeled(col, tau)) else { continue };
        pairs.extend(column_pairs(&q, j, q3));
    }
    properties::same(&pairs)
}

/// `sub`'s rows are among `sup`'s, `sub`'s scan `k` being `sup`'s
/// `σ[k]`: `|sub| ≤ |sup|`, and each base column's values within
/// ([`properties::within`]).
fn subset_link(sub: &Class, sup: &Class, sigma: &[usize]) -> Vec<Bool> {
    let mut pairs = vec![Pair::Card(&sub.card, &sup.card)];
    for (c, q) in &sub.columns {
        let Some(p) = sup.columns.get(&relabeled(c, sigma)) else { continue };
        pairs.push(Pair::Ndv(&q.ndv, &p.ndv));
        if let (Some(a), Some(b)) = (&q.min, &p.min) {
            pairs.push(Pair::Min(a, b));
        }
        if let (Some(a), Some(b)) = (&q.max, &p.max) {
            pairs.push(Pair::Max(a, b));
        }
    }
    properties::within(&pairs)
}

/// No row of the cross product of `scans`' tables is both `c1`'s and
/// `c2`'s: `|c1| + |c2| ≤ Π |T_i|` ([`properties::disjoint`]). None if the
/// product has more than `max_product` factors.
fn disjoint_link(a: &Analyzer, c1: &Class, c2: &Class, scans: &[(String, SchemaRef)]) -> Vec<Bool> {
    let tables: Option<Vec<Int>> = scans
        .iter()
        .map(|(t, _)| {
            let mut vars = a.tables.values().filter(|v| v.display == *t);
            match (vars.next(), vars.next()) {
                (Some(v), None) => Some(v.var.clone()),
                _ => None,
            }
        })
        .collect();
    let Some(tables) = tables else { return vec![] };
    let Some(whole) = product(&tables.iter().collect::<Vec<_>>(), a.max_product) else { return vec![] };
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
    fn of(a: &Analyzer, c: &SpjNode) -> Quantities {
        let n = &a.nodes[c.node];
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
/// both have them. Both are one base column, so they share a type and
/// unit.
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

/// A single node's quantities, as a class: per base column, those of the
/// first column projecting it.
fn own(a: &Analyzer, c: &SpjNode) -> Class {
    let q = Quantities::of(a, c);
    let mut columns = BTreeMap::new();
    for (j, col) in c.columns.iter().enumerate() {
        if let Some(Expr::Column(col)) = col {
            columns.entry(col.clone()).or_insert_with(|| Column3 { ndv: q.ndv[j].clone(), min: q.min[j].clone(), max: q.max[j].clone() });
        }
    }
    Class { card: q.card, columns }
}

/// The [`SpjNode`] of each of `a`'s nodes, if it is one.
fn spj_nodes(a: &Analyzer) -> Vec<Option<SpjNode>> {
    let mut out: Vec<Option<SpjNode>> = Vec::with_capacity(a.nodes.len());
    for i in 0..a.nodes.len() {
        let c = spj_node(a, i, &out);
        out.push(c.filter(|c| c.columns.len() == a.nodes[i].ndv_vars.len()));
    }
    out
}

/// The [`SpjNode`] of `a`'s node `i`, given its inputs' in `built`.
fn spj_node(a: &Analyzer, i: usize, built: &[Option<SpjNode>]) -> Option<SpjNode> {
    let node = &a.nodes[i];
    let input = |k: usize| built.get(*node.inputs.get(k)?)?.clone();
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
                node: i,
                scans: vec![(display.clone(), scan.source.schema())],
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
            let mut c = input(0)?;
            c.preds.push(substitute(&f.predicate, f.input.schema(), &c.columns)?);
            c
        }
        LogicalPlan::Projection(p) => {
            let mut c = input(0)?;
            c.columns = p.expr.iter().map(|e| substitute(e, p.input.schema(), &c.columns)).collect();
            c
        }
        LogicalPlan::Join(j) if j.join_type == JoinType::Inner => {
            let (mut l, r) = (input(0)?, input(1)?);
            let shift = l.scans.len();
            let r = r.mapped(&(0..r.scans.len()).map(|k| k + shift).collect::<Vec<_>>(), &[]);
            let op = match j.null_equality {
                NullEquality::NullEqualsNull => Operator::IsNotDistinctFrom,
                NullEquality::NullEqualsNothing => Operator::Eq,
            };
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
        LogicalPlan::SubqueryAlias(_) | LogicalPlan::Repartition(_) => input(0)?,
        LogicalPlan::Sort(s) if s.fetch.is_none() => input(0)?,
        _ => return None,
    };
    out.node = i;
    out.preds = canonical(out.preds);
    Some(out)
}

impl SpjNode {
    /// This node with its scans sorted by table, so that nodes over the
    /// same tables have the same scans.
    fn sorted(&self) -> SpjNode {
        let mut order: Vec<usize> = (0..self.scans.len()).collect();
        order.sort_by(|&x, &y| self.scans[x].0.cmp(&self.scans[y].0));
        let mut sigma = vec![0; order.len()];
        for (p, &k) in order.iter().enumerate() {
            sigma[k] = p;
        }
        let scans: Vec<_> = order.iter().map(|&k| self.scans[k].clone()).collect();
        self.mapped(&sigma, &scans)
    }

    /// This node with each scan `k` renamed `sigma[k]`, over `scans` (its
    /// own if empty), its predicates canonical again.
    fn mapped(&self, sigma: &[usize], scans: &[(String, SchemaRef)]) -> SpjNode {
        let rename = |e: &Expr| -> Expr {
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
        };
        SpjNode {
            node: self.node,
            scans: if scans.is_empty() { self.scans.clone() } else { scans.to_vec() },
            preds: canonical(self.preds.iter().map(rename).collect()),
            columns: self.columns.iter().map(|c| c.as_ref().map(rename)).collect(),
        }
    }
}

/// Base column `name` of scan `k`.
fn base_column(k: usize, name: &str) -> Column {
    Column::new(Some(TableReference::bare(format!("i{k}"))), name)
}

/// The scan a base column names.
fn instance(c: &Column) -> Option<usize> {
    c.relation.as_ref()?.table().strip_prefix('i')?.parse().ok()
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
/// in `Display` order, sorted by `Display` and deduplicated.
fn canonical(preds: Vec<Expr>) -> Vec<Expr> {
    let mut out: Vec<Expr> =
        preds.into_iter().flat_map(split_conjunction_owned).map(|e| ordered(e.unalias_nested().data)).collect();
    out.sort_by_cached_key(|e| e.to_string());
    let mut seen = HashSet::new();
    out.retain(|e| seen.insert(e.clone()));
    out
}

/// `e` with each comparison's operands in `Display` order.
fn ordered(e: Expr) -> Expr {
    e.transform_up(|x| match x {
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

/// The base columns of `scans`, each scan `k` qualified `i{k}`.
fn base_schema(scans: &[(String, SchemaRef)]) -> Option<DFSchema> {
    let mut out = DFSchema::empty();
    for (k, (_, schema)) in scans.iter().enumerate() {
        out = out.join(&DFSchema::try_from_qualified_schema(format!("i{k}"), schema).ok()?).ok()?;
    }
    Some(out)
}

/// Each mapping of `scans` onto themselves, within each table, the
/// identity first.
fn mappings(scans: &[(String, SchemaRef)]) -> Vec<Mapping> {
    let mut out = vec![(0..scans.len()).collect::<Mapping>()];
    let tables: BTreeSet<&String> = scans.iter().map(|(t, _)| t).collect();
    for t in tables {
        let of: Vec<usize> = scans.iter().enumerate().filter(|(_, (u, _))| u == t).map(|(k, _)| k).collect();
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
        // x's scans 0, 1 are y's 1, 0; y's are z's 1, 0: x's are z's.
        let mut uf = UnionFind::new(3, 2);
        uf.union(0, 1, &[1, 0]);
        uf.union(1, 2, &[1, 0]);
        assert_eq!(uf.find(0), (2, vec![0, 1]));
        assert_eq!(uf.find(1), (2, vec![1, 0]));
    }

    #[test]
    fn mappings_permute_within_tables() {
        let s = || std::sync::Arc::new(datafusion::arrow::datatypes::Schema::empty());
        let scans = vec![("a".to_string(), s()), ("a".to_string(), s()), ("b".to_string(), s())];
        assert_eq!(mappings(&scans), vec![vec![0, 1, 2], vec![1, 0, 2]]);
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
