//! Plans as terms (§5): executed plans, with what each operator actually
//! computed (`part`, `opt`, `rt`), and DataFusion's plans of a query to
//! bound.
//!
//! Projections, sorts and windows keep every row, so they are their
//! input's term; what they compute is read through, as expressions over
//! the columns below. A column is named by its table, and a table read
//! twice where both reads meet (a join) has its second read renamed by an
//! alias (§5, Aliases).

use std::collections::{BTreeMap, BTreeSet, HashMap};

use datafusion::common::tree_node::TreeNode;
use datafusion::common::{Column, JoinType, NullEquality, TableReference};
use datafusion::datasource::source_as_provider;
use datafusion::logical_expr::logical_plan::{Distinct, LogicalPlan};
use datafusion::logical_expr::utils::split_conjunction;
use datafusion::logical_expr::{BinaryExpr, Expr, Operator};

use super::expr::{Cmp, Col, E, Lit, Reader, Ty, flat_and};
use super::preds;
use super::terms::{CmpOp, Family, JoinKind, Pred, PredId, Rel, RelId, Terms, alias_col};
use crate::observed::{Catalog, ObservedPlan, Op, base_table, relation};

/// A fact about a term (§6.4).
#[derive(Debug, Clone)]
pub(crate) enum Fact {
    Card(RelId, u64),
    /// The build side's keys lie in `[lo, hi]` (`|rtv|` facts).
    KeyRange(RelId, Col, Option<i128>, Option<i128>),
    /// The build side has at least and at most this many distinct keys.
    KeyCount(RelId, Col, u64),
}

/// A translated relation: its term, and each output column as an
/// expression over the term's columns, where known.
#[derive(Clone)]
pub(crate) struct Out {
    pub rel: RelId,
    pub cols: Vec<Option<E>>,
    /// The scalar subqueries among its inputs whose single row each row
    /// carries (a cross join with an ungrouped aggregate), by column.
    pub scalars: BTreeMap<Col, RelId>,
}

/// What translation needs to know of the tables.
pub(crate) struct Tables<'a> {
    pub catalog: &'a Catalog,
}

impl Tables<'_> {
    pub(crate) fn ty(&self, table: &str, column: &str) -> Ty {
        self.catalog
            .tables
            .get(table)
            .and_then(|s| s.field_with_name(column).ok())
            .map_or(Ty::Other, |f| Ty::of(f.data_type()))
    }

    pub(crate) fn columns(&self, table: &str) -> Vec<String> {
        self.catalog.columns(table).unwrap_or_default()
    }
}

/// Shared building steps.
pub(crate) struct Builder<'a> {
    pub terms: &'a mut Terms,
    pub tables: &'a Tables<'a>,
}

impl Builder<'_> {
    /// `scan T`, aliased by `alias` if nonzero.
    pub(crate) fn scan(&mut self, table: &str, alias: u32) -> RelId {
        let r = self.terms.rel(Rel::Scan(table.to_string()));
        let cols: BTreeSet<Col> = self.tables.columns(table).iter().map(|c| format!("{table}.{c}")).collect();
        for c in self.tables.columns(table) {
            self.terms.types.insert(format!("{table}.{c}"), self.tables.ty(table, &c));
        }
        self.terms.set_cols(r, cols);
        if alias == 0 {
            return r;
        }
        for c in self.tables.columns(table) {
            self.terms.types.insert(alias_col(&format!("{table}.{c}"), alias), self.tables.ty(table, &c));
        }
        self.terms.rel(Rel::Alias(alias, r))
    }

    /// The column of a base table's column through `alias`.
    pub(crate) fn column(&self, table: &str, column: &str, alias: u32) -> (Col, Ty) {
        let c = format!("{table}.{column}");
        let c = if alias == 0 { c } else { alias_col(&c, alias) };
        (c, self.tables.ty(table, column))
    }

    /// `x` filtered by each conjunct of `e`.
    pub(crate) fn filter(&mut self, x: RelId, e: &E) -> RelId {
        let ps = preds::conjuncts(self.terms, e);
        self.filter_preds(x, &ps)
    }

    pub(crate) fn filter_preds(&mut self, mut x: RelId, ps: &[PredId]) -> RelId {
        for p in ps {
            if matches!(self.terms.get_pred(*p), Pred::True) {
                continue;
            }
            x = self.terms.rel(Rel::Filter(*p, x));
        }
        x
    }

    /// A column for expression `e`: itself if a column, else an
    /// expression column, which `x` is extended with.
    pub(crate) fn column_of(&mut self, x: &mut RelId, e: &E) -> Col {
        if let E::Col(c, t) = e {
            self.terms.types.insert(c.clone(), *t);
            return c.clone();
        }
        let g = format!("c:{}", e.text());
        self.terms.types.insert(g.clone(), e.ty());
        self.terms.exprs.insert(g.clone(), e.clone());
        self.terms.one(&g);
        let has = self.terms.cols_of(*x).is_some_and(|cs| cs.contains(&g));
        if !has {
            *x = self.terms.rel(Rel::Extend(g.clone(), *x));
        }
        g
    }

    /// A join of `kind` on equal pairs `on` (each side's expression), with
    /// `residual` the rest of its condition.
    pub(crate) fn join(
        &mut self,
        kind: JoinType,
        null_aware: bool,
        on: &[(E, E)],
        residual: Option<E>,
        null_eq: bool,
        l: RelId,
        r: RelId,
    ) -> Option<RelId> {
        // A right join is the left join with its inputs swapped, and so on.
        let (kind, l, r, on, swapped) = match kind {
            JoinType::Right => (JoinType::Left, r, l, flip(on), true),
            JoinType::RightSemi => (JoinType::LeftSemi, r, l, flip(on), true),
            JoinType::RightAnti => (JoinType::LeftAnti, r, l, flip(on), true),
            k => (k, l, r, on.to_vec(), false),
        };
        let _ = swapped;
        let (mut l, mut r) = (l, r);
        let mut pairs = vec![];
        for (a, b) in &on {
            let a = self.column_of(&mut l, a);
            let b = self.column_of(&mut r, b);
            pairs.push((a, b));
        }
        pairs.sort();
        pairs.dedup();
        // An inner join's residual is a filter above it.
        let (fam_residual, above) = match (kind, residual) {
            (JoinType::Inner, Some(e)) => (None, Some(e)),
            (_, Some(e)) => (Some(self.residual(&e)), None),
            (_, None) => (None, None),
        };
        let fam = self.terms.family(Family { pairs, null_eq, residual: fam_residual });
        let k = match kind {
            JoinType::Inner => JoinKind::Inner,
            JoinType::Left => JoinKind::Left,
            JoinType::LeftSemi => JoinKind::Semi,
            JoinType::LeftAnti if null_aware => JoinKind::NotIn,
            JoinType::LeftAnti => JoinKind::Anti,
            JoinType::Full => JoinKind::Full,
            _ => return None,
        };
        let j = self.terms.rel(Rel::Join(k, fam, l, r));
        Some(match above {
            Some(e) => self.filter(j, &e),
            None => j,
        })
    }

    /// A join of `kind` on predicate `q` alone, which nothing models.
    pub(crate) fn join_on(&mut self, kind: JoinType, null_aware: bool, q: PredId, l: RelId, r: RelId) -> Option<RelId> {
        let (kind, l, r) = match kind {
            JoinType::Right => (JoinType::Left, r, l),
            JoinType::RightSemi => (JoinType::LeftSemi, r, l),
            JoinType::RightAnti => (JoinType::LeftAnti, r, l),
            k => (k, l, r),
        };
        let k = match kind {
            JoinType::Inner => {
                let f = self.terms.family(Family { pairs: vec![], null_eq: false, residual: None });
                let j = self.terms.rel(Rel::Join(JoinKind::Inner, f, l, r));
                return Some(self.filter_preds(j, &[q]));
            }
            JoinType::Left => JoinKind::Left,
            JoinType::LeftSemi => JoinKind::Semi,
            JoinType::LeftAnti if null_aware => JoinKind::NotIn,
            JoinType::LeftAnti => JoinKind::Anti,
            JoinType::Full => JoinKind::Full,
            _ => return None,
        };
        let f = self.terms.family(Family { pairs: vec![], null_eq: false, residual: Some(q) });
        Some(self.terms.rel(Rel::Join(k, f, l, r)))
    }

    fn residual(&mut self, e: &E) -> PredId {
        let e = e.nnf(false).sorted();
        preds::make(self.terms, &e)
    }

    /// GROUP BY `keys` over `x`, with aggregate `values` (named columns) if
    /// anything reads them.
    pub(crate) fn group(&mut self, mut x: RelId, keys: &[E], values: &[(Col, Agg)]) -> (RelId, Vec<Col>) {
        let mut ks = vec![];
        for k in keys {
            let c = self.column_of(&mut x, k);
            ks.push(c);
        }
        let kset: BTreeSet<Col> = ks.iter().cloned().collect();
        let k = self.terms.colset(kset);
        if values.is_empty() {
            if keys.is_empty() {
                let g = self.terms.colset(BTreeSet::new());
                return (self.terms.rel(Rel::Scalar(g, x)), ks);
            }
            return (self.terms.rel(Rel::Group(k, x)), ks);
        }
        for (c, a) in values {
            self.terms.aggs.insert(c.clone(), a.clone());
            self.terms.types.insert(c.clone(), a.ty);
            self.terms.one(c);
        }
        let g = self.terms.colset(values.iter().map(|(c, _)| c.clone()).collect());
        if keys.is_empty() {
            return (self.terms.rel(Rel::Scalar(g, x)), ks);
        }
        (self.terms.rel(Rel::Aggregate(k, g, x)), ks)
    }

    /// The comparison `a op g` with `g` the column of scalar subquery `y`.
    pub(crate) fn cmp(&mut self, op: Cmp, a: &str, y: RelId, g: &str) -> Option<PredId> {
        let op = match op {
            Cmp::Gt => CmpOp::Gt,
            Cmp::Ge => CmpOp::Ge,
            Cmp::Lt => CmpOp::Lt,
            Cmp::Le => CmpOp::Le,
            Cmp::Eq => CmpOp::Eq,
            Cmp::Ne => return None,
        };
        self.terms.one(a);
        self.terms.one(g);
        Some(self.terms.pred(Pred::Cmp { op, a: a.to_string(), y, g: g.to_string() }))
    }

    /// A filter's predicates: comparisons of a column with a scalar
    /// subquery's value (one `scalars` holds) as `cmp_op`, the rest as
    /// their conjuncts.
    pub(crate) fn filter_with(&mut self, mut x: RelId, e: &E, scalars: &BTreeMap<Col, RelId>) -> RelId {
        let e = e.nnf(false);
        let parts = match e {
            E::And(xs) => xs,
            e => vec![e],
        };
        let mut rest = vec![];
        let mut cmps = vec![];
        for p in parts {
            if let E::Cmp(op, a, b) = &p {
                let found = match (a.as_ref(), b.as_ref()) {
                    (E::Col(a, _), E::Col(g, _)) if scalars.contains_key(g) && !scalars.contains_key(a) => Some((*op, a, g)),
                    (E::Col(g, _), E::Col(a, _)) if scalars.contains_key(g) && !scalars.contains_key(a) => Some((op.flip(), a, g)),
                    _ => None,
                };
                if let Some((op, a, g)) = found
                    && let Some(c) = self.cmp(op, a, scalars[g], g)
                {
                    cmps.push(c);
                    continue;
                }
            }
            rest.push(p);
        }
        x = self.filter(x, &flat_and(rest));
        self.filter_preds(x, &cmps)
    }

    /// `x` read without the inexact filters (`opt`) below it that `e`
    /// checks again: a filter keeping only rows satisfying `p`, over
    /// `opt o p y`, keeps those of `y` (§7.4 `opt_check`, here so that
    /// the filter needs no other filters moved out of its way).
    pub(crate) fn rechecked(&mut self, x: RelId, e: &E) -> RelId {
        let checked: BTreeSet<PredId> = preds::conjuncts(self.terms, e).into_iter().collect();
        self.strip_opts(x, &checked)
    }

    fn strip_opts(&mut self, x: RelId, checked: &BTreeSet<PredId>) -> RelId {
        match self.terms.get(x).clone() {
            Rel::Opt(_, p, y) if checked.contains(&p) => self.strip_opts(y, checked),
            Rel::Opt(o, p, y) => {
                let y2 = self.strip_opts(y, checked);
                if y2 == y { x } else { self.terms.rel(Rel::Opt(o, p, y2)) }
            }
            Rel::Filter(p, y) => {
                let y2 = self.strip_opts(y, checked);
                if y2 == y { x } else { self.terms.rel(Rel::Filter(p, y2)) }
            }
            Rel::Rt(f, o, y, bld) => {
                let y2 = self.strip_opts(y, checked);
                if y2 == y { x } else { self.terms.rel(Rel::Rt(f, o, y2, bld)) }
            }
            _ => x,
        }
    }

    /// A relation nothing models, with columns `cols` if known.
    pub(crate) fn opaque(&mut self, name: &str, cols: Option<BTreeSet<Col>>) -> RelId {
        let r = self.terms.rel(Rel::Opaque(name.to_string()));
        if let Some(cs) = cols {
            self.terms.set_cols(r, cs);
        }
        r
    }
}

fn flip(on: &[(E, E)]) -> Vec<(E, E)> {
    on.iter().map(|(a, b)| (b.clone(), a.clone())).collect()
}

/// An aggregate column's definition.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Agg {
    pub func: String,
    pub arg: Option<E>,
    pub distinct: bool,
    pub ty: Ty,
}

/// An aggregate expression as a column name and definition.
pub(crate) fn aggregate(e: &Expr, read: &dyn Fn(&Expr) -> Option<E>) -> Option<(Col, Agg)> {
    let e = match e {
        Expr::Alias(a) => a.expr.as_ref(),
        e => e,
    };
    let Expr::AggregateFunction(f) = e else { return None };
    if f.params.filter.is_some() || !f.params.order_by.is_empty() {
        return None;
    }
    let func = f.func.name().to_lowercase();
    let distinct = f.params.distinct;
    let arg = match f.params.args.as_slice() {
        [] => None,
        [Expr::Literal(..)] if func == "count" => None,
        [a] => Some(read(a)?),
        _ => return None,
    };
    let ty = match func.as_str() {
        "count" => Ty::Int,
        "avg" | "mean" => Ty::Real,
        "sum" | "min" | "max" | "first_value" | "last_value" | "any_value" => arg.as_ref().map_or(Ty::Other, E::ty),
        _ => Ty::Other,
    };
    let text = match &arg {
        None => format!("{func}(*)"),
        Some(a) if distinct => format!("{func}(DISTINCT {})", a.text()),
        Some(a) => format!("{func}({})", a.text()),
    };
    Some((format!("a:{text}"), Agg { func, arg, distinct, ty }))
}

// ---------------------------------------------------------------------
// Executed plans.
// ---------------------------------------------------------------------

/// Operators that may not have run to completion: below a `LIMIT`, the
/// probe side of a join that output nothing, and a scan that says it was
/// cut short.
fn stopped(plan: &ObservedPlan) -> Vec<bool> {
    let mut stopped = vec![false; plan.nodes.len()];
    for i in (0..plan.nodes.len()).rev() {
        let node = &plan.nodes[i];
        let empty = |n: &crate::observed::ONode| n.counted && n.rows == 0;
        let stops = match &node.op {
            Op::Limit { .. } => node.children.clone(),
            Op::Join { kind, .. }
                if (empty(&plan.nodes[node.children[1]]) || empty(node))
                    && !matches!(kind, JoinType::Left | JoinType::Full | JoinType::LeftAnti | JoinType::LeftMark) =>
            {
                vec![node.children[0]]
            }
            _ => vec![],
        };
        stopped[i] |= node.cut_short;
        if matches!(node.op, Op::Reuse { .. }) || node.blocking {
            continue;
        }
        for c in node.children.iter().copied() {
            stopped[c] |= stopped[i] || stops.contains(&c);
        }
    }
    stopped
}

/// An executed plan as terms: each counted operator's count is a fact on
/// its term.
pub(crate) fn executed(b: &mut Builder, plan: &ObservedPlan) -> (Vec<(String, Fact)>, RelId) {
    translate_observed(b, plan, true)
}

/// A plan as an engine planned it, as the query to bound: its operators'
/// logical meaning, without what the run did (early stops, pruning).
pub(crate) fn planned(b: &mut Builder, plan: &ObservedPlan) -> RelId {
    translate_observed(b, plan, false).1
}

fn translate_observed(b: &mut Builder, plan: &ObservedPlan, physical: bool) -> (Vec<(String, Fact)>, RelId) {
    let mut t = Executed {
        plan,
        name: plan.name.clone(),
        physical,
        stopped: if physical { stopped(plan) } else { vec![false; plan.nodes.len()] },
        alias: HashMap::new(),
        parents: parents(plan),
        memo: HashMap::new(),
        facts: vec![],
        read_values: read_values(plan),
        resolved_at: HashMap::new(),
        dropping: BTreeSet::new(),
    };
    if physical {
        for (i, n) in plan.nodes.iter().enumerate() {
            if let Op::Scan { runtime_filters, .. } = &n.op {
                for c in runtime_filters.iter().filter_map(|f| f.column.as_ref()).collect::<BTreeSet<_>>() {
                    if let Some(h) = t.resolver(i, c) {
                        t.resolved_at.entry(h).or_default().push((i, c.clone()));
                    }
                }
            }
        }
    }
    t.plan_aliases(plan.root, "");
    let root = t.node(b, plan.root, "").rel;
    // A scan read with and without its runtime filters states their
    // values once.
    let mut seen = BTreeSet::new();
    t.facts.retain(|(n, _)| seen.insert(n.clone()));
    (t.facts, root)
}

fn parents(plan: &ObservedPlan) -> Vec<Vec<usize>> {
    let mut out = vec![vec![]; plan.nodes.len()];
    for (i, n) in plan.nodes.iter().enumerate() {
        for &c in &n.children {
            out[c].push(i);
        }
    }
    out
}

/// The aggregate values something in the plan reads, as `@k.name`.
fn read_values(plan: &ObservedPlan) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut add = |e: &Expr| {
        for c in e.column_refs() {
            if let Some(r) = relation(c)
                && r.starts_with('@')
            {
                out.insert(format!("{}.{}", r.split('~').next().unwrap(), c.name));
            }
        }
    };
    for n in &plan.nodes {
        match &n.op {
            Op::Scan { filters, .. } => filters.iter().filter_map(|p| p.expr.as_ref()).for_each(&mut add),
            Op::Filter { predicate } => predicate.iter().filter_map(|p| p.expr.as_ref()).for_each(&mut add),
            Op::Join { on, .. } => on.iter().filter_map(|p| p.expr.as_ref()).for_each(&mut add),
            Op::Aggregate { keys, values } => keys.iter().chain(values).flatten().for_each(&mut add),
            _ => {}
        }
    }
    out
}

struct Executed<'p> {
    plan: &'p ObservedPlan,
    name: String,
    /// Whether what the run did is modelled: its counts are facts.
    physical: bool,
    stopped: Vec<bool>,
    /// Each scan instance's alias, if renamed.
    alias: HashMap<String, u32>,
    parents: Vec<Vec<usize>>,
    memo: HashMap<(usize, String), Out>,
    facts: Vec<(String, Fact)>,
    read_values: BTreeSet<String>,
    /// The scans' runtime filters on a column (by scan and `instance.col`)
    /// that each join's output does not depend on: the highest join on
    /// the column above the scan, by node.
    resolved_at: HashMap<usize, Vec<(usize, String)>>,
    /// The runtime filters the node being translated is read without: its
    /// rows are those of a join above that they cannot change.
    dropping: BTreeSet<(usize, String)>,
}

impl Executed<'_> {
    /// The join whose output scan `s`'s runtime filters on `column` cannot
    /// change: the highest join on the column above it, which drops rows
    /// without a partner on it, with only operators between that keep a
    /// row's rows above or drop them (filters, inner joins, the kept side
    /// of semi and left joins). Every join that can have built the filters
    /// is between, and drops the rows it pruned anyway.
    fn resolver(&self, s: usize, column: &str) -> Option<usize> {
        let mut path = vec![];
        let mut at = s;
        while let [p] = self.parents[at][..] {
            path.push((p, self.plan.nodes[p].children.first() == Some(&at)));
            at = p;
        }
        // A materialized result (a CTE) is computed whole before anything
        // reads it: its reads are as far as its filters reach.
        let reused = self.parents[at].iter().all(|p| matches!(self.plan.nodes[*p].op, Op::Reuse { .. }));
        if !reused {
            return None;
        }
        let h = path.iter().rposition(|(p, _)| matches!(&self.plan.nodes[*p].op, Op::Join { on, .. } if keys(on).contains(column)))?;
        for (k, (p, left)) in path[..=h].iter().enumerate() {
            let ok = match &self.plan.nodes[*p].op {
                Op::Filter { .. } | Op::Project | Op::Sort | Op::Window => true,
                Op::Join { kind, on } => {
                    if on.iter().any(|q| q.expr.is_none()) {
                        return None;
                    }
                    match kind {
                        JoinType::Inner => true,
                        JoinType::LeftSemi | JoinType::Right | JoinType::RightSemi | JoinType::RightAnti => *left,
                        JoinType::Left | JoinType::LeftAnti => *left && k < h,
                        _ => false,
                    }
                }
                _ => false,
            };
            if !ok {
                return None;
            }
        }
        Some(path[h].0)
    }

    /// The instances (suffixed) node `i` outputs columns of.
    fn instances(&self, i: usize, suffix: &str) -> BTreeSet<String> {
        let node = &self.plan.nodes[i];
        match &node.op {
            Op::Scan { instance, .. } => [format!("{instance}{suffix}")].into(),
            Op::Reuse { suffix: s, .. } => self.instances(node.children[0], &format!("{s}{suffix}")),
            Op::Join { kind: JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark, .. } => {
                self.instances(node.children[0], suffix)
            }
            Op::Join { kind: JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark, .. } => {
                self.instances(node.children[1], suffix)
            }
            _ => node.children.iter().flat_map(|&c| self.instances(c, suffix)).collect(),
        }
    }

    /// Every instance under node `i`, the other sides of semi joins too.
    fn all_instances(&self, i: usize, suffix: &str) -> BTreeSet<String> {
        let node = &self.plan.nodes[i];
        match &node.op {
            Op::Scan { instance, .. } => [format!("{instance}{suffix}")].into(),
            Op::Reuse { suffix: s, .. } => self.all_instances(node.children[0], &format!("{s}{suffix}")),
            _ => node.children.iter().flat_map(|&c| self.all_instances(c, suffix)).collect(),
        }
    }

    fn table_alias(&self, instance: &str) -> (String, u32) {
        (base_table(instance).unwrap_or(instance).to_string(), self.alias.get(instance).copied().unwrap_or(0))
    }

    /// Renames the instances of a join's right side that share a table
    /// (and alias) with its left side's, bottom-up.
    fn plan_aliases(&mut self, i: usize, suffix: &str) {
        let node = &self.plan.nodes[i];
        let child_suffix = match &node.op {
            Op::Reuse { suffix: s, .. } => format!("{s}{suffix}"),
            _ => suffix.to_string(),
        };
        for &c in &node.children {
            self.plan_aliases(c, &child_suffix);
        }
        let (l, r) = match (&node.op, node.children.as_slice()) {
            (Op::Join { .. }, [l, r]) => (*l, *r),
            _ => return,
        };
        let (li, ra, la) = (self.instances(l, suffix), self.all_instances(r, suffix), self.all_instances(l, suffix));
        resolve_conflicts(&mut self.alias, &li, &ra, &la);
    }

    /// The column `c` of an expression of the plan, read in the copy
    /// `suffix`.
    fn col(&self, b: &Builder, c: &Column, suffix: &str) -> Option<(Col, Ty)> {
        let rel = relation(c)?;
        if let Some(table) = base_table(rel) {
            let instance = format!("{rel}{suffix}");
            let (_, alias) = self.table_alias(&instance);
            return Some(b.column(table, &c.name, alias));
        }
        // An aggregate's value: `@k`.
        let k: usize = rel.strip_prefix('@')?.split('~').next()?.parse().ok()?;
        let node = self.plan.nodes.get(k)?;
        let Op::Aggregate { keys, values } = &node.op else { return None };
        let j = node.columns[keys.len()..].iter().position(|col| col.name == c.name)?;
        let read = |e: &Expr| Reader { col: &|c| self.col(b, c, suffix) }.read(e);
        match values.get(j)?.as_ref().and_then(|v| aggregate(v, &read)) {
            Some((name, agg)) => Some((name, agg.ty)),
            // A value that did not read is still a column of its own.
            None => Some((self.opaque_value(k, suffix, &c.name), Ty::Other)),
        }
    }

    fn read(&self, b: &Builder, e: &Expr, suffix: &str) -> Option<E> {
        Reader { col: &|c| self.col(b, c, suffix) }.read(e)
    }

    /// A predicate that did not resolve: opaque, with the columns it reads
    /// if they do.
    fn opaque_pred(&self, b: &mut Builder, i: usize, k: usize, e: Option<&Expr>, suffix: &str) -> PredId {
        let reads = e.and_then(|e| e.column_refs().into_iter().map(|c| self.col(b, c, suffix).map(|(c, _)| c)).collect());
        b.terms.pred(Pred::Opaque(format!("{}#{i}{suffix}:{k}", self.name), reads))
    }

    /// The column of aggregate `k`'s value `name` that did not read: a
    /// value of that operator alone.
    fn opaque_value(&self, k: usize, suffix: &str, name: &str) -> Col {
        format!("a:{}#{k}{suffix}.{name}", self.name)
    }

    fn occ(&self, i: usize, suffix: &str, what: &str) -> String {
        format!("{}#{i}{suffix}{what}", self.name)
    }

    fn node(&mut self, b: &mut Builder, i: usize, suffix: &str) -> Out {
        let key = (i, format!("{suffix}{:?}", self.dropping));
        if let Some(o) = self.memo.get(&key) {
            return o.clone();
        }
        // A join whose output the runtime filters below it cannot change:
        // its inputs read without them.
        let resolved = self.resolved_at.get(&i).cloned().unwrap_or_default();
        // Its inputs as they ran, for their counts.
        if !resolved.is_empty() {
            let inner = match &self.plan.nodes[i].op {
                Op::Reuse { suffix: s, .. } => format!("{s}{suffix}"),
                _ => suffix.to_string(),
            };
            for c in self.plan.nodes[i].children.clone() {
                self.node(b, c, &inner);
            }
        }
        let saved = self.dropping.clone();
        self.dropping.extend(resolved);
        let mut out = self.build(b, i, suffix);
        self.dropping = saved;
        if self.stopped[i] && !matches!(self.plan.nodes[i].op, Op::Reuse { .. }) {
            out.rel = b.terms.rel(Rel::Part(self.occ(i, suffix, ""), out.rel));
        }
        let node = &self.plan.nodes[i];
        // Counts are of what the run computed, not of what is read below
        // a join without its runtime filters.
        if self.physical && self.plan.counted && node.counted && self.dropping.is_empty() {
            self.facts.push((format!("obs:{}#{i}{suffix}", self.name), Fact::Card(out.rel, node.rows)));
        }
        self.memo.insert(key, out.clone());
        out
    }

    fn build(&mut self, b: &mut Builder, i: usize, suffix: &str) -> Out {
        let node = &self.plan.nodes[i];
        let width = node.columns.len();
        let lineage = |me: &Self, b: &Builder| -> Vec<Option<E>> {
            node.columns
                .iter()
                .map(|c| match &c.lineage {
                    crate::observed::Lineage::Exact(e) => me.read(b, e, suffix),
                    _ => None,
                })
                .collect()
        };
        match &node.op {
            Op::Scan { table, instance, filters, runtime_filters } => {
                let inst = format!("{instance}{suffix}");
                let (_, alias) = self.table_alias(&inst);
                let mut x = b.scan(table, alias);
                let (optional, required): (Vec<_>, Vec<_>) = filters.iter().partition(|p| p.optional);
                // One conjunction, in the canonical order (§5).
                let mut exprs = vec![];
                for (k, p) in required.iter().enumerate() {
                    match p.expr.as_ref().and_then(|e| self.read(b, e, suffix)) {
                        Some(e) => exprs.push(e),
                        None => {
                            let q = self.opaque_pred(b, i, k, p.expr.as_ref(), suffix);
                            x = b.filter_preds(x, &[q]);
                        }
                    }
                }
                x = b.filter(x, &flat_and(exprs));
                for (k, p) in optional.iter().enumerate().filter(|_| self.physical) {
                    let o = self.occ(i, suffix, &format!(":opt{k}"));
                    match p.expr.as_ref().and_then(|e| self.read(b, e, suffix)) {
                        Some(e) => {
                            for q in preds::conjuncts(b.terms, &e) {
                                x = b.terms.rel(Rel::Opt(o.clone(), q, x));
                            }
                        }
                        None => x = b.terms.rel(Rel::Part(o, x)),
                    }
                }
                if self.physical {
                    x = self.runtime(b, i, suffix, x, runtime_filters);
                }
                Out { rel: x, cols: lineage(self, b), scalars: BTreeMap::new() }
            }
            Op::Filter { predicate } => {
                let input = self.node(b, node.children[0], suffix);
                let mut x = input.rel;
                let mut exprs = vec![];
                for (k, p) in predicate.iter().enumerate() {
                    match p.expr.as_ref().and_then(|e| self.read(b, e, suffix)) {
                        Some(e) => exprs.push(e),
                        None => {
                            let q = self.opaque_pred(b, i, k, p.expr.as_ref(), suffix);
                            x = b.filter_preds(x, &[q]);
                        }
                    }
                }
                let all = flat_and(exprs);
                x = b.rechecked(x, &all);
                x = b.filter_with(x, &all, &input.scalars);
                Out { rel: x, cols: input.cols, scalars: input.scalars }
            }
            Op::Project | Op::Sort | Op::Window => {
                let input = self.node(b, node.children[0], suffix);
                let mut cols = lineage(self, b);
                if cols.len() != width {
                    cols.resize(width, None);
                }
                Out { rel: input.rel, cols, scalars: input.scalars }
            }
            Op::Reuse { suffix: s, .. } => {
                let inner = format!("{s}{suffix}");
                let input = self.node(b, node.children[0], &inner);
                Out { rel: input.rel, cols: input.cols, scalars: input.scalars }
            }
            Op::Aggregate { keys, values } => {
                let input = self.node(b, node.children[0], suffix);
                let ks: Option<Vec<E>> = keys.iter().map(|k| k.as_ref().and_then(|k| self.read(b, k, suffix))).collect();
                let Some(ks) = ks else { return self.opaque(b, i, suffix) };
                let mut vals = vec![];
                let mut cols: Vec<Option<E>> = ks.iter().cloned().map(Some).collect();
                for (j, v) in values.iter().enumerate() {
                    let col = &node.columns[keys.len() + j];
                    let read = format!("@{i}.{}", col.name);
                    let named = v.as_ref().and_then(|v| aggregate(v, &|e| self.read(b, e, suffix))).or_else(|| {
                        let name = self.opaque_value(i, suffix, &col.name);
                        Some((name, Agg { func: "opaque".into(), arg: None, distinct: false, ty: Ty::Other }))
                    });
                    match named {
                        Some((c, a)) => {
                            cols.push(Some(E::Col(c.clone(), a.ty)));
                            if self.read_values.contains(&read) {
                                vals.push((c, a));
                            }
                        }
                        None => cols.push(None),
                    }
                }
                vals.sort_by(|a, b| a.0.cmp(&b.0));
                vals.dedup_by(|a, b| a.0 == b.0);
                let (rel, _) = b.group(input.rel, &ks, &vals);
                let mut scalars = BTreeMap::new();
                if ks.is_empty() {
                    for (c, _) in &vals {
                        scalars.insert(c.clone(), rel);
                    }
                }
                Out { rel, cols, scalars }
            }
            Op::Join { kind, on } => self.join(b, i, *kind, on, suffix).unwrap_or_else(|| self.opaque(b, i, suffix)),
            Op::MarkFilter { negated } => {
                let mark = &self.plan.nodes[node.children[0]];
                if let Op::Join { kind: JoinType::LeftMark, on } = &mark.op {
                    let kind = if *negated { JoinType::LeftAnti } else { JoinType::LeftSemi };
                    let m = node.children[0];
                    if let Some(o) = self.join_as(b, m, kind, *negated, on, suffix) {
                        return o;
                    }
                }
                self.opaque(b, i, suffix)
            }
            Op::TopN { fetch, offset } => {
                let input = self.node(b, node.children[0], suffix);
                let mut x = b.terms.rel(Rel::Limit(fetch + offset, input.rel));
                if *offset > 0 {
                    x = b.terms.rel(Rel::Part(self.occ(i, suffix, ":offset"), x));
                }
                Out { rel: x, cols: input.cols, scalars: input.scalars }
            }
            Op::Limit { at_most } => {
                let input = self.node(b, node.children[0], suffix);
                let x = match at_most {
                    Some(n) => b.terms.rel(Rel::Limit(*n, input.rel)),
                    None => b.terms.rel(Rel::Part(self.occ(i, suffix, ":limit"), input.rel)),
                };
                Out { rel: x, cols: input.cols, scalars: input.scalars }
            }
            Op::Union => {
                let kids: Vec<Out> = node.children.clone().iter().map(|&c| self.node(b, c, suffix)).collect();
                let mut x = kids.last().unwrap().rel;
                for k in kids[..kids.len() - 1].iter().rev() {
                    x = b.terms.rel(Rel::Union(k.rel, x));
                }
                Out { rel: x, cols: kids[0].cols.clone(), scalars: BTreeMap::new() }
            }
            Op::Other => self.opaque(b, i, suffix),
        }
    }

    fn opaque(&mut self, b: &mut Builder, i: usize, suffix: &str) -> Out {
        if std::env::var("CARDINAL_UF_OPAQUE").is_ok() {
            let n = &self.plan.nodes[i];
            let detail = match &n.op {
                Op::Join { on, .. } => on.iter().map(|p| format!("{} => {:?}", p.text, p.expr.as_ref().map(|e| e.to_string()))).collect::<Vec<_>>().join("; "),
                Op::Aggregate { keys, values } => format!("keys {keys:?} values {values:?}"),
                _ => String::new(),
            };
            eprintln!("uf: opaque {}#{i} {}: {detail}", self.name, n.op);
        }
        // Its inputs are still terms with counts.
        for &c in &self.plan.nodes[i].children.clone() {
            self.node(b, c, suffix);
        }
        let rel = b.opaque(&format!("{}#{i}{suffix}", self.name), None);
        Out { rel, cols: vec![None; self.plan.nodes[i].columns.len()], scalars: BTreeMap::new() }
    }

    /// A join's condition: equal pairs of each side's expressions (whether
    /// all `IS NOT DISTINCT FROM`), and the rest.
    #[allow(clippy::type_complexity)]
    fn condition(
        &self,
        b: &Builder,
        on: &[crate::observed::Pred],
        l: &Out,
        r: &Out,
        suffix: &str,
    ) -> Option<(Vec<(E, E)>, Option<E>, bool)> {
        let exprs: Option<Vec<E>> = on.iter().map(|p| self.read(b, p.expr.as_ref()?, suffix)).collect();
        if exprs.is_none() && std::env::var("CARDINAL_UF_OPAQUE").is_ok() {
            for p in on {
                let refs: Vec<String> = p.expr.iter().flat_map(|e| e.column_refs()).map(|c| format!("{c} -> {:?}", self.col(b, c, suffix))).collect();
                eprintln!("uf: condition {} reads {refs:?}: {:?}", p.text, p.expr.as_ref().map(|e| self.read(b, e, suffix)));
            }
        }
        let exprs = exprs?;
        let side = |e: &E, o: &Out| e.reads().iter().all(|c| o.cols.iter().flatten().any(|x| x.reads().contains(c)));
        let null_eq = !on.is_empty()
            && on.iter().all(|p| {
                matches!(&p.expr, Some(Expr::BinaryExpr(BinaryExpr { op: Operator::IsNotDistinctFrom, .. })))
            });
        let mut pairs = vec![];
        let mut rest = vec![];
        for (p, e) in on.iter().zip(exprs) {
            if let Some(Expr::BinaryExpr(BinaryExpr { left, op, right })) = &p.expr
                && (*op == Operator::Eq || (null_eq && *op == Operator::IsNotDistinctFrom))
                && let (Some(a), Some(c)) = (self.read(b, left, suffix), self.read(b, right, suffix))
                && !a.reads().is_empty()
                && !c.reads().is_empty()
            {
                if side(&a, l) && side(&c, r) {
                    pairs.push((a, c));
                    continue;
                }
                if side(&c, l) && side(&a, r) {
                    pairs.push((c, a));
                    continue;
                }
            }
            rest.push(e);
        }
        let residual = if rest.is_empty() { None } else { Some(flat_and(rest)) };
        Some((pairs, residual, null_eq))
    }

    fn join(&mut self, b: &mut Builder, i: usize, kind: JoinType, on: &[crate::observed::Pred], suffix: &str) -> Option<Out> {
        match kind {
            // A mark join's rows are its left side's.
            JoinType::LeftMark => {
                let r = self.plan.nodes[i].children[1];
                self.node(b, r, suffix);
                let l = self.node(b, self.plan.nodes[i].children[0], suffix);
                Some(l)
            }
            _ => self.join_as(b, i, kind, false, on, suffix),
        }
    }

    fn join_as(&mut self, b: &mut Builder, i: usize, kind: JoinType, null_aware: bool, on: &[crate::observed::Pred], suffix: &str) -> Option<Out> {
        let node = &self.plan.nodes[i];
        let (lc, rc) = (node.children[0], node.children[1]);
        let r = self.node(b, rc, suffix);
        let l = self.node(b, lc, suffix);
        let rel = match self.condition(b, on, &l, &r, suffix) {
            Some((pairs, residual, null_eq)) => b.join(kind, null_aware, &pairs, residual, null_eq, l.rel, r.rel)?,
            // A condition that did not read is a predicate of its own.
            None => {
                let reads = None;
                let q = b.terms.pred(Pred::Opaque(format!("{}#{i}{suffix}:on", self.name), reads));
                b.join_on(kind, null_aware, q, l.rel, r.rel)?
            }
        };
        let cols = match kind {
            JoinType::LeftSemi | JoinType::LeftAnti => l.cols.clone(),
            JoinType::RightSemi | JoinType::RightAnti => r.cols.clone(),
            _ => l.cols.iter().chain(&r.cols).cloned().collect(),
        };
        let mut scalars = l.scalars.clone();
        if matches!(kind, JoinType::Inner) {
            scalars.extend(r.scalars.clone());
        }
        Some(Out { rel, cols, scalars })
    }

    /// Scan `i`'s term `x` after its runtime filters: lossless ones from
    /// the one join that can have built them as `rt`, others as `part`.
    fn runtime(&mut self, b: &mut Builder, i: usize, suffix: &str, mut x: RelId, filters: &[crate::observed::RuntimeFilter]) -> RelId {
        let mut columns: BTreeMap<String, Vec<&crate::observed::RuntimeFilter>> = BTreeMap::new();
        let mut unknown = false;
        for f in filters {
            match &f.column {
                Some(c) => columns.entry(c.clone()).or_default().push(f),
                None => unknown = true,
            }
        }
        // Joins already applied, by node, to apply each once.
        let mut applied: BTreeSet<usize> = BTreeSet::new();
        for (column, fs) in &columns {
            if self.dropping.contains(&(i, column.clone())) {
                continue;
            }
            let lossless = fs.iter().all(|f| f.expr.is_some());
            let built = self.builder(i, column);
            match (built, lossless) {
                (Some((j, build_col)), true) => {
                    if !applied.insert(j) {
                        continue;
                    }
                    let Some(rt) = self.rt(b, i, j, suffix, x) else {
                        x = b.terms.rel(Rel::Part(self.occ(i, suffix, &format!(":rt{j}")), x));
                        continue;
                    };
                    x = rt;
                    // The values the filters printed bound the build
                    // side's keys.
                    let build = self.node(b, self.plan.nodes[j].children[1], suffix);
                    let Some((col, _)) = self.col(b, &build_col, suffix) else { continue };
                    let (mut lo, mut hi, mut listed) = (None, None, None);
                    for f in fs {
                        let (a, z, n) = admits(f.expr.as_ref().unwrap());
                        lo = lo.max(a);
                        hi = match (hi, z) {
                            (Some(h), Some(z)) => Some(std::cmp::min(h, z)),
                            (h, z) => h.or(z),
                        };
                        if let Some(n) = n {
                            listed = Some(listed.map_or(n, |l: u64| l.min(n)));
                        }
                    }
                    let name = format!("rtv:{}#{i}{suffix}:{column}", self.name);
                    if lo.is_some() || hi.is_some() {
                        self.facts.push((name.clone(), Fact::KeyRange(build.rel, col.clone(), lo, hi)));
                    }
                    if let Some(n) = listed {
                        self.facts.push((format!("{name}:n"), Fact::KeyCount(build.rel, col, n)));
                    }
                }
                _ => unknown = true,
            }
        }
        if unknown {
            x = b.terms.rel(Rel::Part(self.occ(i, suffix, ":rt"), x));
        }
        x
    }

    /// The join that built the runtime filters on scan `i`'s `column`, and
    /// the build side's column equal to it: the only join on the column
    /// above the scan, with the scan on its probe side, and nothing in
    /// between that another join could have pushed through.
    fn builder(&self, i: usize, column: &str) -> Option<(usize, Column)> {
        let mut at = i;
        let mut joins = vec![];
        loop {
            match &self.parents[at][..] {
                [] => break,
                [p] => {
                    match &self.plan.nodes[*p].op {
                        Op::Union => return None,
                        Op::Join { on, .. } if on.iter().any(|p| p.expr.is_none()) => return None,
                        Op::Join { on, .. } if keys(on).contains(column) => {
                            joins.push((*p, self.plan.nodes[*p].children[0] == at));
                        }
                        _ => {}
                    }
                    at = *p;
                }
                _ => return None,
            }
        }
        let [(j, true)] = joins[..] else { return None };
        let Op::Join { kind: JoinType::Inner | JoinType::LeftSemi | JoinType::Right | JoinType::RightSemi, on } =
            &self.plan.nodes[j].op
        else {
            return None;
        };
        let reads = |p: &crate::observed::Pred| p.expr.as_ref().is_some_and(|e| e.column_refs().iter().any(|c| key(c) == column));
        if on.iter().filter(|p| reads(p)).count() != 1 {
            return None;
        }
        on.iter().find_map(|p| match &p.expr {
            Some(Expr::BinaryExpr(BinaryExpr { left, op: Operator::Eq, right })) => match (left.as_ref(), right.as_ref()) {
                (Expr::Column(a), Expr::Column(c)) if key(a) == column => Some((j, c.clone())),
                (Expr::Column(a), Expr::Column(c)) if key(c) == column => Some((j, a.clone())),
                _ => None,
            },
            _ => None,
        })
    }

    /// `rt` of join `j`'s family over `x`, the scan `i` on its probe side.
    fn rt(&mut self, b: &mut Builder, i: usize, j: usize, suffix: &str, x: RelId) -> Option<RelId> {
        let node = &self.plan.nodes[j];
        let Op::Join { kind, on } = &node.op else { return None };
        let (lc, rc) = (node.children[0], node.children[1]);
        let build = self.node(b, rc, suffix);
        // The probe side's columns, without translating it (the scan is
        // in it): its output instances.
        let probe = Out { rel: x, cols: self.instance_cols(b, lc, suffix), scalars: BTreeMap::new() };
        let (pairs, residual, null_eq) = self.condition(b, on, &probe, &build, suffix)?;
        if residual.is_some() || null_eq || pairs.is_empty() || !matches!(kind, JoinType::Inner | JoinType::LeftSemi) {
            return None;
        }
        let mut cols = vec![];
        for (a, c) in &pairs {
            let (E::Col(a, _), E::Col(c, _)) = (a, c) else { return None };
            cols.push((a.clone(), c.clone()));
        }
        cols.sort();
        let fam = b.terms.family(Family { pairs: cols, null_eq: false, residual: None });
        Some(b.terms.rel(Rel::Rt(fam, self.occ(i, suffix, &format!(":rt{j}")), x, build.rel)))
    }

    /// Every column of the instances node `i` outputs, as expressions.
    fn instance_cols(&self, b: &Builder, i: usize, suffix: &str) -> Vec<Option<E>> {
        let mut out = vec![];
        for inst in self.instances(i, suffix) {
            let (table, alias) = self.table_alias(&inst);
            for c in b.tables.columns(&table) {
                let (name, ty) = b.column(&table, &c, alias);
                out.push(Some(E::Col(name, ty)));
            }
        }
        out
    }
}

/// Renames instances of `right` that share a name with `left`'s, to the
/// next free alias of their table.
fn resolve_conflicts(alias: &mut HashMap<String, u32>, left: &BTreeSet<String>, right: &BTreeSet<String>, left_all: &BTreeSet<String>) {
    let name = |alias: &HashMap<String, u32>, i: &str| (base_table(i).unwrap_or(i).to_string(), alias.get(i).copied().unwrap_or(0));
    let left_names: BTreeSet<(String, u32)> = left.iter().map(|i| name(alias, i)).collect();
    let mut used: BTreeSet<(String, u32)> = left_all.iter().chain(right).map(|i| name(alias, i)).collect();
    for inst in right {
        let n = name(alias, inst);
        if !left_names.contains(&n) || left.contains(inst) {
            continue;
        }
        let mut k = 2;
        while used.contains(&(n.0.clone(), k)) {
            k += 1;
        }
        used.insert((n.0.clone(), k));
        alias.insert(inst.clone(), k);
    }
}

fn key(c: &Column) -> String {
    format!("{}.{}", relation(c).unwrap_or(""), c.name)
}

fn keys(on: &[crate::observed::Pred]) -> BTreeSet<String> {
    on.iter().filter_map(|p| p.expr.as_ref()).flat_map(|e| e.column_refs().into_iter().map(key).collect::<Vec<_>>()).collect()
}

/// The values runtime filter `e` admits: the least and greatest, if they
/// are integers, and how many, if it lists them.
fn admits(e: &Expr) -> (Option<i128>, Option<i128>, Option<u64>) {
    let int = |e: &Expr| match e {
        Expr::Literal(v, _) => match Lit::from_scalar(v) {
            Some(Lit::Int(n)) => Some(n),
            _ => None,
        },
        _ => None,
    };
    let mut listed = vec![];
    let mut todo = vec![e];
    let mut list = true;
    while let Some(e) = todo.pop() {
        match e {
            Expr::BinaryExpr(BinaryExpr { left, op: Operator::Or, right }) => todo.extend([left.as_ref(), right.as_ref()]),
            Expr::BinaryExpr(BinaryExpr { op: Operator::Eq, right, .. }) if matches!(right.as_ref(), Expr::Literal(..)) => {
                listed.push(right.as_ref())
            }
            Expr::InList(l) if !l.negated && l.list.iter().all(|v| matches!(v, Expr::Literal(..))) => listed.extend(l.list.iter()),
            _ => {
                list = false;
                break;
            }
        }
    }
    if list && !listed.is_empty() {
        let ints: Option<Vec<i128>> = listed.iter().map(|v| int(v)).collect();
        let (lo, hi) = ints.map_or((None, None), |v| (v.iter().min().copied(), v.iter().max().copied()));
        return (lo, hi, Some(listed.len() as u64));
    }
    match e {
        Expr::BinaryExpr(BinaryExpr { op, right, .. }) => {
            let k = int(right);
            match op {
                Operator::GtEq => (k, None, None),
                Operator::Gt => (k.map(|k| k + 1), None, None),
                Operator::LtEq => (None, k, None),
                Operator::Lt => (None, k.map(|k| k - 1), None),
                _ => (None, None, None),
            }
        }
        _ => (None, None, None),
    }
}

// ---------------------------------------------------------------------
// DataFusion's plans.
// ---------------------------------------------------------------------

/// A DataFusion plan of the query to bound, as a term; facts its own
/// shape gives (an empty relation's or a VALUES list's rows) in `facts`.
pub(crate) fn logical(b: &mut Builder, plan: &LogicalPlan, name: &str, facts: &mut Vec<(String, Fact)>) -> RelId {
    let mut t = Logical { name: name.to_string(), next: 0, alias: HashMap::new(), facts: vec![] };
    // Instances first, to rename a join's right side.
    let mut probe = Logical { name: name.to_string(), next: 0, alias: HashMap::new(), facts: vec![] };
    probe.plan_aliases(plan);
    t.alias = probe.alias;
    let out = t.node(b, plan);
    facts.extend(t.facts);
    out.rel
}

struct Logical {
    name: String,
    /// The next node's number, in visit order.
    next: usize,
    alias: HashMap<String, u32>,
    facts: Vec<(String, Fact)>,
}

impl Logical {
    fn id(&mut self) -> usize {
        self.next += 1;
        self.next - 1
    }

    /// Numbers the scans (`table#n`), in the order [`Logical::node`]
    /// visits them, and renames the right side's on conflicts. Returns the
    /// instances `plan` outputs, and every instance under it.
    fn plan_aliases(&mut self, plan: &LogicalPlan) -> (BTreeSet<String>, BTreeSet<String>) {
        let id = self.id();
        match plan {
            LogicalPlan::TableScan(scan) => {
                let inst = format!("{}#{id}", scan.table_name.table());
                ([inst.clone()].into(), [inst].into())
            }
            LogicalPlan::Join(j) => {
                let (l, la) = self.plan_aliases(&j.left);
                let (r, ra) = self.plan_aliases(&j.right);
                resolve_conflicts(&mut self.alias, &l, &ra, &la);
                let out = match j.join_type {
                    JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => l,
                    JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => r,
                    _ => l.union(&r).cloned().collect(),
                };
                (out, la.union(&ra).cloned().collect())
            }
            p => {
                let mut out = BTreeSet::new();
                let mut all = BTreeSet::new();
                for i in p.inputs() {
                    let (o, a) = self.plan_aliases(i);
                    out.extend(o);
                    all.extend(a);
                }
                // Scalar subqueries in expressions, in the order `node`
                // reads them.
                for s in subqueries(p) {
                    let (_, a) = self.plan_aliases(&s);
                    all.extend(a);
                }
                (out, all)
            }
        }
    }

    fn node(&mut self, b: &mut Builder, plan: &LogicalPlan) -> Out {
        let id = self.id();
        match self.build(b, plan, id) {
            Some(o) => o,
            None => {
                let rel = b.opaque(&format!("{}#{id}", self.name), None);
                Out { rel, cols: vec![None; plan.schema().fields().len()], scalars: BTreeMap::new() }
            }
        }
    }

    fn build(&mut self, b: &mut Builder, plan: &LogicalPlan, id: usize) -> Option<Out> {
        Some(match plan {
            LogicalPlan::TableScan(scan) => {
                let table = scan.table_name.table().to_string();
                if b.tables.catalog.columns(&table).is_none() {
                    return None;
                }
                let inst = format!("{table}#{id}");
                let alias = self.alias.get(&inst).copied().unwrap_or(0);
                let mut x = b.scan(&table, alias);
                let col = |c: &Column| Some(b.column(&table, &c.name, alias));
                let filters: Option<Vec<E>> = scan.filters.iter().map(|f| Reader { col: &col }.read(f)).collect();
                let inexact = crate::analyzer::inexact_filters(scan);
                match filters {
                    Some(fs) => {
                        let e = flat_and(fs);
                        if inexact {
                            for q in preds::conjuncts(b.terms, &e) {
                                x = b.terms.rel(Rel::Opt(format!("{}#{id}", self.name), q, x));
                            }
                        } else {
                            x = b.filter(x, &e);
                        }
                    }
                    None if scan.filters.is_empty() => {}
                    None => x = b.terms.rel(Rel::Part(format!("{}#{id}", self.name), x)),
                }
                if let Some(n) = scan.fetch {
                    x = b.terms.rel(Rel::Limit(n as u64, x));
                }
                let cols = scan.projected_schema.fields().iter().map(|f| {
                    let (c, t) = b.column(&table, f.name(), alias);
                    Some(E::Col(c, t))
                });
                Out { rel: x, cols: cols.collect(), scalars: BTreeMap::new() }
            }
            LogicalPlan::Projection(p) => {
                let input = self.node(b, &p.input);
                let cols = p.expr.iter().map(|e| read_in(b, &p.input, &input, e)).collect();
                Out { rel: input.rel, cols, scalars: input.scalars }
            }
            LogicalPlan::Filter(f) => {
                let input = self.node(b, &f.input);
                let mut x = input.rel;
                let mut exprs = vec![];
                for (k, c) in split_conjunction(&f.predicate).into_iter().enumerate() {
                    // A comparison with a scalar subquery.
                    if let Some(p) = self.subquery_cmp(b, &f.input, &input, c) {
                        x = b.filter_preds(x, &[p]);
                        continue;
                    }
                    match read_in(b, &f.input, &input, c) {
                        Some(e) => exprs.push(e),
                        None => {
                            let reads = c
                                .column_refs()
                                .into_iter()
                                .map(|col| match lookup(&f.input, &input, col) {
                                    Some(E::Col(n, _)) => Some(n),
                                    _ => None,
                                })
                                .collect();
                            let q = b.terms.pred(Pred::Opaque(format!("{}#{id}:{k}", self.name), reads));
                            x = b.filter_preds(x, &[q]);
                        }
                    }
                }
                let all = flat_and(exprs);
                x = b.rechecked(x, &all);
                x = b.filter_with(x, &all, &input.scalars);
                Out { rel: x, cols: input.cols, scalars: input.scalars }
            }
            LogicalPlan::SubqueryAlias(a) => {
                let input = self.node(b, &a.input);
                input
            }
            LogicalPlan::Repartition(r) => self.node(b, &r.input),
            LogicalPlan::Subquery(s) => self.node(b, &s.subquery),
            LogicalPlan::Window(w) => {
                let mut input = self.node(b, &w.input);
                input.cols.resize(plan.schema().fields().len(), None);
                input
            }
            LogicalPlan::Sort(s) => {
                let mut input = self.node(b, &s.input);
                if let Some(n) = s.fetch {
                    input.rel = b.terms.rel(Rel::Limit(n as u64, input.rel));
                }
                input
            }
            LogicalPlan::Limit(l) => {
                let mut input = self.node(b, &l.input);
                let skip = match l.get_skip_type().ok()? {
                    datafusion::logical_expr::SkipType::Literal(n) => n,
                    _ => return None,
                };
                let fetch = match l.get_fetch_type().ok()? {
                    datafusion::logical_expr::FetchType::Literal(n) => n,
                    _ => return None,
                };
                match (skip, fetch) {
                    (0, Some(n)) => input.rel = b.terms.rel(Rel::Limit(n as u64, input.rel)),
                    (0, None) => {}
                    (s, f) => {
                        if let Some(f) = f {
                            input.rel = b.terms.rel(Rel::Limit((f + s) as u64, input.rel));
                        }
                        input.rel = b.terms.rel(Rel::Part(format!("{}#{id}", self.name), input.rel));
                    }
                }
                input
            }
            LogicalPlan::Distinct(Distinct::All(input)) => {
                let o = self.node(b, input);
                let keys: Option<Vec<E>> = o.cols.iter().cloned().collect();
                let keys = keys?;
                let (rel, _) = b.group(o.rel, &keys, &[]);
                Out { rel, cols: o.cols, scalars: BTreeMap::new() }
            }
            LogicalPlan::Distinct(Distinct::On(d)) => {
                let o = self.node(b, &d.input);
                let keys: Option<Vec<E>> = d.on_expr.iter().map(|e| read_in(b, &d.input, &o, e)).collect();
                let (rel, _) = b.group(o.rel, &keys?, &[]);
                let cols = vec![None; plan.schema().fields().len()];
                Out { rel, cols, scalars: BTreeMap::new() }
            }
            LogicalPlan::Aggregate(agg) => {
                if agg.group_expr.iter().any(|e| matches!(e, Expr::GroupingSet(_))) {
                    self.node(b, &agg.input);
                    return None;
                }
                let input = self.node(b, &agg.input);
                let keys: Option<Vec<E>> = agg.group_expr.iter().map(|e| read_in(b, &agg.input, &input, e)).collect();
                let keys = keys?;
                let mut cols: Vec<Option<E>> = keys.iter().cloned().map(Some).collect();
                let mut vals = vec![];
                for e in &agg.aggr_expr {
                    match aggregate(e, &|x| read_in(b, &agg.input, &input, x)) {
                        Some((c, a)) => {
                            cols.push(Some(E::Col(c.clone(), a.ty)));
                            vals.push((c, a));
                        }
                        None => cols.push(None),
                    }
                }
                vals.sort_by(|a, b| a.0.cmp(&b.0));
                vals.dedup_by(|a, b| a.0 == b.0);
                // Only what something above reads is modelled; a later pass
                // cannot see that, so values are kept when few.
                let (rel, _) = b.group(input.rel, &keys, &vals);
                let mut scalars = BTreeMap::new();
                if keys.is_empty() {
                    for (c, _) in &vals {
                        scalars.insert(c.clone(), rel);
                    }
                }
                Out { rel, cols, scalars }
            }
            LogicalPlan::Join(j) => {
                let l = self.node(b, &j.left);
                let r = self.node(b, &j.right);
                let mut pairs = vec![];
                let mut rest = vec![];
                let null_eq = j.null_equality == NullEquality::NullEqualsNull;
                for (a, c) in &j.on {
                    let (x, y) = (read_in(b, &j.left, &l, a), read_in(b, &j.right, &r, c));
                    match (x, y) {
                        (Some(x), Some(y)) => pairs.push((x, y)),
                        _ => return None,
                    }
                }
                if let Some(f) = &j.filter {
                    for c in split_conjunction(f) {
                        // An equality of the two sides in the condition is a
                        // key pair as well (as an unoptimized plan has it).
                        if let Expr::BinaryExpr(BinaryExpr { left: x, op: Operator::Eq, right: y }) = c
                            && !null_eq
                        {
                            let side = |e: &Expr, input: &LogicalPlan, o: &Out| {
                                let refs = e.column_refs();
                                let mine = !refs.is_empty() && refs.iter().all(|c| lookup(input, o, c).is_some());
                                mine.then(|| read_in(b, input, o, e)).flatten()
                            };
                            let pair = match (side(x, &j.left, &l), side(y, &j.right, &r)) {
                                (Some(a), Some(c)) => Some((a, c)),
                                _ => match (side(y, &j.left, &l), side(x, &j.right, &r)) {
                                    (Some(a), Some(c)) => Some((a, c)),
                                    _ => None,
                                },
                            };
                            if let Some(p) = pair {
                                pairs.push(p);
                                continue;
                            }
                        }
                        // Expressions of the inputs' computed columns too.
                        let e = read_with(b, c, &|c| lookup(&j.left, &l, c).or_else(|| lookup(&j.right, &r, c)));
                        rest.push(e?);
                    }
                }
                let residual = if rest.is_empty() { None } else { Some(flat_and(rest)) };
                if null_eq && !pairs.is_empty() && residual.is_none() {
                    // NULL keys match each other.
                }
                let rel = b.join(j.join_type, j.null_aware, &pairs, residual, null_eq, l.rel, r.rel)?;
                let cols = match j.join_type {
                    JoinType::LeftSemi | JoinType::LeftAnti => l.cols.clone(),
                    JoinType::RightSemi | JoinType::RightAnti => r.cols.clone(),
                    JoinType::LeftMark => {
                        let mut c = l.cols.clone();
                        c.push(None);
                        c
                    }
                    _ => l.cols.iter().chain(&r.cols).cloned().collect(),
                };
                let mut scalars = l.scalars.clone();
                if j.join_type == JoinType::Inner {
                    scalars.extend(r.scalars.clone());
                }
                Out { rel, cols, scalars }
            }
            LogicalPlan::Union(u) => {
                let kids: Vec<Out> = u.inputs.iter().map(|i| self.node(b, i)).collect();
                let mut x = kids.last()?.rel;
                for k in kids[..kids.len() - 1].iter().rev() {
                    x = b.terms.rel(Rel::Union(k.rel, x));
                }
                Out { rel: x, cols: kids[0].cols.clone(), scalars: BTreeMap::new() }
            }
            LogicalPlan::EmptyRelation(e) => {
                let rel = b.opaque(&format!("{}#{id}", self.name), None);
                self.facts.push((format!("shape:{}#{id}", self.name), Fact::Card(rel, u64::from(e.produce_one_row))));
                Out { rel, cols: vec![None; plan.schema().fields().len()], scalars: BTreeMap::new() }
            }
            LogicalPlan::Values(v) => {
                let rel = b.opaque(&format!("{}#{id}", self.name), None);
                self.facts.push((format!("shape:{}#{id}", self.name), Fact::Card(rel, v.values.len() as u64)));
                Out { rel, cols: vec![None; plan.schema().fields().len()], scalars: BTreeMap::new() }
            }
            p => {
                for i in p.inputs() {
                    self.node(b, i);
                }
                return None;
            }
        })
    }

    /// `c` as `a op (y)`, a column compared with an uncorrelated scalar
    /// subquery.
    fn subquery_cmp(&mut self, b: &mut Builder, input: &LogicalPlan, o: &Out, c: &Expr) -> Option<PredId> {
        let (op, a, s, negated) = match c {
            Expr::BinaryExpr(BinaryExpr { left, op, right }) => match (left.as_ref(), right.as_ref()) {
                (a, Expr::ScalarSubquery(s)) => (*op, a, s, false),
                (Expr::ScalarSubquery(s), a) => (*op, a, s, true),
                _ => return None,
            },
            _ => return None,
        };
        if !s.outer_ref_columns.is_empty() {
            return None;
        }
        let mut op = super::expr::Cmp::of_op(op)?;
        if negated {
            op = op.flip();
        }
        let a = match read_in(b, input, o, a)? {
            E::Col(c, _) => c,
            _ => return None,
        };
        let y = self.node(b, &s.subquery);
        let g = match y.cols.first()?.as_ref()? {
            E::Col(c, _) => c.clone(),
            _ => return None,
        };
        b.cmp(op, &a, y.rel, &g)
    }
}

/// The scalar subqueries `plan`'s own expressions read.
fn subqueries(plan: &LogicalPlan) -> Vec<LogicalPlan> {
    let mut out = vec![];
    for e in plan.expressions() {
        let _ = e.apply(|x| {
            if let Expr::ScalarSubquery(s) = x {
                out.push(s.subquery.as_ref().clone());
            }
            Ok(datafusion::common::tree_node::TreeNodeRecursion::Continue)
        });
    }
    out
}

/// Column `c` of `input`'s output, as an expression over term columns.
fn lookup(input: &LogicalPlan, o: &Out, c: &Column) -> Option<E> {
    let j = input.schema().maybe_index_of_column(c)?;
    o.cols.get(j).cloned().flatten()
}

/// `e`, over `input`'s output.
fn read_in(b: &Builder, input: &LogicalPlan, o: &Out, e: &Expr) -> Option<E> {
    read_with(b, e, &|c| lookup(input, o, c))
}

/// `e` with each column given by `col`, an expression over term columns.
fn read_with(_b: &Builder, e: &Expr, col: &dyn Fn(&Column) -> Option<E>) -> Option<E> {
    // Columns stand for expressions: read with placeholders, then
    // substitute.
    let names: std::cell::RefCell<HashMap<String, E>> = Default::default();
    let reader = Reader {
        col: &|c| {
            let x = col(c)?;
            let key = format!("@@{}", names.borrow().len());
            let t = x.ty();
            names.borrow_mut().insert(key.clone(), x);
            Some((key, t))
        },
    };
    let e = reader.read(e)?;
    let names = names.into_inner();
    Some(e.map_cols(&|c, t| names.get(c).cloned().unwrap_or(E::Col(c.to_string(), t))))
}

#[allow(dead_code)]
fn qualifier(c: &Column) -> Option<&TableReference> {
    c.relation.as_ref()
}

#[allow(dead_code)]
fn provider_columns(plan: &LogicalPlan) -> Option<Vec<String>> {
    let LogicalPlan::TableScan(s) = plan else { return None };
    let p = source_as_provider(&s.source).ok()?;
    Some(p.schema().fields().iter().map(|f| f.name().clone()).collect())
}
