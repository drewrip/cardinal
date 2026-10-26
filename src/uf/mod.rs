//! Cardinality bounds from abstract relations and axioms.
//!
//! Every plan node becomes a term, the same subplan always the same term:
//! the nodes of plans an engine ran, and those of the plan to bound. Each
//! operator's semantics are stated once, as quantified axioms over terms
//! (`axioms`), and an executed node's row count is a fact on its term. Z3
//! then bounds the target's root by optimize-then-confirm: the tightest
//! `B` the axioms and facts entail.
//!
//! ```ignore
//! let mut enc = uf::Encoder::new(&catalog, &foreign_keys);
//! for p in &profiles { enc.observe(p); }
//! let b = enc.bound(&logical_plan, &[])?;   // b.lower <= rows <= b.upper
//! ```

mod axioms;
mod expr;
#[cfg(test)]
mod pattern_check;
mod preds;
mod program;
mod solve;
mod terms;
mod translate;

pub use program::Stats;

use std::collections::{BTreeSet, HashMap};
use std::time::{Duration, Instant};

use datafusion::logical_expr::LogicalPlan;

use crate::observed::{Catalog, ObservedPlan};
use crate::{ForeignKey, Result};
use program::Schema;
use terms::{Pred, Rel, RelId, Terms};
use translate::{Builder, Fact, Tables};

/// The proven bounds on a target's row count.
#[derive(Debug, Clone)]
pub struct Bound {
    pub lower: u64,
    /// `None`: no upper bound proven.
    pub upper: Option<u64>,
    /// Facts dropped because, with the others, they proved `false`.
    pub dropped: Vec<String>,
    /// Solver checks made.
    pub checks: usize,
    /// The most quantifier instances a proven check made: what a budget
    /// must allow.
    pub needed: u64,
    pub time: Duration,
    pub stats: Stats,
}

/// Executed plans, as terms with facts, to bound other plans with.
pub struct Encoder<'c> {
    catalog: &'c Catalog,
    schema: Schema,
    terms: Terms,
    /// Each executed plan: its name, its facts, and its relations.
    plans: Vec<(String, Vec<(String, Fact)>, Vec<RelId>)>,
}

impl<'c> Encoder<'c> {
    /// An encoder over `catalog`'s tables: their primary keys and UNIQUE
    /// constraints, non-NULL columns, and `foreign_keys`.
    pub fn new(catalog: &'c Catalog, foreign_keys: &[ForeignKey]) -> Encoder<'c> {
        let mut schema = Schema::default();
        let mut names: Vec<&String> = catalog.tables.keys().collect();
        names.sort();
        for t in names {
            let s = &catalog.tables[t];
            for f in s.fields() {
                if !f.is_nullable() {
                    schema.nonnull.insert((t.clone(), f.name().clone()));
                }
            }
            if let Some(p) = catalog.providers.get(t)
                && let Some(cs) = p.constraints()
            {
                for c in cs.iter() {
                    let idx = match c {
                        datafusion::common::Constraint::PrimaryKey(i) | datafusion::common::Constraint::Unique(i) => i,
                    };
                    let cols: Option<Vec<String>> = idx.iter().map(|i| s.fields().get(*i).map(|f| f.name().clone())).collect();
                    if let Some(cols) = cols {
                        if matches!(c, datafusion::common::Constraint::PrimaryKey(_)) {
                            for col in &cols {
                                schema.nonnull.insert((t.clone(), col.clone()));
                            }
                        }
                        schema.keys.push((t.clone(), cols));
                    }
                }
            }
        }
        for fk in foreign_keys {
            schema.fks.push((fk.table.clone(), fk.columns.clone(), fk.references.clone(), fk.referenced.clone()));
        }
        Encoder { catalog, schema, terms: Terms::default(), plans: vec![] }
    }

    /// Adds an executed plan's facts: each counted operator's row count.
    pub fn observe(&mut self, plan: &ObservedPlan) {
        let tables = Tables { catalog: self.catalog };
        let mut b = Builder { terms: &mut self.terms, tables: &tables };
        let (facts, _) = translate::executed(&mut b, plan);
        let roots: Vec<RelId> = facts.iter().flat_map(|(_, f)| fact_rel(f)).collect();
        let map = prune(&mut self.terms, &roots);
        let facts = facts.into_iter().map(|(n, f)| (n, remap(&f, &map))).collect::<Vec<_>>();
        let rels: Vec<RelId> = roots.iter().map(|r| map.get(r).copied().unwrap_or(*r)).collect();
        self.plans.push((plan.name.clone(), facts, rels));
    }

    /// Each fact of plan `name`, as SMT: what it says of which term.
    pub fn describe(&self, name: &str) -> Vec<String> {
        let mut out = vec![];
        for (n, facts, _) in &self.plans {
            if n != name {
                continue;
            }
            for (f, fact) in facts {
                let text = match fact {
                    Fact::Card(r, v) => format!("card {} = {v}", self.terms.rel_smt(*r)),
                    Fact::KeyRange(r, c, lo, hi) => format!("{c} in [{lo:?}, {hi:?}] over {}", self.terms.rel_smt(*r)),
                    Fact::KeyCount(r, c, k) => format!("ndv {c} ~ {k} over {}", self.terms.rel_smt(*r)),
                };
                out.push(format!("{f}: {text}"));
            }
        }
        out
    }

    /// The term of DataFusion plan `target`, as SMT.
    pub fn target_term(&self, target: &LogicalPlan) -> String {
        let mut terms = self.terms.clone();
        let tables = Tables { catalog: self.catalog };
        let mut b = Builder { terms: &mut terms, tables: &tables };
        let r = translate::logical(&mut b, target, "target", &mut vec![]);
        let map = prune(&mut terms, &[r]);
        terms.rel_smt(map.get(&r).copied().unwrap_or(r))
    }

    /// The term of `target`, a plan as an engine planned it, as SMT.
    pub fn planned_term(&self, target: &ObservedPlan) -> String {
        let mut terms = self.terms.clone();
        let tables = Tables { catalog: self.catalog };
        let mut b = Builder { terms: &mut terms, tables: &tables };
        let r = translate::planned(&mut b, target);
        let map = prune(&mut terms, &[r]);
        terms.rel_smt(map.get(&r).copied().unwrap_or(r))
    }

    /// The names of the plans observed.
    pub fn plans(&self) -> impl Iterator<Item = &str> {
        self.plans.iter().map(|(n, ..)| n.as_str())
    }

    /// Bounds the row count of DataFusion plan `target`, with the facts of
    /// every observed plan but those named in `except`.
    pub fn bound(&self, target: &LogicalPlan, except: &[&str]) -> Result<Bound> {
        let mut terms = self.terms.clone();
        let tables = Tables { catalog: self.catalog };
        let mut shape = vec![];
        let root = {
            let mut b = Builder { terms: &mut terms, tables: &tables };
            translate::logical(&mut b, target, "target", &mut shape)
        };
        self.solve(terms, root, shape, except)
    }

    /// Bounds the row count of `target`, a plan as an engine planned it
    /// (its counts, if any, are not used).
    pub fn bound_observed(&self, target: &ObservedPlan, except: &[&str]) -> Result<Bound> {
        let mut terms = self.terms.clone();
        let tables = Tables { catalog: self.catalog };
        let mut plan = target.clone();
        plan.name = "target".into();
        let root = {
            let mut b = Builder { terms: &mut terms, tables: &tables };
            translate::planned(&mut b, &plan)
        };
        self.solve(terms, root, vec![], except)
    }

    fn solve(&self, mut terms: Terms, root: RelId, shape: Vec<(String, Fact)>, except: &[&str]) -> Result<Bound> {
        let start = Instant::now();
        let map = prune(&mut terms, &[root]);
        let root = map.get(&root).copied().unwrap_or(root);
        let shape: Vec<(String, Fact)> = shape.into_iter().map(|(n, f)| (n, remap(&f, &map))).collect();
        // Facts about the target's tables only.
        let allowed = tables_of(&terms, root);
        let relevant = |r: &RelId| tables_of(&terms, *r).is_subset(&allowed);
        let mut facts = vec![];
        let mut groups = vec![];
        for (name, fs, rels) in &self.plans {
            if except.contains(&name.as_str()) {
                continue;
            }
            facts.extend(fs.iter().filter(|(_, f)| fact_rel(f).iter().all(relevant)).cloned());
            groups.push(rels.iter().copied().filter(relevant).collect::<Vec<_>>());
        }
        let tables = Tables { catalog: self.catalog };
        // First the target alone: what the axioms prove of its shape, on a
        // program small enough to search quickly. The facts' program then
        // starts from there.
        let alone = program::build(&mut terms, &tables, &self.schema, &shape, &[], root);
        if let Ok(path) = std::env::var("CARDINAL_UF_DUMP") {
            static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
            let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let _ = std::fs::write(path.replace("{}", &format!("alone{n}")), &alone.text);
        }
        facts.extend(shape);
        let timing = std::env::var("CARDINAL_UF_TIME").is_ok();
        let t0 = Instant::now();
        let program = program::build(&mut terms, &tables, &self.schema, &facts, &groups, root);
        if timing {
            eprintln!("uf: program {:.2}s, {} bytes", t0.elapsed().as_secs_f64(), program.text.len());
        }
        if let Ok(path) = std::env::var("CARDINAL_UF_DUMP") {
            // `{}` in the path numbers each program.
            static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
            let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let _ = std::fs::write(path.replace("{}", &n.to_string()), &program.text);
        }
        // The target alone, and the facts' consistency check (§6.6), at
        // once: neither needs the other.
        let mut s = solve::Session::new(&program);
        let t0 = Instant::now();
        let ((structural, structural_checks), dropped) = std::thread::scope(|scope| {
            let a = scope.spawn(|| {
                let mut s = solve::Session::new(&alone);
                let b = s.bounds((0, None), false);
                (b, s.checks)
            });
            let dropped = s.consistent();
            (a.join().unwrap(), dropped)
        });
        if timing {
            eprintln!("uf: alone {structural:?} in {structural_checks} checks, and consistent, {:.2}s", t0.elapsed().as_secs_f64());
        }
        let t0 = Instant::now();
        let (mut lower, mut upper) = s.bounds(structural, true);
        s.checks += structural_checks;
        if timing {
            eprintln!("uf: bounds {:.2}s", t0.elapsed().as_secs_f64());
        }
        // A probe proving both sides apart exposes a contradiction the
        // check missed (§6.6): no bound.
        if upper.is_some_and(|u| u < lower) {
            upper = None;
            lower = 0;
        }
        let _ = s.in_use();
        Ok(Bound { lower, upper, dropped, checks: s.checks, needed: s.needed, time: start.elapsed(), stats: program.stats })
    }
}

/// The tables under relation `r`, its subqueries' too.
fn tables_of(terms: &Terms, r: RelId) -> BTreeSet<String> {
    terms
        .reachable([r])
        .into_iter()
        .filter_map(|x| match terms.get(x) {
            Rel::Scan(t) => Some(t.clone()),
            _ => None,
        })
        .collect()
}

fn fact_rel(f: &Fact) -> Vec<RelId> {
    match f {
        Fact::Card(r, _) | Fact::KeyRange(r, ..) | Fact::KeyCount(r, ..) => vec![*r],
    }
}

fn remap(f: &Fact, map: &HashMap<RelId, RelId>) -> Fact {
    let m = |r: &RelId| map.get(r).copied().unwrap_or(*r);
    match f {
        Fact::Card(r, n) => Fact::Card(m(r), *n),
        Fact::KeyRange(r, c, lo, hi) => Fact::KeyRange(m(r), c.clone(), *lo, *hi),
        Fact::KeyCount(r, c, n) => Fact::KeyCount(m(r), c.clone(), *n),
    }
}

/// Drops the aggregate values nothing under `roots` reads (§5): an
/// aggregate keeps only the values its plan reads, and one with none is
/// a GROUP BY. Returns each relation's replacement.
fn prune(terms: &mut Terms, roots: &[RelId]) -> HashMap<RelId, RelId> {
    let rels = terms.reachable(roots.iter().copied());
    // Every column something reads.
    let mut read: BTreeSet<String> = BTreeSet::new();
    for r in &rels {
        for p in terms.rel_preds(*r) {
            if let Some(cs) = terms.reads(p) {
                read.extend(cs);
            }
            if let Pred::Cmp { g, .. } = terms.get_pred(p) {
                read.insert(g.clone());
            }
        }
        match terms.get(*r) {
            Rel::Group(k, _) | Rel::Aggregate(k, _, _) => read.extend(terms.cols[k.0 as usize].iter().cloned()),
            Rel::Join(_, f, ..) | Rel::Rt(f, ..) => {
                for (a, b) in &terms.families[f.0 as usize].pairs {
                    read.insert(a.clone());
                    read.insert(b.clone());
                }
            }
            Rel::Extend(g, _) => {
                read.insert(g.clone());
            }
            _ => {}
        }
    }
    let exprs: Vec<_> = terms.exprs.values().map(|e| e.reads()).collect();
    for e in exprs {
        read.extend(e);
    }
    let mut map: HashMap<RelId, RelId> = HashMap::new();
    let mut pmap: HashMap<terms::PredId, terms::PredId> = HashMap::new();
    for r in rels {
        let m = |x: &RelId, map: &HashMap<RelId, RelId>| map.get(x).copied().unwrap_or(*x);
        let mut p_of = |p: terms::PredId, terms: &mut Terms, map: &HashMap<RelId, RelId>| -> terms::PredId {
            if let Some(q) = pmap.get(&p) {
                return *q;
            }
            let q = match terms.get_pred(p).clone() {
                Pred::Cmp { op, a, y, g } => terms.pred(Pred::Cmp { op, a, y: m(&y, map), g }),
                _ => p,
            };
            pmap.insert(p, q);
            q
        };
        let new = match terms.get(r).clone() {
            Rel::Aggregate(k, g, x) => {
                let kept: BTreeSet<String> = terms.cols[g.0 as usize].iter().filter(|c| read.contains(*c)).cloned().collect();
                let x = m(&x, &map);
                if kept.is_empty() {
                    Rel::Group(k, x)
                } else {
                    Rel::Aggregate(k, terms.colset(kept), x)
                }
            }
            Rel::Scalar(g, x) => {
                let kept: BTreeSet<String> = terms.cols[g.0 as usize].iter().filter(|c| read.contains(*c)).cloned().collect();
                Rel::Scalar(terms.colset(kept), m(&x, &map))
            }
            Rel::Filter(p, x) => Rel::Filter(p_of(p, terms, &map), m(&x, &map)),
            Rel::Group(k, x) => Rel::Group(k, m(&x, &map)),
            Rel::Limit(n, x) => Rel::Limit(n, m(&x, &map)),
            Rel::Offset(n, x) => Rel::Offset(n, m(&x, &map)),
            Rel::Union(x, y) => Rel::Union(m(&x, &map), m(&y, &map)),
            Rel::Join(k, f, x, y) => Rel::Join(k, f, m(&x, &map), m(&y, &map)),
            Rel::Part(o, x) => Rel::Part(o, m(&x, &map)),
            Rel::Opt(o, p, x) => Rel::Opt(o, p, m(&x, &map)),
            Rel::Rt(f, o, x, y) => Rel::Rt(f, o, m(&x, &map), m(&y, &map)),
            Rel::Extend(g, x) => Rel::Extend(g, m(&x, &map)),
            Rel::Alias(i, x) => Rel::Alias(i, m(&x, &map)),
            rel @ (Rel::Scan(_) | Rel::Opaque(_)) => rel,
        };
        let cols = terms.rel_cols[r.0 as usize];
        let id = terms.rel(new);
        if terms.rel_cols[id.0 as usize].is_none() {
            terms.rel_cols[id.0 as usize] = cols;
        }
        if id != r {
            map.insert(r, id);
        }
    }
    map
}
