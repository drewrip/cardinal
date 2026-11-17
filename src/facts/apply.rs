//! Facts put in place in an analysis.
//!
//! Each operator of the query gets the context facts would name its rows by
//! ([`Logical`]). Every value a fact, bound or floor gives of an operator's
//! rows, or of rows a containment relates to them ([`fewer`],
//! [`groups_among`]), is then a claim on the operator's variables: its rows,
//! a column's distinct values, least or greatest value. Each claim joins
//! the constraints; with [`Options::check_facts`](crate::Options::check_facts),
//! only if it is consistent with them and those before it.

use std::collections::{BTreeSet, HashMap};
use std::panic::Location;
use std::sync::{Arc, Mutex};

use datafusion::logical_expr::Expr;
use z3::ast::{Bool, Int};

use crate::analysis::{Node, RawScan, Unit, unit};
use crate::rows::bases;
use crate::postprocess::Role;
use crate::facts::{Context, Fact, FactKind, FactSet, Term};
use crate::rows::canonical::Canonicals;
use crate::rows::contain::{fewer, groups_among, renamed_in};
use crate::rows::logical::Logical;
use crate::trace::{FactClaim, FactInfo, FactRef};
use crate::{Analysis, Result};

/// A [`FactSet`] made ready for analyses
/// ([`Builder::with_facts`](crate::Builder::with_facts)): checked once,
/// with what every analysis looks up in it indexed. Clones share it,
/// so one set of facts serves many analyses without being rebuilt.
#[derive(Debug, Clone)]
pub struct Facts(Arc<Shared>);

#[derive(Debug)]
struct Shared {
    set: FactSet,
    /// Kinds two plans disagree on, which are left out.
    conflicted: BTreeSet<FactKind>,
    /// The base tables ([`bases`]) of each context a bound on one column's
    /// distinct count is over.
    bounded: BTreeSet<Vec<String>>,
    /// The base tables of each context a floor or bound on a column's
    /// least or greatest value is over.
    ranged: BTreeSet<Vec<String>>,
    /// Each fact kind looked up so far, canonically renamed: canonical forms
    /// are costly with several instances of a table, and the same contexts
    /// come up for many operators and queries.
    canonical: Mutex<HashMap<FactKind, FactKind>>,
    /// Each context's canonical form, for the kinds not yet in `canonical`,
    /// and of the parts of contexts renamed to relate them.
    canonicals: Mutex<Canonicals>,
}

impl Facts {
    /// `set`, with each bound or floor an exact fact contradicts recorded
    /// as a conflict ([`FactSet::conflicts`]).
    pub fn new(mut set: FactSet) -> Facts {
        set.check_bounds();
        let conflicted = set.conflicts.iter().map(|c| c.kind.clone()).collect();
        let bounded = tables_of(set.bounds().filter_map(|f| match &f.kind {
            FactKind::Distinct { keys, over } if keys.len() == 1 => Some(over),
            _ => None,
        }));
        let ranged = tables_of(set.floors().chain(set.bounds()).filter_map(|f| match &f.kind {
            FactKind::Min { over, .. } | FactKind::Max { over, .. } => Some(over),
            _ => None,
        }));
        Facts(Arc::new(Shared { set, conflicted, bounded, ranged, canonical: Mutex::default(), canonicals: Mutex::default() }))
    }

    /// The facts.
    pub fn set(&self) -> &FactSet {
        &self.0.set
    }
}

/// `analysis` with every claim `facts` give among its constraints. Checking
/// ([`Options::check_facts`](crate::Options::check_facts)), claims that
/// contradict them, or whose consistency is undecided, are left out.
pub(crate) fn apply(analysis: &Analysis, facts: &Facts) -> Result<Analysis> {
    let logical = Logical::new(&analysis.nodes, &analysis.scans);
    let lookup = Lookup { nodes: &analysis.nodes, logical: &logical, facts: &facts.0.set, shared: &facts.0 };
    let search = if analysis.check_facts { Some(analysis.search_all()?) } else { None };
    let mut claims: Vec<FactClaim> = vec![];
    let mut assume = |claim: Bool, node: usize, source: &str, fact: FactRef, value: String| {
        let kept = search.as_ref().is_none_or(|s| s.assume(&claim) == Some(true));
        if kept {
            claims.push(fact_claim(claim, Some(node), source, vec![fact], value));
        }
        kept
    };

    // Every row count a fact gives.
    let mut pinned = BTreeSet::new();
    for (node, var, n, fact) in lookup.sizes() {
        if assume(Int::new_const(var.as_str()).eq(Int::from_u64(n)), node, "pinned rows", fact, format!("= {n}")) {
            pinned.insert(var);
        }
    }
    // Each column's distinct values: the constraints carry them up through
    // filters and joins to the GROUP BYs and DISTINCTs above.
    for (node, var, n, exact, fact) in lookup.ndvs() {
        let (v, k) = (Int::new_const(var.as_str()), Int::from_u64(n));
        let (claim, source, op) = if exact { (v.eq(k), "pinned ndv", "=") } else { (v.le(k), "ndv cap", "<=") };
        assume(claim, node, source, fact, format!("{op} {n}"));
    }
    // Each column's least and greatest values, which bound its distinct
    // values and what it joins with.
    for (node, var, n, floor, fact) in lookup.ranges() {
        let (v, k) = (Int::new_const(var.as_str()), Int::from_u64(n));
        let (claim, source, op) = if floor { (v.ge(k), "range floor", ">=") } else { (v.le(k), "range cap", "<=") };
        assume(claim, node, source, fact, format!("{op} {n}"));
    }
    // Every upper bound on a row count not pinned.
    for (node, var, n, fact) in lookup.caps() {
        if !pinned.contains(&var) {
            assume(Int::new_const(var.as_str()).le(Int::from_u64(n)), node, "row cap", fact, format!("<= {n}"));
        }
    }
    // Every row count of narrower rows than an operator's: a lower bound.
    for (node, var, n, fact) in lookup.floors() {
        assume(Int::new_const(var.as_str()).ge(Int::from_u64(n)), node, "floor", fact, format!(">= {n}"));
    }

    let mut out = analysis.clone();
    for c in &claims {
        out.constraints.push_str(&format!("(assert {})\n", c.claim));
        if let Some(parts) = &mut out.parts {
            parts.push(c.claim.to_string(), Role::Gen);
        }
    }
    out.assertions += claims.len();
    out.trace = analysis.trace.as_ref().map(|t| t.with_facts(&claims));
    Ok(out)
}

/// A claim from `facts` on `node`'s variable, made at the caller's line.
#[track_caller]
fn fact_claim(claim: Bool, node: Option<usize>, source: &str, facts: Vec<FactRef>, value: String) -> FactClaim {
    FactClaim {
        claim,
        node,
        info: FactInfo { source: source.to_string(), facts, value },
        at: Location::caller(),
    }
}

/// Facts about the operators of one plan.
struct Lookup<'a> {
    nodes: &'a [Node],
    logical: &'a Logical,
    facts: &'a FactSet,
    shared: &'a Shared,
}

impl<'a> Lookup<'a> {
    /// `kind`, canonically renamed, once per kind across analyses.
    fn canonical(&self, kind: FactKind) -> FactKind {
        if let Some(c) = self.shared.canonical.lock().unwrap().get(&kind) {
            return c.clone();
        }
        let c = kind.canonical_in(&mut self.shared.canonicals.lock().unwrap());
        self.shared.canonical.lock().unwrap().insert(kind, c.clone());
        c
    }

    /// `ctx`, canonically renamed, as [`Context::canonical`] does.
    fn canonical_ctx(&self, ctx: &Context) -> Context {
        match self.canonical(FactKind::Cardinality(ctx.clone())) {
            FactKind::Cardinality(c) => c,
            _ => unreachable!(),
        }
    }

    /// Fact `kind`, unless two plans disagree on it.
    fn get(&self, kind: FactKind) -> Option<&'a Fact> {
        self.get_canonical(&self.canonical(kind))
    }

    /// [`Self::get`], of a `kind` already canonical.
    fn get_canonical(&self, kind: &FactKind) -> Option<&'a Fact> {
        if self.shared.conflicted.contains(kind) {
            return None;
        }
        self.facts.get(kind)
    }

    /// Every operator's upper bound on its rows that a bound gives, or a
    /// row count of wider rows than its own ([`fewer`]), or for a GROUP BY a
    /// distinct count of its keys over wider rows than its input's
    /// ([`groups_among`]), by variable.
    fn caps(&self) -> Vec<(usize, String, u64, FactRef)> {
        let mut out = vec![];
        for (i, node) in self.nodes.iter().enumerate() {
            let Ok(ctx) = &self.logical.contexts[i] else { continue };
            let kind = match ctx {
                Context::Derived { op, args, inputs } if op == "group" => {
                    FactKind::Distinct { keys: args.iter().cloned().collect(), over: inputs[0].clone() }
                }
                ctx => FactKind::Cardinality(ctx.clone()),
            };
            if let Some(b) = self.facts.bound(&self.canonical(kind))
                && let Some(n) = b.value.as_int()
            {
                out.push((i, node.var.clone(), n, FactRef::of(b)));
            }
            // Row counts, exact or bounds, of wider rows than the operator's.
            let ctx = self.canonical_ctx(ctx);
            let tables = ctx.tables();
            for f in self.facts.iter().chain(self.facts.bounds()) {
                let FactKind::Cardinality(c) = &f.kind else { continue };
                if *c != ctx
                    && !self.shared.conflicted.contains(&f.kind)
                    && c.tables().is_subset(&tables)
                    && let Some(n) = f.value.as_int()
                    && renamed_in(&ctx, c, fewer, &mut self.shared.canonicals.lock().unwrap())
                {
                    out.push((i, node.var.clone(), n, FactRef::of(f)));
                }
            }
            // Distinct counts, exact or bounds, of the keys over wider rows
            // than the GROUP BY's input: a subset of the rows has no more
            // groups.
            if !matches!(&ctx, Context::Derived { op, .. } if op == "group") {
                continue;
            }
            for f in self.facts.iter().chain(self.facts.bounds()) {
                let FactKind::Distinct { keys, over } = &f.kind else { continue };
                let wider = Context::Derived { op: "group".into(), args: keys.iter().cloned().collect(), inputs: vec![over.clone()] };
                if wider != ctx
                    && !self.shared.conflicted.contains(&f.kind)
                    && over.tables().is_subset(&tables)
                    && let Some(n) = f.value.as_int()
                    && renamed_in(&ctx, &wider, groups_among, &mut self.shared.canonicals.lock().unwrap())
                {
                    out.push((i, node.var.clone(), n, FactRef::of(f)));
                }
            }
        }
        out
    }

    /// Every base-table column's distinct count that a fact gives over its
    /// table, by the scan's NDV variable (the raw scan's, under pushed
    /// filters), and whether it is exact (else an upper bound). The
    /// constraints carry each up through filters, joins and GROUP BYs, so
    /// no operator above a scan needs its own, unless a bound gives one of
    /// its rows: those are read at every operator. Float columns are left
    /// out: the constraints count their values by bits, the facts by SQL
    /// equality.
    fn ndvs(&self) -> Vec<(usize, String, u64, bool, FactRef)> {
        let mut out = vec![];
        for (i, node) in self.nodes.iter().enumerate() {
            let Ok(ctx) = &self.logical.contexts[i] else { continue };
            // A base table's are read below.
            if !self.shared.bounded.contains(&bases(ctx)) || (self.logical.instances[i].is_some() && node.raw_scan.is_none()) {
                continue;
            }
            let schema = node.plan.schema();
            for (j, var) in node.ndv_vars.iter().enumerate() {
                let Some(Some(e @ Expr::Column(_))) = self.logical.lineage[i].get(j) else { continue };
                if j >= schema.fields().len() || schema.field(j).data_type().is_floating() {
                    continue;
                }
                let kind = self.canonical(FactKind::Distinct { keys: [Term::new(e.clone())].into(), over: ctx.clone() });
                if let Some(b) = self.facts.bound(&kind)
                    && !self.shared.conflicted.contains(&kind)
                    && let Some(n) = b.value.as_int()
                {
                    out.push((i, var.clone(), n, false, FactRef::of(b)));
                }
            }
        }
        for (i, node) in self.nodes.iter().enumerate() {
            let Some(instance) = &self.logical.instances[i] else { continue };
            let vars = node.raw_scan.as_ref().map_or(&node.ndv_vars, |r| &r.ndv_vars);
            let schema = node.plan.schema();
            let over = Context::table(instance);
            for (j, var) in vars.iter().enumerate() {
                let Some(Some(e @ Expr::Column(_))) = self.logical.lineage[i].get(j) else { continue };
                if j >= schema.fields().len() || schema.field(j).data_type().is_floating() {
                    continue;
                }
                let keys = [Term::new(e.clone())].into();
                let kind = self.canonical(FactKind::Distinct { keys, over: over.clone() });
                if let Some(f) = self.get_canonical(&kind)
                    && let Some(n) = f.value.as_int()
                {
                    out.push((i, var.clone(), n, true, FactRef::of(f)));
                } else if let Some(b) = self.facts.bound(&kind)
                    && let Some(n) = b.value.as_int()
                {
                    out.push((i, var.clone(), n, false, FactRef::of(b)));
                }
            }
        }
        out
    }

    /// Each column's least value that a floor gives over its operator's
    /// rows, and its greatest that a bound gives, by its min or max variable
    /// (the raw scan's for a base table under pushed filters), and whether
    /// it is a floor.
    fn ranges(&self) -> Vec<(usize, String, u64, bool, FactRef)> {
        let mut out = vec![];
        for (i, node) in self.nodes.iter().enumerate() {
            let mut rows = vec![];
            if let (Some(raw), Some(instance)) = (&node.raw_scan, &self.logical.instances[i]) {
                rows.push((Context::table(instance), &raw.min_vars, &raw.max_vars));
            }
            if let Ok(ctx) = &self.logical.contexts[i] {
                rows.push((ctx.clone(), &node.min_vars, &node.max_vars));
            }
            for (ctx, mins, maxs) in rows {
                if !self.shared.ranged.contains(&bases(&ctx)) {
                    continue;
                }
                for (j, (lo, hi)) in mins.iter().zip(maxs).enumerate() {
                    let Some(Some(e @ Expr::Column(_))) = self.logical.lineage[i].get(j) else { continue };
                    // Facts read ends off integer literals: they count as an
                    // integer column's values do, not a date's or decimal's.
                    let schema = node.plan.schema();
                    if j >= schema.fields().len() || unit(schema.field(j).data_type()) != Some(Unit::Int) {
                        continue;
                    }
                    let key = Term::new(e.clone());
                    let ends = [
                        (lo, FactKind::Min { key: key.clone(), over: ctx.clone() }, true),
                        (hi, FactKind::Max { key, over: ctx.clone() }, false),
                    ];
                    for (var, kind, floor) in ends {
                        let Some(var) = var else { continue };
                        let kind = self.canonical(kind);
                        let found = if floor { self.facts.floor(&kind) } else { self.facts.bound(&kind) };
                        if let Some(f) = found
                            && !self.shared.conflicted.contains(&kind)
                            && let Some(n) = f.value.as_int()
                        {
                            out.push((i, var.clone(), n, floor, FactRef::of(f)));
                        }
                    }
                }
            }
        }
        out
    }

    /// Each operator's lower bounds on its rows that facts give of narrower
    /// rows ([`fewer`]), and that floors give of its own rows or narrower
    /// ones, by variable, with the fact each is from. Each is asserted, and
    /// the solver keeps the largest.
    fn floors(&self) -> Vec<(usize, String, u64, FactRef)> {
        // Each count, and whether it is a floor: one holds of its own rows.
        let exact = self.facts.iter().map(|f| (f, false));
        let floors = self.facts.floors().map(|f| (f, true));
        let counts: Vec<(&Context, u64, &Fact, bool)> = exact
            .chain(floors)
            .filter(|(f, _)| !self.shared.conflicted.contains(&f.kind))
            .filter_map(|(f, floor)| match &f.kind {
                FactKind::Cardinality(c) => Some((c, f.value.as_int()?, f, floor)),
                _ => None,
            })
            .collect();
        let mut out = vec![];
        for (i, node) in self.nodes.iter().enumerate() {
            let Ok(ctx) = &self.logical.contexts[i] else { continue };
            let ctx = self.canonical_ctx(ctx);
            let tables = ctx.tables();
            for (c, n, fact, floor) in &counts {
                if tables.is_subset(&c.tables()) && if **c == ctx { *floor } else { renamed_in(c, &ctx, fewer, &mut self.shared.canonicals.lock().unwrap()) } {
                    out.push((i, node.var.clone(), *n, FactRef::of(fact)));
                }
            }
        }
        out
    }

    /// Every operator's row count that a fact gives, by variable.
    fn sizes(&self) -> Vec<(usize, String, u64, FactRef)> {
        let mut out = vec![];
        for (i, node) in self.nodes.iter().enumerate() {
            if let (Some(RawScan { var: raw, .. }), Some(instance)) = (&node.raw_scan, &self.logical.instances[i])
                && let Some(f) = self.get(FactKind::Cardinality(Context::table(instance)))
                && let Some(n) = f.value.as_int()
            {
                out.push((i, raw.clone(), n, FactRef::of(f)));
            }
            let Ok(ctx) = &self.logical.contexts[i] else { continue };
            let fact = match ctx {
                // A grouping's rows are its keys' distinct values.
                Context::Derived { op, args, inputs } if op == "group" => {
                    self.get(FactKind::Distinct { keys: args.iter().cloned().collect(), over: inputs[0].clone() })
                }
                ctx => self.get(FactKind::Cardinality(ctx.clone())),
            };
            if let Some(f) = fact
                && let Some(n) = f.value.as_int()
            {
                out.push((i, node.var.clone(), n, FactRef::of(f)));
            }
        }
        out
    }
}

/// [`bases`] of each of `contexts`.
fn tables_of<'c>(contexts: impl Iterator<Item = &'c Context>) -> BTreeSet<Vec<String>> {
    contexts.map(bases).collect()
}
