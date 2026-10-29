//! Bounds informed by facts: selectivities seen before, put in place.
//!
//! A query's output cardinality is a formula over table sizes and
//! selectivities ([`SelectivityReport`]), each of which belongs to one
//! operator and is a share of that operator's input. A [`FactSet`] holds
//! exact values read off plans that ran. Each operator of the query gets the
//! context facts would name its rows by ([`Logical`]), so a selectivity's
//! value is a lookup: the share of `over`'s rows satisfying a predicate, a
//! join's share of pairs, the share of a kept side with a partner, or a
//! distinct count over its input's size. Where none is stored, the sizes of
//! the operator's output and inputs give it.
//!
//! A matched value replaces its selectivity in the formula, and its
//! operator's relation to its inputs (`X = s·l`) joins the constraints,
//! where it combines with everything else they know.

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::fmt;
use std::panic::Location;

use datafusion::common::JoinType;
use datafusion::logical_expr::Expr;
use serde::{Deserialize, Serialize};
use z3::ast::{Bool, Int, Real};

use crate::analyzer::Node;
use crate::bounds::{Bounds, Search, SearchStats};
use crate::facts::contain::{fewer, groups_among, renamed};
use crate::facts::logical::Logical;
use crate::facts::{Context, Fact, FactKind, FactSet, Ratio, Term};
use crate::selectivity::{Card, Interval, Kind, Selectivity, SelectivityReport};
use crate::trace::{self, FactClaim, FactInfo, FactRef, Proof, Trace};
use crate::{Analysis, Error, Result};

/// What facts may stand for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FactMode {
    /// Only selectivities: table sizes stay unknowns, so the bounds hold as
    /// the tables grow, as long as their selectivities stay the same. That is
    /// a weaker assumption for a filter's or join's share than for a
    /// GROUP BY's, whose groups need not grow with its input.
    Ratios,
    /// Also the row counts of tables and operators: exact for the data the
    /// facts were read from, and wrong once it changes.
    Pinned,
}

/// A selectivity whose value is known.
#[derive(Debug, Clone, PartialEq)]
pub struct Matched {
    /// The selectivity, by name.
    pub name: String,
    pub value: Ratio,
    /// The facts it was read from.
    pub facts: Vec<String>,
}

impl fmt::Display for Matched {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {} from {}", self.name, self.value, self.facts.join(", "))
    }
}

/// An analysis with facts put in place.
#[derive(Debug, Clone)]
pub struct Informed {
    pub mode: FactMode,
    /// The output cardinality with every matched selectivity (and, pinned,
    /// every known size) substituted.
    pub output: Card,
    /// Selectivities with a value.
    pub matched: Vec<Matched>,
    /// Selectivities the output needs that have none, and why.
    pub unmatched: Vec<(String, String)>,
    /// Values that were found but not used, and why: outside the range the
    /// constraints prove, or contradicting them. Either means a fact was
    /// matched to the wrong rows, or the data changed.
    pub rejected: Vec<(String, String)>,
    /// Operator variables pinned to a known row count.
    pub pinned: Vec<(String, u64)>,
    /// Operator variables capped by a known upper bound on their rows.
    pub capped: Vec<(String, u64)>,
    /// NDV variables of base-table scans' columns, held at (or capped by)
    /// the distinct count a fact gives over the table. The constraints
    /// carry them to the operators above. Pinned only.
    pub pinned_ndv: Vec<(String, u64)>,
    /// Min variables held at or above, and max variables at or below, the
    /// least and greatest values facts give of their columns. Pinned only.
    pub ranges: Vec<(String, u64)>,
    /// Operator variables held at or above a row count the facts give of
    /// narrower rows: the same rows with more filters, say. These hold in
    /// either mode, as the tables grow too.
    pub floors: Vec<(String, u64)>,
    /// Selectivities whose relation to the constraints could not be checked
    /// in time, and so is not among them.
    pub unchecked: Vec<String>,
    /// The analysis's [`Trace`] with a constraint for each claim the facts
    /// added, if the analysis was traced.
    pub trace: Option<Trace>,
    /// Where each fact [`Informed::matched`] names was read, by its text;
    /// filled only when traced.
    origins: HashMap<String, Vec<String>>,
    /// The formula, for evaluating with the selectivities still unknown.
    report: SelectivityReport,
    /// The constraint set with the facts' relations added.
    constraints: String,
    assertions: usize,
    root: String,
    scans: Vec<String>,
    tables: Vec<(String, String)>,
}

impl Informed {
    /// The output cardinality given each table's row count, as a range over
    /// the selectivities still unknown.
    pub fn evaluate(&self, tables: &HashMap<String, u64>) -> Result<Interval> {
        self.report.eval(&self.output, tables, &HashMap::new())
    }

    /// [`Informed::evaluate`], with a value for some of the selectivities
    /// still unknown, by name, as [`SelectivityReport::evaluate`] takes
    /// them: the facts' values first, then these for what they left.
    pub fn evaluate_with(&self, tables: &HashMap<String, u64>, values: &HashMap<String, f64>) -> Result<Interval> {
        self.report.eval(&self.output, tables, values)
    }

    /// Bounds proven with the facts among the constraints, as
    /// [`Analysis::bounds`].
    pub fn bounds(&self) -> Result<Bounds> {
        let search = self.search()?;
        Ok(crate::prove_bounds(&search, &self.scans, &self.tables))
    }

    /// The proven `lo <= X <= hi`, with no `hi` if none is proven: a constant
    /// range, cheaper than [`Informed::bounds`]. `lo` takes in the
    /// [`Informed::floors`].
    pub fn range(&self) -> Result<(u64, Option<u64>)> {
        let search = self.search()?;
        Ok((search.lower(), search.constant()))
    }

    /// [`Informed::bounds`], and how its solver checks went.
    #[doc(hidden)]
    pub fn bounds_with_stats(&self) -> Result<(Bounds, SearchStats)> {
        let search = self.search()?;
        let bounds = crate::prove_bounds(&search, &self.scans, &self.tables);
        Ok((bounds, search.stats()))
    }

    /// [`Informed::range`], and how its solver checks went.
    #[doc(hidden)]
    pub fn range_with_stats(&self) -> Result<((u64, Option<u64>), SearchStats)> {
        let search = self.search()?;
        let range = (search.lower(), search.constant());
        Ok((range, search.stats()))
    }

    /// Proves the claims of [`Analysis::explain`] for `bounds` (these
    /// bounds, say) from the constraints with the facts' among them, each
    /// with a minimal set of constraints, facts' or the analyzer's, that
    /// proves it. Needs [`crate::Options::trace`].
    pub fn explain(&self, bounds: Option<&Bounds>) -> Result<Vec<Proof>> {
        let trace = self.trace.as_ref().ok_or_else(|| Error::Internal("explain needs Options::trace".into()))?;
        trace.explain(&trace::claims(&self.root, &self.scans, &self.tables, bounds))
    }

    /// [`Informed::explain`] without the facts' constraints: which of the
    /// claims hold without them.
    pub fn explain_without_facts(&self, bounds: Option<&Bounds>) -> Result<Vec<Proof>> {
        let trace = self.trace.as_ref().ok_or_else(|| Error::Internal("explain needs Options::trace".into()))?;
        trace.without_facts().explain(&trace::claims(&self.root, &self.scans, &self.tables, bounds))
    }

    /// What the facts gave and left, to show or store.
    pub fn report(&self) -> FactReport {
        FactReport {
            mode: self.mode.to_string(),
            output: self.output.to_string(),
            matched: self
                .matched
                .iter()
                .map(|m| MatchedReport {
                    name: m.name.clone(),
                    value: m.value.to_string(),
                    facts: m
                        .facts
                        .iter()
                        .map(|f| FactRef {
                            text: f.clone(),
                            origins: self.origins.get(f).cloned().unwrap_or_default(),
                        })
                        .collect(),
                })
                .collect(),
            unmatched: self.unmatched.clone(),
            rejected: self.rejected.clone(),
            pinned: self.pinned.clone(),
            capped: self.capped.clone(),
            pinned_ndv: self.pinned_ndv.clone(),
            ranges: self.ranges.clone(),
            floors: self.floors.clone(),
            unchecked: self.unchecked.clone(),
        }
    }

    fn search(&self) -> Result<Search> {
        let (search, parsed) = Search::new(&self.constraints, &self.root);
        if parsed != self.assertions {
            return Err(Error::Internal(format!(
                "constraints parsed back to {parsed} assertions, expected {}",
                self.assertions
            )));
        }
        Ok(search)
    }
}

impl fmt::Display for FactMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            FactMode::Ratios => "ratios",
            FactMode::Pinned => "pinned",
        })
    }
}

/// [`Informed`]'s account of its facts, as text.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactReport {
    pub mode: String,
    pub output: String,
    pub matched: Vec<MatchedReport>,
    pub unmatched: Vec<(String, String)>,
    pub rejected: Vec<(String, String)>,
    pub pinned: Vec<(String, u64)>,
    pub capped: Vec<(String, u64)>,
    pub pinned_ndv: Vec<(String, u64)>,
    #[serde(default)]
    pub ranges: Vec<(String, u64)>,
    pub floors: Vec<(String, u64)>,
    pub unchecked: Vec<String>,
}

/// A [`Matched`] selectivity, with where its facts were read.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MatchedReport {
    pub name: String,
    pub value: String,
    pub facts: Vec<FactRef>,
}

impl fmt::Display for Informed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "X = {}", self.output)?;
        for m in &self.matched {
            write!(f, "\n  {m}")?;
        }
        for (s, why) in &self.unmatched {
            write!(f, "\n  {s}: unknown ({why})")?;
        }
        for (s, why) in &self.rejected {
            write!(f, "\n  {s}: rejected ({why})")?;
        }
        for (v, n) in &self.floors {
            write!(f, "\n  {v} >= {n}")?;
        }
        Ok(())
    }
}

/// The fact each selectivity `analysis` requires is looked up as, by
/// selectivity name, or why it is none.
pub(crate) fn kinds(analysis: &Analysis) -> Vec<(String, std::result::Result<FactKind, String>)> {
    kinds_in(analysis, &Logical::new(&analysis.nodes, &analysis.scans))
}

/// [`kinds`], with the operators' rows named by `logical`.
pub(crate) fn kinds_in(analysis: &Analysis, logical: &Logical) -> Vec<(String, std::result::Result<FactKind, String>)> {
    let Some(report) = &analysis.selectivity else { return vec![] };
    let none = FactSet::default();
    let lookup = Lookup::new(&analysis.nodes, logical, &none);
    report.required.iter().map(|s| (s.name.clone(), lookup.kind(s).map(|k| lookup.canonical(k)))).collect()
}

/// `analysis` with what `facts` know put in place.
pub(crate) fn inform(analysis: &Analysis, facts: &FactSet, mode: FactMode) -> Result<Informed> {
    let Some(report) = &analysis.selectivity else {
        return Err(Error::Internal("facts need an analysis with selectivities".into()));
    };
    let logical = Logical::new(&analysis.nodes, &analysis.scans);
    let lookup = Lookup::new(&analysis.nodes, &logical, facts);

    // Each selectivity's value, if a fact gives one in its proven range.
    let mut matched: Vec<Matched> = vec![];
    let mut rejected = vec![];
    let mut missing = HashMap::new();
    for s in &report.all {
        match lookup.selectivity(s) {
            Ok((value, facts)) if s.range.contains(value.as_f64()) => {
                matched.push(Matched { name: s.name.clone(), value, facts })
            }
            Ok((value, _)) => rejected.push((s.name.clone(), format!("{value} is outside {}", s.range))),
            Err(why) => {
                missing.insert(s.name.clone(), why);
            }
        }
    }

    // Each operator whose cardinality the known values determine, relative
    // to its inputs', joins the constraints, if consistent with them.
    let (search, parsed) = Search::new(&analysis.constraints, &analysis.root);
    if parsed != analysis.assertions {
        return Err(Error::Internal("constraints did not parse back".into()));
    }
    let symbols: HashMap<&str, &str> = analysis.tables.iter().map(|(t, s)| (t.as_str(), s.as_str())).collect();
    let traced = analysis.trace.is_some();
    // Where the fact printed as `text` was read, looked up only when traced.
    let origins = |text: &str| -> Vec<String> {
        if !traced {
            return vec![];
        }
        facts.find(text).map(|f| FactRef::of(f).origins).unwrap_or_default()
    };
    let mut extra: Vec<FactClaim> = vec![];
    let mut unchecked = vec![];
    for (var, local) in &report.local {
        let mut sels = vec![];
        local.leaves(&mut |c| {
            if let Card::Sel(s) = c {
                sels.push(s.clone());
            }
        });
        if sels.is_empty() {
            continue;
        }
        let value = |c: &Card| match c {
            Card::Sel(s) => matched.iter().find(|m| m.name == *s).map(|m| ratio_card(m.value)),
            _ => None,
        };
        let relation = local.substitute(&value);
        if !relation.is_known() {
            continue;
        }
        let Some(rhs) = real(&relation, &symbols) else { continue };
        let claim = Int::new_const(var.as_str()).to_real().eq(&rhs);
        match search.assume(&claim) {
            Some(true) => {
                let from = sels
                    .iter()
                    .filter_map(|s| matched.iter().find(|m| m.name == *s))
                    .flat_map(|m| &m.facts)
                    .map(|f| FactRef { text: f.clone(), origins: origins(f) })
                    .collect();
                extra.push(fact_claim(claim, lookup.node(var), "selectivity", from, format!("= {relation}")));
            }
            Some(false) => {
                for s in &sels {
                    if let Some(i) = matched.iter().position(|m| m.name == *s) {
                        let m = matched.remove(i);
                        rejected.push((m.name, format!("{} contradicts the constraints on {var}", m.value)));
                    }
                }
            }
            None => unchecked.extend(sels),
        }
    }

    // Pinned: every row count a fact gives, and every upper bound on one,
    // where consistent.
    let mut pinned = vec![];
    let mut capped = vec![];
    let mut pinned_ndv = vec![];
    let mut ranges = vec![];
    if mode == FactMode::Pinned {
        for (node, var, n, fact) in lookup.sizes() {
            let claim = Int::new_const(var.as_str()).eq(Int::from_u64(n));
            match search.assume(&claim) {
                Some(true) => {
                    extra.push(fact_claim(claim, Some(node), "pinned rows", vec![fact], format!("= {n}")));
                    pinned.push((var, n));
                }
                Some(false) => rejected.push((var, format!("{n} rows contradicts the constraints"))),
                None => unchecked.push(format!("{var} = {n}")),
            }
        }
        // Each column's distinct values: the constraints carry them up
        // through filters and joins to the GROUP BYs and DISTINCTs above.
        for (node, var, n, exact, fact) in lookup.ndvs() {
            let (v, k) = (Int::new_const(var.as_str()), Int::from_u64(n));
            let (claim, source, op) = if exact { (v.eq(k), "pinned ndv", "=") } else { (v.le(k), "ndv cap", "<=") };
            match search.assume(&claim) {
                Some(true) => {
                    extra.push(fact_claim(claim, Some(node), source, vec![fact], format!("{op} {n}")));
                    pinned_ndv.push((var, n));
                }
                Some(false) => rejected.push((var, format!("{n} distinct values contradicts the constraints"))),
                None => unchecked.push(format!("{var} {op} {n}")),
            }
        }
        // Each column's least and greatest values, which bound its distinct
        // values and what it joins with.
        for (node, var, n, floor, fact) in lookup.ranges() {
            let (v, k) = (Int::new_const(var.as_str()), Int::from_u64(n));
            let (claim, source, op) = if floor { (v.ge(k), "range floor", ">=") } else { (v.le(k), "range cap", "<=") };
            match search.assume(&claim) {
                Some(true) => {
                    extra.push(fact_claim(claim, Some(node), source, vec![fact], format!("{op} {n}")));
                    ranges.push((var, n));
                }
                Some(false) => rejected.push((var, format!("{op} {n} contradicts the constraints"))),
                None => unchecked.push(format!("{var} {op} {n}")),
            }
        }
        for (node, var, n, fact) in lookup.caps() {
            if pinned.iter().any(|(p, _)| *p == var) {
                continue;
            }
            let claim = Int::new_const(var.as_str()).le(Int::from_u64(n));
            match search.assume(&claim) {
                Some(true) => {
                    extra.push(fact_claim(claim, Some(node), "row cap", vec![fact], format!("<= {n}")));
                    capped.push((var, n));
                }
                Some(false) => rejected.push((var, format!("at most {n} rows contradicts the constraints"))),
                None => unchecked.push(format!("{var} <= {n}")),
            }
        }
    }

    // Every row count of narrower rows than an operator's: a lower bound.
    let mut floors = vec![];
    for (node, var, n, fact) in lookup.floors() {
        let claim = Int::new_const(var.as_str()).ge(Int::from_u64(n));
        match search.assume(&claim) {
            Some(true) => {
                extra.push(fact_claim(claim, Some(node), "floor", vec![fact], format!(">= {n}")));
                floors.push((var, n));
            }
            Some(false) => {
                rejected.push((var, format!("at least {n} rows from {} contradicts the constraints", fact.text)))
            }
            None => unchecked.push(format!("{var} >= {n}")),
        }
    }

    // The formula, with the values substituted.
    let tables: HashMap<String, u64> = match mode {
        FactMode::Ratios => HashMap::new(),
        FactMode::Pinned => {
            let mut known = HashMap::new();
            for (t, _) in &analysis.tables {
                if let Some(n) = lookup.card(&Context::table(t)).and_then(|r| r.as_int()) {
                    known.insert(t.clone(), n);
                }
            }
            known
        }
    };
    let output = report.output.substitute(&|c| match c {
        Card::Sel(s) => matched.iter().find(|m| m.name == *s).map(|m| ratio_card(m.value)),
        Card::Table(t) => tables.get(t).map(|n| Card::Const(*n)),
        Card::Operator(v) => pinned.iter().find(|(p, _)| p == v).map(|(_, n)| Card::Const(*n)),
        _ => None,
    });
    let mut unmatched = vec![];
    output.leaves(&mut |c| {
        if let Card::Sel(s) = c {
            let why = missing.get(s).cloned().unwrap_or_else(|| "rejected".into());
            unmatched.push((s.clone(), why));
        }
    });

    let mut constraints = analysis.constraints.clone();
    for c in &extra {
        constraints.push_str(&format!("(assert {})\n", c.claim));
    }
    let assertions = analysis.assertions + extra.len();
    let trace = analysis.trace.as_ref().map(|t| t.with_facts(&extra));
    if let Some(t) = &trace {
        debug_assert_eq!(t.constraints.len(), assertions, "every fact claim is traced");
    }
    let origins = if traced {
        matched.iter().flat_map(|m| &m.facts).map(|f| (f.clone(), origins(f))).collect()
    } else {
        HashMap::new()
    };
    Ok(Informed {
        mode,
        output,
        matched,
        unmatched,
        rejected,
        pinned,
        capped,
        pinned_ndv,
        ranges,
        floors,
        unchecked,
        trace,
        origins,
        report: report.clone(),
        constraints,
        assertions,
        root: analysis.root.clone(),
        scans: analysis.scans.iter().map(|(s, _)| s.clone()).collect(),
        tables: analysis.tables.clone(),
    })
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

fn ratio_card(r: Ratio) -> Card {
    match r.as_int() {
        Some(n) => Card::Const(n),
        None => Card::Ratio(r.num(), r.den()),
    }
}

/// `card` as a real-valued term, with tables named by their symbols. `None`
/// if it has an unknown selectivity.
fn real(card: &Card, symbols: &HashMap<&str, &str>) -> Option<Real> {
    let rational = |n: u64, d: u64| Some(Real::from_rational(i64::try_from(n).ok()?, i64::try_from(d).ok()?));
    let all = |ps: &[Card]| ps.iter().map(|p| real(p, symbols)).collect::<Option<Vec<Real>>>();
    Some(match card {
        Card::Const(n) => rational(*n, 1)?,
        Card::Ratio(n, d) => rational(*n, *d)?,
        Card::Table(t) => Int::new_const(*symbols.get(t.as_str())?).to_real(),
        Card::Operator(v) => Int::new_const(v.as_str()).to_real(),
        Card::Sel(_) => return None,
        Card::Mul(ps) => Real::mul(&all(ps)?),
        Card::Add(ps) => Real::add(&all(ps)?),
        Card::Not(c) => Real::sub(&[rational(1, 1)?, real(c, symbols)?]),
        Card::Min(a, b) => {
            let (a, b) = (real(a, symbols)?, real(b, symbols)?);
            a.le(&b).ite(&a, &b)
        }
        Card::Max(a, b) => {
            let (a, b) = (real(a, symbols)?, real(b, symbols)?);
            a.ge(&b).ite(&a, &b)
        }
        Card::Sub(c, k) => Real::sub(&[real(c, symbols)?, rational(*k, 1)?]),
    })
}

/// Facts about the operators of one plan.
struct Lookup<'a> {
    nodes: &'a [Node],
    logical: &'a Logical,
    facts: &'a FactSet,
    /// Each node, by its variable; a raw scan's variable gives its scan.
    by_var: HashMap<&'a str, (usize, bool)>,
    conflicted: BTreeSet<&'a FactKind>,
    /// Each fact kind looked up so far, canonically renamed: canonical forms
    /// are costly with several instances of a table, and the same contexts
    /// come up for many operators and selectivities.
    canonical: RefCell<HashMap<FactKind, FactKind>>,
}

impl<'a> Lookup<'a> {
    fn new(nodes: &'a [Node], logical: &'a Logical, facts: &'a FactSet) -> Self {
        let mut by_var = HashMap::new();
        for (i, n) in nodes.iter().enumerate() {
            by_var.insert(n.var.as_str(), (i, false));
            if let Some((raw, _, _)) = &n.raw_scan {
                by_var.insert(raw.as_str(), (i, true));
            }
        }
        let conflicted = facts.conflicts.iter().map(|c| &c.kind).collect();
        Lookup { nodes, logical, facts, by_var, conflicted, canonical: RefCell::default() }
    }

    /// `kind`, canonically renamed, once per kind.
    fn canonical(&self, kind: FactKind) -> FactKind {
        if let Some(c) = self.canonical.borrow().get(&kind) {
            return c.clone();
        }
        let c = kind.canonical();
        self.canonical.borrow_mut().insert(kind, c.clone());
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
        if self.conflicted.contains(kind) {
            return None;
        }
        self.facts.get(kind)
    }

    /// The value of fact `kind`, and its text, unless two plans disagree on it.
    fn fact(&self, kind: FactKind) -> Option<(Ratio, String)> {
        self.fact_canonical(&self.canonical(kind))
    }

    /// [`Self::fact`], of a `kind` already canonical.
    fn fact_canonical(&self, kind: &FactKind) -> Option<(Ratio, String)> {
        self.get_canonical(kind).map(|f| (f.value, f.kind.to_string()))
    }

    /// The node whose variable is `var`.
    fn node(&self, var: &str) -> Option<usize> {
        self.by_var.get(var).map(|&(i, _)| i)
    }

    fn card(&self, ctx: &Context) -> Option<Ratio> {
        self.fact(FactKind::Cardinality(ctx.clone())).map(|(v, _)| v)
    }

    /// The rows of the operator with variable `var`.
    fn context(&self, var: &str) -> std::result::Result<Context, String> {
        let &(i, raw) = self.by_var.get(var).ok_or_else(|| format!("no operator {var}"))?;
        if raw {
            let instance = self.logical.instances[i].as_ref().ok_or("not a base table")?;
            return Ok(Context::table(instance));
        }
        self.logical.contexts[i].clone().map_err(|t| t.to_string())
    }

    /// The fact that gives `s`: the share, distinct count or match it is.
    fn kind(&self, s: &Selectivity) -> std::result::Result<FactKind, String> {
        let &(i, _) = self.by_var.get(s.operator.as_str()).ok_or("no operator")?;
        let args = || self.logical.args[i].clone().ok_or_else(|| "unresolved terms".to_string());
        let input = |k: usize| self.context(&self.nodes[self.nodes[i].inputs[k]].var);
        Ok(match &s.kind {
            Kind::Filter(_) => {
                let over = self.context(&s.over[0])?;
                FactKind::Selectivity { pred: without(args()?, &over), over }
            }
            Kind::Join { .. } => {
                let (l, r) = (self.context(&s.over[0])?, self.context(&s.over[1])?);
                let over = l.cross(&r).ok_or("a self-join")?;
                FactKind::Selectivity { pred: without(args()?, &over), over }
            }
            Kind::Match { left, .. } => {
                let (l, r) = (input(0)?, input(1)?);
                let (kept, other) = if *left { (l, r) } else { (r, l) };
                FactKind::Match { on: args()?, kept, other }
            }
            Kind::NotIn { .. } => FactKind::Cardinality(self.logical.contexts[i].clone().map_err(|t| t.to_string())?),
            Kind::Distinct(_) => FactKind::Distinct { keys: args()?, over: self.context(&s.over[0])? },
            Kind::Limit => return Err("a limit".into()),
        })
    }

    /// The value of `s`, and the facts it is read from, or why there is none.
    fn selectivity(&self, s: &Selectivity) -> std::result::Result<(Ratio, Vec<String>), String> {
        let &(i, _) = self.by_var.get(s.operator.as_str()).ok_or("no operator")?;
        let args = || self.logical.args[i].clone().ok_or_else(|| "unresolved terms".to_string());
        let input = |k: usize| self.context(&self.nodes[self.nodes[i].inputs[k]].var);
        // `num / den`, where each is a size from a fact.
        let sizes = |num: &Context, den: &[&Context]| -> Option<(Ratio, Vec<String>)> {
            let mut value = self.card(num)?;
            let mut from = vec![format!("|{}|", self.canonical_ctx(num))];
            for d in den {
                value = value.over(self.card(d)?)?;
                from.push(format!("|{}|", self.canonical_ctx(d)));
            }
            Some((value, from))
        };
        let none = |what: &str| format!("no fact for {what}");
        match &s.kind {
            Kind::Filter(_) => {
                let over = self.context(&s.over[0])?;
                let pred = without(args()?, &over);
                if pred.is_empty() {
                    return Ok((Ratio::int(1), vec!["implied by its input".into()]));
                }
                let kind = FactKind::Selectivity { pred: pred.clone(), over: over.clone() };
                let kind = self.canonical(kind);
                let text = kind.to_string();
                self.fact_canonical(&kind)
                    .map(|(v, f)| (v, vec![f]))
                    .or_else(|| sizes(&over.filter(&pred), &[&over]))
                    .ok_or_else(|| none(&text))
            }
            Kind::Join { .. } => {
                let (l, r) = (self.context(&s.over[0])?, self.context(&s.over[1])?);
                let over = l.cross(&r).ok_or("a self-join")?;
                let pred = without(args()?, &over);
                if pred.is_empty() {
                    return Ok((Ratio::int(1), vec!["implied by its inputs".into()]));
                }
                let kind = FactKind::Selectivity { pred: pred.clone(), over: over.clone() };
                let kind = self.canonical(kind);
                let text = kind.to_string();
                self.fact_canonical(&kind)
                    .map(|(v, f)| (v, vec![f]))
                    .or_else(|| sizes(&over.filter(&pred), &[&l, &r]))
                    .ok_or_else(|| none(&text))
            }
            Kind::Match { left, .. } => {
                let (l, r) = (input(0)?, input(1)?);
                let on = args()?;
                let (kept, other) = if *left { (&l, &r) } else { (&r, &l) };
                let kind = FactKind::Match { on: on.clone(), kept: kept.clone(), other: other.clone() };
                let kind = self.canonical(kind);
                let text = kind.to_string();
                let derived = |semi: bool| {
                    let kind = match (left, semi) {
                        (true, true) => JoinType::LeftSemi,
                        (true, false) => JoinType::LeftAnti,
                        (false, true) => JoinType::RightSemi,
                        (false, false) => JoinType::RightAnti,
                    };
                    Context::join(kind, on.clone(), l.clone(), r.clone())
                };
                self.fact_canonical(&kind)
                    .map(|(v, f)| (v, vec![f]))
                    .or_else(|| sizes(&derived(true), &[kept]))
                    .or_else(|| {
                        let (anti, from) = sizes(&derived(false), &[kept])?;
                        Some((Ratio::int(1).minus(anti)?, from))
                    })
                    .ok_or_else(|| none(&text))
            }
            Kind::NotIn { .. } => {
                let out = self.logical.contexts[i].clone().map_err(|t| t.to_string())?;
                let l = input(0)?;
                sizes(&out, &[&l]).ok_or_else(|| none(&format!("|{}|", self.canonical_ctx(&out))))
            }
            Kind::Distinct(_) => {
                let over = self.context(&s.over[0])?;
                let keys = args()?;
                let unique = FactKind::Unique { keys: keys.clone(), over: over.clone() };
                if let Some((_, f)) = self.fact(unique) {
                    return Ok((Ratio::int(1), vec![f]));
                }
                let kind = FactKind::Distinct { keys, over: over.clone() };
                let kind = self.canonical(kind);
                let text = kind.to_string();
                let (ndv, f) = self.fact_canonical(&kind).ok_or_else(|| none(&text))?;
                let over_text = format!("|{}|", self.canonical_ctx(&over));
                let n = self.card(&over).ok_or_else(|| none(&over_text))?;
                let value = ndv.over(n).ok_or("no rows")?;
                Ok((value, vec![f, over_text]))
            }
            Kind::Limit => Err("a limit".into()),
        }
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
                    && !self.conflicted.contains(&f.kind)
                    && c.tables().is_subset(&tables)
                    && let Some(n) = f.value.as_int()
                    && renamed(&ctx, c, fewer)
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
                    && !self.conflicted.contains(&f.kind)
                    && over.tables().is_subset(&tables)
                    && let Some(n) = f.value.as_int()
                    && renamed(&ctx, &wider, groups_among)
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
        let bounded = tables_of(self.facts.bounds().filter_map(|f| match &f.kind {
            FactKind::Distinct { keys, over } if keys.len() == 1 => Some(over),
            _ => None,
        }));
        for (i, node) in self.nodes.iter().enumerate() {
            let Ok(ctx) = &self.logical.contexts[i] else { continue };
            // A base table's are read below.
            if !bounded.contains(&bases(ctx)) || (self.logical.instances[i].is_some() && node.raw_scan.is_none()) {
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
                    && !self.conflicted.contains(&kind)
                    && let Some(n) = b.value.as_int()
                {
                    out.push((i, var.clone(), n, false, FactRef::of(b)));
                }
            }
        }
        for (i, node) in self.nodes.iter().enumerate() {
            let Some(instance) = &self.logical.instances[i] else { continue };
            let vars = node.raw_scan.as_ref().map_or(&node.ndv_vars, |(_, raw, _)| raw);
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
        let ranged = tables_of(self.facts.floors().chain(self.facts.bounds()).filter_map(|f| match &f.kind {
            FactKind::Min { over, .. } | FactKind::Max { over, .. } => Some(over),
            _ => None,
        }));
        let mut out = vec![];
        for (i, node) in self.nodes.iter().enumerate() {
            let mut rows = vec![];
            if let (Some(_), Some(instance)) = (&node.raw_scan, &self.logical.instances[i]) {
                rows.push((Context::table(instance), &node.raw_min_vars, &node.raw_max_vars));
            }
            if let Ok(ctx) = &self.logical.contexts[i] {
                rows.push((ctx.clone(), &node.min_vars, &node.max_vars));
            }
            for (ctx, mins, maxs) in rows {
                if !ranged.contains(&bases(&ctx)) {
                    continue;
                }
                for (j, (lo, hi)) in mins.iter().zip(maxs).enumerate() {
                    let Some(Some(e @ Expr::Column(_))) = self.logical.lineage[i].get(j) else { continue };
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
                            && !self.conflicted.contains(&kind)
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
            .filter(|(f, _)| !self.conflicted.contains(&f.kind))
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
                if tables.is_subset(&c.tables()) && if **c == ctx { *floor } else { renamed(c, &ctx, fewer) } {
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
            if let (Some((raw, _, _)), Some(instance)) = (&node.raw_scan, &self.logical.instances[i])
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

/// The tables `ctx` draws on, by base table, each as often as it does: a
/// context can only be named canonically as one with the same.
fn bases(ctx: &Context) -> Vec<String> {
    let mut out: Vec<String> = ctx.tables().iter().map(|t| crate::observed::base_table(t).unwrap_or(t).to_string()).collect();
    out.sort();
    out
}

/// [`bases`] of each of `contexts`.
fn tables_of<'c>(contexts: impl Iterator<Item = &'c Context>) -> BTreeSet<Vec<String>> {
    contexts.map(bases).collect()
}

/// `terms` without those the rows of `over` already satisfy.
fn without(mut terms: BTreeSet<Term>, over: &Context) -> BTreeSet<Term> {
    if let Context::Spj { preds, .. } = over {
        terms.retain(|t| !preds.contains(t));
    }
    terms
}
