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

use std::collections::{BTreeSet, HashMap};
use std::fmt;

use datafusion::common::JoinType;
use z3::ast::{Int, Real};

use crate::analyzer::Node;
use crate::bounds::{Bounds, Search};
use crate::facts::logical::Logical;
use crate::facts::{Context, FactKind, FactSet, Ratio, Term};
use crate::selectivity::{Card, Interval, Kind, Selectivity, SelectivityReport};
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
    /// Selectivities whose relation to the constraints could not be checked
    /// in time, and so is not among them.
    pub unchecked: Vec<String>,
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

    /// Bounds proven with the facts among the constraints, as
    /// [`Analysis::bounds`].
    pub fn bounds(&self) -> Result<Bounds> {
        let search = self.search()?;
        Ok(crate::prove_bounds(&search, &self.scans, &self.tables))
    }

    /// The proven `lo <= X <= hi`, with no `hi` if none is proven: a constant
    /// range, cheaper than [`Informed::bounds`].
    pub fn range(&self) -> Result<(u64, Option<u64>)> {
        let search = self.search()?;
        Ok((search.lower(), search.constant()))
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
    report.required.iter().map(|s| (s.name.clone(), lookup.kind(s).map(|k| k.canonical()))).collect()
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
    let mut extra = vec![];
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
            Some(true) => extra.push(claim),
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
    if mode == FactMode::Pinned {
        for (var, n) in lookup.sizes() {
            let claim = Int::new_const(var.as_str()).eq(Int::from_u64(n));
            match search.assume(&claim) {
                Some(true) => {
                    extra.push(claim);
                    pinned.push((var, n));
                }
                Some(false) => rejected.push((var, format!("{n} rows contradicts the constraints"))),
                None => {}
            }
        }
        for (var, n) in lookup.caps() {
            if pinned.iter().any(|(p, _)| *p == var) {
                continue;
            }
            let claim = Int::new_const(var.as_str()).le(Int::from_u64(n));
            match search.assume(&claim) {
                Some(true) => {
                    extra.push(claim);
                    capped.push((var, n));
                }
                Some(false) => rejected.push((var, format!("at most {n} rows contradicts the constraints"))),
                None => {}
            }
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
    for claim in &extra {
        constraints.push_str(&format!("(assert {claim})\n"));
    }
    Ok(Informed {
        mode,
        output,
        matched,
        unmatched,
        rejected,
        pinned,
        capped,
        unchecked,
        report: report.clone(),
        constraints,
        assertions: analysis.assertions + extra.len(),
        root: analysis.root.clone(),
        scans: analysis.scans.iter().map(|(s, _)| s.clone()).collect(),
        tables: analysis.tables.clone(),
    })
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
        Lookup { nodes, logical, facts, by_var, conflicted }
    }

    /// The value of fact `kind`, unless two plans disagree on it.
    fn fact(&self, kind: FactKind) -> Option<(Ratio, String)> {
        let kind = kind.canonical();
        if self.conflicted.contains(&kind) {
            return None;
        }
        self.facts.get(&kind).map(|f| (f.value, f.kind.to_string()))
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
            let mut from = vec![format!("|{}|", num.canonical())];
            for d in den {
                value = value.over(self.card(d)?)?;
                from.push(format!("|{}|", d.canonical()));
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
                let text = kind.canonical().to_string();
                self.fact(kind)
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
                let text = kind.canonical().to_string();
                self.fact(kind)
                    .map(|(v, f)| (v, vec![f]))
                    .or_else(|| sizes(&over.filter(&pred), &[&l, &r]))
                    .ok_or_else(|| none(&text))
            }
            Kind::Match { left, .. } => {
                let (l, r) = (input(0)?, input(1)?);
                let on = args()?;
                let (kept, other) = if *left { (&l, &r) } else { (&r, &l) };
                let kind = FactKind::Match { on: on.clone(), kept: kept.clone(), other: other.clone() };
                let text = kind.canonical().to_string();
                let derived = |semi: bool| {
                    let kind = match (left, semi) {
                        (true, true) => JoinType::LeftSemi,
                        (true, false) => JoinType::LeftAnti,
                        (false, true) => JoinType::RightSemi,
                        (false, false) => JoinType::RightAnti,
                    };
                    Context::join(kind, on.clone(), l.clone(), r.clone())
                };
                self.fact(kind)
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
                sizes(&out, &[&l]).ok_or_else(|| none(&format!("|{}|", out.canonical())))
            }
            Kind::Distinct(_) => {
                let over = self.context(&s.over[0])?;
                let keys = args()?;
                let unique = FactKind::Unique { keys: keys.clone(), over: over.clone() };
                if let Some((_, f)) = self.fact(unique) {
                    return Ok((Ratio::int(1), vec![f]));
                }
                let kind = FactKind::Distinct { keys, over: over.clone() };
                let text = kind.canonical().to_string();
                let (ndv, f) = self.fact(kind).ok_or_else(|| none(&text))?;
                let n = self.card(&over).ok_or_else(|| none(&format!("|{}|", over.canonical())))?;
                let value = ndv.over(n).ok_or("no rows")?;
                Ok((value, vec![f, format!("|{}|", over.canonical())]))
            }
            Kind::Limit => Err("a limit".into()),
        }
    }

    /// Every operator's upper bound on its rows that a bound gives, by
    /// variable.
    fn caps(&self) -> Vec<(String, u64)> {
        let mut out = vec![];
        for (i, node) in self.nodes.iter().enumerate() {
            let Ok(ctx) = &self.logical.contexts[i] else { continue };
            let kind = match ctx {
                Context::Derived { op, args, inputs } if op == "group" => {
                    FactKind::Distinct { keys: args.iter().cloned().collect(), over: inputs[0].clone() }
                }
                ctx => FactKind::Cardinality(ctx.clone()),
            };
            if let Some(n) = self.facts.bound(&kind.canonical()).and_then(|b| b.value.as_int()) {
                out.push((node.var.clone(), n));
            }
        }
        out
    }

    /// Every operator's row count that a fact gives, by variable.
    fn sizes(&self) -> Vec<(String, u64)> {
        let mut out = vec![];
        for (i, node) in self.nodes.iter().enumerate() {
            if let (Some((raw, _, _)), Some(instance)) = (&node.raw_scan, &self.logical.instances[i])
                && let Some(n) = self.card(&Context::table(instance)).and_then(|r| r.as_int())
            {
                out.push((raw.clone(), n));
            }
            let Ok(ctx) = &self.logical.contexts[i] else { continue };
            let n = match ctx {
                // A grouping's rows are its keys' distinct values.
                Context::Derived { op, args, inputs } if op == "group" => self
                    .fact(FactKind::Distinct { keys: args.iter().cloned().collect(), over: inputs[0].clone() })
                    .map(|(v, _)| v),
                ctx => self.card(ctx),
            };
            if let Some(n) = n.and_then(|r| r.as_int()) {
                out.push((node.var.clone(), n));
            }
        }
        out
    }
}

/// `terms` without those the rows of `over` already satisfy.
fn without(mut terms: BTreeSet<Term>, over: &Context) -> BTreeSet<Term> {
    if let Context::Spj { preds, .. } = over {
        terms.retain(|t| !preds.contains(t));
    }
    terms
}
