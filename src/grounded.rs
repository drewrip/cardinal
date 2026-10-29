//! An analysis grounded in observations of the data.
//!
//! Observations are claims about the data (a row count, a distinct count,
//! a least value), each held by a tracker so that Z3 can name the ones a
//! contradiction needs. Axioms hold of any data and are asserted as they
//! are. Everything is checked twice: the claims and axioms alone, then with
//! the analysis's constraints. Each time it is unsatisfiable, the claims of
//! a minimal core are dropped as rejected and the check runs again. What
//! survives joins the constraints, so the bounds come from the same search
//! as [`Analysis::bounds`], over a solver that also knows the data.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;
use std::panic::Location;
use std::time::{Duration, Instant};

use z3::ast::{Ast, Bool, Dynamic};
use z3::{AstKind, DeclKind, SatResult, Solver};

use crate::analyzer::new_solver;
use crate::bounds::{Bounds, Search, SearchStats};
use crate::facts::axioms::Axiom;
use crate::trace::{self, FactClaim, FactInfo, FactRef, Proof, Trace};
use crate::{Analysis, Error, Result};

/// A claim about the data, and where it is from.
pub(crate) struct Tracked {
    pub claim: Bool,
    /// The query's plan node whose variable it holds, if any.
    pub node: Option<usize>,
    pub info: FactInfo,
    pub at: &'static Location<'static>,
}

impl Tracked {
    /// `claim`, from `facts`, read as `value` of a kind of claim `source`,
    /// made at the caller's line.
    #[track_caller]
    pub fn new(claim: Bool, node: Option<usize>, source: &str, facts: Vec<FactRef>, value: String) -> Tracked {
        Tracked { claim, node, info: FactInfo { source: source.to_string(), facts, value }, at: Location::caller() }
    }

    /// The claim as text, for reports.
    pub fn text(&self) -> String {
        let facts: Vec<&str> = self.info.facts.iter().map(|f| f.text.as_str()).collect();
        format!("{} {}", facts.join(", "), self.info.value)
    }
}

/// How large a solver's problem is.
#[doc(hidden)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SolverSize {
    pub assertions: usize,
    /// Uninterpreted constants.
    pub vars: usize,
    /// Products of two or more terms that are not numerals.
    pub nonlinear: usize,
}

/// How long the steps before the bounds search took.
#[doc(hidden)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Timings {
    /// Reading the observations into claims and axioms.
    pub setup: Duration,
    /// Checking them, and dropping what contradicts.
    pub check: Duration,
}

/// An analysis with observations of the data among its constraints.
#[derive(Debug, Clone)]
pub struct Grounded {
    /// The claims kept, as text.
    pub asserted: Vec<String>,
    /// Claims dropped, and what they contradicted. On data the
    /// observations were read from, any is a claim about the wrong rows.
    pub rejected: Vec<(String, String)>,
    /// Claims whose consistency was undecided, left out.
    pub unchecked: Vec<String>,
    /// Axioms asserted, by rule.
    pub axioms: BTreeMap<String, usize>,
    /// The problem searched.
    #[doc(hidden)]
    pub size: SolverSize,
    #[doc(hidden)]
    pub timings: Timings,
    /// The analysis's trace with a constraint for each claim and axiom, if
    /// the analysis was traced.
    pub trace: Option<Trace>,
    constraints: String,
    assertions: usize,
    root: String,
    scans: Vec<String>,
    tables: Vec<(String, String)>,
}

impl Grounded {
    /// Bounds proven with the observations among the constraints, as
    /// [`Analysis::bounds`].
    pub fn bounds(&self) -> Result<Bounds> {
        Ok(self.bounds_with_stats()?.0)
    }

    /// The proven `lo <= X <= hi`, with no `hi` if none is proven.
    pub fn range(&self) -> Result<(u64, Option<u64>)> {
        Ok(self.range_with_stats()?.0)
    }

    #[doc(hidden)]
    pub fn bounds_with_stats(&self) -> Result<(Bounds, SearchStats)> {
        let search = self.search()?;
        let bounds = crate::prove_bounds(&search, &self.scans, &self.tables);
        Ok((bounds, search.stats()))
    }

    #[doc(hidden)]
    pub fn range_with_stats(&self) -> Result<((u64, Option<u64>), SearchStats)> {
        let search = self.search()?;
        let range = (search.lower(), search.constant());
        Ok((range, search.stats()))
    }

    /// Proves the claims of [`Analysis::explain`] for `bounds`, each with a
    /// minimal set of constraints, the analyzer's, axioms or observations,
    /// that proves it. Needs [`crate::Options::trace`].
    pub fn explain(&self, bounds: Option<&Bounds>) -> Result<Vec<Proof>> {
        let trace = self.trace.as_ref().ok_or_else(|| Error::Internal("explain needs Options::trace".into()))?;
        trace.explain(&trace::claims(&self.root, &self.scans, &self.tables, bounds))
    }

    /// The constraints the bounds are searched over, in SMT-LIB.
    pub fn constraints(&self) -> &str {
        &self.constraints
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

impl fmt::Display for Grounded {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let axioms: usize = self.axioms.values().sum();
        write!(f, "{} claims, {axioms} axioms", self.asserted.len())?;
        for (c, why) in &self.rejected {
            write!(f, "\n  rejected {c}: {why}")?;
        }
        for c in &self.unchecked {
            write!(f, "\n  unchecked {c}")?;
        }
        Ok(())
    }
}

/// What an approach read off its observations.
pub(crate) struct Observations {
    pub axioms: Vec<Axiom>,
    pub tracked: Vec<Tracked>,
    pub setup: Duration,
}

/// `analysis` with `obs` checked and put among its constraints.
pub(crate) fn ground(analysis: &Analysis, obs: Observations) -> Result<Grounded> {
    let start = Instant::now();
    let solver = new_solver();
    for a in &obs.axioms {
        solver.assert(&a.claim);
    }
    let trackers: Vec<Bool> = (0..obs.tracked.len()).map(|i| Bool::new_const(format!("cardinal_claim_{i}"))).collect();
    for (t, c) in trackers.iter().zip(&obs.tracked) {
        solver.assert(t.implies(&c.claim));
    }
    let index: HashMap<String, usize> = trackers.iter().enumerate().map(|(i, t)| (t.to_string(), i)).collect();
    let mut active: Vec<usize> = (0..trackers.len()).collect();
    let mut rejected = vec![];
    let mut unchecked = vec![];
    // The claims and axioms alone, then with the query's constraints.
    for (phase, against) in [(1, "other claims"), (2, "the constraints")] {
        if phase == 2 {
            solver.from_string(analysis.constraints.as_str());
        }
        prune(&solver, &trackers, &index, &obs.tracked, &mut active, &mut rejected, &mut unchecked, against)?;
    }

    // The constraints to search: the query's, the axioms and every claim
    // kept, as plain assertions.
    let kept: Vec<&Tracked> = active.iter().map(|&i| &obs.tracked[i]).collect();
    let all = Solver::new();
    all.from_string(analysis.constraints.as_str());
    for a in &obs.axioms {
        all.assert(&a.claim);
    }
    for c in &kept {
        all.assert(&c.claim);
    }
    let assertions = all.get_assertions();
    let constraints = all.to_string();
    let check = start.elapsed();

    let mut axioms: BTreeMap<String, usize> = BTreeMap::new();
    for a in &obs.axioms {
        *axioms.entry(a.rule.to_string()).or_default() += 1;
    }
    let trace = analysis.trace.as_ref().map(|t| {
        let mut claims: Vec<FactClaim> = vec![];
        let here = Location::caller();
        for a in &obs.axioms {
            claims.push(FactClaim { claim: a.claim.clone(), node: None, info: info("axiom", a.rule, ""), at: here });
        }
        for c in &kept {
            claims.push(FactClaim { claim: c.claim.clone(), node: c.node, info: c.info.clone(), at: c.at });
        }
        let mut t = t.clone();
        t.declare(&constraints_with_all(analysis, &obs, &kept));
        t.with_facts(&claims)
    });
    Ok(Grounded {
        asserted: kept.iter().map(|c| c.text()).collect(),
        rejected,
        unchecked,
        axioms,
        size: size(&assertions),
        timings: Timings { setup: obs.setup, check },
        trace,
        constraints,
        assertions: assertions.len(),
        root: analysis.root.clone(),
        scans: analysis.scans.iter().map(|(s, _)| s.clone()).collect(),
        tables: analysis.tables.clone(),
    })
}

/// Checks the `active` claims until they are consistent with what
/// `solver` holds, dropping each minimal core's into `rejected`. If a check
/// is undecided, each claim is checked on its own instead, and the
/// undecided ones are left out.
#[allow(clippy::too_many_arguments)]
fn prune(
    solver: &Solver,
    trackers: &[Bool],
    index: &HashMap<String, usize>,
    tracked: &[Tracked],
    active: &mut Vec<usize>,
    rejected: &mut Vec<(String, String)>,
    unchecked: &mut Vec<String>,
    against: &str,
) -> Result<()> {
    loop {
        let assumptions: Vec<Bool> = active.iter().map(|&i| trackers[i].clone()).collect();
        match solver.check_assumptions(&assumptions) {
            SatResult::Sat => return Ok(()),
            SatResult::Unsat => {
                let core = trace::shrink(solver, solver.get_unsat_core());
                let ids: Vec<usize> = core.iter().filter_map(|t| index.get(&t.to_string()).copied()).collect();
                if ids.is_empty() {
                    return Err(Error::Internal(format!("the axioms contradict {against} without any claim")));
                }
                let texts: Vec<String> = ids.iter().map(|&i| tracked[i].text()).collect();
                for &i in &ids {
                    let others: Vec<&str> = texts.iter().filter(|t| **t != tracked[i].text()).map(String::as_str).collect();
                    let why = match others.is_empty() {
                        true => format!("contradicts {against}"),
                        false => format!("contradicts {against} with {}", others.join("; ")),
                    };
                    rejected.push((tracked[i].text(), why));
                }
                active.retain(|i| !ids.contains(i));
            }
            SatResult::Unknown => {
                let mut kept = vec![];
                for &i in active.iter() {
                    let mut assumptions: Vec<Bool> = kept.iter().map(|&k: &usize| trackers[k].clone()).collect();
                    assumptions.push(trackers[i].clone());
                    match solver.check_assumptions(&assumptions) {
                        SatResult::Sat => kept.push(i),
                        SatResult::Unsat => rejected.push((tracked[i].text(), format!("contradicts {against}"))),
                        SatResult::Unknown => unchecked.push(tracked[i].text()),
                    }
                }
                *active = kept;
                return Ok(());
            }
        }
    }
}

fn info(source: &str, text: &str, value: &str) -> FactInfo {
    FactInfo { source: source.to_string(), facts: vec![FactRef { text: text.to_string(), origins: vec![] }], value: value.to_string() }
}

/// The declarations of every variable the claims and axioms use, in
/// SMT-LIB.
fn constraints_with_all(analysis: &Analysis, obs: &Observations, kept: &[&Tracked]) -> String {
    let s = Solver::new();
    s.from_string(analysis.constraints.as_str());
    for a in &obs.axioms {
        s.assert(&a.claim);
    }
    for c in kept {
        s.assert(&c.claim);
    }
    s.to_string()
}

/// The size of the problem `assertions` pose.
fn size(assertions: &[Bool]) -> SolverSize {
    let mut vars = BTreeSet::new();
    let mut nonlinear = 0;
    let mut todo: Vec<Dynamic> = assertions.iter().map(|a| Dynamic::from_ast(a)).collect();
    let mut seen = std::collections::HashSet::new();
    while let Some(e) = todo.pop() {
        if !seen.insert(e.clone()) || e.kind() != AstKind::App {
            continue;
        }
        if e.is_const() {
            if e.decl().kind() == DeclKind::Uninterpreted {
                vars.insert(e.decl().name());
            }
            continue;
        }
        let children = e.children();
        if e.decl().kind() == DeclKind::Mul && children.iter().filter(|c| c.kind() != AstKind::Numeral).count() >= 2 {
            nonlinear += 1;
        }
        todo.extend(children);
    }
    SolverSize { assertions: assertions.len(), vars: vars.len(), nonlinear }
}
