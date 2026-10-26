//! Z3 checks over a program: the consistency check (§6.6) and bound
//! extraction (§9).
//!
//! Every check runs under an instantiation budget (`smt.qi.max_instances`)
//! besides the time limit: pattern matching never saturates on a program
//! of many plans, so a claim it cannot prove would otherwise run to the
//! time limit. A solver whose check stopped short proves less afterwards,
//! so a check after one that failed starts a fresh solver; a proven check
//! leaves its solver as it was (`push`/`pop`).
//!
//! Z3's optimizer gives no candidate over quantified axioms (its interval
//! is unbounded), so bounds are searched for by checks alone: the lower
//! bound by galloping up from 1, then the upper bound, first at the lower
//! bound itself, else by bisection from the cap. The search runs on a
//! small budget, and its last step again on a large one. The lower and
//! upper searches run in threads of their own. Only proven bounds are
//! returned.

use z3::ast::Bool;
use z3::{Params, SatResult, Solver};

use super::program::Program;

/// Per-check time limit. §8 has 1 s; while the budget is very high,
/// longer, to see what the axioms can prove (`CARDINAL_UF_TIMEOUT_MS`).
pub(crate) const TIMEOUT_MS: u32 = 5_000;

fn timeout_ms() -> u32 {
    std::env::var("CARDINAL_UF_TIMEOUT_MS").ok().and_then(|t| t.parse().ok()).unwrap_or(TIMEOUT_MS)
}
/// Quantifier instances per check while searching, and to confirm.
/// For now set very high, while the instances proofs need are logged
/// (`Session::needed`), to choose a budget from.
const BUDGET: u32 = 2_000_000;
const BUDGET_CONFIRM: u32 = 2_000_000;
/// Largest bound tried; a bound needing more is no bound.
const CAP: u64 = 1 << 30;

/// Checks of claims about the root, in one thread.
struct Checker<'a> {
    text: &'a str,
    assertions: usize,
    root: &'a str,
    /// The literals of the facts in use.
    active: Vec<Bool>,
    solver: Option<Solver>,
    budget: u32,
    checks: usize,
    /// The most instances a proven check made.
    needed: u64,
}

impl<'a> Checker<'a> {
    fn new(text: &'a str, assertions: usize, root: &'a str, active: &[String], budget: u32) -> Checker<'a> {
        let active = active.iter().map(|l| Bool::new_const(l.trim_matches('|'))).collect();
        Checker { text, assertions, root, active, solver: None, budget, checks: 0, needed: 0 }
    }

    fn solver(&mut self) -> &Solver {
        if self.solver.is_none() {
            let s = Solver::new();
            let mut p = Params::new();
            p.set_u32("timeout", timeout_ms());
            p.set_bool("smt.auto_config", false);
            p.set_bool("smt.mbqi", false);
            s.set_params(&p);
            s.from_string(self.text);
            // Z3 drops what follows a declaration it rejects.
            assert_eq!(s.get_assertions().len(), self.assertions, "the program did not parse whole");
            self.solver = Some(s);
        }
        self.solver.as_ref().unwrap()
    }

    /// Whether the axioms and facts in use entail `claim`. The claim's
    /// negation is guarded by a literal of its own, assumed for this
    /// check only, so that what the check instantiates serves the next
    /// ones; each check has `budget` more instances than those before it.
    /// (Z3 cancels a check in a pushed scope under an instance limit at
    /// once.)
    fn proves(&mut self, claim: &str) -> bool {
        self.checks += 1;
        let k = self.checks;
        let root = self.root.to_string();
        let mut assumptions = self.active.clone();
        let budget = self.budget;
        let s = self.solver();
        s.from_string(format!(
            "(declare-const |claim!{k}| Bool) (assert (=> |claim!{k}| (not {})))",
            claim.replace("|root!|", &root)
        ));
        assumptions.push(Bool::new_const(format!("claim!{k}")));
        let made = instances(s);
        let mut p = Params::new();
        p.set_u32("smt.qi.max_instances", made.saturating_add(budget));
        s.set_params(&p);
        let t = std::time::Instant::now();
        let r = s.check_assumptions(&assumptions);
        let after = instances(s);
        if std::env::var("CARDINAL_UF_TIME").is_ok() {
            eprintln!(
                "uf: check {claim} {r:?} {:.2}s {} instances {:?}",
                t.elapsed().as_secs_f64(),
                after - made,
                s.get_reason_unknown()
            );
        }
        // A check cut short leaves a solver that proves less.
        let cut = r != SatResult::Unsat && s.get_reason_unknown().is_some_and(|w| w.contains("canceled") || w.contains("timeout"));
        if r == SatResult::Unsat {
            self.needed = self.needed.max((after - made) as u64);
        }
        if cut {
            self.solver = None;
        }
        r == SatResult::Unsat
    }

    fn le(&mut self, b: u64) -> bool {
        self.proves(&format!("(<= |root!| {b})"))
    }

    fn ge(&mut self, b: u64) -> bool {
        b == 0 || self.proves(&format!("(>= |root!| {b})"))
    }

    /// The budget for checks from now on.
    fn budget(&mut self, b: u32) {
        self.budget = b;
    }

    /// The greatest `B` proven `root ≥ B`.
    fn lower(&mut self, proven: u64) -> u64 {
        if proven == 0 && !self.ge(1) {
            return 0;
        }
        // Galloping: `lo` proven, `hi` not.
        let (mut lo, mut hi) = (proven.max(1), None);
        while hi.is_none() {
            let next = lo.saturating_mul(2).min(CAP);
            if next == lo {
                return lo;
            }
            if self.ge(next) {
                lo = next;
            } else {
                hi = Some(next);
            }
        }
        let mut hi = hi.unwrap();
        loop {
            while hi - lo > 1 {
                let mid = lo + (hi - lo) / 2;
                if self.ge(mid) {
                    lo = mid;
                } else {
                    hi = mid;
                }
            }
            // The last step again, on the large budget.
            if self.budget == BUDGET_CONFIRM || !{
                self.budget(BUDGET_CONFIRM);
                self.ge(hi)
            } {
                return lo;
            }
            lo = hi;
            hi = (hi.saturating_mul(2)).min(CAP);
            if lo == hi {
                return lo;
            }
        }
    }

    /// The least `B` proven `root ≤ B`, if any, given the root is at
    /// least `lower`.
    fn upper(&mut self, lower: u64, proven: Option<u64>) -> Option<u64> {
        if lower > 0 && self.le(lower) {
            return Some(lower);
        }
        let start = match proven {
            Some(h) => h,
            None => {
                if !self.le(CAP) {
                    self.budget(BUDGET_CONFIRM);
                    if !self.le(CAP) {
                        return None;
                    }
                }
                CAP
            }
        };
        // `hi` proven, nothing below `lo` provable.
        let (mut lo, mut hi) = (lower, start);
        loop {
            while lo < hi {
                let mid = lo + (hi - lo) / 2;
                if self.le(mid) {
                    hi = mid;
                } else {
                    lo = mid + 1;
                }
            }
            if hi == lower || self.budget == BUDGET_CONFIRM {
                return Some(hi);
            }
            self.budget(BUDGET_CONFIRM);
            if !self.le(hi - 1) {
                return Some(hi);
            }
            hi -= 1;
            lo = lower;
        }
    }
}

/// The quantifier instances `s` has made.
fn instances(s: &Solver) -> u32 {
    s.get_statistics()
        .entries()
        .find(|e| e.key == "quant instantiations")
        .and_then(|e| match e.value {
            z3::StatisticsValue::UInt(n) => Some(n),
            _ => None,
        })
        .unwrap_or(0)
}

pub(crate) struct Session {
    text: String,
    assertions: usize,
    /// Each tracked fact's name and literal.
    tracked: Vec<(String, String)>,
    /// The literals of the facts in use.
    active: Vec<String>,
    root: String,
    budget: u32,
    pub checks: usize,
    /// The most instances a proven check of the bounds made.
    pub needed: u64,
}

impl Session {
    pub(crate) fn new(program: &Program) -> Session {
        let budget = std::env::var("CARDINAL_UF_BUDGET").ok().and_then(|b| b.parse().ok()).unwrap_or(BUDGET);
        Session {
            text: program.text.clone(),
            assertions: program.assertions,
            tracked: program.tracked.clone(),
            active: program.tracked.iter().map(|(_, l)| l.clone()).collect(),
            root: format!("(card {})", program.root),
            budget,
            checks: 0,
            needed: 0,
        }
    }

    /// Checks that the facts are consistent (§6.6): while they prove
    /// `false`, drops every fact of the unsat core. The names dropped.
    pub(crate) fn consistent(&mut self) -> Vec<String> {
        let mut dropped = vec![];
        for _ in 0..8 {
            self.checks += 1;
            let mut c = Checker::new(&self.text, self.assertions, &self.root, &self.active, self.budget);
            let active = c.active.clone();
            let s = c.solver();
            let mut p = Params::new();
            p.set_u32("smt.qi.max_instances", self.budget);
            s.set_params(&p);
            if s.check_assumptions(&active) != SatResult::Unsat {
                break;
            }
            let core: Vec<String> = s.get_unsat_core().iter().map(|b| format!("|{}|", b.to_string().trim_matches('|'))).collect();
            if core.is_empty() {
                break;
            }
            for (n, l) in &self.tracked {
                if core.contains(l) {
                    dropped.push(n.clone());
                }
            }
            self.active.retain(|l| !core.contains(l));
        }
        dropped
    }

    /// The facts whose literals are in use.
    pub(crate) fn in_use(&self) -> usize {
        self.active.len()
    }

    /// The proven bounds `(lower, upper)`, given bounds `proven` already:
    /// the lower and the upper bound each searched for in a thread of its
    /// own, from `proven`.
    pub(crate) fn bounds(&mut self, proven: (u64, Option<u64>)) -> (u64, Option<u64>) {
        let (text, n, root, active, budget) = (&self.text, self.assertions, &self.root, &self.active, self.budget);
        let ((lower, lc, ln), (upper, uc, un)) = std::thread::scope(|scope| {
            let low = scope.spawn(move || {
                let mut c = Checker::new(text, n, root, active, budget);
                let l = c.lower(proven.0);
                (l, c.checks, c.needed)
            });
            let up = scope.spawn(move || {
                let mut c = Checker::new(text, n, root, active, budget);
                let u = c.upper(proven.0, proven.1);
                (u, c.checks, c.needed)
            });
            (low.join().unwrap(), up.join().unwrap())
        });
        self.checks += lc + uc;
        self.needed = ln.max(un);
        (lower.max(proven.0), match (upper, proven.1) {
            (Some(u), Some(p)) => Some(u.min(p)),
            (u, p) => u.or(p),
        })
    }
}
