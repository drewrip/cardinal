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

use std::sync::atomic::{AtomicU64, Ordering};

use z3::ast::Bool;
use z3::{Params, SatResult, Solver};

use super::program::Program;

/// How long a check may run: its resource limit (Z3's `rlimit`, about
/// 4M a second here: deterministic, unlike time, so that bounds do not
/// depend on the machine's load), its quantifier instances beyond those
/// made before it, and a time limit as a last resort. Pattern matching
/// never saturates on a program of many plans, so a claim the axioms do
/// not prove runs to the limit: the search runs on a small tier, and each
/// bound found is confirmed one step further on a large one.
#[derive(Clone, Copy, PartialEq)]
struct Tier {
    rlimit: u32,
    budget: u32,
    timeout_ms: u32,
}

fn env(k: &str, d: u32) -> u32 {
    std::env::var(k).ok().and_then(|t| t.parse().ok()).unwrap_or(d)
}

/// About §8's 1 s per check (`CARDINAL_UF_RLIMIT`, `CARDINAL_UF_BUDGET`).
fn search() -> Tier {
    Tier { rlimit: env("CARDINAL_UF_RLIMIT", 4_000_000), budget: env("CARDINAL_UF_BUDGET", 150_000), timeout_ms: 10_000 }
}

fn confirm() -> Tier {
    Tier {
        rlimit: env("CARDINAL_UF_CONFIRM_RLIMIT", 8_000_000),
        budget: env("CARDINAL_UF_CONFIRM_BUDGET", 2_000_000),
        timeout_ms: 20_000,
    }
}

/// Instances made before a check past which one cut short is tried again
/// on a fresh solver.
const POLLUTED: u32 = 100_000;

/// Largest bound tried; a bound needing more is no bound.
const CAP: u64 = 1 << 30;

/// What the two searches have proven so far, shared between their
/// threads: neither tries a claim the other's bound refutes.
struct Proven {
    lower: AtomicU64,
    /// `u64::MAX` while there is none.
    upper: AtomicU64,
}

/// Checks of claims about the root, in one thread.
struct Checker<'a> {
    text: &'a str,
    assertions: usize,
    root: &'a str,
    /// The literals of the facts in use.
    active: Vec<Bool>,
    solver: Option<Solver>,
    tier: Tier,
    /// The tier a bound found is confirmed on.
    last: Tier,
    proven: &'a Proven,
    checks: usize,
    /// Claims whose check ran out of instances to make: more budget
    /// proves them no better.
    saturated: std::collections::HashSet<String>,
    /// The most instances a proven check made.
    needed: u64,
}

impl<'a> Checker<'a> {
    fn new(text: &'a str, assertions: usize, root: &'a str, active: &[String], proven: &'a Proven, last: Tier) -> Checker<'a> {
        let active = active.iter().map(|l| Bool::new_const(l.trim_matches('|'))).collect();
        Checker { text, assertions, root, active, solver: None, tier: search(), last, proven, checks: 0, saturated: Default::default(), needed: 0 }
    }

    fn solver(&mut self) -> &Solver {
        if self.solver.is_none() {
            let s = Solver::new();
            let mut p = Params::new();
            p.set_bool("smt.auto_config", false);
            p.set_bool("smt.mbqi", false);
            s.set_params(&p);
            s.from_string(self.text);
            // Z3 drops what follows a declaration it rejects.
            let parsed = s.get_assertions().len();
            if parsed != self.assertions {
                let path = std::env::temp_dir().join(format!("uf_unparsed_{}.smt2", std::process::id()));
                let _ = std::fs::write(&path, self.text);
                panic!("the program did not parse whole: {parsed} of {} assertions; it is in {}", self.assertions, path.display());
            }
            self.solver = Some(s);
        }
        self.solver.as_ref().unwrap()
    }

    /// Whether the axioms and facts in use entail `claim`. The claim's
    /// negation is guarded by a literal of its own, assumed for this
    /// check only, so that what the check instantiates serves the next
    /// ones; each check runs on the current tier.
    /// (Z3 cancels a check in a pushed scope under an instance limit at
    /// once.)
    fn proves(&mut self, claim: &str) -> bool {
        if self.saturated.contains(claim) {
            return false;
        }
        self.checks += 1;
        let k = self.checks;
        let root = self.root.to_string();
        let mut assumptions = self.active.clone();
        let tier = self.tier;
        let s = self.solver();
        s.from_string(format!(
            "(declare-const |claim!{k}| Bool) (assert (=> |claim!{k}| (not {})))",
            claim.replace("|root!|", &root)
        ));
        assumptions.push(Bool::new_const(format!("claim!{k}")));
        let made = instances(s);
        let spent = stat(s, "rlimit count");
        let mut p = Params::new();
        p.set_u32("smt.qi.max_instances", made.saturating_add(tier.budget));
        p.set_u32("timeout", tier.timeout_ms);
        p.set_u32("rlimit", tier.rlimit);
        s.set_params(&p);
        let t = std::time::Instant::now();
        let r = s.check_assumptions(&assumptions);
        let after = instances(s);
        if std::env::var("CARDINAL_UF_TIME").is_ok() {
            eprintln!(
                "uf: check {claim} {r:?} {:.2}s {} instances {} rlimit {:?}",
                t.elapsed().as_secs_f64(),
                after - made,
                stat(s, "rlimit count").saturating_sub(spent),
                s.get_reason_unknown()
            );
        }
        // A check cut short leaves a solver that proves less.
        let cut = r != SatResult::Unsat && s.get_reason_unknown().is_some_and(|w| w.contains("canceled") || w.contains("timeout") || w.contains("resource"));
        if r == SatResult::Unsat {
            self.needed = self.needed.max((after - made) as u64);
        }
        if cut {
            self.solver = None;
            // What earlier checks made slows this one: again, on a
            // fresh solver.
            if made > POLLUTED {
                return self.proves(claim);
            }
        } else if r != SatResult::Unsat {
            self.saturated.insert(claim.to_string());
        }
        r == SatResult::Unsat
    }

    /// Whether `root ≤ b` is proven; not tried below the proven lower
    /// bound.
    fn le(&mut self, b: u64) -> bool {
        if b < self.proven.lower.load(Ordering::Relaxed) {
            return false;
        }
        let r = self.proves(&format!("(<= |root!| {b})"));
        if r {
            self.proven.upper.fetch_min(b, Ordering::Relaxed);
        }
        r
    }

    /// Whether `root ≥ b` is proven; not tried above the proven upper
    /// bound.
    fn ge(&mut self, b: u64) -> bool {
        if b == 0 {
            return true;
        }
        if b > self.proven.upper.load(Ordering::Relaxed) {
            return false;
        }
        let r = self.proves(&format!("(>= |root!| {b})"));
        if r {
            self.proven.lower.fetch_max(b, Ordering::Relaxed);
        }
        r
    }

    /// The greatest `B` proven `root ≥ B`, from `B = proven`.
    fn lower(&mut self, proven: u64) -> u64 {
        if proven == 0 && !self.ge(1) {
            if self.tier == self.last || {
                self.tier = self.last;
                !self.ge(1)
            } {
                return 0;
            }
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
                let up = self.proven.upper.load(Ordering::Relaxed);
                hi = hi.min(up.saturating_add(1)).max(lo + 1);
                if hi - lo <= 1 {
                    break;
                }
                let mid = lo + (hi - lo) / 2;
                if self.ge(mid) {
                    lo = mid;
                } else {
                    hi = mid;
                }
            }
            // The last step again, on the large tier.
            if self.tier == self.last || !{
                self.tier = self.last;
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

    /// The least `B` proven `root ≤ B`, if any, from `B = proven`,
    /// given the root is at least `lower`.
    fn upper(&mut self, lower: u64, proven: Option<u64>) -> Option<u64> {
        if lower > 0 && self.le(lower) {
            return Some(lower);
        }
        let start = match proven {
            Some(h) => h,
            None => {
                if !self.le(CAP) {
                    if self.tier == self.last || {
                        self.tier = self.last;
                        !self.le(CAP)
                    } {
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
                lo = lo.max(self.proven.lower.load(Ordering::Relaxed)).min(hi);
                if lo == hi {
                    break;
                }
                let mid = lo + (hi - lo) / 2;
                if self.le(mid) {
                    hi = mid;
                } else {
                    lo = mid + 1;
                }
            }
            if hi == 0 || hi <= self.proven.lower.load(Ordering::Relaxed) || self.tier == self.last {
                return Some(hi);
            }
            self.tier = self.last;
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
    stat(s, "quant instantiations")
}

fn stat(s: &Solver, key: &str) -> u32 {
    s.get_statistics()
        .entries()
        .find(|e| e.key == key)
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
    pub checks: usize,
    /// The most instances a proven check of the bounds made.
    pub needed: u64,
}

impl Session {
    pub(crate) fn new(program: &Program) -> Session {
        Session {
            text: program.text.clone(),
            assertions: program.assertions,
            tracked: program.tracked.clone(),
            active: program.tracked.iter().map(|(_, l)| l.clone()).collect(),
            root: format!("(card {})", program.root),
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
            let proven = Proven { lower: AtomicU64::new(0), upper: AtomicU64::new(u64::MAX) };
            let mut c = Checker::new(&self.text, self.assertions, &self.root, &self.active, &proven, search());
            let active = c.active.clone();
            let s = c.solver();
            let tier = search();
            let mut p = Params::new();
            p.set_u32("smt.qi.max_instances", tier.budget);
            p.set_u32("timeout", tier.timeout_ms);
            p.set_u32("rlimit", tier.rlimit);
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
    /// own, from `proven`. Unless `confirming`, on the search tier only.
    pub(crate) fn bounds(&mut self, proven: (u64, Option<u64>), confirming: bool) -> (u64, Option<u64>) {
        let last = if confirming { confirm() } else { search() };
        let (text, n, root, active) = (&self.text, self.assertions, &self.root, &self.active);
        let shared = Proven { lower: AtomicU64::new(proven.0), upper: AtomicU64::new(proven.1.unwrap_or(u64::MAX)) };
        let shared = &shared;
        let ((lower, lc, ln), (upper, uc, un)) = std::thread::scope(|scope| {
            let low = scope.spawn(move || {
                let mut c = Checker::new(text, n, root, active, shared, last);
                let l = c.lower(proven.0);
                (l, c.checks, c.needed)
            });
            // The upper bound is confirmed even without `confirming`: its
            // last step is one check, and proves what the facts' program,
            // larger, may not.
            let up = scope.spawn(move || {
                let mut c = Checker::new(text, n, root, active, shared, confirm());
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
