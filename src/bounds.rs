//! Bounds on a query's output cardinality.
//!
//! The largest `lo` and smallest `hi` with `lo <= X <= hi` that Z3 proves,
//! each by binary search. A bound is reported only when Z3 proves it; an
//! undecided check never yields one.

use std::cell::Cell;
use std::fmt;
use std::time::{Duration, Instant};

use z3::ast::{Bool, Int};
use z3::{SatResult, Solver};

use crate::analysis::solver_with_timeout;

/// The proven range of a query's output cardinality `X`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Bounds {
    /// `X >= lower`.
    pub lower: u64,
    /// `X <= upper`, if any is proven.
    pub upper: Option<u64>,
}

impl Bounds {
    /// True if `rows` is in the range.
    pub fn holds(&self, rows: u64) -> bool {
        self.lower <= rows && self.upper.is_none_or(|hi| rows <= hi)
    }
}

impl fmt::Display for Bounds {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.upper {
            Some(hi) if hi == self.lower => write!(f, "X = {hi}"),
            Some(hi) => write!(f, "{} <= X <= {hi}", self.lower),
            None => write!(f, "X >= {}", self.lower),
        }
    }
}

/// Largest constant tried; a bound needing more is treated as unbounded.
const CAP: u64 = 1 << 30;
/// Per-check timeout: bounds are best-effort, so give up quickly.
const TIMEOUT_MS: u32 = 1_000;

/// How a bounds search's solver checks came out, and how long they took.
#[doc(hidden)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SearchStats {
    /// Checks that found a model: a claim refuted, or a claim added.
    pub sat: u32,
    /// Checks that found none: a claim proven, or contradicted.
    pub unsat: u32,
    /// Checks that gave up, mostly at the timeout.
    pub unknown: u32,
    pub time: Duration,
}

impl SearchStats {
    pub fn checks(&self) -> u32 {
        self.sat + self.unsat + self.unknown
    }
}

impl std::ops::AddAssign for SearchStats {
    fn add_assign(&mut self, o: SearchStats) {
        self.sat += o.sat;
        self.unsat += o.unsat;
        self.unknown += o.unknown;
        self.time += o.time;
    }
}

pub(crate) struct Search {
    solver: Solver,
    output: Int,
    stats: Cell<SearchStats>,
}

impl Search {
    /// A solver loaded with `constraints`, bounding variable `root`.
    pub(crate) fn new(constraints: &str, root: &str) -> (Self, usize) {
        let solver = solver_with_timeout(TIMEOUT_MS);
        solver.from_string(constraints);
        let parsed = solver.get_assertions().len();
        (
            Search {
                solver,
                output: Int::new_const(root),
                stats: Cell::default(),
            },
            parsed,
        )
    }

    /// The checks so far.
    pub(crate) fn stats(&self) -> SearchStats {
        self.stats.get()
    }

    /// Checks the solver, counting the outcome.
    fn check(&self) -> SatResult {
        let start = Instant::now();
        let result = self.solver.check();
        let mut stats = self.stats.get();
        stats.time += start.elapsed();
        match result {
            SatResult::Sat => stats.sat += 1,
            SatResult::Unsat => stats.unsat += 1,
            SatResult::Unknown => stats.unknown += 1,
        }
        self.stats.set(stats);
        result
    }

    /// True if the constraints entail `claim`.
    fn proves(&self, claim: Bool) -> bool {
        self.solver.push();
        self.solver.assert(claim.not());
        let unsat = self.check() == SatResult::Unsat;
        self.solver.pop(1);
        unsat
    }

    /// Adds `claim` to the constraints if it is consistent with them:
    /// `Some(true)` if added, `Some(false)` if it contradicts them, and
    /// `None` if that is undecided (it is then not added).
    pub(crate) fn assume(&self, claim: &Bool) -> Option<bool> {
        self.solver.push();
        self.solver.assert(claim);
        match self.check() {
            SatResult::Sat => Some(true),
            result => {
                self.solver.pop(1);
                (result == SatResult::Unsat).then_some(false)
            }
        }
    }

    /// The largest `N` with `X >= N`.
    pub(crate) fn lower(&self) -> u64 {
        smallest(0, CAP, |n| !self.proves(self.output.ge(Int::from_u64(n + 1))))
    }

    /// The smallest `N` with `X <= N`.
    pub(crate) fn constant(&self) -> Option<u64> {
        if !self.proves(self.output.le(Int::from_u64(CAP))) {
            return None;
        }
        Some(smallest(0, CAP, |n| {
            self.proves(self.output.le(Int::from_u64(n)))
        }))
    }

    /// The proven range of `X`.
    pub(crate) fn bounds(&self) -> Bounds {
        Bounds { lower: self.lower(), upper: self.constant() }
    }
}

/// The smallest value in `lo..=hi` satisfying a monotone `pred` that holds at `hi`.
fn smallest(mut lo: u64, mut hi: u64, pred: impl Fn(u64) -> bool) -> u64 {
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if pred(mid) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    hi
}
