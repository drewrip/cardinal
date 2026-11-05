//! Bounds on a query's output cardinality.
//!
//! The largest `lo` and smallest `hi` with `lo <= X <= hi` that Z3 proves,
//! each by binary search, of the root's cardinality or of any operator's
//! ([`PlanBounds`]). A bound is reported only when Z3 proves it; an undecided
//! check never yields one.

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

/// The proven range of every operator's output cardinality, and of their sum.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PlanBounds {
    /// One per plan node, children before parents, as in
    /// [`Trace::nodes`](crate::Trace::nodes): a node's id is its index.
    pub nodes: Vec<NodeBounds>,
    /// The sum of every node's output cardinality: the rows the plan's
    /// operators produce in all.
    pub total: Bounds,
}

/// The proven range of one operator's output cardinality.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NodeBounds {
    /// The cardinality variable.
    pub var: String,
    /// The operator, as DataFusion shows it on one line.
    pub operator: String,
    /// Node ids of the operator's inputs, in order.
    pub inputs: Vec<usize>,
    pub bounds: Bounds,
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

    /// The largest `N` with `x >= N`.
    fn lower(&self, x: &Int) -> u64 {
        smallest(0, CAP, |n| !self.proves(x.ge(Int::from_u64(n + 1))))
    }

    /// The smallest `N` with `x <= N`.
    fn constant(&self, x: &Int) -> Option<u64> {
        if !self.proves(x.le(Int::from_u64(CAP))) {
            return None;
        }
        Some(smallest(0, CAP, |n| self.proves(x.le(Int::from_u64(n)))))
    }

    /// The proven range of `x`.
    fn range(&self, x: &Int) -> Bounds {
        Bounds { lower: self.lower(x), upper: self.constant(x) }
    }

    /// The proven range of `X`.
    pub(crate) fn bounds(&self) -> Bounds {
        self.range(&self.output)
    }

    /// The proven range of each of `cards`, and of their sum. `X` is one of
    /// them, and its range is [`Search::bounds`]. `same[i]` is a card that
    /// `cards[i]` may equal: if it provably does, they share a range.
    pub(crate) fn plan(&self, cards: &[Int], same: &[Option<usize>]) -> (Vec<Bounds>, Bounds) {
        let root = self.bounds();
        let mut out: Vec<Bounds> = vec![];
        for (i, x) in cards.iter().enumerate() {
            let b = match same[i] {
                _ if *x == self.output => root,
                Some(j) if self.proves(x.eq(&cards[j])) => out[j],
                _ => self.range(x),
            };
            out.push(b);
        }
        (out, self.range(&Int::add(cards)))
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
