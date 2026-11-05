//! Bounds on a query's output cardinality.
//!
//! The largest `lo` and smallest `hi` with `lo <= X <= hi` that Z3 proves,
//! each by binary search, of the root's cardinality or of any operator's
//! ([`PlanBounds`]). A bound is reported only when Z3 proves it; an undecided
//! check never yields one.

use std::cell::{Cell, RefCell};
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
    /// The variables a [`Search::plan`] bounds, and what the checks so far
    /// tell of each.
    targets: RefCell<Vec<(Int, Known)>>,
}

/// What the checks so far tell of one target `x`.
#[derive(Debug, Clone, Copy, Default)]
struct Known {
    /// `x >= floor` is proven.
    floor: u64,
    /// `x <= ceil` is proven, if any.
    ceil: Option<u64>,
    /// The least and greatest `x` in a model of the constraints, if any
    /// was seen (`u64::MAX` for one beyond it): `x > least` and `x < most`
    /// are not provable.
    least: Option<u64>,
    most: Option<u64>,
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
                targets: RefCell::default(),
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
        let result = self.check();
        if result == SatResult::Sat {
            self.observe();
        }
        self.solver.pop(1);
        result == SatResult::Unsat
    }

    /// Records each target's value in the model the last check found, a
    /// model of the constraints.
    fn observe(&self) {
        let mut targets = self.targets.borrow_mut();
        if targets.is_empty() {
            return;
        }
        let Some(model) = self.solver.get_model() else { return };
        for (x, k) in targets.iter_mut() {
            let v = model.eval(x, true).and_then(|v| v.as_u64()).unwrap_or(u64::MAX);
            k.least = Some(k.least.map_or(v, |l| l.min(v)));
            k.most = Some(k.most.map_or(v, |m| m.max(v)));
        }
    }

    fn known(&self, i: usize) -> Known {
        self.targets.borrow()[i].1
    }

    /// True if the constraints entail `x >= n` of target `i`.
    fn proves_at_least(&self, i: usize, n: u64) -> bool {
        let x = self.targets.borrow()[i].0.clone();
        let proven = self.proves(x.ge(Int::from_u64(n)));
        if proven {
            let k = &mut self.targets.borrow_mut()[i].1;
            k.floor = k.floor.max(n);
        }
        proven
    }

    /// True if the constraints entail `x <= n` of target `i`.
    fn proves_at_most(&self, i: usize, n: u64) -> bool {
        let x = self.targets.borrow()[i].0.clone();
        let proven = self.proves(x.le(Int::from_u64(n)));
        if proven {
            let k = &mut self.targets.borrow_mut()[i].1;
            k.ceil = Some(k.ceil.map_or(n, |c| c.min(n)));
        }
        proven
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

    /// The largest `N` with `x >= N` of target `i`, searched only where the
    /// checks so far leave it: from what is proven up to the least value seen.
    fn lower_of(&self, i: usize) -> u64 {
        let k = self.known(i);
        let mut hi = [k.least, k.ceil, Some(CAP)].into_iter().flatten().min().unwrap_or(CAP);
        let mut lo = k.floor.min(hi);
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if self.proves_at_least(i, mid + 1) {
                lo = mid + 1;
            } else {
                hi = self.known(i).least.map_or(mid, |l| l.min(mid)).max(lo);
            }
        }
        hi
    }

    /// The smallest `N` with `x <= N` of target `i`, searched only where the
    /// checks so far leave it: from the greatest value seen up to what is
    /// proven.
    fn constant_of(&self, i: usize) -> Option<u64> {
        if self.known(i).most.is_some_and(|m| m > CAP) {
            return None;
        }
        if self.known(i).ceil.is_none_or(|c| c > CAP) && !self.proves_at_most(i, CAP) {
            return None;
        }
        let k = self.known(i);
        let mut hi = k.ceil.unwrap_or(CAP).min(CAP);
        let mut lo = k.floor.max(k.most.unwrap_or(0)).min(hi);
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if self.proves_at_most(i, mid) {
                hi = mid;
            } else {
                lo = (mid + 1).max(self.known(i).most.unwrap_or(0)).min(hi);
            }
        }
        Some(hi)
    }

    fn range_of(&self, i: usize) -> Bounds {
        Bounds { lower: self.lower_of(i), upper: self.constant_of(i) }
    }

    /// The proven range of each of `cards`, and of their sum. Each card is
    /// non-negative, and `X` is one of them, whose range is
    /// [`Search::bounds`]. `same[i]` is a card that
    /// `cards[i]` may equal: if it provably does, they share a range.
    ///
    /// Every model a check finds bounds each card's search: `X >= v + 1` and
    /// `X <= v - 1` are unprovable of a card that is `v` in it.
    pub(crate) fn plan(&self, cards: &[Int], same: &[Option<usize>]) -> (Vec<Bounds>, Bounds) {
        let total = Int::add(cards);
        *self.targets.borrow_mut() = cards.iter().chain([&total]).map(|x| (x.clone(), Known::default())).collect();
        let root = self.bounds();
        let mut out: Vec<Bounds> = vec![];
        for (i, x) in cards.iter().enumerate() {
            let b = match same[i] {
                _ if *x == self.output => root,
                Some(j) if self.proves(x.eq(&cards[j])) => out[j],
                _ => self.range_of(i),
            };
            out.push(b);
        }
        // The sum is at least the cards' least, and at most their greatest.
        let t = cards.len();
        {
            let k = &mut self.targets.borrow_mut()[t].1;
            k.floor = k.floor.max(out.iter().map(|b| b.lower).sum());
            if let Some(hi) = out.iter().map(|b| b.upper).sum::<Option<u64>>() {
                k.ceil = Some(k.ceil.map_or(hi, |c| c.min(hi)));
            }
        }
        (out, self.range_of(t))
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

#[cfg(test)]
mod tests {
    use super::*;

    /// `plan` gives every card the range a search of it alone gives.
    fn plan_matches_lone_searches(smt: &str, vars: &[&str]) {
        let cards: Vec<Int> = vars.iter().map(|v| Int::new_const(*v)).collect();
        let same: Vec<Option<usize>> = (0..vars.len()).map(|i| i.checked_sub(1)).collect();
        let (search, _) = Search::new(smt, vars[vars.len() - 1]);
        let (ranges, total) = search.plan(&cards, &same);
        for (v, r) in vars.iter().zip(&ranges) {
            let (alone, _) = Search::new(smt, v);
            assert_eq!(*r, alone.bounds(), "{v}");
        }
        let (alone, _) = Search::new(smt, vars[0]);
        assert_eq!(total, alone.range(&Int::add(&cards)), "total");
    }

    #[test]
    fn plan_ranges_are_those_of_lone_searches() {
        let decls = "(declare-const a Int) (declare-const b Int) (declare-const c Int) (declare-const d Int)";
        plan_matches_lone_searches(
            &format!("{decls} (assert (<= 3 a 40)) (assert (<= a b (* 2 a))) (assert (= c (+ a b))) (assert (= d c))"),
            &["a", "b", "c", "d"],
        );
        plan_matches_lone_searches(
            &format!("{decls} (assert (>= a 0)) (assert (<= 0 b 5)) (assert (= c 7)) (assert (<= 0 d b))"),
            &["a", "b", "c", "d"],
        );
        plan_matches_lone_searches(
            &format!("{decls} (assert (<= 0 a 10)) (assert (= (+ a b) 10)) (assert (>= b 0)) (assert (= c (- 10 a))) (assert (<= 0 d 1))"),
            &["a", "b", "c", "d"],
        );
    }
}
