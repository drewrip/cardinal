//! Bounds on a query's output cardinality.
//!
//! The largest `lo` and smallest `hi` with `lo <= X <= hi` that Z3 proves,
//! of the root's cardinality or of any operator's ([`PlanBounds`]). A bound
//! is reported only when Z3 proves it; an undecided check never yields one.
//!
//! `hi` is searched first, by binary search from `2^30` down, and caps the
//! search for `lo`, which gallops up from 0 and then bisects. Each check
//! that fails to prove a claim needs a model, which can take its whole
//! budget, so the searches avoid them: `lo` is most often small.
//!
//! Each check's budget is a resource limit (Z3's `rlimit`), not a time:
//! the same constraints give the same bounds however loaded the machine
//! is. A generous timeout only guards against a check that stalls.

use std::cell::{Cell, RefCell};
use std::fmt;
use std::time::{Duration, Instant};

use z3::ast::{Bool, Int};
use z3::{SatResult, Solver};

use crate::analysis::{set_limits, solver_with_limits};

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
/// Per-check resource limit: bounds are best-effort, so give up quickly.
/// Z3 applies it to each check. Proofs take far less; what reaches it is
/// most often the search for a model refuting a claim, at a few tenths of
/// a second to a few seconds on an unloaded core, as Z3 counts work
/// unevenly.
const RLIMIT: u32 = 300_000;
/// The first check of a search, which also loads the constraints into the
/// solver.
const FIRST_RLIMIT: u32 = 10_000_000;
/// Wall-clock limits, only against a check that stalls without spending
/// its resources: far beyond what its resource limit takes.
const TIMEOUT_MS: u32 = 10_000;
const FIRST_TIMEOUT_MS: u32 = 60_000;

/// How a bounds search's solver checks came out, and how long they took.
#[doc(hidden)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SearchStats {
    /// Checks that found a model: a claim refuted, or a claim added.
    pub sat: u32,
    /// Checks that found none: a claim proven, or contradicted.
    pub unsat: u32,
    /// Checks that gave up, mostly at the resource limit.
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
    /// Whether a check has run, loading the constraints.
    warm: Cell<bool>,
    /// The variables searched for bounds, and what the checks so far tell
    /// of each: every model a check finds narrows each one's search.
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
        let solver = solver_with_limits(FIRST_RLIMIT, FIRST_TIMEOUT_MS);
        solver.from_string(constraints);
        let parsed = solver.get_assertions().len();
        (
            Search {
                solver,
                output: Int::new_const(root),
                stats: Cell::default(),
                warm: Cell::new(false),
                targets: RefCell::default(),
            },
            parsed,
        )
    }

    /// The checks so far.
    pub(crate) fn stats(&self) -> SearchStats {
        self.stats.get()
    }

    /// The resource and time limits of the next check: larger for the
    /// first.
    fn limits(&self) -> (u32, u32) {
        if self.warm.get() { (RLIMIT, TIMEOUT_MS) } else { (FIRST_RLIMIT, FIRST_TIMEOUT_MS) }
    }

    /// Checks the solver, counting the outcome.
    fn check(&self) -> SatResult {
        let first = !self.warm.get();
        let start = Instant::now();
        let result = self.solver.check();
        self.warm.set(true);
        if first {
            let (rlimit, ms) = self.limits();
            set_limits(&self.solver, rlimit, ms);
        }
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

    /// The proven range of `x`, a target of the search.
    fn range(&self, x: &Int) -> Bounds {
        let i = self.target(x);
        self.range_of(i)
    }

    /// The proven range of `X`.
    pub(crate) fn bounds(&self) -> Bounds {
        self.range(&self.output)
    }

    /// The index of target `x`, made one if it is not yet.
    fn target(&self, x: &Int) -> usize {
        let mut targets = self.targets.borrow_mut();
        match targets.iter().position(|(t, _)| t == x) {
            Some(i) => i,
            None => {
                targets.push((x.clone(), Known::default()));
                targets.len() - 1
            }
        }
    }

    /// The largest `N` with `x >= N` of target `i`, searched only where the
    /// checks so far leave it: from what is proven up to the least value seen.
    ///
    /// It gallops up from what is proven (`+1`, `+2`, `+4`, …), then
    /// bisects below the first claim that fails. A proof is cheap, while a
    /// refutation needs a model, which can take the whole timeout: a small
    /// lower bound, the most common, costs about one failed check.
    fn lower(&self, i: usize) -> u64 {
        let k = self.known(i);
        let top = [k.least, k.ceil, Some(CAP)].into_iter().flatten().min().unwrap_or(CAP);
        let mut lo = k.floor.min(top);
        let mut step = 1;
        let mut hi = loop {
            let n = (lo + step).min(top);
            if n <= lo {
                return lo;
            }
            if !self.proves_at_least(i, n) {
                break self.known(i).least.map_or(n - 1, |l| l.min(n - 1)).max(lo);
            }
            lo = n;
            step *= 2;
        };
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
    /// proven. Searched before [`Self::lower`], which it caps.
    fn upper(&self, i: usize) -> Option<u64> {
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

    /// The proven range of target `i`: the upper bound first, whose proof
    /// caps the lower bound's search.
    fn range_of(&self, i: usize) -> Bounds {
        let upper = self.upper(i);
        Bounds { lower: self.lower(i), upper }
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

    fn bounds_of(smt: &str) -> Bounds {
        Search::new(&format!("(declare-const x Int) {smt}"), "x").0.bounds()
    }

    #[test]
    fn lower_bounds_are_exact() {
        for n in [0, 1, 7, 1_000] {
            let b = bounds_of(&format!("(assert (<= {n} x 5000))"));
            assert_eq!(b, Bounds { lower: n, upper: Some(5000) });
        }
        assert_eq!(bounds_of("(assert (= x 5))"), Bounds { lower: 5, upper: Some(5) });
    }

    #[test]
    fn lower_bound_without_an_upper_one() {
        assert_eq!(bounds_of("(assert (>= x 7))"), Bounds { lower: 7, upper: None });
    }

    /// Once the upper bound is searched, a lower bound of 0 costs at most
    /// two checks.
    #[test]
    fn small_lower_bound_is_cheap() {
        let (search, _) = Search::new("(declare-const x Int) (assert (<= 0 x 5000))", "x");
        let i = search.target(&Int::new_const("x"));
        assert_eq!(search.upper(i), Some(5000));
        let before = search.stats().checks();
        assert_eq!(search.lower(i), 0);
        assert!(search.stats().checks() - before <= 2, "{:?}", search.stats());
    }

    /// The first check, which loads the constraints, gets the larger
    /// limits; the rest the usual ones.
    #[test]
    fn first_check_gets_more_time() {
        let (search, _) = Search::new("(declare-const x Int) (assert (<= 0 x 5))", "x");
        assert_eq!(search.limits(), (FIRST_RLIMIT, FIRST_TIMEOUT_MS));
        search.check();
        assert_eq!(search.limits(), (RLIMIT, TIMEOUT_MS));
        search.check();
        assert_eq!(search.limits(), (RLIMIT, TIMEOUT_MS));
    }

    /// Z3 is the pinned release, not an older system library: older ones
    /// prove far slower.
    #[test]
    fn z3_is_recent() {
        let v: Vec<u32> = z3::full_version().split('.').take(2).map(|n| n.parse().unwrap()).collect();
        assert!(v >= vec![4, 13], "Z3 {}", z3::full_version());
    }
}
