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
//! is. A generous timeout only guards against a check that stalls
//! ([`Limits`](crate::Limits)).

use std::cell::{Cell, RefCell};
use std::fmt;
use std::time::{Duration, Instant};

use z3::ast::{Bool, Int};
use z3::{SatResult, Solver};

use crate::Limits;
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

/// How solver checks came out: decided, or why not; and the work and
/// time they took.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CheckStats {
    /// Checks that found a model: a claim refuted, or a claim added.
    pub sat: u32,
    /// Checks that found none: a claim proven, or contradicted.
    pub unsat: u32,
    /// Gave up at the resource limit: a bigger budget might have decided
    /// it. Depends only on the constraints, never on the machine's load.
    pub limited: u32,
    /// Gave up at the wall-clock guard: can depend on the machine's load.
    pub timed_out: u32,
    /// Gave up for another reason (Z3 is incomplete on nonlinear integer
    /// arithmetic): no budget would decide it.
    pub incomplete: u32,
    /// Z3's `rlimit count`, summed over the checks.
    pub rlimit: u64,
    pub time: Duration,
}

impl CheckStats {
    /// Every check.
    pub fn checks(&self) -> u32 {
        self.sat + self.unsat + self.unknown()
    }

    /// Checks that gave up, for any reason.
    pub fn unknown(&self) -> u32 {
        self.limited + self.timed_out + self.incomplete
    }

    /// Checks `solver`, counting the outcome. `rlimit` is the check's
    /// resource limit, which tells a check that spent it from one canceled
    /// otherwise.
    pub(crate) fn check(&mut self, solver: &Solver, rlimit: u32) -> SatResult {
        let before = rlimit_count(solver);
        let start = Instant::now();
        let result = solver.check();
        self.time += start.elapsed();
        let spent = rlimit_count(solver).saturating_sub(before);
        self.rlimit += spent;
        match result {
            SatResult::Sat => self.sat += 1,
            SatResult::Unsat => self.unsat += 1,
            SatResult::Unknown => match solver.get_reason_unknown().as_deref() {
                Some("timeout") => self.timed_out += 1,
                Some("canceled" | "max. resource limit exceeded") => self.limited += 1,
                _ if spent >= u64::from(rlimit) => self.limited += 1,
                _ => self.incomplete += 1,
            },
        }
        result
    }
}

impl std::ops::AddAssign for CheckStats {
    fn add_assign(&mut self, o: CheckStats) {
        self.sat += o.sat;
        self.unsat += o.unsat;
        self.limited += o.limited;
        self.timed_out += o.timed_out;
        self.incomplete += o.incomplete;
        self.rlimit += o.rlimit;
        self.time += o.time;
    }
}

/// Z3's resource count of `solver`'s context so far.
fn rlimit_count(solver: &Solver) -> u64 {
    match solver.get_statistics().value("rlimit count") {
        Some(z3::StatisticsValue::UInt(n)) => n.into(),
        _ => 0,
    }
}

/// How a bounds search's solver checks went.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SearchStats {
    pub checks: CheckStats,
}

impl std::ops::AddAssign for SearchStats {
    fn add_assign(&mut self, o: SearchStats) {
        self.checks += o.checks;
    }
}

pub(crate) struct Search {
    solver: Solver,
    output: Int,
    limits: Limits,
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
    /// A search over `constraints`, bounding variable `root`.
    pub(crate) fn new(constraints: &[Bool], root: &str, limits: Limits) -> Self {
        let solver = solver_with_limits(limits.search_first, limits.first_timeout_ms());
        constraints.iter().for_each(|f| solver.assert(f));
        Search {
            solver,
            output: Int::new_const(root),
            limits,
            stats: Cell::default(),
            warm: Cell::new(false),
            targets: RefCell::default(),
        }
    }

    /// The checks so far.
    pub(crate) fn stats(&self) -> SearchStats {
        self.stats.get()
    }

    /// The resource and time limits of the next check: larger for the
    /// first.
    fn limits(&self) -> (u32, Option<u32>) {
        let l = &self.limits;
        if self.warm.get() { (l.search, l.timeout_ms) } else { (l.search_first, l.first_timeout_ms()) }
    }

    /// Checks the solver, counting the outcome.
    fn check(&self) -> SatResult {
        let first = !self.warm.get();
        let mut stats = self.stats.get();
        let result = stats.checks.check(&self.solver, self.limits().0);
        self.stats.set(stats);
        self.warm.set(true);
        if first {
            let (rlimit, ms) = self.limits();
            set_limits(&self.solver, rlimit, ms);
        }
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
    pub(crate) fn range(&self, x: &Int) -> Bounds {
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

    /// A search over the SMT-LIB `smt`.
    fn over(smt: &str, root: &str) -> Search {
        let solver = Solver::new();
        solver.from_string(smt);
        Search::new(&solver.get_assertions(), root, Limits::default())
    }

    /// `plan` gives every card the range a search of it alone gives.
    fn plan_matches_lone_searches(smt: &str, vars: &[&str]) {
        let cards: Vec<Int> = vars.iter().map(|v| Int::new_const(*v)).collect();
        let same: Vec<Option<usize>> = (0..vars.len()).map(|i| i.checked_sub(1)).collect();
        let search = over(smt, vars[vars.len() - 1]);
        let (ranges, total) = search.plan(&cards, &same);
        for (v, r) in vars.iter().zip(&ranges) {
            let alone = over(smt, v);
            assert_eq!(*r, alone.bounds(), "{v}");
        }
        let alone = over(smt, vars[0]);
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
        over(&format!("(declare-const x Int) {smt}"), "x").bounds()
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
        let search = over("(declare-const x Int) (assert (<= 0 x 5000))", "x");
        let i = search.target(&Int::new_const("x"));
        assert_eq!(search.upper(i), Some(5000));
        let before = search.stats().checks.checks();
        assert_eq!(search.lower(i), 0);
        assert!(search.stats().checks.checks() - before <= 2, "{:?}", search.stats());
    }

    /// The first check, which loads the constraints, gets the larger
    /// limits; the rest the usual ones.
    #[test]
    fn first_check_gets_more_time() {
        let search = over("(declare-const x Int) (assert (<= 0 x 5))", "x");
        let l = Limits::default();
        assert_eq!(search.limits(), (l.search_first, l.first_timeout_ms()));
        search.check();
        assert_eq!(search.limits(), (l.search, l.timeout_ms));
        search.check();
        assert_eq!(search.limits(), (l.search, l.timeout_ms));
    }

    /// Z3 is the pinned release, not an older system library: older ones
    /// prove far slower.
    #[test]
    fn z3_is_recent() {
        let v: Vec<u32> = z3::full_version().split('.').take(2).map(|n| n.parse().unwrap()).collect();
        assert!(v >= vec![4, 13], "Z3 {}", z3::full_version());
    }
}
