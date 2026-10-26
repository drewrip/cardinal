//! Bounds on a query's output cardinality relative to its source relations.
//!
//! Each bound has the form `X <= c·S + d`, where `X` is the output cardinality,
//! `S` the size of one source table or the total rows scanned, `c` a small
//! non-negative fraction and `d` a constant. The smallest `c` is found first, then the smallest `d` for it. A
//! bound is reported only when Z3 proves it; an undecided check never yields one.

use std::cmp::Ordering;
use std::fmt;

use z3::ast::{Bool, Int};
use z3::{Model, SatResult, Solver};

use crate::analyzer::solver_with_timeout;

/// `num/den · S + add` for some quantity `S`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Linear {
    pub num: u64,
    pub den: u64,
    pub add: u64,
}

impl Linear {
    /// True if `output <= num/den · x + add`.
    pub fn holds(&self, output: u64, x: u64) -> bool {
        self.den as u128 * output as u128
            <= self.num as u128 * x as u128 + self.den as u128 * self.add as u128
    }

    /// The coefficient `num/den`.
    pub fn coefficient(&self) -> f64 {
        self.num as f64 / self.den as f64
    }

    /// Renders the bound with `x` as the quantity, e.g. `1/2·Σ + 3`.
    pub fn render(&self, x: &str) -> String {
        let term = match (self.num, self.den) {
            (0, _) => None,
            (1, 1) => Some(x.to_string()),
            (n, 1) => Some(format!("{n}·{x}")),
            (n, d) => Some(format!("{n}/{d}·{x}")),
        };
        match (term, self.add) {
            (None, a) => a.to_string(),
            (Some(t), 0) => t,
            (Some(t), a) => format!("{t} + {a}"),
        }
    }
}

/// A bound relative to one source table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TableBound {
    pub table: String,
    pub bound: Linear,
    /// The output is provably *equal* to the bound, not just at most it.
    pub exact: bool,
}

/// Every bound proven for a query's output cardinality `X`.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Bounds {
    /// `X <= N` regardless of table sizes.
    pub constant: Option<u64>,
    /// `X <= c·Σ + d`, where `Σ` is the total rows scanned (one term per scan).
    pub sum: Option<Linear>,
    /// `X <= c·|T| + d` for each table `T` that bounds the output.
    pub tables: Vec<TableBound>,
}

impl fmt::Display for Bounds {
    /// The claims worth stating: a constant bound, or else the table bounds
    /// and the sum bound where it adds information.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut parts = vec![];
        if let Some(n) = self.constant {
            parts.push(format!("X <= {n}"));
        } else {
            for t in &self.tables {
                let op = if t.exact { "=" } else { "<=" };
                parts.push(format!(
                    "X {op} {}",
                    t.bound.render(&format!("|{}|", t.table))
                ));
            }
            // The sum bound adds information if it has a reducing factor, or if
            // no single table bounds the output.
            if let Some(s) = self.sum
                && (s.num < s.den || self.tables.is_empty())
            {
                parts.push(format!("X <= {}", s.render("Σ")));
            }
        }
        if parts.is_empty() {
            write!(f, "unbounded")
        } else {
            write!(f, "{}", parts.join("; "))
        }
    }
}

/// Largest constant tried; a bound needing more is treated as unbounded.
const CAP: u64 = 1 << 30;
/// Candidate coefficients `p/q` have `q <= MAX_DEN` and value `<= MAX_COEFF`.
const MAX_DEN: u64 = 12;
const MAX_COEFF: u64 = 8;
/// Per-check timeout: bounds are best-effort, so give up quickly.
const TIMEOUT_MS: u32 = 1_000;

pub(crate) struct Search {
    solver: Solver,
    output: Int,
}

/// The outcome of trying to prove a claim.
enum Check {
    Proved,
    /// A model of the constraints in which the claim fails.
    Refuted(Model),
    Undecided,
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
            },
            parsed,
        )
    }

    /// Whether the constraints entail `claim`, with a counterexample if not.
    fn check(&self, claim: Bool) -> Check {
        self.solver.push();
        self.solver.assert(claim.not());
        let check = match self.solver.check() {
            SatResult::Unsat => Check::Proved,
            SatResult::Sat => self
                .solver
                .get_model()
                .map_or(Check::Undecided, Check::Refuted),
            SatResult::Unknown => Check::Undecided,
        };
        self.solver.pop(1);
        check
    }

    /// True if the constraints entail `claim`.
    fn proves(&self, claim: Bool) -> bool {
        matches!(self.check(claim), Check::Proved)
    }

    /// The smallest `i` in `0..=hi` with `claim(i)` proven, for claims that
    /// weaken as `i` grows, `claim(hi)` proven. A counterexample to one claim
    /// skips the later ones it also refutes: `at` reads values off its model,
    /// and `holds(v, j)` says whether `claim(j)` holds at them.
    fn first<V>(
        &self,
        hi: u64,
        claim: impl Fn(u64) -> Bool,
        at: impl Fn(&Model) -> Option<V>,
        holds: impl Fn(&V, u64) -> bool,
    ) -> u64 {
        smallest(0, hi, |i| match self.check(claim(i)) {
            Check::Proved => Ok(i),
            Check::Refuted(m) => Err(match at(&m) {
                Some(v) => (i + 1..hi).find(|&j| holds(&v, j)).unwrap_or(hi),
                None => i + 1,
            }),
            Check::Undecided => Err(i + 1),
        })
    }

    /// True if variable `x` is provably zero.
    pub(crate) fn zero(&self, x: &str) -> bool {
        self.proves(Int::new_const(x).eq(Int::from_u64(0)))
    }

    /// True if variables `x` and `y` are provably equal.
    pub(crate) fn equal(&self, x: &str, y: &str) -> bool {
        self.proves(Int::new_const(x).eq(Int::new_const(y)))
    }

    /// The tightest proven `lo·d <= x <= hi·d`, as fractions `(num, den)` in
    /// `0..=1`, for variables with `x <= d` (so `[0, 1]` needs no proof).
    pub(crate) fn ratio(&self, x: &str, d: &str) -> ((u64, u64), (u64, u64)) {
        let (x, d) = (Int::new_const(x), Int::new_const(d));
        let candidates: Vec<(u64, u64)> =
            coefficients().into_iter().filter(|(p, q)| p <= q).collect();
        let last = candidates.len() - 1;
        let below = |i: usize| {
            let (p, q) = candidates[i];
            (&x * Int::from_u64(q)).le(&d * Int::from_u64(p))
        };
        let above = |i: usize| {
            let (p, q) = candidates[i];
            (&x * Int::from_u64(q)).ge(&d * Int::from_u64(p))
        };
        // A model with values `x` and `d` refutes `p/q` as an upper ratio
        // if `q·x > p·d`, and as a lower one if `q·x < p·d`.
        let at = |m: &Model| Some((value(m, &x)?, value(m, &d)?));
        let scaled = |i: usize, x: i128, d: i128| {
            let (p, q) = candidates[i];
            (q as i128 * x, p as i128 * d)
        };
        // Most ratios are unconstrained: try the weakest claim on each side
        // before searching.
        let hi = if self.proves(below(last - 1)) {
            let holds = |&(x, d): &(i128, i128), j: u64| {
                let (qx, pd) = scaled(j as usize, x, d);
                qx <= pd
            };
            self.first(last as u64 - 1, |i| below(i as usize), at, holds) as usize
        } else {
            last
        };
        let lo = if self.proves(above(1)) {
            // `above` holds up to some index; search from the top.
            let holds = |&(x, d): &(i128, i128), j: u64| {
                let (qx, pd) = scaled(last - j as usize, x, d);
                qx >= pd
            };
            last - self.first(last as u64 - 1, |i| above(last - i as usize), at, holds) as usize
        } else {
            0
        };
        (candidates[lo], candidates[hi])
    }

    /// `den·X <= num·s + den·add`
    fn upper(&self, x: &Int, num: u64, den: u64, add: u64) -> Bool {
        let (lhs, rhs) = sides(&self.output, x, &Linear { num, den, add });
        lhs.le(rhs)
    }

    /// Adds `claim` to the constraints if it is consistent with them:
    /// `Some(true)` if added, `Some(false)` if it contradicts them, and
    /// `None` if that is undecided (it is then not added).
    pub(crate) fn assume(&self, claim: &Bool) -> Option<bool> {
        self.solver.push();
        self.solver.assert(claim);
        match self.solver.check() {
            SatResult::Sat => Some(true),
            result => {
                self.solver.pop(1);
                (result == SatResult::Unsat).then_some(false)
            }
        }
    }

    /// The largest `N` with `X >= N`.
    pub(crate) fn lower(&self) -> u64 {
        // A model with `X = v` leaves `X >= v + 1` unproven.
        smallest(0, CAP, |n| {
            match self.check(self.output.ge(Int::from_u64(n + 1))) {
                Check::Proved => Err(n + 1),
                Check::Refuted(m) => Ok(natural(value(&m, &self.output)).unwrap_or(n)),
                Check::Undecided => Ok(n),
            }
        })
    }

    /// The smallest `N` with `X <= N`.
    pub(crate) fn constant(&self) -> Option<u64> {
        if !self.proves(self.output.le(Int::from_u64(CAP))) {
            return None;
        }
        // A model with `X = v` refutes `X <= n` for every `n < v`.
        Some(smallest(0, CAP, |n| {
            match self.check(self.output.le(Int::from_u64(n))) {
                Check::Proved => Ok(n),
                Check::Refuted(m) => Err(natural(value(&m, &self.output)).unwrap_or(n + 1)),
                Check::Undecided => Err(n + 1),
            }
        }))
    }

    /// The smallest `c`, then smallest `d`, with `X <= c·s + d`.
    pub(crate) fn linear(&self, x: &Int) -> Option<(Linear, bool)> {
        let candidates = coefficients();
        let claim = |i: u64| {
            let (num, den) = candidates[i as usize];
            self.upper(x, num, den, CAP)
        };
        let last = candidates.len() as u64 - 1;
        if !self.proves(claim(last)) {
            return None;
        }
        // A model with `X = o` and `s` refutes `p/q` if `q·o > p·s + q·CAP`,
        // and, for `num/den`, every `d` with `den·d < den·o - num·s`.
        let at = |m: &Model| Some((value(m, &self.output)?, value(m, x)?));
        let i = self.first(last, claim, at, |&(o, s), j| {
            let (p, q) = candidates[j as usize];
            q as i128 * o <= p as i128 * s + (q * CAP) as i128
        });
        let (num, den) = candidates[i as usize];
        let add = smallest(0, CAP, |d| match self.check(self.upper(x, num, den, d)) {
            Check::Proved => Ok(d),
            Check::Refuted(m) => Err(at(&m)
                .and_then(|(o, s)| {
                    let (den, num) = (den as i128, num as i128);
                    natural(Some((den * o - num * s + den - 1) / den))
                })
                .unwrap_or(d + 1)),
            Check::Undecided => Err(d + 1),
        });
        let bound = Linear { num, den, add };
        // Also at least the bound?
        let (lhs, rhs) = sides(&self.output, x, &bound);
        let exact = self.proves(lhs.ge(rhs));
        Some((bound, exact))
    }
}

/// `den·output` and `num·x + den·add`: the sides of `output <= bound` over `x`
/// with the fraction cleared.
pub(crate) fn sides(output: &Int, x: &Int, bound: &Linear) -> (Int, Int) {
    let lhs = output * Int::from_u64(bound.den);
    let rhs = x * Int::from_u64(bound.num) + Int::from_u64(bound.den * bound.add);
    (lhs, rhs)
}

/// The smallest value in `lo..=hi` satisfying a monotone predicate that holds
/// at `hi`. `test(n)` decides it at `n` and may tell more: `Ok(m)` that it
/// holds at `m <= n`, `Err(m)` that it fails below `m > n`.
///
/// Answers are mostly far below `hi`, and only failures tell more, so this
/// gallops up from `lo` in doubling steps before bisecting.
fn smallest(mut lo: u64, mut hi: u64, test: impl Fn(u64) -> Result<u64, u64>) -> u64 {
    let mut step = 0u64;
    while lo < hi {
        let n = lo.saturating_add(step).min(lo + (hi - lo) / 2);
        match test(n) {
            Ok(m) => hi = m.clamp(lo, n),
            Err(m) => {
                lo = m.clamp(n + 1, hi);
                step = 2 * step + 1;
            }
        }
    }
    hi
}

/// `x`'s value in `model`.
fn value(model: &Model, x: &Int) -> Option<i128> {
    model.eval(x, true)?.as_i64().map(i128::from)
}

/// `v` if it is a `u64`.
fn natural(v: Option<i128>) -> Option<u64> {
    u64::try_from(v?).ok()
}

/// Reduced fractions `p/q` with `q <= MAX_DEN` and `p/q <= MAX_COEFF`, ascending.
fn coefficients() -> Vec<(u64, u64)> {
    let mut out: Vec<(u64, u64)> = (1..=MAX_DEN)
        .flat_map(|q| (0..=MAX_COEFF * q).map(move |p| (p, q)))
        .filter(|&(p, q)| gcd(p, q) == 1)
        .collect();
    out.sort_by(|a, b| (a.0 * b.1).cmp(&(b.0 * a.1)).then(Ordering::Equal));
    out
}

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ratio_finds_the_tightest_fractions() {
        let declare = "(declare-fun x () Int) (declare-fun d () Int) (assert (>= x 0)) (assert (<= x d))";
        let ratio = |facts: &str| Search::new(&format!("{declare} {facts}"), "x").0.ratio("x", "d");
        assert_eq!(ratio(""), ((0, 1), (1, 1)));
        assert_eq!(ratio("(assert (<= (* 2 x) d))"), ((0, 1), (1, 2)));
        assert_eq!(ratio("(assert (>= (* 3 x) d))"), ((1, 3), (1, 1)));
        assert_eq!(
            ratio("(assert (>= (* 4 x) d)) (assert (<= (* 3 x) (* 2 d)))"),
            ((1, 4), (2, 3))
        );
        assert_eq!(ratio("(assert (= x 0))"), ((0, 1), (0, 1)));
        assert_eq!(ratio("(assert (= x d))"), ((1, 1), (1, 1)));
    }
}
