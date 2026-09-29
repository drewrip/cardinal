//! Bounds on a query's output cardinality relative to its source relations.
//!
//! Each bound has the form `O <= c·X + d`, where `X` is the size of one source
//! table or the total rows scanned, `c` a small non-negative fraction and `d` a
//! constant. The smallest `c` is found first, then the smallest `d` for it. A
//! bound is reported only when Z3 proves it; an undecided check never yields one.

use std::cmp::Ordering;
use std::fmt;

use z3::ast::{Bool, Int};
use z3::{SatResult, Solver};

use crate::analyzer::solver_with_timeout;

/// `num/den · X + add` for some quantity `X`.
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

/// Every bound proven for a query's output cardinality `O`.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Bounds {
    /// `O <= N` regardless of table sizes.
    pub constant: Option<u64>,
    /// `O <= c·Σ + d`, where `Σ` is the total rows scanned (one term per scan).
    pub sum: Option<Linear>,
    /// `O <= c·|T| + d` for each table `T` that bounds the output.
    pub tables: Vec<TableBound>,
}

impl fmt::Display for Bounds {
    /// The claims worth stating: a constant bound, or else the table bounds
    /// and the sum bound where it adds information.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut parts = vec![];
        if let Some(n) = self.constant {
            parts.push(format!("O <= {n}"));
        } else {
            for t in &self.tables {
                let op = if t.exact { "=" } else { "<=" };
                parts.push(format!(
                    "O {op} {}",
                    t.bound.render(&format!("|{}|", t.table))
                ));
            }
            // The sum bound adds information if it has a reducing factor, or if
            // no single table bounds the output.
            if let Some(s) = self.sum
                && (s.num < s.den || self.tables.is_empty())
            {
                parts.push(format!("O <= {}", s.render("Σ")));
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

    /// True if the constraints entail `claim`.
    fn proves(&self, claim: Bool) -> bool {
        self.solver.push();
        self.solver.assert(claim.not());
        let unsat = self.solver.check() == SatResult::Unsat;
        self.solver.pop(1);
        unsat
    }

    /// `den·O <= num·x + den·add`
    fn upper(&self, x: &Int, num: u64, den: u64, add: u64) -> Bool {
        let lhs = &self.output * Int::from_u64(den);
        let rhs = x * Int::from_u64(num) + Int::from_u64(den * add);
        lhs.le(rhs)
    }

    /// The smallest `N` with `O <= N`.
    pub(crate) fn constant(&self) -> Option<u64> {
        if !self.proves(self.output.le(Int::from_u64(CAP))) {
            return None;
        }
        Some(smallest(0, CAP, |n| {
            self.proves(self.output.le(Int::from_u64(n)))
        }))
    }

    /// The smallest `c`, then smallest `d`, with `O <= c·x + d`.
    pub(crate) fn linear(&self, x: &Int) -> Option<(Linear, bool)> {
        let candidates = coefficients();
        let feasible = |i: usize| {
            let (num, den) = candidates[i];
            self.proves(self.upper(x, num, den, CAP))
        };
        let last = candidates.len() - 1;
        if !feasible(last) {
            return None;
        }
        let i = smallest(0, last as u64, |i| feasible(i as usize)) as usize;
        let (num, den) = candidates[i];
        let add = smallest(0, CAP, |d| self.proves(self.upper(x, num, den, d)));
        let bound = Linear { num, den, add };
        // Also at least the bound?
        let lhs = &self.output * Int::from_u64(den);
        let rhs = x * Int::from_u64(num) + Int::from_u64(den * add);
        let exact = self.proves(lhs.ge(rhs));
        Some((bound, exact))
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
