//! Facts: numbers known exactly from having watched queries run.
//!
//! An executed plan tells how many rows each operator output. Read against
//! the rows each operator consumed, those counts are facts about the data:
//! `|lineitem| = 60175`, `s(l_quantity < 10 | lineitem) = 10816/60175`, or
//! `ndv(l_suppkey | lineitem) = 100`. Each holds for one input [`Context`],
//! and [`derive_facts`] combines what several plans show into everything
//! that follows from it.

mod canonical;
mod context;
mod derive;
pub(crate) mod logical;
mod rules;

pub use context::{Context, Pending, State, Taint, Term, states};
pub use rules::{FactRule, Observation, RULES};

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::observed::ObservedPlan;
use context::join;

/// A non-negative rational, in lowest terms.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ratio {
    num: u64,
    den: u64,
}

impl Ratio {
    /// `num / den`; `None` if `den` is zero.
    pub fn new(num: u64, den: u64) -> Option<Ratio> {
        if den == 0 {
            return None;
        }
        let g = gcd(num, den);
        Some(Ratio { num: num / g, den: den / g })
    }

    pub fn int(n: u64) -> Ratio {
        Ratio { num: n, den: 1 }
    }

    pub fn num(&self) -> u64 {
        self.num
    }

    pub fn den(&self) -> u64 {
        self.den
    }

    pub fn as_f64(&self) -> f64 {
        self.num as f64 / self.den as f64
    }

    /// The value as an integer, if it is one.
    pub fn as_int(&self) -> Option<u64> {
        (self.den == 1).then_some(self.num)
    }

    pub fn times(self, o: Ratio) -> Option<Ratio> {
        let (a, b) = (gcd(self.num, o.den), gcd(o.num, self.den));
        let num = (self.num / a).checked_mul(o.num / b)?;
        let den = (self.den / b).checked_mul(o.den / a)?;
        Ratio::new(num, den)
    }

    pub fn over(self, o: Ratio) -> Option<Ratio> {
        self.times(Ratio::new(o.den, o.num)?)
    }

    pub fn plus(self, o: Ratio) -> Option<Ratio> {
        let g = gcd(self.den, o.den);
        let den = (self.den / g).checked_mul(o.den)?;
        let num = self.num.checked_mul(o.den / g)?.checked_add(o.num.checked_mul(self.den / g)?)?;
        Ratio::new(num, den)
    }

    /// `self − o`; `None` if negative.
    pub fn minus(self, o: Ratio) -> Option<Ratio> {
        let g = gcd(self.den, o.den);
        let den = (self.den / g).checked_mul(o.den)?;
        let num = self.num.checked_mul(o.den / g)?.checked_sub(o.num.checked_mul(self.den / g)?)?;
        Ratio::new(num, den)
    }
}

impl PartialOrd for Ratio {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Ratio {
    fn cmp(&self, o: &Self) -> std::cmp::Ordering {
        (self.num as u128 * o.den as u128).cmp(&(o.num as u128 * self.den as u128))
    }
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a.max(1)
}

impl fmt::Display for Ratio {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.den {
            1 => write!(f, "{}", self.num),
            _ => write!(f, "{}/{} ≈ {:.4}", self.num, self.den, self.as_f64()),
        }
    }
}

/// What a fact is the value of.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FactKind {
    /// `|ctx|`: the rows in a context.
    Cardinality(Context),
    /// `s(pred | over)`: the share of `over`'s rows satisfying `pred`.
    Selectivity { pred: BTreeSet<Term>, over: Context },
    /// `m(on | kept ⋉ other)`: the share of `kept`'s rows with a partner in
    /// `other` under `on`. A semi join keeps `m`, an anti join `1 − m`.
    Match { on: BTreeSet<Term>, kept: Context, other: Context },
    /// `ndv(keys | over)`: the distinct combinations of `keys` over `over`.
    Distinct { keys: BTreeSet<Term>, over: Context },
    /// `keys` take a different value in each of `over`'s rows. Its value is 1.
    Unique { keys: BTreeSet<Term>, over: Context },
}

impl fmt::Display for FactKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FactKind::Cardinality(c) => write!(f, "|{c}|"),
            FactKind::Selectivity { pred, over } => write!(f, "s({} | {over})", join(pred, " and ")),
            FactKind::Match { on, kept, other } => write!(f, "m({} | {kept} ⋉ {other})", join(on, " and ")),
            FactKind::Distinct { keys, over } => write!(f, "ndv({} | {over})", join(keys, ", ")),
            FactKind::Unique { keys, over } => write!(f, "unique({} | {over})", join(keys, ", ")),
        }
    }
}

/// Where a fact came from.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Origin {
    /// Read off operator `node` of plan `query` by `rule`.
    Observed { query: String, node: usize, rule: &'static str },
    /// Inferred from other facts by `rule`.
    Derived { rule: &'static str },
}

impl fmt::Display for Origin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Origin::Observed { query, node, rule } => write!(f, "{query}#{node} ({rule})"),
            Origin::Derived { rule } => write!(f, "derived ({rule})"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Fact {
    pub kind: FactKind,
    pub value: Ratio,
    pub origins: Vec<Origin>,
}

impl fmt::Display for Fact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.kind, self.value)
    }
}

/// Two values for the same fact: the data changed between runs, or a rule
/// is wrong.
#[derive(Debug, Clone)]
pub struct Conflict {
    pub kind: FactKind,
    pub values: (Ratio, Ratio),
    pub origins: (Vec<Origin>, Vec<Origin>),
}

/// Facts, one per kind.
#[derive(Debug, Clone, Default)]
pub struct FactSet {
    facts: BTreeMap<FactKind, Fact>,
    pub conflicts: Vec<Conflict>,
}

impl FactSet {
    /// Adds a fact, returning whether its kind is new. A different value for
    /// a known kind is recorded as a conflict and the first value kept.
    pub fn insert(&mut self, fact: Fact) -> bool {
        match self.facts.get_mut(&fact.kind) {
            None => {
                self.facts.insert(fact.kind.clone(), fact);
                true
            }
            Some(known) if known.value == fact.value => {
                for o in fact.origins {
                    if !known.origins.contains(&o) {
                        known.origins.push(o);
                    }
                }
                false
            }
            Some(known) => {
                let value = fact.value;
                if self.conflicts.iter().any(|c| c.kind == fact.kind && c.values.1 == value) {
                    return false;
                }
                self.conflicts.push(Conflict {
                    kind: fact.kind,
                    values: (known.value, fact.value),
                    origins: (known.origins.clone(), fact.origins),
                });
                false
            }
        }
    }

    /// Adds every fact the rules read off `plan`.
    pub fn observe(&mut self, plan: &ObservedPlan) {
        for fact in rules::observe(plan) {
            self.insert(fact);
        }
    }

    /// Adds everything that follows from the facts, until nothing new does.
    pub fn close(&mut self) {
        derive::close(self);
    }

    pub fn get(&self, kind: &FactKind) -> Option<&Fact> {
        self.facts.get(kind)
    }

    /// The fact printed as `text` (without its value), e.g. `|lineitem|`.
    pub fn find(&self, text: &str) -> Option<&Fact> {
        self.facts.values().find(|f| f.kind.to_string() == text)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Fact> {
        self.facts.values()
    }

    pub fn len(&self) -> usize {
        self.facts.len()
    }

    pub fn is_empty(&self) -> bool {
        self.facts.is_empty()
    }
}

impl fmt::Display for FactSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for fact in self.facts.values() {
            writeln!(f, "{fact}")?;
        }
        for c in &self.conflicts {
            writeln!(f, "CONFLICT {} = {} vs {}", c.kind, c.values.0, c.values.1)?;
        }
        Ok(())
    }
}

/// Every fact `plans` show, and every fact that follows from them.
pub fn derive_facts(plans: &[ObservedPlan]) -> FactSet {
    let mut set = FactSet::default();
    for p in plans {
        set.observe(p);
    }
    set.close();
    set
}
