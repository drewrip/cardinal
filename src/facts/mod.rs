//! Facts: numbers known exactly from having watched queries run.
//!
//! An executed plan tells how many rows each operator output. Read against
//! the rows each operator consumed, those counts are facts about the data:
//! `|lineitem| = 60175`, `s(l_quantity < 10 | lineitem) = 10816/60175`, or
//! `ndv(l_suppkey | lineitem) = 100`. Each holds for one input [`Context`],
//! and [`derive_facts`] combines what several plans show into everything
//! that follows from it.
//!
//! # Notation
//!
//! Every rule and axiom is stated in these terms.
//!
//! - `C`, `D`: [`Context`]s, sets of rows named by how they derive from the
//!   base tables. An *SPJ* ([`Context::Spj`]) is the cross product of its
//!   tables and atoms, filtered by its predicates and its semi and anti join
//!   conditions ([`Exists`]); any other operator's rows are
//!   [`Context::Derived`]. Two SPJs have the *same inputs* if they have the
//!   same tables and atoms, and the *same inputs and conditions* if their
//!   conditions match too.
//! - `C ∧ P`: `C` with the predicates `P` added ([`Context::filter`]).
//! - `|C|`: how many rows `C` has.
//! - `s(P | C)`: the share of `C`'s rows satisfying `P`, `|C ∧ P| / |C|`.
//! - `m(on | K ⋉ O)`: the share of `K`'s rows with a partner in `O` under
//!   `on`. A semi join keeps `m·|K|` rows, an anti join `(1 − m)·|K|`.
//! - `ndv(K | C)`: the distinct combinations of keys `K` in `C`'s rows,
//!   NULL counting as a value. `unique(K | C)`: `ndv(K | C) = |C|`.
//! - `min(k | C)`, `max(k | C)`: the least and greatest non-NULL value of
//!   `k` in `C`'s rows, as an integer.
//!
//! These are [`FactKind`]s. A *fact* gives one its exact value, a *bound* an
//! upper limit and a *floor* a lower one ([`FactSet`] keeps all three). A
//! *quantity* is a kind among `|C|`, `ndv`, `min` and `max`: what the store
//! hands to Z3.
//!
//! # Pipeline
//!
//! Three sets of rules turn executed plans into constraints on a query:
//!
//! ```text
//!  ObservedPlan ─[observe]─▶ FactSet ─[derive]─▶ closed FactSet ─▶ Analysis::with_facts
//!                              facts   = v
//!                              bounds  ≤ v
//!                              floors  ≥ v
//!                              unobserved
//!                                │
//!                                └─[axioms]─▶ Analysis::with_store ─▶ Grounded
//! ```
//!
//! 1. [`observe`] reads each operator of one executed plan
//!    ([`FactSet::observe`], and [`FactSet::observe_translated`] for the
//!    rows only a query names). Out come facts, bounds, floors, and the kinds
//!    of operators whose rows were not counted ([`FactSet::unobserved`]),
//!    which a query can count ([`FactKind::counted`]).
//! 2. [`derive`](mod@derive) combines exact facts across plans until nothing new follows
//!    ([`FactSet::close`]): a size from one plan over a size from another is
//!    a selectivity. Bounds and floors are carried along unchanged; one that
//!    an exact fact contradicts is recorded in [`FactSet::conflicts`], as is
//!    a second value for one fact. [`Analysis::with_facts`] substitutes the
//!    closed set's selectivities into the query's formula.
//! 3. [`axioms`](crate::axioms), asserted in every analysis, also relate
//!    the facts' rows to the query's rows inside Z3
//!    ([`Analysis::with_store`]), taking the facts as observed. Each
//!    fact, bound and floor on a quantity becomes a tracked claim on a Z3
//!    term; the axioms relating the terms are asserted untracked. Claims in
//!    a contradiction are dropped ([`Grounded::rejected`](crate::Grounded::rejected)),
//!    and the rest join the query's constraints for the bounds search.
//!
//! Each fact records the rule it came from ([`Origin`]), and
//! [`Grounded::axioms`](crate::Grounded::axioms) counts axioms by rule: the
//! name is the heading of its spec in [`observe`], [`derive`](mod@derive) or [`axioms`](crate::axioms).
//!
//! [`Analysis::with_facts`]: crate::Analysis::with_facts
//! [`Analysis::with_store`]: crate::Analysis::with_store

pub mod derive;
pub mod observe;
mod sql;
mod state;
pub(crate) mod store;

pub use crate::rows::{Context, Exists, ExistsKind, Term};
pub use state::{Pending, State, Taint, Value, states};
pub use observe::{FactRule, Observation, RULES};
pub use sql::{CountDialect, Counts};

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::Options;
use crate::observed::{Catalog, ObservedPlan};
use crate::rows::join;

/// A non-negative rational, in lowest terms.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(try_from = "RawRatio")]
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

/// A ratio as read, before it is checked and reduced.
#[derive(Deserialize)]
struct RawRatio {
    num: u64,
    den: u64,
}

impl TryFrom<RawRatio> for Ratio {
    type Error = &'static str;

    fn try_from(r: RawRatio) -> Result<Ratio, Self::Error> {
        Ratio::new(r.num, r.den).ok_or("a ratio over zero")
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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
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
    /// `min(key | over)`: the least non-NULL value of `key` in `over`'s
    /// rows, an integer (a date as days). Known only by its bounds so far.
    Min { key: Term, over: Context },
    /// `max(key | over)`: the greatest.
    Max { key: Term, over: Context },
}

impl FactKind {
    /// This fact, with the value its queries counted ([`Counts`]): `value`,
    /// and for a share or a uniqueness, `of`. `None` if they give it no
    /// value: a share of no rows, or keys that are not unique.
    pub fn counted(&self, value: u64, of: Option<u64>) -> Option<Fact> {
        let value = match (self, of) {
            (FactKind::Cardinality(_) | FactKind::Distinct { .. } | FactKind::Min { .. } | FactKind::Max { .. }, _) => {
                Ratio::int(value)
            }
            (FactKind::Unique { .. }, Some(of)) if value == of => Ratio::int(1),
            (FactKind::Selectivity { .. } | FactKind::Match { .. }, Some(of)) => Ratio::new(value, of)?,
            _ => return None,
        };
        Some(Fact { kind: self.clone(), value, origins: vec![Origin::Counted] })
    }
}

impl fmt::Display for FactKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FactKind::Cardinality(c) => write!(f, "|{c}|"),
            FactKind::Selectivity { pred, over } => write!(f, "s({} | {over})", join(pred, " and ")),
            FactKind::Match { on, kept, other } => write!(f, "m({} | {kept} ⋉ {other})", join(on, " and ")),
            FactKind::Distinct { keys, over } => write!(f, "ndv({} | {over})", join(keys, ", ")),
            FactKind::Unique { keys, over } => write!(f, "unique({} | {over})", join(keys, ", ")),
            FactKind::Min { key, over } => write!(f, "min({key} | {over})"),
            FactKind::Max { key, over } => write!(f, "max({key} | {over})"),
        }
    }
}

/// Where a fact came from.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Origin {
    /// Read off operator `node` of plan `query` by `rule`.
    Observed { query: String, node: usize, rule: Cow<'static, str> },
    /// Inferred from other facts by `rule`.
    Derived { rule: Cow<'static, str> },
    /// Counted by a query of its own (see [`FactKind::counted`]).
    Counted,
}

impl fmt::Display for Origin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Origin::Observed { query, node, rule } => write!(f, "{query}#{node} ({rule})"),
            Origin::Derived { rule } => write!(f, "derived ({rule})"),
            Origin::Counted => write!(f, "counted"),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
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
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Conflict {
    pub kind: FactKind,
    pub values: (Ratio, Ratio),
    pub origins: (Vec<Origin>, Vec<Origin>),
}

/// Facts, one per kind, and upper and lower bounds on what no fact gives
/// exactly.
///
/// Serde writes each map as the list of its values, and reads a list back
/// as [`FactSet::insert`], [`FactSet::insert_bound`],
/// [`FactSet::insert_floor`] and [`FactSet::insert_value`] would add it.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(default)]
pub struct FactSet {
    #[serde(serialize_with = "serialize_values", deserialize_with = "facts")]
    facts: BTreeMap<FactKind, Fact>,
    /// The least upper bound seen on each size, distinct count or greatest
    /// value: the rows of an operator that may have let through more than
    /// its context's, or the values a runtime filter let through.
    #[serde(serialize_with = "serialize_values", deserialize_with = "bounds")]
    bounds: BTreeMap<FactKind, Fact>,
    /// The greatest lower bound seen on each size, distinct count or least
    /// value: the rows of an operator that may have kept fewer than its
    /// context's, or the values a runtime filter let through.
    #[serde(serialize_with = "serialize_values", deserialize_with = "floors")]
    floors: BTreeMap<FactKind, Fact>,
    /// What each aggregate value the facts read is, by name.
    #[serde(serialize_with = "serialize_values", deserialize_with = "values")]
    values: BTreeMap<String, Value>,
    /// The facts of operators whose rows were not counted.
    unobserved: BTreeSet<FactKind>,
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

    /// Adds an upper bound, keeping the least known. A bound below the
    /// exact value is recorded as a conflict.
    pub fn insert_bound(&mut self, bound: Fact) {
        match self.bounds.get_mut(&bound.kind) {
            Some(known) if known.value < bound.value => {}
            Some(known) if known.value == bound.value => {
                for o in bound.origins {
                    if !known.origins.contains(&o) {
                        known.origins.push(o);
                    }
                }
            }
            _ => {
                self.bounds.insert(bound.kind.clone(), bound);
            }
        }
    }

    /// Adds a lower bound, keeping the greatest known. A floor above the
    /// exact value is recorded as a conflict.
    pub fn insert_floor(&mut self, floor: Fact) {
        match self.floors.get_mut(&floor.kind) {
            Some(known) if known.value > floor.value => {}
            Some(known) if known.value == floor.value => {
                for o in floor.origins {
                    if !known.origins.contains(&o) {
                        known.origins.push(o);
                    }
                }
            }
            _ => {
                self.floors.insert(floor.kind.clone(), floor);
            }
        }
    }

    /// Adds every fact and bound the rules read off `plan`, and notes the
    /// facts it could not give a value (see [`FactSet::unobserved`]).
    pub fn observe(&mut self, plan: &ObservedPlan) {
        let observed = observe::observe(plan);
        for fact in observed.facts {
            self.insert(fact);
        }
        for bound in observed.bounds {
            self.insert_bound(bound);
        }
        for floor in observed.floors {
            self.insert_floor(floor);
        }
        for value in observed.values {
            self.insert_value(value);
        }
        self.unobserved.extend(observed.unobserved);
    }

    /// Adds the facts `plan`'s counts give the rows of its operators as a
    /// query names them, once translated with `catalog` (see
    /// [rule `translated`](observe#translated)): rows the rules may not name. A plan that does not
    /// translate adds none.
    pub fn observe_translated(&mut self, catalog: &Catalog, plan: &ObservedPlan, options: &Options) {
        for (fact, floor) in observe::observe_translated(catalog, plan, options) {
            if floor {
                self.insert_floor(fact);
            } else {
                self.insert(fact);
            }
        }
    }

    /// The facts the observed plans have and did not count, that nothing
    /// here gives either: of operators an engine stopped early or ran
    /// several times, and of every operator of a plan that was not run.
    /// Each is of rows its plan names, so a query can count it
    /// ([`FactKind::count_sql_in`]), and its count be added
    /// ([`FactKind::counted`], then [`FactSet::insert`] and
    /// [`FactSet::close`]).
    pub fn unobserved(&self) -> impl Iterator<Item = &FactKind> {
        self.unobserved.iter().filter(|k| !self.facts.contains_key(*k))
    }

    /// Adds everything that follows from the facts, until nothing new does.
    pub fn close(&mut self) {
        derive::close(self);
        self.check_bounds();
    }

    pub fn get(&self, kind: &FactKind) -> Option<&Fact> {
        self.facts.get(kind)
    }

    /// Records what an aggregate value is. A name says what it is, so two
    /// definitions of one name agree.
    pub fn insert_value(&mut self, value: Value) {
        self.values.entry(value.name.clone()).or_insert(value);
    }

    /// What the value read as `"value"."{name}"` is.
    pub fn value(&self, name: &str) -> Option<&Value> {
        self.values.get(name)
    }

    pub fn values(&self) -> impl Iterator<Item = &Value> {
        self.values.values()
    }

    /// The least upper bound known on `kind`, a size or distinct count.
    pub fn bound(&self, kind: &FactKind) -> Option<&Fact> {
        self.bounds.get(kind)
    }

    pub fn bounds(&self) -> impl Iterator<Item = &Fact> {
        self.bounds.values()
    }

    /// The greatest lower bound known on `kind`, a size.
    pub fn floor(&self, kind: &FactKind) -> Option<&Fact> {
        self.floors.get(kind)
    }

    pub fn floors(&self) -> impl Iterator<Item = &Fact> {
        self.floors.values()
    }

    /// Records as a conflict each bound below its kind's exact value, and
    /// each floor above it: the rows were named wrongly, or the data
    /// changed.
    fn check_bounds(&mut self) {
        let bounds = self.bounds.iter().map(|b| (b, std::cmp::Ordering::Greater));
        let floors = self.floors.iter().map(|f| (f, std::cmp::Ordering::Less));
        for ((kind, bound), wrong) in bounds.chain(floors) {
            if let Some(exact) = self.facts.get(kind)
                && exact.value.cmp(&bound.value) == wrong
                && !self.conflicts.iter().any(|c| c.kind == *kind && c.values == (exact.value, bound.value))
            {
                self.conflicts.push(Conflict {
                    kind: kind.clone(),
                    values: (exact.value, bound.value),
                    origins: (exact.origins.clone(), bound.origins.clone()),
                });
            }
        }
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
        for bound in self.bounds.values() {
            writeln!(f, "{} <= {}", bound.kind, bound.value)?;
        }
        for floor in self.floors.values() {
            writeln!(f, "{} >= {}", floor.kind, floor.value)?;
        }
        for c in &self.conflicts {
            writeln!(f, "CONFLICT {} = {} vs {}", c.kind, c.values.0, c.values.1)?;
        }
        Ok(())
    }
}

fn facts<'de, D: Deserializer<'de>>(d: D) -> Result<BTreeMap<FactKind, Fact>, D::Error> {
    let mut set = FactSet::default();
    for fact in Vec::<Fact>::deserialize(d)? {
        set.insert(fact);
    }
    Ok(set.facts)
}

fn bounds<'de, D: Deserializer<'de>>(d: D) -> Result<BTreeMap<FactKind, Fact>, D::Error> {
    let mut set = FactSet::default();
    for bound in Vec::<Fact>::deserialize(d)? {
        set.insert_bound(bound);
    }
    Ok(set.bounds)
}

fn floors<'de, D: Deserializer<'de>>(d: D) -> Result<BTreeMap<FactKind, Fact>, D::Error> {
    let mut set = FactSet::default();
    for floor in Vec::<Fact>::deserialize(d)? {
        set.insert_floor(floor);
    }
    Ok(set.floors)
}

fn values<'de, D: Deserializer<'de>>(d: D) -> Result<BTreeMap<String, Value>, D::Error> {
    let mut set = FactSet::default();
    for value in Vec::<Value>::deserialize(d)? {
        set.insert_value(value);
    }
    Ok(set.values)
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

/// A map's values, written as a list.
fn serialize_values<K, V: Serialize, S: Serializer>(m: &BTreeMap<K, V>, s: S) -> Result<S::Ok, S::Error> {
    s.collect_seq(m.values())
}
