//! What relating an analysis's contexts on egglog took and found
//! ([`crate::Options::egglog`]), for inspecting it.

use serde::{Deserialize, Serialize};

/// One run of egglog relating an analysis's contexts
/// ([`crate::Analysis::egglog`]).
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct EgglogStats {
    /// How far relevant contexts reach: `two steps` or `fixpoint`.
    pub reach: String,
    /// The distinct contexts with a quantity, encoded as terms.
    pub contexts: usize,
    /// Of those, the analysis's own operators' (the reach starts there).
    pub seeds: usize,
    /// Of those, the relevant ones: within reach of the seeds.
    pub reached: usize,
    /// Contexts with their instances renamed, to relate up to renaming.
    pub renamings: usize,
    /// Pairs of contexts over the same tables asked about, renamed or not.
    pub asked: usize,
    /// Predicate sets the rules asked Rust to compare, and how many cover.
    pub cover_checks: usize,
    pub covers: usize,
    /// Pairs related, between contexts in play: `a ⊆ b`, `|a| ≤ |b|`, and
    /// GROUP BY `a` with at most `b`'s groups.
    pub subset: usize,
    pub fewer: usize,
    pub groups_among: usize,
    /// Tuples in the e-graph once the contexts are in, and once saturated.
    pub nodes: usize,
    pub tuples: usize,
    /// Whether a fresh e-graph was made (large inputs), not the thread's.
    pub fresh_graph: bool,
    /// Seconds spent encoding, running the rules, and reading back.
    pub encode_secs: f64,
    pub saturate_secs: f64,
    pub extract_secs: f64,
    /// Saturating iterations, and how often each rule matched and its time,
    /// most matches first.
    pub iterations: usize,
    pub rules: Vec<RuleStats>,
}

/// One egglog rule's work in one run.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct RuleStats {
    /// The rule, as egglog names it (its text).
    pub rule: String,
    pub matches: usize,
    pub secs: f64,
}
