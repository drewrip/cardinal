//! What the analysis decides between contexts, recorded for the egglog
//! parity harness (`tests/egglog_parity.rs`): the contexts, the relations
//! between them, the relevant ones, and the axioms asserted. Not part of
//! the API.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Mutex;
use std::time::Duration;

use serde::{Deserialize, Serialize};

use crate::rows::{Context, Exists, ExistsKind, Term};

/// What one call of [`crate::analysis::Analyzer::between_contexts`] decided.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Snapshot {
    /// Every canonical context with a quantity, by [`key`].
    pub contexts: BTreeSet<String>,
    /// `(a, b)` with `a ⊆ b`, up to renaming `a`'s instances.
    pub subset: BTreeSet<(String, String)>,
    /// `(a, b)` with `|a| ≤ |b|`, up to renaming.
    pub fewer: BTreeSet<(String, String)>,
    /// `(a, b)` with GROUP BY `a` having no more groups than `b`, up to
    /// renaming.
    pub groups_among: BTreeSet<(String, String)>,
    /// The relevant contexts.
    pub relevant: BTreeSet<String>,
    /// Each axiom's claim, with the rules that gave it.
    pub axioms: BTreeMap<String, BTreeSet<String>>,
    pub timings: Timings,
    /// Tuples in the e-graph with the contexts, and once saturated.
    #[serde(default)]
    pub nodes: usize,
    #[serde(default)]
    pub tuples: usize,
}

/// Seconds spent, per stage.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Timings {
    /// Building the contexts and the space of their quantities.
    pub build: f64,
    /// Relating them: the relevant contexts and the axioms.
    pub between: f64,
    /// Of `between`, encoding the contexts into an e-graph.
    pub encode: f64,
    /// Of `between`, running the rules.
    pub saturate: f64,
    /// Of `between`, reading the relations back.
    pub extract: f64,
}

impl Timings {
    pub(crate) fn secs(d: Duration) -> f64 {
        d.as_secs_f64()
    }
}

static RECORDED: Mutex<Option<Vec<Snapshot>>> = Mutex::new(None);

/// Starts recording a [`Snapshot`] per analysis, dropping any recorded.
pub fn start() {
    *RECORDED.lock().unwrap() = Some(vec![]);
}

/// The snapshots recorded since [`start`]; stops recording.
pub fn take() -> Vec<Snapshot> {
    RECORDED.lock().unwrap().take().unwrap_or_default()
}

pub(crate) fn recording() -> bool {
    RECORDED.lock().unwrap().is_some()
}

pub(crate) fn push(s: Snapshot) {
    if let Some(v) = RECORDED.lock().unwrap().as_mut() {
        v.push(s);
    }
}

/// `c` as text that tells any two contexts apart: terms by their key, which
/// shows literals' types.
pub fn key(c: &Context) -> String {
    let mut out = String::new();
    write(c, &mut out);
    out
}

fn terms<'a>(ts: impl IntoIterator<Item = &'a Term>, out: &mut String) {
    out.push('[');
    for (i, t) in ts.into_iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        out.push_str(t.key());
    }
    out.push(']');
}

fn write(c: &Context, out: &mut String) {
    match c {
        Context::Spj { tables, atoms, preds, exists } => {
            out.push_str("spj(");
            out.push_str(&tables.iter().cloned().collect::<Vec<_>>().join(" "));
            out.push_str("; ");
            for a in atoms {
                write(a, out);
                out.push(' ');
            }
            out.push_str("; ");
            terms(preds, out);
            for Exists { kind, on, other } in exists {
                out.push_str(match kind {
                    ExistsKind::Semi => " semi",
                    ExistsKind::Anti => " anti",
                    ExistsKind::NotIn => " notin",
                });
                terms(on, out);
                out.push('(');
                write(other, out);
                out.push(')');
            }
            out.push(')');
        }
        Context::Derived { op, args, inputs } => {
            out.push_str(op);
            terms(args, out);
            out.push('(');
            for (i, x) in inputs.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write(x, out);
            }
            out.push(')');
        }
    }
}
