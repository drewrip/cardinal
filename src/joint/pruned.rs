//! Which operators of an executed plan counted the rows their translation
//! computes, given what the engine pruned or stopped early.
//!
//! A runtime filter (from a join's other side) or an optional filter (one
//! the engine may or may not have applied) prunes a scan: its count is of
//! other rows than the translation's, which leaves both out. Each such
//! filter is *pending* until something above makes it moot: a join on its
//! column, which drops the rows it pruned anyway, or a filter checking the
//! same predicate. An operator's count is then:
//!
//! - its rows, if no filter pruned at or below it, or every one is moot;
//! - a floor, if only runtime filters are pending and every operator since
//!   keeps fewer rows for fewer input;
//! - nothing, otherwise, or if it may have stopped early ([`stopped`]).

use std::collections::BTreeSet;

use datafusion::common::JoinType;
use datafusion::common::tree_node::TreeNode;
use datafusion::logical_expr::Expr;
use datafusion::logical_expr::utils::split_conjunction_owned;

use crate::observed::{ObservedPlan, Op, Pred, base_table, column_key, requalify};

/// What an operator's count says of its translation's rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Count {
    /// Exactly its rows.
    Rows,
    /// At most its rows.
    Floor,
    /// Nothing.
    Unknown,
}

/// A filter that pruned an operator's rows, not yet moot.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Pending {
    /// A runtime filter on `table.column`, if known. `subset` while the rows
    /// are still among the translation's: every operator since keeps fewer
    /// rows for fewer input.
    Join { column: Option<String>, subset: bool },
    /// An optional filter pushed into a scan: the rows are the
    /// translation's, and maybe more. Its predicate's text, if it read.
    Filter { pred: Option<Key> },
}

/// An expression, compared by its text.
#[derive(Debug, Clone)]
struct Key(Expr);

impl PartialEq for Key {
    fn eq(&self, o: &Self) -> bool {
        self.0.to_string() == o.0.to_string()
    }
}
impl Eq for Key {}
impl PartialOrd for Key {
    fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for Key {
    fn cmp(&self, o: &Self) -> std::cmp::Ordering {
        self.0.to_string().cmp(&o.0.to_string())
    }
}

impl Pending {
    fn rename(&self, f: &dyn Fn(&str) -> Option<String>) -> Pending {
        match self {
            Pending::Join { column, subset } => Pending::Join {
                column: column.as_ref().map(|c| match c.rsplit_once('.') {
                    Some((r, n)) => format!("{}.{n}", f(r).unwrap_or_else(|| r.to_string())),
                    None => c.clone(),
                }),
                subset: *subset,
            },
            Pending::Filter { pred } => Pending::Filter { pred: pred.as_ref().map(|k| Key(requalify(&k.0, f))) },
        }
    }

    /// This filter, once the rows may no longer be among the translation's.
    fn loosened(self) -> Pending {
        match self {
            Pending::Join { column, .. } => Pending::Join { column, subset: false },
            p => p,
        }
    }
}

fn loosened(pending: BTreeSet<Pending>) -> BTreeSet<Pending> {
    pending.into_iter().map(Pending::loosened).collect()
}

/// Whether an operator's rows are its translation's.
#[derive(Debug, Clone, PartialEq, Eq)]
enum State {
    /// Exactly.
    Clean,
    /// Once the pending filters are moot.
    Pending(BTreeSet<Pending>),
    /// Not, or not knowably.
    Tainted,
}

impl State {
    fn with(pending: BTreeSet<Pending>) -> State {
        match pending.is_empty() {
            true => State::Clean,
            false => State::Pending(pending),
        }
    }

    fn pending(&self) -> BTreeSet<Pending> {
        match self {
            State::Pending(p) => p.clone(),
            _ => BTreeSet::new(),
        }
    }

    fn count(&self) -> Count {
        match self {
            State::Clean => Count::Rows,
            State::Pending(p) if p.iter().all(|p| matches!(p, Pending::Join { subset: true, .. })) => Count::Floor,
            _ => Count::Unknown,
        }
    }
}

/// What each operator of `plan`'s count says of its translation's rows,
/// by index. Uncounted operators get [`Count::Unknown`].
pub(crate) fn counts(plan: &ObservedPlan) -> Vec<Count> {
    let stopped = stopped(plan);
    let mut pruned = vec![false; plan.nodes.len()];
    for (j, n) in plan.nodes.iter().enumerate() {
        let own = match &n.op {
            Op::Scan { runtime_filters, filters, .. } => !runtime_filters.is_empty() || filters.iter().any(|f| f.optional),
            _ => false,
        };
        pruned[j] = own || n.children.iter().any(|&c| pruned[c]);
    }
    let states = states(plan);
    plan.nodes
        .iter()
        .enumerate()
        .map(|(j, n)| match () {
            _ if !n.counted || stopped[j] => Count::Unknown,
            _ if !pruned[j] => Count::Rows,
            _ => states[j].count(),
        })
        .collect()
}

/// Operators that may not have run to completion: below a `LIMIT`, the
/// probe side of a join that output nothing, and a scan that says it was
/// cut short.
fn stopped(plan: &ObservedPlan) -> Vec<bool> {
    let mut stopped = vec![false; plan.nodes.len()];
    for i in (0..plan.nodes.len()).rev() {
        let node = &plan.nodes[i];
        let stops = match &node.op {
            Op::Limit { .. } => node.children.clone(),
            // A join that keeps only matched probe rows and output none may
            // have stopped probing: its build side was empty, or had no key
            // that could match (all NULL).
            Op::Join { kind, .. } if (empty(&plan.nodes[node.children[1]]) || empty(node)) && !preserves_probe(*kind) => {
                vec![node.children[0]]
            }
            _ => vec![],
        };
        stopped[i] |= node.cut_short;
        // A reused result was materialized in full before it was read, and
        // a blocking operator read all of its input: a read cut short leaves
        // it whole.
        if matches!(node.op, Op::Reuse { .. }) || node.blocking {
            continue;
        }
        for c in node.children.iter().copied() {
            stopped[c] |= stopped[i] || stops.contains(&c);
        }
    }
    stopped
}

/// Whether `node` was counted, and output nothing.
fn empty(node: &crate::observed::ONode) -> bool {
    node.counted && node.rows == 0
}

/// Join kinds whose output includes probe-side rows without a match.
fn preserves_probe(kind: JoinType) -> bool {
    matches!(kind, JoinType::Left | JoinType::Full | JoinType::LeftAnti | JoinType::LeftMark)
}

/// The state of every operator of `plan`, by index.
fn states(plan: &ObservedPlan) -> Vec<State> {
    // The columns joined on above each operator. A runtime filter on a
    // column may come from any join on it, so only the highest makes it
    // moot.
    let mut above = vec![BTreeSet::<String>::new(); plan.nodes.len()];
    for i in (0..plan.nodes.len()).rev() {
        let mut keys = above[i].clone();
        if let Op::Join { on, .. } = &plan.nodes[i].op {
            keys.extend(join_keys(on));
        }
        for &c in &plan.nodes[i].children {
            above[c].extend(keys.iter().cloned());
        }
    }
    let stopped = stopped(plan);
    let mut states: Vec<State> = vec![];
    for (i, above) in above.iter().enumerate() {
        let inputs: Vec<State> = plan.nodes[i].children.iter().map(|&c| states[c].clone()).collect();
        let s = state(plan, i, &inputs, above, &stopped);
        states.push(s);
    }
    states
}

fn state(plan: &ObservedPlan, i: usize, inputs: &[State], above: &BTreeSet<String>, stopped: &[bool]) -> State {
    let node = &plan.nodes[i];
    if inputs.contains(&State::Tainted) {
        return State::Tainted;
    }
    match &node.op {
        Op::Scan { filters, runtime_filters, .. } => {
            let mut pending: BTreeSet<Pending> =
                runtime_filters.iter().map(|r| Pending::Join { column: r.column.clone(), subset: true }).collect();
            for p in filters.iter().filter(|p| p.optional) {
                pending.insert(Pending::Filter { pred: p.expr.clone().map(Key) });
            }
            State::with(pending)
        }
        Op::Project | Op::Sort => inputs[0].clone(),
        // A window's values are computed over the rows it reads: over pruned
        // rows, they are no values of the translation's rows.
        Op::Window => State::with(loosened(inputs[0].pending())),
        Op::Reuse { suffix, checked } => {
            let of = node.children[0];
            let (read, whole) = (node, &plan.nodes[of]);
            if stopped[of] || (*checked && read.counted && whole.counted && whole.rows != read.rows) {
                return State::Tainted;
            }
            let f = |r: &str| base_table(r).map(|_| format!("{r}{suffix}"));
            State::with(inputs[0].pending().iter().map(|p| p.rename(&f)).collect())
        }
        Op::Filter { predicate } => {
            let mut pending = inputs[0].pending();
            if pending.is_empty() {
                return State::Clean;
            }
            // A predicate that did not read, or reads a window's values,
            // computed over the pruned rows, may keep other rows.
            let reads = |p: &Pred| p.expr.as_ref().is_some_and(|e| !e.exists(|x| Ok(matches!(x, Expr::WindowFunction(_)))).unwrap_or(true));
            if !predicate.iter().all(reads) {
                return State::Tainted;
            }
            let checked: BTreeSet<Key> =
                predicate.iter().filter_map(|p| p.expr.clone()).flat_map(split_conjunction_owned).map(Key).collect();
            pending.retain(|p| !matches!(p, Pending::Filter { pred: Some(k) } if checked.contains(k)));
            State::with(pending)
        }
        // NOT IN keeps the rows that pruning would have dropped.
        Op::MarkFilter { negated } => {
            let pending = inputs[0].pending();
            State::with(if *negated { loosened(pending) } else { pending })
        }
        Op::Join { kind, on } => {
            let (lp, rp) = (inputs[0].pending(), inputs[1].pending());
            // Extra rows on a side give extra rows out only where the join
            // keeps more for more input: not on the other side of an anti
            // join, nor the padded side of an outer join, whose rows decide
            // which rows are padded.
            let (l_more, r_more) = match kind {
                JoinType::Inner | JoinType::LeftSemi | JoinType::RightSemi => (true, true),
                JoinType::LeftAnti | JoinType::Left => (true, false),
                JoinType::RightAnti | JoinType::Right => (false, true),
                _ => (false, false),
            };
            let loose = |p: &BTreeSet<Pending>| p.iter().any(|p| matches!(p, Pending::Filter { .. }));
            if (!l_more && loose(&lp)) || (!r_more && loose(&rp)) {
                return State::Tainted;
            }
            // Fewer rows on a side give a subset of the rows out only where
            // the join keeps fewer for fewer input: not on the padded side of
            // an outer join, where pruning adds padded rows, nor the other
            // side of an anti or mark join.
            let (l_sub, r_sub) = match kind {
                JoinType::Inner | JoinType::LeftSemi | JoinType::RightSemi => (true, true),
                JoinType::Left | JoinType::LeftAnti | JoinType::LeftMark => (true, false),
                JoinType::Right | JoinType::RightAnti | JoinType::RightMark => (false, true),
                JoinType::Full => (false, false),
            };
            let (lp, rp) = (if l_sub { lp } else { loosened(lp) }, if r_sub { rp } else { loosened(rp) });
            // The join makes moot the runtime filters on its keys, where the
            // rows they pruned are ones it would drop anyway.
            let mut pending: BTreeSet<Pending> = lp.union(&rp).cloned().collect();
            if matches!(kind, JoinType::Inner | JoinType::Right | JoinType::LeftSemi | JoinType::RightSemi | JoinType::RightAnti) {
                let keys = join_keys(on);
                pending.retain(|p| !matches!(p, Pending::Join { column: Some(c), .. } if keys.contains(c) && !above.contains(c)));
            }
            State::with(pending)
        }
        // Over pruned rows, groups and their values are no translation's.
        Op::Aggregate { .. } | Op::Union => match inputs.iter().all(|s| *s == State::Clean) {
            true => State::Clean,
            false => State::Tainted,
        },
        Op::Limit { .. } | Op::TopN { .. } | Op::Other => State::Tainted,
    }
}

/// The `table.column`s a join's condition reads.
fn join_keys(on: &[Pred]) -> BTreeSet<String> {
    on.iter()
        .filter_map(|p| p.expr.as_ref())
        .flat_map(|e| e.column_refs().into_iter().map(column_key).collect::<Vec<_>>())
        .collect()
}
