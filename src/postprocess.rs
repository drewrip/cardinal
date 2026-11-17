//! Postprocess: simplifications of the constraints before solving.
//!
//! Runs last, after the [rules](crate::rules), [axioms](crate::axioms) and
//! [facts](crate::facts), when the bounds are searched for: facts arrive
//! after an analysis is built and change what its constraints need.
//!
//! # Dead columns
//!
//! Most constraints are about columns (`ndv`, `min`, `max`), and few of
//! those columns can move a row-count bound. A backward liveness analysis,
//! as in a compiler, finds the live ones, and the constraints over dead
//! ones are left out ([`Options::postprocess`](crate::Options::postprocess)).
//!
//! - **Input**: every assertion, each with its [`Role`], and the column
//!   variables it mentions.
//! - **Output**: the assertions to solve with: every one that mentions no
//!   column variable or only live ones, and every [`Role::Gen`].
//! - **Liveness**: a [`Role::Gen`]'s columns are live, and so are those of
//!   a [`Role::Flow`] that equates a row count with a column's (`X =
//!   ndv`), as some axioms between contexts do. Otherwise a
//!   [`Role::Flow`] makes the columns it mentions live if one of them is
//!   live, but never a column of a node above that one's: liveness flows
//!   from a node down to the inputs it reads. Per column: its `ndv`, `min`
//!   and `max` together.
//! - **Guarantees**: sound whatever is left out, since fewer constraints
//!   admit more models; a bound proven from them holds. Only tightness is
//!   at stake: a missing [`Role::Gen`] can loosen a bound.
//! - **Not done**: [`Analysis::constraints`](crate::Analysis::constraints),
//!   `validate` and checking facts use every assertion.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::analysis::Analyzer;

/// Simplifications of the constraints before solving. None by default.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Postprocess {
    /// Leave out constraints over columns that cannot bound a row count.
    pub dead_columns: bool,
}

/// How an assertion bears on which columns are live. Unlabeled assertions
/// are [`Role::Gen`], which keeps them and their columns.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    /// Its columns are live: it bounds a row count by them (`X ≤ Π ndv`,
    /// `X = ndv(key)`, a fact), or is not labeled. Always kept.
    Gen,
    /// Relates a node's columns to its inputs' or to each other: liveness
    /// flows through it. Kept if all its columns are live; a
    /// [`Role::Gen`] if it equates a row count with a column's.
    Flow,
    /// Bounds its columns by what they belong to. Kept if all its columns
    /// are live.
    Local,
}

/// Every assertion of an analysis, with what [`Postprocess`] reads of it.
#[derive(Debug, Clone)]
pub(crate) struct Assertions {
    index: Arc<Index>,
    smt: Vec<String>,
    roles: Vec<Role>,
    /// The columns each assertion mentions.
    columns: Vec<Vec<usize>>,
}

/// Each column's variables and node, and the plan's shape.
#[derive(Debug)]
struct Index {
    declarations: String,
    /// Every declared variable.
    declared: HashSet<String>,
    /// Each column variable's column.
    column: HashMap<String, usize>,
    /// Each column's node, if known.
    node: Vec<Option<usize>>,
    /// `above[a][b]`: node `b` is above node `a`, an ancestor of it.
    above: Vec<Vec<bool>>,
}

impl Assertions {
    /// The assertions of `a`, once its axioms are asserted, and its
    /// constraints as SMT-LIB.
    pub(crate) fn new(a: &Analyzer, constraints: &str) -> Assertions {
        let declarations: String = constraints
            .lines()
            .filter(|l| l.starts_with("(declare-"))
            .map(|l| format!("{l}\n"))
            .collect();
        let declared = declarations
            .lines()
            .filter_map(|l| l.split_whitespace().nth(1))
            .map(String::from)
            .collect();
        let mut column = HashMap::new();
        let mut node = vec![];
        for r in &a.relations {
            let n = r.frame.and_then(|f| a.frame_node.get(&f).copied());
            for j in 0..r.rel.ndv.len() {
                let vars = [
                    Some(&r.rel.ndv[j]),
                    r.rel.min[j].as_ref(),
                    r.rel.max[j].as_ref(),
                ];
                for v in vars.into_iter().flatten() {
                    column.insert(v.to_string(), node.len());
                }
                node.push(n);
            }
        }
        // A node's ancestors are its parents and theirs. Children come
        // before parents, so walking back finds the parents' first.
        let n = a.nodes.len();
        let mut parents = vec![vec![]; n];
        for (p, node) in a.nodes.iter().enumerate() {
            for &c in &node.inputs {
                parents[c].push(p);
            }
        }
        let mut above = vec![vec![false; n]; n];
        for c in (0..n).rev() {
            let mut row = vec![false; n];
            for &p in &parents[c] {
                row[p] = true;
                for (x, y) in row.iter_mut().zip(&above[p]) {
                    *x |= *y;
                }
            }
            above[c] = row;
        }
        let index = Arc::new(Index {
            declarations,
            declared,
            column,
            node,
            above,
        });
        let mut out = Assertions {
            index,
            smt: vec![],
            roles: vec![],
            columns: vec![],
        };
        for (b, &role) in a
            .solver
            .get_assertions()
            .iter()
            .zip(a.roles.borrow().iter())
        {
            out.push(b.to_string(), role);
        }
        out
    }

    /// Adds an assertion in SMT-LIB.
    pub(crate) fn push(&mut self, smt: String, role: Role) {
        let ix = &self.index;
        // The columns it mentions, and whether it mentions another variable:
        // a row count or a table's size.
        let (mut cols, mut count) = (vec![], false);
        for t in smt.split(|c: char| c.is_whitespace() || c == '(' || c == ')') {
            match ix.column.get(t) {
                Some(&c) => cols.push(c),
                None => count |= ix.declared.contains(t),
            }
        }
        cols.sort_unstable();
        cols.dedup();
        // `X = ndv`: a row count is a column's distinct count.
        let role = if role == Role::Flow && count && smt.starts_with("(= ") {
            Role::Gen
        } else {
            role
        };
        self.columns.push(cols);
        self.smt.push(smt);
        self.roles.push(role);
    }

    pub(crate) fn len(&self) -> usize {
        self.smt.len()
    }

    /// Which columns are live.
    fn live(&self) -> Vec<bool> {
        let ix = &self.index;
        // A column of no known node is live: nothing says where it flows.
        let mut live: Vec<bool> = ix.node.iter().map(Option::is_none).collect();
        let mut links: Vec<Vec<usize>> = vec![vec![]; live.len()];
        let mut work = vec![];
        for (cols, role) in self.columns.iter().zip(&self.roles) {
            match role {
                Role::Gen => work.extend(cols),
                Role::Flow => {
                    for &u in cols {
                        links[u].extend(cols.iter().filter(|&&v| v != u));
                    }
                }
                Role::Local => {}
            }
        }
        work.extend((0..live.len()).filter(|&c| live[c]));
        while let Some(c) = work.pop() {
            live[c] = true;
            for &d in &links[c] {
                // Never up: from a node to one of its ancestors.
                let up = matches!((ix.node[c], ix.node[d]), (Some(a), Some(b)) if ix.above[a][b]);
                if !live[d] && !up {
                    live[d] = true;
                    work.push(d);
                }
            }
        }
        live
    }

    /// Whether each assertion is solved with.
    pub(crate) fn kept(&self) -> Vec<bool> {
        let live = self.live();
        (0..self.len())
            .map(|i| self.roles[i] == Role::Gen || self.columns[i].iter().all(|&c| live[c]))
            .collect()
    }

    /// The assertions to solve with, as an SMT-LIB script, and how many.
    pub(crate) fn pruned(&self) -> (String, usize) {
        let mut out = self.index.declarations.clone();
        let mut n = 0;
        for (smt, kept) in self.smt.iter().zip(self.kept()) {
            if kept {
                out.push_str(&format!("(assert {smt})\n"));
                n += 1;
            }
        }
        (out, n)
    }
}
