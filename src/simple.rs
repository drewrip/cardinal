//! Which of a query's selectivities are *simple*: a share of the rows of
//! stored tables alone.
//!
//! A selectivity is a share of its operator's input, and an input is often
//! the output of other operators: a filtered table, a join, a GROUP BY. A
//! simple selectivity is one whose input is one stored table, whole or
//! filtered:
//!
//! - a filter's share of one table's rows, `s(p | T)`, or of the rows of a
//!   chain of filters over it, `s(p | T where q)`;
//! - a GROUP BY's or DISTINCT's distinct count per row of one table,
//!   `ndv(k | T) / |T|`.
//!
//! Only filters (and scans' pushed filters) may stand between a filter and
//! its table: an operator proven to keep its input's rows (below) does not.
//!
//! A join's share of pairs, or a semi join's of rows with a partner, is not
//! simple.
//!
//! An operator's rows are named as facts name them ([`Logical`]): views,
//! CTEs, subqueries, projections and aliases are seen through to the scans of
//! stored tables below them, and predicates and keys are read as expressions
//! over those tables' columns. Where that names an input as more than whole
//! tables, the constraints may still prove it holds the same rows as one:
//!
//! - a filter (or a scan's pushed filters) proven to keep every row is no
//!   condition on its rows;
//! - a semi or anti join proven to keep every row is no condition either;
//! - an inner join where each row of one side has exactly one partner (a key
//!   of the other side unique, or a foreign key, and the join provably as
//!   large as the side), or a left join where each preserved row has at most
//!   one, outputs that side's rows one for one. Where nothing above reads
//!   the other side's columns, the other side is dropped.
//!
//! And a join's share of pairs whose condition reads one table only is that
//! table's filter share: `s(p | T × U) = s(p | T)`.

use std::collections::BTreeSet;
use std::fmt;

use datafusion::common::{JoinType, NullEquality};
use datafusion::logical_expr::logical_plan::LogicalPlan;

use crate::analysis::Node;
use crate::rows::logical::Logical;
use crate::facts::{Context, FactKind, Term};
use crate::informed::kinds_in;
use crate::rows::first;
use crate::{Analysis, Error, Result};

/// What a simple selectivity is a share of.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SimpleKind {
    /// `s(p | T)`: the share of one table's rows satisfying a predicate, or
    /// `s(p | T where q)` of the rows of a chain of filters over it.
    Filter,
    /// `ndv(k | T) / |T|`: distinct values of keys per row of one table.
    Distinct,
}

impl fmt::Display for SimpleKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            SimpleKind::Filter => "filter",
            SimpleKind::Distinct => "distinct",
        })
    }
}

/// A selectivity over stored tables alone.
#[derive(Debug, Clone, PartialEq)]
pub struct Simple {
    pub kind: SimpleKind,
    /// The stored table it is a share of, whole or filtered.
    pub tables: Vec<String>,
    /// The fact that is its value, canonically named, over that table's
    /// rows: [`FactKind::Selectivity`] or [`FactKind::Distinct`] (whose value
    /// is over the table's size).
    pub fact: FactKind,
    /// What the constraints proved to name it over the tables, if more than
    /// seeing through views, CTEs and projections: each operator below it
    /// that keeps its input's rows one for one.
    pub proof: Vec<String>,
}

/// One required selectivity, and whether it is simple.
#[derive(Debug, Clone, PartialEq)]
pub struct SimpleSelectivity {
    /// The selectivity, by name.
    pub name: String,
    /// What it is over stored tables, or why it is not over them alone.
    pub simple: std::result::Result<Simple, String>,
}

impl fmt::Display for SimpleSelectivity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.simple {
            Ok(s) => {
                write!(f, "{} = {}: {} on {}", self.name, s.fact, s.kind, s.tables.join(", "))?;
                if !s.proof.is_empty() {
                    write!(f, " ({})", s.proof.join("; "))?;
                }
                Ok(())
            }
            Err(why) => write!(f, "{}: not simple ({why})", self.name),
        }
    }
}

/// Each selectivity `analysis` requires, and whether it is simple.
pub(crate) fn simple(analysis: &Analysis) -> Result<Vec<SimpleSelectivity>> {
    let Some(report) = &analysis.selectivity else {
        return Err(Error::Internal("simple selectivities need an analysis with selectivities".into()));
    };
    let (nodes, scans) = (&analysis.nodes, &analysis.scans);
    let plain = kinds_in(analysis, &Logical::new(nodes, scans));
    let same = one_for_one(analysis);
    let reduced = if same.iter().any(Option::is_some) {
        kinds_in(analysis, &Logical::reduced(nodes, scans, &same))
    } else {
        plain.clone()
    };
    let mut out = vec![];
    for (s, ((name, plain), (_, reduced))) in report.required.iter().zip(plain.into_iter().zip(reduced)) {
        let simple = match plain.and_then(|k| classify(&k, true)) {
            Ok(simple) => Ok(simple),
            Err(why) => match reduced.and_then(|k| classify(&k, false)) {
                Ok(mut simple) => {
                    let at = nodes.iter().position(|n| n.var == s.operator);
                    simple.proof = at.map_or(vec![], |at| proof(nodes, &same, at));
                    Ok(simple)
                }
                Err(_) => Err(why),
            },
        };
        out.push(SimpleSelectivity { name, simple });
    }
    Ok(out)
}

/// The fact `kind` (canonically named) as a simple selectivity, or why it is
/// not one. With `chain`, a filter's share of a table's filtered rows is
/// simple too.
fn classify(kind: &FactKind, chain: bool) -> std::result::Result<Simple, String> {
    let simple = |kind: SimpleKind, tables: Vec<&String>, fact: FactKind| Simple {
        kind,
        tables: tables.into_iter().map(|t| table(t).to_string()).collect(),
        fact,
        proof: vec![],
    };
    match kind {
        FactKind::Selectivity { over, .. } if chain && filtered(over).is_some() => {
            Ok(simple(SimpleKind::Filter, vec![filtered(over).unwrap()], kind.clone()))
        }
        FactKind::Selectivity { pred, over } => {
            let tables = whole(over)?;
            match &tables[..] {
                [t] => Ok(simple(SimpleKind::Filter, vec![t], kind.clone())),
                [t, u] => match (reads(pred, t), reads(pred, u)) {
                    (true, true) => Err("a join condition".into()),
                    // A condition on one side's rows: that side's share.
                    (true, false) | (false, true) => {
                        let t = if reads(pred, t) { t } else { u };
                        let fact = FactKind::Selectivity { pred: pred.clone(), over: Context::table(t) }.canonical();
                        let FactKind::Selectivity { over, .. } = &fact else { unreachable!() };
                        let t = whole(over)?[0].clone();
                        Ok(simple(SimpleKind::Filter, vec![&t], fact))
                    }
                    (false, false) => Err("a condition on no table".into()),
                },
                _ => Err(format!("over {} tables", tables.len())),
            }
        }
        FactKind::Match { .. } => Err("a semi join".into()),
        FactKind::Distinct { over, .. } => match &whole(over)?[..] {
            [t] => Ok(simple(SimpleKind::Distinct, vec![t], kind.clone())),
            tables => Err(format!("distinct over {} tables", tables.len())),
        },
        FactKind::Cardinality(_) => Err("a NOT IN".into()),
        FactKind::Unique { .. } => Err("a key".into()),
        FactKind::Min { .. } | FactKind::Max { .. } => Err("a least or greatest value".into()),
    }
}

/// The instances of `ctx`, if it is every row of their cross product.
fn whole(ctx: &Context) -> std::result::Result<Vec<String>, String> {
    match ctx {
        Context::Spj { tables, atoms, preds, exists } if atoms.is_empty() && preds.is_empty() && exists.is_empty() => {
            Ok(tables.iter().cloned().collect())
        }
        Context::Spj { atoms, exists, .. } => Err(match atoms.first() {
            Some(atom) => format!("over {atom}"),
            None if !exists.is_empty() => format!("over rows with a semi or anti join: {ctx}"),
            None => format!("over filtered rows: {ctx}"),
        }),
        Context::Derived { .. } => Err(format!("over {ctx}")),
    }
}

/// The instance of `ctx`, if it is the rows of one table satisfying some
/// predicates.
fn filtered(ctx: &Context) -> Option<&String> {
    match ctx {
        Context::Spj { tables, atoms, exists, .. } if tables.len() == 1 && atoms.is_empty() && exists.is_empty() => {
            tables.first()
        }
        _ => None,
    }
}

/// True if a term of `terms` reads a column of instance `instance`.
fn reads(terms: &BTreeSet<Term>, instance: &str) -> bool {
    terms
        .iter()
        .any(|t| t.expr.column_refs().iter().any(|c| c.relation.as_ref().is_some_and(|r| r.table() == instance)))
}

/// The stored table of canonical instance `instance` (`lineitem@2`).
fn table(instance: &str) -> &str {
    match instance.rsplit_once('@') {
        Some((t, k)) if k.parse::<usize>().is_ok() => t,
        _ => instance,
    }
}

/// For each node, `Some(k)` if it provably outputs input `k`'s rows one for
/// one (a raw scan's, for a scan): see [`Logical::reduced`].
fn one_for_one(analysis: &Analysis) -> Vec<Option<usize>> {
    let report = analysis.selectivity.as_ref().expect("checked by the caller");
    let card = |var: &str| report.operators.iter().rev().find(|(v, _)| v == var).map(|(_, c)| c);
    let nodes = &analysis.nodes;
    let mut out = vec![None; nodes.len()];
    for (i, node) in nodes.iter().enumerate() {
        let input = |k: usize| nodes[node.inputs[k]].var.as_str();
        // An operator the constraints do not determine names a new share,
        // so its formula is an input's only if they proved it has as many
        // rows. Formulas without a share are equal for any data.
        let kept = |input: &str| card(&node.var).is_some_and(|c| Some(c) == card(input));
        out[i] = match &node.plan {
            LogicalPlan::TableScan(scan) if scan.fetch.is_none() => match &node.raw_scan {
                Some((raw, _, _)) if kept(raw) => Some(0),
                _ => None,
            },
            LogicalPlan::Filter(f) if first::first_rows(f).is_none() && kept(input(0)) => Some(0),
            LogicalPlan::Join(join) => {
                let equi = !join.on.is_empty() && join.null_equality == NullEquality::NullEqualsNothing;
                let (left, right) = node.at_most_once;
                match join.join_type {
                    // Each row of a side has at most one partner, and the
                    // join has as many rows as the side: exactly one each.
                    JoinType::Inner if equi && left && kept(input(0)) => Some(0),
                    JoinType::Inner if equi && right && kept(input(1)) => Some(1),
                    JoinType::Left if equi && left => Some(0),
                    JoinType::Right if equi && right => Some(1),
                    // Every row kept.
                    JoinType::LeftSemi | JoinType::LeftAnti if !join.null_aware && kept(input(0)) => Some(0),
                    JoinType::RightSemi | JoinType::RightAnti if kept(input(1)) => Some(1),
                    _ => None,
                }
            }
            _ => None,
        };
    }
    out
}

/// What `same` proves of the operators below node `at`.
fn proof(nodes: &[Node], same: &[Option<usize>], at: usize) -> Vec<String> {
    // A dropped side's operators name nothing.
    let mut below = vec![];
    let mut stack: Vec<usize> = nodes[at].inputs.clone();
    while let Some(i) = stack.pop() {
        below.push(i);
        match (&nodes[i].plan, same[i]) {
            (LogicalPlan::Join(_), Some(k)) => stack.push(nodes[i].inputs[k]),
            _ => stack.extend(&nodes[i].inputs),
        }
    }
    below.sort();
    below
        .into_iter()
        .filter_map(|i| {
            let k = same[i]?;
            let node = &nodes[i];
            Some(match &node.plan {
                LogicalPlan::TableScan(scan) => {
                    format!("{}'s filters keep every row of {}", node.var, scan.table_name)
                }
                LogicalPlan::Filter(_) => format!("{} keeps every row", node.var),
                LogicalPlan::Join(join) if !matches!(join.join_type, JoinType::Inner | JoinType::Left | JoinType::Right) => {
                    format!("{} keeps every row of {}", node.var, nodes[node.inputs[k]].var)
                }
                _ => format!(
                    "{} keeps each row of {} once, and nothing reads {}",
                    node.var,
                    nodes[node.inputs[k]].var,
                    nodes[node.inputs[1 - k]].var
                ),
            })
        })
        .collect()
}
