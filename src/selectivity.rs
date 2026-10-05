//! An exact formula for a query's output cardinality, in terms of table sizes
//! and operator selectivities.
//!
//! Where `bounds` proves inequalities, this names what is unknown. Each
//! operator that keeps a data-dependent share of its input gets a selectivity
//! `s` in `0..=1`, with the predicate or expressions it depends on, and its
//! output cardinality is written as `s` times its input's. The root's formula
//! then gives the exact output cardinality once every selectivity it mentions
//! is known. The constraint set is used to prove a static range for each
//! selectivity, and to drop those whose operator it already determines.

use std::collections::HashMap;
use std::fmt;

use datafusion::common::{Column, JoinType};
use datafusion::logical_expr::logical_plan::{Distinct, FetchType, Join, LogicalPlan, SkipType};
use datafusion::logical_expr::utils::conjunction;
use datafusion::logical_expr::Expr;

use crate::analyzer::Node;
use crate::bounds::Search;
use crate::{Error, Result};

/// A cardinality as an expression over table sizes and selectivities.
#[derive(Debug, Clone, PartialEq)]
pub enum Card {
    Const(u64),
    /// The row count of a base table, by name.
    Table(String),
    /// A selectivity, by name.
    Sel(String),
    /// The cardinality of an operator with no formula (a table function,
    /// `UNNEST`, a recursive CTE, ...), by variable name. It is an unknown of
    /// its own, and not a fraction.
    Operator(String),
    Mul(Vec<Card>),
    Add(Vec<Card>),
    /// `1 - s`
    Not(Box<Card>),
    Min(Box<Card>, Box<Card>),
    Max(Box<Card>, Box<Card>),
    /// `c - k`, which may be negative.
    Sub(Box<Card>, u64),
}

impl Card {
    fn mul(parts: Vec<Card>) -> Card {
        let mut constant: u64 = 1;
        let mut out = vec![];
        let mut stack: Vec<Card> = parts.into_iter().rev().collect();
        while let Some(p) = stack.pop() {
            match p {
                Card::Const(n) => constant = constant.saturating_mul(n),
                Card::Mul(ps) => stack.extend(ps.into_iter().rev()),
                p => out.push(p),
            }
        }
        if constant == 0 {
            return Card::Const(0);
        }
        // Selectivities first, then sizes, each in plan order.
        out.sort_by_key(|p| !matches!(p, Card::Sel(_) | Card::Not(_)));
        if constant != 1 || out.is_empty() {
            out.insert(0, Card::Const(constant));
        }
        if out.len() == 1 { out.remove(0) } else { Card::Mul(out) }
    }

    fn add(parts: Vec<Card>) -> Card {
        let mut constant: u64 = 0;
        let mut out = vec![];
        let mut stack: Vec<Card> = parts.into_iter().rev().collect();
        while let Some(p) = stack.pop() {
            match p {
                Card::Const(n) => constant = constant.saturating_add(n),
                Card::Add(ps) => stack.extend(ps.into_iter().rev()),
                p => out.push(p),
            }
        }
        if constant != 0 || out.is_empty() {
            out.push(Card::Const(constant));
        }
        if out.len() == 1 { out.remove(0) } else { Card::Add(out) }
    }

    fn min(a: Card, b: Card) -> Card {
        match (a, b) {
            (Card::Const(x), Card::Const(y)) => Card::Const(x.min(y)),
            (Card::Const(0), _) | (_, Card::Const(0)) => Card::Const(0),
            (a, b) => Card::Min(Box::new(a), Box::new(b)),
        }
    }

    /// `max(self - k, 0)`
    fn minus(self, k: u64) -> Card {
        match (self, k) {
            (c, 0) => c,
            (Card::Const(n), k) => Card::Const(n.saturating_sub(k)),
            (c, k) => Card::Max(Box::new(Card::Sub(Box::new(c), k)), Box::new(Card::Const(0))),
        }
    }

    /// Calls `f` on every leaf.
    fn leaves<'a>(&'a self, f: &mut dyn FnMut(&'a Card)) {
        match self {
            Card::Const(_) | Card::Table(_) | Card::Sel(_) | Card::Operator(_) => f(self),
            Card::Mul(ps) | Card::Add(ps) => ps.iter().for_each(|p| p.leaves(f)),
            Card::Not(c) | Card::Sub(c, _) => c.leaves(f),
            Card::Min(a, b) | Card::Max(a, b) => {
                a.leaves(f);
                b.leaves(f);
            }
        }
    }

    /// The range of values this takes as its leaves range over `leaf`'s.
    fn eval(&self, leaf: &dyn Fn(&Card) -> Result<Interval>) -> Result<Interval> {
        // 0 · ∞ = 0: a product with no rows on one side has none.
        let times = |a: f64, b: f64| if a == 0.0 || b == 0.0 { 0.0 } else { a * b };
        Ok(match self {
            Card::Const(n) => Interval::point(*n as f64),
            Card::Table(_) | Card::Sel(_) | Card::Operator(_) => leaf(self)?,
            Card::Mul(ps) => {
                let mut out = Interval::point(1.0);
                for p in ps {
                    let i = p.eval(leaf)?;
                    out = Interval {
                        lo: times(out.lo, i.lo),
                        hi: times(out.hi, i.hi),
                    };
                }
                out
            }
            Card::Add(ps) => {
                let mut out = Interval::point(0.0);
                for p in ps {
                    let i = p.eval(leaf)?;
                    out = Interval {
                        lo: out.lo + i.lo,
                        hi: out.hi + i.hi,
                    };
                }
                out
            }
            Card::Not(c) => {
                let i = c.eval(leaf)?;
                Interval {
                    lo: 1.0 - i.hi,
                    hi: 1.0 - i.lo,
                }
            }
            Card::Min(a, b) => {
                let (a, b) = (a.eval(leaf)?, b.eval(leaf)?);
                Interval {
                    lo: a.lo.min(b.lo),
                    hi: a.hi.min(b.hi),
                }
            }
            Card::Max(a, b) => {
                let (a, b) = (a.eval(leaf)?, b.eval(leaf)?);
                Interval {
                    lo: a.lo.max(b.lo),
                    hi: a.hi.max(b.hi),
                }
            }
            Card::Sub(c, k) => {
                let i = c.eval(leaf)?;
                Interval {
                    lo: i.lo - *k as f64,
                    hi: i.hi - *k as f64,
                }
            }
        })
    }
}

impl fmt::Display for Card {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let join = |ps: &[Card], sep: &str, parens: bool| {
            ps.iter()
                .map(|p| match p {
                    Card::Add(_) if parens => format!("({p})"),
                    _ => p.to_string(),
                })
                .collect::<Vec<_>>()
                .join(sep)
        };
        match self {
            Card::Const(n) => write!(f, "{n}"),
            Card::Table(t) => write!(f, "|{t}|"),
            Card::Sel(s) => write!(f, "{s}"),
            Card::Operator(v) => write!(f, "|{v}|"),
            Card::Mul(ps) => write!(f, "{}", join(ps, "·", true)),
            Card::Add(ps) => write!(f, "{}", join(ps, " + ", false)),
            Card::Not(c) => write!(f, "(1 - {c})"),
            Card::Min(a, b) => write!(f, "min({a}, {b})"),
            Card::Max(a, b) => write!(f, "max({a}, {b})"),
            Card::Sub(c, k) => write!(f, "{c} - {k}"),
        }
    }
}

/// A closed range of values.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Interval {
    pub lo: f64,
    pub hi: f64,
}

impl Interval {
    fn point(x: f64) -> Self {
        Interval { lo: x, hi: x }
    }

    /// The value, if the range holds just one.
    pub fn exact(&self) -> Option<f64> {
        (self.lo == self.hi).then_some(self.lo)
    }

    /// True if `x` is in the range, up to rounding.
    pub fn contains(&self, x: f64) -> bool {
        let slack = 1e-9 * x.abs().max(1.0);
        self.lo - slack <= x && x <= self.hi + slack
    }
}

impl fmt::Display for Interval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}, {}]", self.lo, self.hi)
    }
}

/// What a selectivity is the selectivity of.
#[derive(Debug, Clone, PartialEq)]
pub enum Kind {
    /// `s(p)`: the share of the input's rows on which predicate `p` is true.
    Filter(Expr),
    /// The number of distinct combinations of these expressions over the
    /// input's rows, per input row: the groups of a GROUP BY, or the rows of a
    /// DISTINCT.
    Distinct(Vec<Expr>),
    /// The share of the pairs of rows of the two inputs that satisfy the join
    /// condition.
    Join {
        on: Vec<(Expr, Expr)>,
        filter: Option<Expr>,
    },
    /// The share of one input's rows (the left's if `left`) that satisfy the
    /// join condition with at least one row of the other input.
    Match {
        on: Vec<(Expr, Expr)>,
        filter: Option<Expr>,
        left: bool,
    },
    /// The share of the left input's rows a `NOT IN` keeps: none if a key of
    /// the right input is NULL, else those whose key is not NULL and matches
    /// no row.
    NotIn {
        on: Vec<(Expr, Expr)>,
        filter: Option<Expr>,
    },
    /// The share of the input's rows kept by a limit that is not a literal.
    Limit,
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list = |es: &[Expr]| {
            es.iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        };
        let condition = |on: &[(Expr, Expr)], filter: &Option<Expr>| {
            let parts = on
                .iter()
                .map(|(a, b)| format!("{a} = {b}"))
                .chain(filter.iter().map(|e| e.to_string()))
                .collect::<Vec<_>>();
            if parts.is_empty() {
                "true".to_string()
            } else {
                parts.join(" AND ")
            }
        };
        match self {
            Kind::Filter(p) => write!(f, "s({p})"),
            Kind::Distinct(es) => write!(f, "distinct({})", list(es)),
            Kind::Join { on, filter } => write!(f, "join({})", condition(on, filter)),
            Kind::Match { on, filter, .. } => write!(f, "matched({})", condition(on, filter)),
            Kind::NotIn { on, filter } => write!(f, "not_in({})", condition(on, filter)),
            Kind::Limit => write!(f, "limit"),
        }
    }
}

/// One operator's selectivity: a number in `0..=1` that depends on the data.
#[derive(Debug, Clone, PartialEq)]
pub struct Selectivity {
    /// The name formulas use for it, e.g. `s3`.
    pub name: String,
    /// The variable of the operator it belongs to.
    pub operator: String,
    /// The predicate or expressions it depends on.
    pub kind: Kind,
    /// The operators whose rows it is a share of: one input, or for
    /// [`Kind::Join`] the two inputs whose pairs of rows it is a share of.
    pub over: Vec<String>,
    /// The range it provably lies in, whatever the data.
    pub range: Interval,
    /// The count that, divided by the row counts of `over`, measures it: the
    /// operator's own variable, or an auxiliary count from `validate`.
    measure: String,
}

impl fmt::Display for Selectivity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} = {} over {}, in {}",
            self.name,
            self.kind,
            self.over.join(" × "),
            self.range
        )
    }
}

/// The output cardinality of a query as a formula, and the selectivities
/// needed to compute it.
#[derive(Debug, Clone, PartialEq)]
pub struct SelectivityReport {
    /// The output cardinality `X`.
    pub output: Card,
    /// The selectivities `output` mentions, in plan order. With a value for
    /// each (and for each [`Card::Operator`]), `output` is the exact count.
    pub required: Vec<Selectivity>,
    /// Selectivities that are not needed: their operator's cardinality is
    /// proven to be zero or one of its inputs' whatever their value.
    pub resolved: Vec<Selectivity>,
    /// Every operator's cardinality, by variable name, children before parents.
    pub operators: Vec<(String, Card)>,
    /// Every selectivity `operators` mentions.
    all: Vec<Selectivity>,
}

/// Result of checking a [`SelectivityReport`] against a real execution.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct SelectivityCheck {
    /// The measured value of every selectivity that could be measured, by name.
    pub values: HashMap<String, f64>,
    /// The first selectivity outside its proven range, or operator whose
    /// formula does not give its actual row count. `None` means every formula
    /// reproduced the execution.
    pub violation: Option<String>,
}

impl SelectivityReport {
    /// True if `output` has no unknowns: the output cardinality is a function
    /// of the table sizes alone.
    pub fn is_exact(&self) -> bool {
        let mut exact = true;
        self.output
            .leaves(&mut |c| exact &= !matches!(c, Card::Sel(_) | Card::Operator(_)));
        exact
    }

    /// The output cardinality given each table's row count and a value for
    /// some of the unknowns, by selectivity name or operator variable. A
    /// selectivity without a value ranges over its proven range, and an
    /// operator without one over every count, so the result is a single value
    /// only if every unknown of `output` has one.
    pub fn evaluate(
        &self,
        tables: &HashMap<String, u64>,
        values: &HashMap<String, f64>,
    ) -> Result<Interval> {
        self.eval(&self.output, tables, values)
    }

    fn eval(
        &self,
        card: &Card,
        tables: &HashMap<String, u64>,
        values: &HashMap<String, f64>,
    ) -> Result<Interval> {
        card.eval(&|leaf| match leaf {
            Card::Table(t) => tables
                .get(t)
                .map(|n| Interval::point(*n as f64))
                .ok_or_else(|| Error::UnknownTable(t.clone())),
            Card::Sel(s) => Ok(match values.get(s) {
                Some(v) => Interval::point(*v),
                None => self
                    .all
                    .iter()
                    .find(|x| x.name == *s)
                    .map_or(Interval { lo: 0.0, hi: 1.0 }, |x| x.range),
            }),
            Card::Operator(v) => Ok(match values.get(v) {
                Some(n) => Interval::point(*n),
                None => Interval {
                    lo: 0.0,
                    hi: f64::INFINITY,
                },
            }),
            _ => unreachable!("not a leaf"),
        })
    }

    /// Measures every selectivity from one execution's row counts (`rows`, by
    /// variable, and `aux`, the auxiliary join counts), and checks that each
    /// lies in its range and that every operator's formula gives its actual
    /// row count.
    pub(crate) fn check(
        &self,
        scans: &[(String, String)],
        rows: &HashMap<String, u64>,
        aux: &HashMap<String, u64>,
    ) -> SelectivityCheck {
        let mut check = SelectivityCheck::default();
        let tables: HashMap<String, u64> = scans
            .iter()
            .filter_map(|(scan, table)| Some((table.clone(), *rows.get(scan)?)))
            .collect();
        let mut values: HashMap<String, f64> =
            rows.iter().map(|(v, n)| (v.clone(), *n as f64)).collect();
        for s in &self.all {
            let Some(count) = rows.get(&s.measure).or_else(|| aux.get(&s.measure)) else {
                continue;
            };
            let Some(of) = s
                .over
                .iter()
                .map(|v| rows.get(v).map(|n| *n as f64))
                .product::<Option<f64>>()
            else {
                continue;
            };
            // A share of no rows is any share.
            if of == 0.0 {
                continue;
            }
            let value = *count as f64 / of;
            values.insert(s.name.clone(), value);
            check.values.insert(s.name.clone(), value);
            if !s.range.contains(value) && check.violation.is_none() {
                check.violation = Some(format!("{s}, but measured {value}"));
            }
        }
        for (var, card) in &self.operators {
            let (Some(actual), Ok(claimed)) = (rows.get(var), self.eval(card, &tables, &values))
            else {
                continue;
            };
            if !claimed.contains(*actual as f64) && check.violation.is_none() {
                check.violation = Some(format!(
                    "{var} = {card} gives {claimed}, but it has {actual} rows"
                ));
            }
        }
        check
    }
}

impl fmt::Display for SelectivityReport {
    /// The formula, then each selectivity it needs.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "X = {}", self.output)?;
        for s in &self.required {
            write!(f, "\n  {s}")?;
        }
        Ok(())
    }
}

/// Builds the report for `nodes` (children before parents, the root last).
/// `scans` maps each base-table scan's variable to its table, and `search`
/// holds the constraint set.
pub(crate) fn build(nodes: &[Node], scans: &[(String, String)], search: &Search) -> SelectivityReport {
    let mut b = Builder {
        all: vec![],
        ratios: vec![],
        count: 0,
    };
    let mut cards: Vec<Card> = Vec::with_capacity(nodes.len());
    let mut operators = vec![];
    let mut resolved = vec![];
    for node in nodes {
        // The operator's inputs: variable and cardinality.
        let mut inputs: Vec<(String, Card)> = node
            .inputs
            .iter()
            .map(|&i| (nodes[i].var.clone(), cards[i].clone()))
            .collect();
        if let LogicalPlan::TableScan(_) = node.plan {
            let scan = node.raw_scan.as_ref().map_or(&node.var, |(var, _, _)| var);
            if let Some((_, table)) = scans.iter().find(|(s, _)| s == scan) {
                inputs.push((scan.clone(), Card::Table(table.clone())));
                if node.raw_scan.is_some() {
                    operators.push(inputs[0].clone());
                }
            }
        }
        let first = b.all.len();
        let mut card = b.rule(node, &inputs);
        if b.all.len() > first {
            // Does the solver already know this operator's cardinality?
            let known = if search.zero(&node.var) {
                Some(Card::Const(0))
            } else {
                inputs
                    .iter()
                    .find(|(v, _)| search.equal(&node.var, v))
                    .map(|(_, c)| c.clone())
            };
            if let Some(known) = known {
                card = known;
                resolved.extend(b.all.drain(first..));
                b.ratios.truncate(first);
            }
            for i in first..b.all.len() {
                let Some(complement) = b.ratios[i] else { continue };
                let s = &mut b.all[i];
                let (lo, hi) = search.ratio(&node.var, &s.over[0]);
                let (lo, hi) = (lo.0 as f64 / lo.1 as f64, hi.0 as f64 / hi.1 as f64);
                s.range = if complement {
                    Interval {
                        lo: 1.0 - hi,
                        hi: 1.0 - lo,
                    }
                } else {
                    Interval { lo, hi }
                };
            }
        }
        operators.push((node.var.clone(), card.clone()));
        cards.push(card);
    }
    let output = cards.pop().unwrap_or(Card::Const(0));
    let mut mentioned = vec![];
    output.leaves(&mut |c| {
        if let Card::Sel(s) = c {
            mentioned.push(s.as_str());
        }
    });
    let required = b
        .all
        .iter()
        .filter(|s| mentioned.contains(&s.name.as_str()))
        .cloned()
        .collect();
    SelectivityReport {
        output,
        required,
        resolved,
        operators,
        all: b.all,
    }
}

struct Builder {
    all: Vec<Selectivity>,
    /// For each selectivity, whether its operator's cardinality `X` is a share
    /// of one input `l`: `Some(false)` if `X = s·l`, `Some(true)` if
    /// `X = (1 - s)·l`.
    ratios: Vec<Option<bool>>,
    /// Selectivities named so far.
    count: usize,
}

impl Builder {
    /// A new selectivity of `node`, measured as `measure / Π over`.
    fn sel(&mut self, node: &Node, kind: Kind, over: &[&str], measure: String, ratio: Option<bool>) -> Card {
        self.count += 1;
        let name = format!("s{}", self.count);
        self.all.push(Selectivity {
            name: name.clone(),
            operator: node.var.clone(),
            kind,
            over: over.iter().map(|v| v.to_string()).collect(),
            range: Interval { lo: 0.0, hi: 1.0 },
            measure,
        });
        self.ratios.push(ratio);
        Card::Sel(name)
    }

    /// A share of the one input: `X = s·l`.
    fn share(&mut self, node: &Node, kind: Kind, input: &(String, Card)) -> Card {
        let s = self.sel(node, kind, &[&input.0], node.var.clone(), Some(false));
        Card::mul(vec![input.1.clone(), s])
    }

    /// The cardinality of `node` given its inputs' variables and cardinalities.
    fn rule(&mut self, node: &Node, inputs: &[(String, Card)]) -> Card {
        let unknown = || Card::Operator(node.var.clone());
        let input = || inputs[0].1.clone();
        match &node.plan {
            LogicalPlan::TableScan(scan) => match inputs.first() {
                // Not a stored table.
                None => unknown(),
                Some(table) => match conjunction(scan.filters.iter().cloned()) {
                    None => table.1.clone(),
                    Some(p) => self.share(node, Kind::Filter(p), table),
                },
            },
            LogicalPlan::Projection(_)
            | LogicalPlan::Subquery(_)
            | LogicalPlan::SubqueryAlias(_)
            | LogicalPlan::Repartition(_)
            | LogicalPlan::Window(_) => input(),
            LogicalPlan::Filter(f) => self.share(node, Kind::Filter(f.predicate.clone()), &inputs[0]),
            LogicalPlan::Sort(s) => match s.fetch {
                None => input(),
                Some(n) => Card::min(Card::Const(n as u64), input()),
            },
            LogicalPlan::Limit(lim) => {
                let skip = match lim.get_skip_type() {
                    Ok(SkipType::Literal(k)) => Some(k as u64),
                    _ => None,
                };
                let fetch = match lim.get_fetch_type() {
                    Ok(FetchType::Literal(n)) => Some(n.map(|n| n as u64)),
                    _ => None,
                };
                match (skip, fetch) {
                    (Some(k), Some(n)) => {
                        let rest = input().minus(k);
                        match n {
                            Some(n) => Card::min(Card::Const(n), rest),
                            None => rest,
                        }
                    }
                    _ => self.share(node, Kind::Limit, &inputs[0]),
                }
            }
            LogicalPlan::Distinct(Distinct::All(child)) => {
                let schema = child.schema();
                let columns = (0..schema.fields().len())
                    .map(|i| Expr::Column(Column::from(schema.qualified_field(i))))
                    .collect();
                self.share(node, Kind::Distinct(columns), &inputs[0])
            }
            LogicalPlan::Distinct(Distinct::On(on)) => {
                self.share(node, Kind::Distinct(on.on_expr.clone()), &inputs[0])
            }
            LogicalPlan::Aggregate(agg) => {
                if agg.group_expr.iter().any(|e| matches!(e, Expr::GroupingSet(_))) {
                    unknown()
                } else if agg.group_expr.is_empty() {
                    Card::Const(1)
                } else {
                    self.share(node, Kind::Distinct(agg.group_expr.clone()), &inputs[0])
                }
            }
            LogicalPlan::Join(join) => self.join(node, join, inputs),
            LogicalPlan::Union(_) => Card::add(inputs.iter().map(|(_, c)| c.clone()).collect()),
            LogicalPlan::Values(v) => Card::Const(v.values.len() as u64),
            LogicalPlan::EmptyRelation(e) => Card::Const(e.produce_one_row as u64),
            _ => unknown(),
        }
    }

    fn join(&mut self, node: &Node, join: &Join, inputs: &[(String, Card)]) -> Card {
        let ((lv, l), (rv, r)) = (&inputs[0], &inputs[1]);
        let (on, filter) = (join.on.clone(), join.filter.clone());
        let cross = on.is_empty() && filter.is_none();
        // What measures a selectivity: the operator's own rows, or an
        // auxiliary count.
        let own = node.var.clone();
        let aux = |suffix: &str| format!("{}#{suffix}", node.var);
        let pairs = |b: &mut Builder, measure: String| {
            let kind = Kind::Join {
                on: on.clone(),
                filter: filter.clone(),
            };
            let s = b.sel(node, kind, &[lv, rv], measure, None);
            Card::mul(vec![l.clone(), r.clone(), s])
        };
        // The rows of one side with a match, or (`anti`) without one.
        let matched = |b: &mut Builder, left: bool, measure: String, anti: bool, ratio: bool| {
            let kind = Kind::Match {
                on: on.clone(),
                filter: filter.clone(),
                left,
            };
            let (v, side) = if left { (lv, l) } else { (rv, r) };
            let m = b.sel(node, kind, &[v], measure, ratio.then_some(anti));
            let m = if anti { Card::Not(Box::new(m)) } else { m };
            Card::mul(vec![side.clone(), m])
        };
        match join.join_type {
            JoinType::Inner if cross => Card::mul(vec![l.clone(), r.clone()]),
            JoinType::Inner => pairs(self, own),
            JoinType::Left => Card::add(vec![
                pairs(self, aux("inner")),
                matched(self, true, aux("left"), true, false),
            ]),
            JoinType::Right => Card::add(vec![
                pairs(self, aux("inner")),
                matched(self, false, aux("right"), true, false),
            ]),
            JoinType::Full => Card::add(vec![
                pairs(self, aux("inner")),
                matched(self, true, aux("left"), true, false),
                matched(self, false, aux("right"), true, false),
            ]),
            JoinType::LeftSemi => matched(self, true, own, false, true),
            JoinType::RightSemi => matched(self, false, own, false, true),
            JoinType::LeftAnti if join.null_aware => {
                self.share(node, Kind::NotIn { on, filter }, &inputs[0])
            }
            JoinType::LeftAnti => matched(self, true, aux("left"), true, true),
            JoinType::RightAnti => matched(self, false, aux("right"), true, true),
            JoinType::LeftMark => l.clone(),
            JoinType::RightMark => r.clone(),
        }
    }
}

/// The joins whose counts measure the selectivities of outer or anti join
/// `join`, as (suffix of the auxiliary count's name, join type).
pub(crate) fn auxiliary_joins(join: &Join) -> Vec<(&'static str, JoinType)> {
    let (inner, left, right) = (
        ("inner", JoinType::Inner),
        ("left", JoinType::LeftSemi),
        ("right", JoinType::RightSemi),
    );
    match join.join_type {
        JoinType::Left => vec![inner, left],
        JoinType::Right => vec![inner, right],
        JoinType::Full => vec![inner, left, right],
        JoinType::LeftAnti if !join.null_aware => vec![left],
        JoinType::RightAnti => vec![right],
        _ => vec![],
    }
}
