//! Bottom-up walk over a DataFusion `LogicalPlan` that emits Z3 constraints.
//!
//! Every operator gets an integer variable for its output cardinality and one per
//! output column bounding that column's number of distinct values (NDV, with NULL
//! counted as one value). Constraints relate each operator's variables to its
//! inputs'.

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::panic::Location;

use datafusion::arrow::datatypes::DataType;
use datafusion::common::tree_node::{Transformed, TreeNode, TreeNodeRecursion};
use datafusion::common::{Column, Constraint, JoinType, NullEquality};
use datafusion::datasource::source_as_provider;
use datafusion::logical_expr::logical_plan::{
    Aggregate, Distinct, FetchType, Join, LogicalPlan, SkipType, TableScan,
};
use datafusion::logical_expr::utils::split_conjunction;
use datafusion::logical_expr::{
    BinaryExpr, Cast, Expr, ExprSchemable, Operator, TableProviderFilterPushDown, TryCast,
};
use z3::ast::{Bool, Int};
use z3::{Params, Solver};

use crate::domain::{self, Dom, Facts};
use crate::origin::{self, Origin};
use crate::ForeignKey;
use crate::selectivity::auxiliary_joins;

/// How a `TableScan` is treated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ScanKind {
    /// A stored table. `key` identifies it (every scan of the same table must get
    /// the same key); `display` is the name shown to users.
    Base { key: String, display: String },
    /// A scan that does not read a stored table, such as a recursive CTE's work
    /// table or a table function. It adds nothing to the sum of scans and its
    /// output is unconstrained.
    NonBase,
}

pub(crate) struct TableVar {
    pub(crate) display: String,
    pub(crate) symbol: String,
    pub(crate) var: Int,
}

/// The abstract state of a relation: its cardinality and, per output column, a
/// variable bounding its number of distinct values.
#[derive(Clone)]
pub(crate) struct Rel {
    pub(crate) card: Int,
    pub(crate) ndv: Vec<Int>,
    /// Per output column, the ends of an interval holding each of its
    /// non-NULL values (empty, `max < min`, if there is none): for
    /// integer-like columns that a range, a join or a grouping reads.
    pub(crate) min: Vec<Option<Int>>,
    pub(crate) max: Vec<Option<Int>>,
    /// What every row's values satisfy, whatever the data.
    pub(crate) facts: Facts,
    /// Facts that also hold for any subset of the rows.
    pub(crate) rows: Rows,
    /// The stored table this relation's rows are distinct rows of, if any.
    pub(crate) origin: Option<Origin>,
}

/// Facts about a relation's rows that also hold for any subset of them, so
/// they survive operators that keep some rows as they are.
#[derive(Clone, Default)]
pub(crate) struct Rows {
    /// `(column, bound)`: the column holds non-negative integers summing to at
    /// most `bound` over all rows, like the counts of a GROUP BY.
    sums: Vec<(Expr, Int)>,
    /// Sets of columns that are unique together, beyond declared keys.
    keys: Vec<Vec<Expr>>,
    /// `(column, nulls, values)`: at most `nulls` rows have the column NULL,
    /// and at most `values` rows have it non-NULL, like the padded and
    /// matched rows of an outer join.
    nulls: Vec<(Expr, Int, Int)>,
}

impl Rows {
    /// The facts whose columns all map through `map`, over the new columns.
    fn rename(&self, map: &dyn Fn(&Column) -> Option<Column>) -> Rows {
        let r = |c: &Expr| domain::rename(c, map);
        Rows {
            sums: self
                .sums
                .iter()
                .filter_map(|(c, b)| Some((r(c)?, b.clone())))
                .collect(),
            keys: self
                .keys
                .iter()
                .filter_map(|k| k.iter().map(r).collect())
                .collect(),
            nulls: self
                .nulls
                .iter()
                .filter_map(|(c, a, b)| Some((r(c)?, a.clone(), b.clone())))
                .collect(),
        }
    }
}

pub(crate) struct Analyzer<'a> {
    pub(crate) solver: Solver,
    resolve: &'a dyn Fn(&TableScan) -> ScanKind,
    /// One variable per distinct base table, keyed by `ScanKind::Base::key` and
    /// shared by every scan of that table.
    pub(crate) tables: HashMap<String, TableVar>,
    /// Every base-table scan as (scan variable name, table display name), with its variable.
    pub(crate) scans: Vec<(String, String, Int)>,
    /// Every variable, by name, so callers can read them from a model.
    pub(crate) vars: Vec<(String, Int)>,
    /// Every plan node, children before parents, so a validator can evaluate
    /// them bottom-up.
    pub(crate) nodes: Vec<Node>,
    /// Every relation made of distinct rows of one stored table, by cardinality.
    origins: Vec<(Int, Origin)>,
    /// Ids of visited nodes not yet claimed by a parent.
    frontier: Vec<usize>,
    counter: usize,
    /// Most NDV factors multiplied in one constraint.
    max_product: usize,
    /// Declared foreign keys.
    foreign_keys: &'a [ForeignKey],
    /// The last join visited's [`Node::at_most_once`], for its node to take.
    at_most_once: (bool, bool),
    /// Whether to log every assertion, for [`crate::trace`].
    trace: bool,
    /// Every assertion, in order, if `trace` is set.
    pub(crate) log: RefCell<Vec<Logged>>,
    /// Frames of the nodes being visited, innermost last.
    owners: Vec<usize>,
    next_frame: usize,
    /// The node each finished frame became.
    pub(crate) frame_node: HashMap<usize, usize>,
    /// The names of the columns that get min and max variables
    /// ([`ranged_columns`]).
    ranged: BTreeSet<String>,
    /// The last base scan's raw min and max variables, for its node to take.
    raw_ranges: (Vec<Option<String>>, Vec<Option<String>>),
}

/// One assertion: the frame of the node it was made for (none for
/// partitions), and the line of the analyzer that made it.
pub(crate) struct Logged {
    pub(crate) expr: Bool,
    pub(crate) frame: Option<usize>,
    pub(crate) at: &'static Location<'static>,
}

/// One plan node and the variables describing its output.
#[derive(Debug, Clone)]
pub(crate) struct Node {
    /// The cardinality variable.
    pub(crate) var: String,
    /// The NDV variable of each output column.
    pub(crate) ndv_vars: Vec<String>,
    pub(crate) plan: LogicalPlan,
    /// Node ids of `plan.inputs()`, in order.
    pub(crate) inputs: Vec<usize>,
    /// For a base scan with pushed-down filters: the raw scan's cardinality and
    /// NDV variables, and the scan without filters or fetch.
    pub(crate) raw_scan: Option<(String, Vec<String>, LogicalPlan)>,
    /// For an equi-join: whether each left row matches at most one right row
    /// (a unique right key, or a foreign key from the left), and the mirror.
    pub(crate) at_most_once: (bool, bool),
    /// The min and max variable of each output column that has them
    /// ([`Rel::min`]), `op{n}_{kind}_c{j}_min` and `_max`.
    pub(crate) min_vars: Vec<Option<String>>,
    pub(crate) max_vars: Vec<Option<String>>,
    /// The raw scan's, for a base scan with pushed-down filters.
    pub(crate) raw_min_vars: Vec<Option<String>>,
    pub(crate) raw_max_vars: Vec<Option<String>>,
}

/// True if `scan`'s provider may return rows that fail its pushed filters:
/// it takes each only to prune (a parquet scan skipping row groups, say),
/// and DataFusion keeps a filter above to check it.
pub(crate) fn inexact_filters(scan: &TableScan) -> bool {
    let Ok(provider) = source_as_provider(&scan.source) else {
        return false;
    };
    let filters: Vec<&Expr> = scan.filters.iter().collect();
    !filters.is_empty()
        && provider
            .supports_filters_pushdown(&filters)
            .is_ok_and(|s| s.iter().all(|s| *s == TableProviderFilterPushDown::Inexact))
}

/// For filter node `i` over a scan whose pushed filters are all inexact and
/// each among its own conjuncts, that scan's node. The scan's rows are a
/// subset of the table's and hold every row satisfying its filters, so the
/// filter's rows are exactly the table's rows satisfying its predicate.
pub(crate) fn rechecked_scan(nodes: &[Node], i: usize) -> Option<usize> {
    let LogicalPlan::Filter(f) = &nodes[i].plan else {
        return None;
    };
    let k = *nodes[i].inputs.first()?;
    let LogicalPlan::TableScan(scan) = &nodes[k].plan else {
        return None;
    };
    let conjuncts = split_conjunction(&f.predicate);
    let rechecked = scan.filters.iter().all(|p| conjuncts.contains(&p));
    (nodes[k].raw_scan.is_some() && scan.fetch.is_none() && inexact_filters(scan) && rechecked).then_some(k)
}

/// How long Z3 may spend on one check before answering unknown.
pub(crate) const SOLVER_TIMEOUT_MS: u32 = 10_000;

pub(crate) fn new_solver() -> Solver {
    solver_with_timeout(SOLVER_TIMEOUT_MS)
}

pub(crate) fn solver_with_timeout(ms: u32) -> Solver {
    let solver = Solver::new();
    let mut params = Params::new();
    params.set_u32("timeout", ms);
    solver.set_params(&params);
    solver
}

/// Restricts a Z3 symbol to `[A-Za-z0-9_]` so it round-trips through SMT-LIB
/// text unquoted. Uniqueness comes from the numeric prefix, not the name.
fn symbol(s: &str) -> String {
    s.chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect()
}

fn int(n: u64) -> Int {
    Int::from_u64(n)
}

fn max(a: &Int, b: &Int) -> Int {
    a.ge(b).ite(a, b)
}

fn min(a: &Int, b: &Int) -> Int {
    a.le(b).ite(a, b)
}

/// Default for `Options::max_product`.
pub(crate) const DEFAULT_MAX_PRODUCT: usize = 3;

/// The product of `factors`, or `None` if there are more than `cap` of them.
/// Products of NDVs are nonlinear, so larger products are dropped (the bound is
/// then just the cardinality), which is sound but weaker.
fn product(factors: &[&Int], cap: usize) -> Option<Int> {
    match factors.len() {
        0 => Some(int(1)),
        1 => Some(factors[0].clone()),
        n if n <= cap => Some(Int::mul(factors)),
        _ => None,
    }
}

impl<'a> Analyzer<'a> {
    pub(crate) fn new(
        resolve: &'a dyn Fn(&TableScan) -> ScanKind,
        max_product: usize,
        foreign_keys: &'a [ForeignKey],
        trace: bool,
    ) -> Self {
        Self {
            solver: new_solver(),
            resolve,
            tables: HashMap::new(),
            scans: Vec::new(),
            vars: Vec::new(),
            nodes: Vec::new(),
            frontier: Vec::new(),
            counter: 0,
            origins: Vec::new(),
            max_product,
            foreign_keys,
            at_most_once: (false, false),
            trace,
            log: RefCell::new(Vec::new()),
            owners: Vec::new(),
            next_frame: 0,
            frame_node: HashMap::new(),
            ranged: BTreeSet::new(),
            raw_ranges: Default::default(),
        }
    }

    /// Gives min and max variables to the columns of `plan` that need them.
    pub(crate) fn with_ranges(mut self, plan: &LogicalPlan) -> Self {
        self.ranged = ranged_columns(plan);
        self
    }

    /// A variable for an end of a column's values: any integer.
    fn range_var(&mut self, name: String) -> Int {
        let v = Int::new_const(name.as_str());
        self.vars.push((name, v.clone()));
        v
    }

    #[track_caller]
    fn new_var(&mut self, name: String) -> Int {
        let v = Int::new_const(name.as_str());
        self.assert(v.ge(int(0)));
        self.vars.push((name, v.clone()));
        v
    }

    /// Creates a fresh relation for `plan`'s output: a cardinality variable
    /// `op{n}_{kind}` and NDV variables `op{n}_{kind}_c{j}`, with the constraints
    /// every relation satisfies.
    fn fresh(&mut self, kind: &str, plan: &LogicalPlan) -> Rel {
        let base = format!("op{}_{}", self.counter, symbol(kind));
        self.counter += 1;
        let card = self.new_var(base.clone());
        let fields: Vec<DataType> = plan
            .schema()
            .fields()
            .iter()
            .map(|f| f.data_type().clone())
            .collect();
        let ndv = fields
            .iter()
            .enumerate()
            .map(|(j, t)| {
                let v = self.new_var(format!("{base}_c{j}"));
                self.assert(v.le(&card));
                self.assert(card.ge(int(1)).implies(v.ge(int(1))));
                if *t == DataType::Boolean {
                    // true, false, NULL
                    self.assert(v.le(int(3)));
                }
                v
            })
            .collect();
        let schema = plan.schema();
        let (mut min, mut max) = (vec![], vec![]);
        for (j, t) in fields.iter().enumerate() {
            let ranged = integer_like(t) && self.ranged.contains(schema.field(j).name());
            min.push(ranged.then(|| self.range_var(format!("{base}_c{j}_min"))));
            max.push(ranged.then(|| self.range_var(format!("{base}_c{j}_max"))));
        }
        let rel = Rel {
            card,
            ndv,
            min,
            max,
            facts: Facts::default(),
            rows: Rows::default(),
            origin: None,
        };
        self.unique_columns(plan, &rel);
        rel
    }

    /// A column that traces to a declared key takes a distinct value on every
    /// row: its NDV (NULL counted as one value) equals the cardinality.
    fn unique_columns(&self, plan: &LogicalPlan, rel: &Rel) {
        let schema = plan.schema();
        for j in 0..schema.fields().len() {
            let col = Column::from(schema.qualified_field(j));
            if self.covers_key(plan, &[col], Nulls::Equal) {
                self.assert(rel.ndv[j].eq(&rel.card));
            }
        }
    }

    /// The unquoted name of a variable created by `new_var`.
    pub(crate) fn name_of(&self, v: &Int) -> String {
        self.vars
            .iter()
            .find(|(_, x)| x == v)
            .map(|(n, _)| n.clone())
            .expect("variable was created by new_var")
    }

    fn names_of(&self, rel: &Rel) -> Vec<String> {
        rel.ndv.iter().map(|v| self.name_of(v)).collect()
    }

    #[track_caller]
    fn assert(&self, b: Bool) {
        if self.trace {
            self.log.borrow_mut().push(Logged {
                expr: b.clone(),
                frame: self.owners.last().copied(),
                at: Location::caller(),
            });
        }
        self.solver.assert(b);
    }

    fn table(&mut self, key: &str, display: &str) -> Int {
        if let Some(t) = self.tables.get(key) {
            return t.var.clone();
        }
        // Tables are numbered so their symbols cannot collide with each other or
        // with operator variables (which start with `op`).
        let symbol = format!("T{}_{}", self.tables.len(), symbol(display));
        let var = Int::new_const(symbol.as_str());
        self.assert(var.ge(int(0)));
        self.tables.insert(
            key.to_string(),
            TableVar {
                display: display.to_string(),
                symbol,
                var: var.clone(),
            },
        );
        var
    }

    /// Returns the abstract state of `plan`'s output.
    pub(crate) fn visit(&mut self, plan: &LogicalPlan) -> Rel {
        let frame = self.next_frame;
        self.next_frame += 1;
        // Subqueries left inside expressions (e.g. an uncorrelated scalar subquery
        // in a Filter) are not plan inputs, but their scans still read rows, so
        // visit them to register those scans in the sum.
        let mark = self.frontier.len();
        let _ = plan.apply_subqueries(|sub| {
            self.visit(sub);
            Ok(TreeNodeRecursion::Continue)
        });
        // Subquery nodes stand on their own; they are not inputs of this node.
        self.frontier.truncate(mark);
        self.owners.push(frame);
        let (out, raw_scan) = self.visit_node(plan);
        let at_most_once = std::mem::take(&mut self.at_most_once);
        let (raw_min_vars, raw_max_vars) = std::mem::take(&mut self.raw_ranges);
        self.apply_domains(plan, &out);
        if let Some(o) = &out.origin
            && o.informative()
        {
            self.origins.push((out.card.clone(), o.clone()));
        }
        let inputs = self.frontier.split_off(mark);
        debug_assert_eq!(inputs.len(), plan.inputs().len());
        let var = self.name_of(&out.card);
        let ndv_vars = self.names_of(&out);
        self.nodes.push(Node {
            var,
            ndv_vars,
            plan: plan.clone(),
            inputs,
            raw_scan,
            at_most_once,
            min_vars: range_names(&out.min),
            max_vars: range_names(&out.max),
            raw_min_vars,
            raw_max_vars,
        });
        self.owners.pop();
        self.frame_node.insert(frame, self.nodes.len() - 1);
        self.frontier.push(self.nodes.len() - 1);
        out
    }

    /// Bounds each output column's NDV by the size of its domain. A relation
    /// with an expression that can take no value has no rows.
    fn apply_domains(&self, plan: &LogicalPlan, rel: &Rel) {
        let schema = plan.schema();
        if rel.facts.contradictory() {
            self.assert(rel.card.eq(int(0)));
        }
        for (j, v) in rel.ndv.iter().enumerate() {
            let col = Expr::Column(Column::from(schema.qualified_field(j)));
            match rel.facts.dom(&col, schema).size() {
                Some(0) => self.assert(rel.card.eq(int(0))),
                Some(n) if n <= u64::MAX as u128 => self.assert(v.le(int(n as u64))),
                _ => {}
            }
        }
        self.range_domains(plan, rel);
        // A unique set of columns has a distinct combination on every row.
        // Columns with few possible values count as constants, which keeps
        // the product linear where possible.
        'keys: for key in &rel.rows.keys {
            let mut constant: u128 = 1;
            let mut factors: Vec<&Int> = vec![];
            for e in key {
                let Expr::Column(c) = e else { continue 'keys };
                let Ok(i) = schema.index_of_column(c) else { continue 'keys };
                match rel.facts.dom(e, schema).size() {
                    Some(k) => constant = constant.saturating_mul(k),
                    None => factors.push(&rel.ndv[i]),
                }
            }
            if constant > u64::MAX as u128 {
                continue;
            }
            if let Some(p) = product(&factors, self.max_product) {
                self.assert(rel.card.le(p * int(constant as u64)));
            }
        }
        // Rows whose values are each at least `k` and sum to at most `bound`
        // number at most `bound / k`.
        for (c, bound) in &rel.rows.sums {
            if let Some(k) = rel.facts.dom(c, schema).min()
                && k >= 1
                && k <= u64::MAX as i128
            {
                self.assert((&rel.card * int(k as u64)).le(bound));
            }
        }
        for (c, nulls, values) in &rel.rows.nulls {
            let d = rel.facts.dom(c, schema);
            if d.is_null_only() {
                self.assert(rel.card.le(nulls));
            } else if d.never_null() {
                self.assert(rel.card.le(values));
            }
        }
    }

    /// Each column's interval holds the values its domain allows, and isn't
    /// empty where the column has a value; it holds at most its width of
    /// distinct values, and NULL.
    fn range_domains(&self, plan: &LogicalPlan, rel: &Rel) {
        let schema = plan.schema();
        for (j, (lo, hi)) in rel.min.iter().zip(&rel.max).enumerate() {
            let (Some(lo), Some(hi)) = (lo, hi) else { continue };
            let col = Expr::Column(Column::from(schema.qualified_field(j)));
            let d = rel.facts.dom(&col, schema);
            let (from, to) = d.int_range();
            if let Some(from) = from.and_then(|v| i64::try_from(v).ok()) {
                self.assert(lo.ge(Int::from_i64(from)));
            }
            if let Some(to) = to.and_then(|v| i64::try_from(v).ok()) {
                self.assert(hi.le(Int::from_i64(to)));
            }
            if d.never_null() {
                self.assert(rel.card.ge(int(1)).implies(lo.le(hi)));
            }
            let width = hi.ge(lo).ite(&(hi - lo + int(1)), &int(0));
            self.assert(rel.ndv[j].le(width + int(!d.never_null() as u64)));
        }
    }

    /// Every non-NULL value of `o`'s column `j` is one of `l`'s column `i`.
    fn within(&self, o: &Rel, j: usize, l: &Rel, i: usize) {
        if let (Some(a), Some(b)) = (&o.min[j], &l.min[i]) {
            self.assert(a.ge(b));
        }
        if let (Some(a), Some(b)) = (&o.max[j], &l.max[i]) {
            self.assert(a.le(b));
        }
    }

    /// [`Self::within`], for each of `l`'s columns at the same position.
    fn within_all(&self, o: &Rel, l: &Rel) {
        for j in 0..o.min.len().min(l.min.len()) {
            self.within(o, j, l, j);
        }
    }

    /// The ranges `predicate` holds between two columns on every row of
    /// `o`, the output of `plan` keeping only rows that satisfy it: equal
    /// columns take the same values, and `a < b` puts `b`'s least above
    /// `a`'s least and `a`'s greatest below `b`'s.
    fn range_pairs(&self, predicate: &Expr, plan: &LogicalPlan, o: &Rel) {
        let index = |e: &Expr| column_index(plan, e).filter(|&i| o.min[i].is_some());
        for conj in split_conjunction(predicate) {
            let Expr::BinaryExpr(BinaryExpr { left, op, right }) = conj else { continue };
            let (Some(a), Some(b)) = (index(left), index(right)) else { continue };
            let lo_hi = |i: usize| (o.min[i].as_ref().unwrap(), o.max[i].as_ref().unwrap());
            // Each `x` is below a `y` (by one, `strict`ly).
            let below = |x: usize, y: usize, strict: bool| {
                let ((x_lo, x_hi), (y_lo, y_hi)) = (lo_hi(x), lo_hi(y));
                let gap = int(strict as u64);
                self.assert(y_lo.ge(x_lo + &gap));
                self.assert(x_hi.le(y_hi - &gap));
            };
            match op {
                Operator::Eq => {
                    let ((a_lo, a_hi), (b_lo, b_hi)) = (lo_hi(a), lo_hi(b));
                    self.assert(a_lo.eq(b_lo));
                    self.assert(a_hi.eq(b_hi));
                }
                Operator::Lt => below(a, b, true),
                Operator::LtEq => below(a, b, false),
                Operator::Gt => below(b, a, true),
                Operator::GtEq => below(b, a, false),
                _ => {}
            }
        }
    }

    /// Relations over one table whose rows are provably disjoint together hold
    /// at most the table's rows. Each class of relations with the same domains
    /// gets a variable for the table rows in those domains, bounding all of
    /// its members, and disjoint classes' variables sum to at most the table.
    pub(crate) fn assert_partitions(&mut self) {
        let origins: Vec<Origin> = self.origins.iter().map(|(_, o)| o.clone()).collect();
        let (classes, cliques) = origin::disjoint_classes(&origins, 64);
        let mut part: HashMap<usize, Int> = HashMap::new();
        for clique in cliques {
            let table = self.tables[&origins[classes[clique[0]][0]].table].var.clone();
            let mut sum = vec![];
            for c in clique {
                if !part.contains_key(&c) {
                    let v = self.new_var(format!("part{c}"));
                    for &m in &classes[c] {
                        self.assert(self.origins[m].0.le(&v));
                    }
                    self.assert(v.le(&table));
                    part.insert(c, v);
                }
                sum.push(part[&c].clone());
            }
            self.assert(Int::add(&sum).le(&table));
        }
    }

    #[allow(clippy::type_complexity)]
    fn visit_node(
        &mut self,
        plan: &LogicalPlan,
    ) -> (Rel, Option<(String, Vec<String>, LogicalPlan)>) {
        if let LogicalPlan::TableScan(scan) = plan {
            return self.scan(plan, scan);
        }
        let out = match plan {
            LogicalPlan::Projection(p) => {
                let l = self.visit(&p.input);
                let mut o = self.fresh("Projection", plan);
                self.assert(o.card.eq(&l.card));
                for (j, e) in p.expr.iter().enumerate() {
                    self.expr_ndv(&o.ndv[j], e, &p.input, &l);
                    // A column, or an integer cast of it, that keeps its value.
                    if let Some(i) = column_index(&p.input, e) {
                        self.within(&o, j, &l, i);
                    }
                }
                o.facts = computed_facts(plan, &p.expr, &p.input, &l.facts);
                o.rows = l.rows.rename(&|c| passed_column(plan, &p.expr, c));
                o.origin = l.origin.as_ref().map(|origin| {
                    origin.project(p.expr.iter().map(|e| match strip_alias(e) {
                        Expr::Column(c) => p.input.schema().index_of_column(c).ok(),
                        _ => None,
                    }))
                });
                o
            }
            LogicalPlan::Subquery(p) => self.same_rows("Subquery", plan, &p.subquery),
            LogicalPlan::SubqueryAlias(p) => self.same_rows("SubqueryAlias", plan, &p.input),
            LogicalPlan::Repartition(p) => self.same_rows("Repartition", plan, &p.input),
            // Window output is the input's columns, then one column per window
            // function, over the same rows.
            LogicalPlan::Window(p) => {
                let mut o = self.same_rows("Window", plan, &p.input);
                self.window_functions(plan, &p.input, &p.window_expr, &mut o);
                o
            }
            LogicalPlan::Filter(f) => {
                let l = self.visit(&f.input);
                let mut o = self.fresh("Filter", plan);
                self.assert(o.card.le(&l.card));
                self.subset_ndv(&o, &l);
                self.filter_ndv(&f.predicate, &f.input, &o, &l);
                self.within_all(&o, &l);
                self.range_pairs(&f.predicate, plan, &o);
                o.facts = l.facts.clone();
                o.rows = l.rows.clone();
                o.facts.assume(&f.predicate, plan.schema());
                o.origin = l.origin.clone().map(|x| x.narrow(&o.facts, plan.schema()));
                o
            }
            LogicalPlan::Distinct(Distinct::All(input)) => {
                let l = self.visit(input);
                let mut o = self.fresh("Distinct", plan);
                o.facts = l.facts.clone();
                o.rows = l.rows.clone();
                o.origin = l.origin.clone();
                self.assert(o.card.le(&l.card));
                self.assert(l.card.ge(int(1)).implies(o.card.ge(int(1))));
                // DISTINCT keeps every value that occurs.
                self.kept_values(plan, &o, &l);
                self.within_all(&o, &l);
                let all: Vec<&Int> = l.ndv.iter().collect();
                if let Some(p) = product(&all, self.max_product) {
                    self.assert(o.card.le(p));
                }
                // Columns the others determine add no distinct rows.
                let determining = self.determining_keys(input, all.len());
                if determining.len() < all.len() {
                    let factors: Vec<&Int> = determining.iter().map(|&j| &l.ndv[j]).collect();
                    if let Some(p) = product(&factors, self.max_product) {
                        self.assert(o.card.le(p));
                    }
                }
                let cols: Vec<Column> = (0..input.schema().fields().len())
                    .map(|i| Column::from(input.schema().qualified_field(i)))
                    .collect();
                if self.covers_key(input, &cols, Nulls::Equal) {
                    self.assert(o.card.eq(&l.card));
                }
                o
            }
            LogicalPlan::Distinct(Distinct::On(on)) => {
                let l = self.visit(&on.input);
                let mut o = self.fresh("DistinctOn", plan);
                o.facts = computed_facts(plan, &on.select_expr, &on.input, &l.facts);
                self.assert(o.card.le(&l.card));
                self.assert(l.card.ge(int(1)).implies(o.card.ge(int(1))));
                let bounds: Option<Vec<Int>> = on
                    .on_expr
                    .iter()
                    .map(|e| expr_bound(e, &on.input, &l, self.max_product))
                    .collect();
                if let Some(bounds) = bounds
                    && let Some(p) = product(&bounds.iter().collect::<Vec<_>>(), self.max_product)
                {
                    self.assert(o.card.le(p));
                }
                o
            }
            LogicalPlan::Sort(s) => {
                let l = self.visit(&s.input);
                let mut o = self.fresh("Sort", plan);
                self.within_all(&o, &l);
                o.facts = l.facts.clone();
                o.rows = l.rows.clone();
                o.origin = l.origin.clone();
                match s.fetch {
                    None => {
                        self.assert(o.card.eq(&l.card));
                        self.equal_ndv(&o, &l);
                    }
                    // Top-k: exactly the first n rows.
                    Some(n) => {
                        self.assert(o.card.eq(min(&int(n as u64), &l.card)));
                        self.subset_ndv(&o, &l);
                    }
                }
                o
            }
            LogicalPlan::Limit(lim) => {
                let l = self.visit(&lim.input);
                let mut o = self.fresh("Limit", plan);
                self.within_all(&o, &l);
                o.facts = l.facts.clone();
                o.rows = l.rows.clone();
                o.origin = l.origin.clone();
                self.subset_ndv(&o, &l);
                let skip = match lim.get_skip_type() {
                    Ok(SkipType::Literal(k)) => Some(k as u64),
                    _ => None,
                };
                let fetch = match lim.get_fetch_type() {
                    Ok(FetchType::Literal(n)) => Some(n.map(|n| n as u64)),
                    _ => None,
                };
                match (skip, fetch) {
                    // Exactly min(n, max(l - k, 0)) rows.
                    (Some(k), Some(n)) => {
                        let after_skip = max(&(&l.card - int(k)), &int(0));
                        let rows = match n {
                            Some(n) => min(&int(n), &after_skip),
                            None => after_skip,
                        };
                        self.assert(o.card.eq(rows));
                    }
                    (_, fetch) => {
                        self.assert(o.card.le(&l.card));
                        if let Some(Some(n)) = fetch {
                            self.assert(o.card.le(int(n)));
                        }
                    }
                }
                o
            }
            LogicalPlan::Aggregate(agg) => self.aggregate(plan, agg),
            LogicalPlan::Join(join) => self.join(plan, join),
            LogicalPlan::Union(u) => {
                let inputs: Vec<Rel> = u.inputs.iter().map(|i| self.visit(i)).collect();
                let mut o = self.fresh("Union", plan);
                for j in 0..plan.schema().fields().len() {
                    let dom = u.inputs.iter().zip(&inputs).fold(
                        Dom::nothing(),
                        |acc, (input, rel)| {
                            let col = Expr::Column(Column::from(input.schema().qualified_field(j)));
                            acc.union(&rel.facts.dom(&col, input.schema()))
                        },
                    );
                    let col = Expr::Column(Column::from(plan.schema().qualified_field(j)));
                    o.facts.add(&col, dom, plan.schema());
                }
                let cards: Vec<&Int> = inputs.iter().map(|r| &r.card).collect();
                self.assert(o.card.eq(Int::add(&cards)));
                for (j, v) in o.ndv.iter().enumerate() {
                    let parts: Vec<&Int> = inputs.iter().map(|r| &r.ndv[j]).collect();
                    self.assert(v.le(Int::add(&parts)));
                    for part in parts {
                        self.assert(v.ge(part));
                    }
                }
                // Each value is one of some input's.
                for j in 0..o.min.len() {
                    let ends = |ends: fn(&Rel) -> &Vec<Option<Int>>| -> Option<Vec<Int>> {
                        inputs.iter().map(|r| ends(r).get(j).cloned().flatten()).collect()
                    };
                    if let (Some(lo), Some(los)) = (&o.min[j], ends(|r| &r.min)) {
                        self.assert(lo.ge(los.iter().skip(1).fold(los[0].clone(), |a, b| min(&a, b))));
                    }
                    if let (Some(hi), Some(his)) = (&o.max[j], ends(|r| &r.max)) {
                        self.assert(hi.le(his.iter().skip(1).fold(his[0].clone(), |a, b| max(&a, b))));
                    }
                }
                o
            }
            LogicalPlan::Values(v) => {
                let mut o = self.fresh("Values", plan);
                self.assert(o.card.eq(int(v.values.len() as u64)));
                for j in 0..plan.schema().fields().len() {
                    let dom = v.values.iter().fold(Dom::nothing(), |acc, row| {
                        acc.union(&Facts::default().dom(&row[j], plan.schema()))
                    });
                    let col = Expr::Column(Column::from(plan.schema().qualified_field(j)));
                    o.facts.add(&col, dom, plan.schema());
                }
                o
            }
            LogicalPlan::EmptyRelation(e) => {
                let o = self.fresh("EmptyRelation", plan);
                self.assert(o.card.eq(int(e.produce_one_row as u64)));
                o
            }
            other => {
                // Unsupported operator: visit children so their scans still count,
                // but say nothing about this operator's output beyond the basics.
                for input in other.inputs() {
                    self.visit(input);
                }
                self.fresh(&format!("Unknown_{}", variant_name(other)), plan)
            }
        };
        (out, None)
    }

    #[allow(clippy::type_complexity)]
    fn scan(
        &mut self,
        plan: &LogicalPlan,
        scan: &TableScan,
    ) -> (Rel, Option<(String, Vec<String>, LogicalPlan)>) {
        let mut raw_scan = None;
        let mut out = match (self.resolve)(scan) {
            ScanKind::Base { key, display } => {
                let t = self.table(&key, &display);
                let mut s = self.fresh(&format!("Scan_{display}"), plan);
                self.assert(s.card.eq(&t));
                // Stored tables enforce their columns' nullability.
                let schema = plan.schema();
                for (j, field) in schema.fields().iter().enumerate() {
                    if !field.is_nullable() {
                        let col = Expr::Column(Column::from(schema.qualified_field(j)));
                        s.facts.add(&col, Dom::non_null(), schema);
                    }
                }
                self.composite_key(scan, &s);
                let name = self.name_of(&s.card);
                self.scans.push((name.clone(), display, s.card.clone()));
                s.origin = Some(Origin::scan(&key, schema).narrow(&s.facts, schema));
                if !scan.filters.is_empty() {
                    // The raw scan, before pushed-down filters and fetch.
                    let mut raw = scan.clone();
                    raw.filters.clear();
                    raw.fetch = None;
                    raw_scan = Some((name, self.names_of(&s), LogicalPlan::TableScan(raw)));
                    self.raw_ranges = (range_names(&s.min), range_names(&s.max));
                    self.range_domains(plan, &s);
                }
                s
            }
            ScanKind::NonBase => self.fresh(&format!("NonBaseScan_{}", scan.table_name), plan),
        };
        // Pushed-down filters behave like a Filter wrapping the scan: whether the
        // provider applies them exactly or not, it cannot add rows. A pushed-down
        // `fetch` is only a hint: providers must return *at least* that many rows
        // and may return more (DataFusion keeps the Limit above), so it bounds
        // nothing.
        if !scan.filters.is_empty() {
            let mut f = self.fresh("ScanFilter", plan);
            self.assert(f.card.le(&out.card));
            self.subset_ndv(&f, &out);
            self.within_all(&f, &out);
            f.facts = out.facts.clone();
            // Filters applied inexactly may let through rows that fail them.
            if !inexact_filters(scan) {
                for filter in &scan.filters {
                    f.facts.assume(filter, plan.schema());
                    self.range_pairs(filter, plan, &f);
                }
            }
            f.origin = out.origin.clone().map(|x| x.narrow(&f.facts, plan.schema()));
            out = f;
        }
        (out, raw_scan)
    }

    /// A composite primary key, or a composite UNIQUE constraint on NOT NULL
    /// columns, is unique as a tuple: the table has at most as many rows as
    /// the product of its key columns' NDVs.
    fn composite_key(&self, scan: &TableScan, rel: &Rel) {
        let Some(constraints) = scan.source.constraints() else {
            return;
        };
        let schema = scan.source.schema();
        for c in constraints.iter() {
            let pk = match c {
                Constraint::PrimaryKey(pk) => pk,
                Constraint::Unique(u) if u.iter().all(|i| !schema.field(*i).is_nullable()) => u,
                Constraint::Unique(_) => continue,
            };
            if pk.len() < 2 {
                continue;
            }
            let positions: Option<Vec<usize>> = pk
                .iter()
                .map(|src| match &scan.projection {
                    None => Some(*src),
                    Some(proj) => proj.iter().position(|p| p == src),
                })
                .collect();
            if let Some(positions) = positions {
                let factors: Vec<&Int> = positions.iter().map(|i| &rel.ndv[*i]).collect();
                if let Some(p) = product(&factors, self.max_product) {
                    self.assert(rel.card.le(p));
                }
            }
        }
    }

    /// Ranking functions number rows from 1, and `row_number()` numbers each
    /// partition's rows 1, 2, 3, ...: with the partition keys, it is unique.
    fn window_functions(&self, plan: &LogicalPlan, input: &LogicalPlan, exprs: &[Expr], o: &mut Rel) {
        let n = input.schema().fields().len();
        for (i, e) in exprs.iter().enumerate() {
            let Expr::WindowFunction(w) = strip_alias(e) else {
                continue;
            };
            let name = w.fun.name();
            if !matches!(name, "row_number" | "rank" | "dense_rank") || w.params.filter.is_some() {
                continue;
            }
            let c = col(plan, n + i);
            o.facts.add(&c, Dom::at_least(1), plan.schema());
            if name != "row_number" {
                continue;
            }
            let partition: Option<Vec<Expr>> = w
                .params
                .partition_by
                .iter()
                .map(|p| match strip_alias(p) {
                    Expr::Column(_) => Some(strip_alias(p).clone()),
                    _ => None,
                })
                .collect();
            if let Some(mut key) = partition {
                key.push(c);
                o.rows.keys.push(key);
            }
        }
    }

    /// Same rows as the input, whose columns come first and unchanged.
    fn same_rows(&mut self, kind: &str, plan: &LogicalPlan, input: &LogicalPlan) -> Rel {
        let l = self.visit(input);
        let mut o = self.fresh(kind, plan);
        self.assert(o.card.eq(&l.card));
        self.equal_ndv(&o, &l);
        self.within_all(&o, &l);
        o.facts = l.facts.by_position(input.schema(), plan.schema());
        let by_position = |c: &Column| {
            let i = input.schema().index_of_column(c).ok()?;
            child_column(plan, i)
        };
        o.rows = l.rows.rename(&by_position);
        o.origin = l.origin.as_ref().map(|x| x.with_width(plan.schema().fields().len()));
        o
    }

    /// The first columns of `o` hold exactly the values of `l`'s columns.
    fn equal_ndv(&self, o: &Rel, l: &Rel) {
        for (a, b) in o.ndv.iter().zip(&l.ndv) {
            self.assert(a.eq(b));
        }
    }

    /// `o` keeps every distinct value of `l`'s columns, but deduplicates by SQL
    /// equality. For floats that can merge values that are distinct as bits
    /// (`-0.0` and `0.0`), so only `<=` is asserted there.
    fn kept_values(&self, plan: &LogicalPlan, o: &Rel, l: &Rel) {
        for (j, (a, b)) in o.ndv.iter().zip(&l.ndv).enumerate() {
            if plan.schema().field(j).data_type().is_floating() {
                self.assert(a.le(b));
            } else {
                self.assert(a.eq(b));
            }
        }
    }

    /// `o`'s rows are a subset of `l`'s.
    fn subset_ndv(&self, o: &Rel, l: &Rel) {
        for (a, b) in o.ndv.iter().zip(&l.ndv) {
            self.assert(a.le(b));
        }
    }

    /// Bounds output column `v`, computed by `e` over the rows of `input`.
    fn expr_ndv(&self, v: &Int, e: &Expr, input: &LogicalPlan, l: &Rel) {
        if let Some(c) = key_column(input, e)
            && let Ok(i) = input.schema().index_of_column(&c)
        {
            // The same values, or an injective image of them.
            self.assert(v.eq(&l.ndv[i]));
        } else if let Some(bound) = expr_bound(e, input, l, self.max_product) {
            self.assert(v.le(bound));
        }
    }

    /// Tightens the NDVs of `o`, the output of filtering `l` by `predicate`.
    fn filter_ndv(&self, predicate: &Expr, input: &LogicalPlan, o: &Rel, l: &Rel) {
        // SQL equality on floats identifies values that are distinct as bits
        // (`-0.0 = 0.0`), so these rules skip float columns.
        let index = |e: &Expr| {
            let i = key_column(input, e).and_then(|c| input.schema().index_of_column(&c).ok())?;
            (!input.schema().field(i).data_type().is_floating()).then_some(i)
        };
        for conj in split_conjunction(predicate) {
            if let Expr::BinaryExpr(BinaryExpr {
                left,
                op: Operator::Eq,
                right,
            }) = conj
                && let (Some(a), Some(b)) = (index(left), index(right))
            {
                // Every surviving row has a = b (neither NULL).
                self.assert(o.ndv[a].eq(&o.ndv[b]));
                self.assert(o.ndv[a].le(&l.ndv[b]));
                self.assert(o.ndv[b].le(&l.ndv[a]));
            }
        }
    }

    fn aggregate(&mut self, plan: &LogicalPlan, agg: &Aggregate) -> Rel {
        let l = self.visit(&agg.input);
        if agg
            .group_expr
            .iter()
            .any(|e| matches!(e, Expr::GroupingSet(_)))
        {
            // ROLLUP / CUBE / GROUPING SETS can emit more rows than they read.
            return self.fresh("GroupingSets", plan);
        }
        if agg.group_expr.is_empty() {
            let mut o = self.fresh("ScalarAggregate", plan);
            self.assert(o.card.eq(int(1)));
            self.aggregate_ranges(agg, &o, &l);
            o.facts = aggregate_facts(plan, agg, &l.facts);
            return o;
        }
        let mut o = self.fresh("GroupBy", plan);
        o.facts = aggregate_facts(plan, agg, &l.facts);
        self.aggregate_ranges(agg, &o, &l);
        // Groups split the input's rows, so their counts sum to at most its
        // row count.
        for (i, e) in agg.aggr_expr.iter().enumerate() {
            if let Expr::AggregateFunction(f) = strip_alias(e)
                && f.func.name() == "count"
            {
                o.rows.sums.push((col(plan, agg.group_expr.len() + i), l.card.clone()));
            }
        }
        self.assert(o.card.le(&l.card));
        self.assert(l.card.ge(int(1)).implies(o.card.ge(int(1))));
        // One group per distinct combination of group values; every value of a
        // group expression shows up in some group.
        let mut factors = vec![];
        for (j, e) in agg.group_expr.iter().enumerate() {
            if plan.schema().field(j).data_type().is_floating() {
                if let Some(bound) = expr_bound(e, &agg.input, &l, self.max_product) {
                    self.assert(o.ndv[j].le(bound));
                }
            } else {
                self.expr_ndv(&o.ndv[j], e, &agg.input, &l);
            }
            factors.push(&o.ndv[j]);
        }
        if let Some(p) = product(&factors, self.max_product) {
            self.assert(o.card.le(p));
        }
        // Keys the others determine add no groups.
        let determining = self.determining_keys(plan, agg.group_expr.len());
        if determining.len() < factors.len() {
            let factors: Vec<&Int> = determining.iter().map(|&j| &o.ndv[j]).collect();
            if let Some(p) = product(&factors, self.max_product) {
                self.assert(o.card.le(p));
            }
        }
        self.determining_column(agg, &o);
        // Grouping by a unique key leaves every row its own group.
        let cols: Option<Vec<Column>> = agg
            .group_expr
            .iter()
            .map(|e| key_column(&agg.input, e))
            .collect();
        if cols.is_some_and(|cols| self.covers_key(&agg.input, &cols, Nulls::Equal)) {
            self.assert(o.card.eq(&l.card));
        }
        o
    }

    /// A column that determines every key, as a key of `nation` does its
    /// name, has at least as many values as there are groups. It may be one
    /// of the input's, or of the rows the projections and filters below it
    /// read: those keep fewer rows, each computed from one of them. The
    /// first of at most 64 columns tried bounds the groups.
    fn determining_column(&self, agg: &Aggregate, o: &Rel) {
        let (mut node, mut keys) = (self.nodes.len() - 1, agg.group_expr.clone());
        let mut tries = 64;
        loop {
            let plan = &self.nodes[node].plan;
            for c in 0..plan.schema().fields().len() {
                if tries == 0 {
                    return;
                }
                tries -= 1;
                let closed = self.fd_closure(plan, &[c]);
                if keys.iter().all(|e| determined(e, plan, &closed)) {
                    self.assert(o.card.le(Int::new_const(self.nodes[node].ndv_vars[c].as_str())));
                    return;
                }
            }
            // The keys over the operator's input.
            keys = match plan {
                LogicalPlan::Projection(p) => {
                    let unprojected: Option<Vec<Expr>> = keys.iter().map(|e| unproject(e, plan, &p.expr)).collect();
                    match unprojected {
                        Some(k) => k,
                        None => return,
                    }
                }
                LogicalPlan::Filter(_) => keys,
                _ => return,
            };
            node = self.nodes[node].inputs[0];
        }
    }

    /// A grouping key's values, and a MIN's or MAX's, are its input's.
    fn aggregate_ranges(&self, agg: &Aggregate, o: &Rel, l: &Rel) {
        let groups = agg.group_expr.len();
        for (j, e) in agg.group_expr.iter().chain(&agg.aggr_expr).enumerate() {
            let arg = match strip_alias(e) {
                e if j < groups => e,
                Expr::AggregateFunction(f) if matches!(f.func.name(), "min" | "max") && f.params.args.len() == 1 => &f.params.args[0],
                _ => continue,
            };
            if let Some(i) = column_index(&agg.input, arg) {
                self.within(o, j, l, i);
            }
        }
    }

    fn join(&mut self, plan: &LogicalPlan, join: &Join) -> Rel {
        let l = self.visit(&join.left);
        let r = self.visit(&join.right);
        let equi = !join.on.is_empty();
        let cross = !equi && join.filter.is_none();
        let (lk, rk): (Vec<&Expr>, Vec<&Expr>) = join.on.iter().map(|(a, b)| (a, b)).unzip();
        // A unique key on one side means each row of the other side matches at
        // most once.
        let ru = equi && self.key_is_unique(join, &join.right, &rk);
        let lu = equi && self.key_is_unique(join, &join.left, &lk);
        // A foreign key from one side to every row of the other's table: each
        // of the first side's rows matches exactly once.
        let (fl, fr) = self.foreign_key(join);
        let kind = format!(
            "{:?}{}Join",
            join.join_type,
            if ru || lu {
                "Key"
            } else if equi {
                "Equi"
            } else if cross {
                "Cross"
            } else {
                "Theta"
            }
        );
        let mut o = self.fresh(&kind, plan);
        let lr = Int::mul(&[&l.card, &r.card]);
        // Bound on the rows the join's matching produces.
        let mut inner = lr.clone();
        if ru || fl {
            inner = min(&inner, &l.card);
        }
        if lu || fr {
            inner = min(&inner, &r.card);
        }
        match join.join_type {
            JoinType::Inner => {
                if cross {
                    self.assert(o.card.eq(&lr));
                } else {
                    self.assert(o.card.le(&inner));
                }
                if fl {
                    self.assert(o.card.eq(&l.card));
                }
                if fr {
                    self.assert(o.card.eq(&r.card));
                }
            }
            // An outer join emits its inner join's rows plus each unmatched row of
            // the preserved side. If each preserved row matches at most once, it
            // appears exactly once.
            JoinType::Left if ru || fl => self.assert(o.card.eq(&l.card)),
            JoinType::Right if lu || fr => self.assert(o.card.eq(&r.card)),
            JoinType::Left | JoinType::Right => {
                let preserved = if join.join_type == JoinType::Left {
                    &l.card
                } else {
                    &r.card
                };
                self.assert(o.card.ge(preserved));
                self.assert(o.card.le(Int::add(&[&inner, preserved])));
            }
            JoinType::Full => {
                self.assert(o.card.ge(&l.card));
                self.assert(o.card.ge(&r.card));
                self.assert(o.card.le(Int::add(&[&inner, &l.card, &r.card])));
                if ru || lu {
                    // One side's rows each appear exactly once, plus the other
                    // side's unmatched rows.
                    self.assert(o.card.le(Int::add(&[&l.card, &r.card])));
                }
            }
            // Every row of the referencing side has a partner.
            JoinType::LeftSemi if fl => self.assert(o.card.eq(&l.card)),
            JoinType::LeftAnti if fl => self.assert(o.card.eq(int(0))),
            JoinType::RightSemi if fr => self.assert(o.card.eq(&r.card)),
            JoinType::RightAnti if fr => self.assert(o.card.eq(int(0))),
            JoinType::LeftSemi | JoinType::LeftAnti => self.assert(o.card.le(&l.card)),
            JoinType::RightSemi | JoinType::RightAnti => self.assert(o.card.le(&r.card)),
            JoinType::LeftMark => self.assert(o.card.eq(&l.card)),
            JoinType::RightMark => self.assert(o.card.eq(&r.card)),
        }
        self.join_parts(join, &o, &l, &r, &inner, (ru, lu, fl, fr));
        self.at_most_once = (ru || fl, lu || fr);
        self.join_ndv(join, &o, &l, &r);
        self.join_ranges(plan, join, &o, &l, &r);
        o.facts = join_facts(plan, join, &l.facts, &r.facts);
        // Semi, anti and mark joins keep a subset of one side's rows.
        o.rows = match join.join_type {
            JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => l.rows.clone(),
            JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => r.rows.clone(),
            _ => Rows::default(),
        };
        // On an outer join, a padded-side column that is never NULL on matched
        // rows is NULL exactly on the padded rows: at most the other side's
        // rows. It is non-NULL on the matched rows (and, for a full join, the
        // side's own unmatched rows). A full join also keeps each side's own
        // unmatched rows, whose equi-keys may be NULL, so there only columns
        // never NULL on their side qualify.
        let nl = join.left.schema().fields().len();
        let (pad_left, pad_right) = match join.join_type {
            JoinType::Left => (false, true),
            JoinType::Right => (true, false),
            JoinType::Full => (true, true),
            _ => (false, false),
        };
        let full = join.join_type == JoinType::Full;
        if pad_right {
            let values = if full { Int::add(&[&inner, &r.card]) } else { inner.clone() };
            let keys = if full { &[][..] } else { &rk[..] };
            for c in never_null_when_matched(join, &join.right, &r.facts, keys) {
                o.rows.nulls.push((col(plan, nl + c), l.card.clone(), values.clone()));
            }
        }
        if pad_left {
            let values = if full { Int::add(&[&inner, &l.card]) } else { inner.clone() };
            let keys = if full { &[][..] } else { &lk[..] };
            for c in never_null_when_matched(join, &join.left, &l.facts, keys) {
                o.rows.nulls.push((col(plan, c), r.card.clone(), values.clone()));
            }
        }
        let width = plan.schema().fields().len();
        o.origin = match join.join_type {
            JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => l.origin.as_ref(),
            JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => r.origin.as_ref(),
            _ => None,
        }
        .map(|x| x.with_width(width).narrow(&o.facts, plan.schema()));
        o
    }

    /// An outer or anti join's rows, in terms of its inner join's rows
    /// (`{o}_inner`) and the rows of each side with a partner (`{o}_left`,
    /// `{o}_right`): the counts `validate` measures its selectivities with
    /// (`selectivity::auxiliary_joins`). `inner` bounds the inner join's rows;
    /// `keys` says whether the right and left keys are unique, and whether a
    /// foreign key goes from the left or the right side to all of the other.
    fn join_parts(&mut self, join: &Join, o: &Rel, l: &Rel, r: &Rel, inner: &Int, keys: (bool, bool, bool, bool)) {
        let parts = auxiliary_joins(join);
        if parts.is_empty() {
            return;
        }
        let (ru, lu, fl, fr) = keys;
        let name = self.name_of(&o.card);
        let mut count = |suffix: &str| {
            parts.iter().any(|(s, _)| *s == suffix).then(|| self.new_var(format!("{name}_{suffix}")))
        };
        let (i, ml, mr) = (count("inner"), count("left"), count("right"));
        if let Some(i) = &i {
            self.assert(i.le(inner));
        }
        // Each side's rows with a partner. Each matches at most once if the
        // other side's key is unique, and exactly once on a foreign key.
        for (m, side, unique, foreign) in [(&ml, &l.card, ru, fl), (&mr, &r.card, lu, fr)] {
            if let (Some(i), true) = (&i, foreign) {
                self.assert(i.eq(side));
            }
            let Some(m) = m else { continue };
            self.assert(m.le(side));
            if foreign {
                self.assert(m.eq(side));
            }
            let Some(i) = &i else { continue };
            self.assert(m.le(i));
            // A matched pair has a row on each side.
            self.assert(i.ge(int(1)).implies(m.ge(int(1))));
            if unique {
                self.assert(i.eq(m));
            }
        }
        let unmatched = |side: &Int, m: &Option<Int>| m.as_ref().map(|m| Int::sub(&[side, m]));
        let (ul, ur) = (unmatched(&l.card, &ml), unmatched(&r.card, &mr));
        let rows = match (join.join_type, &i, &ul, &ur) {
            (JoinType::Left, Some(i), Some(ul), _) => Int::add(&[i, ul]),
            (JoinType::Right, Some(i), _, Some(ur)) => Int::add(&[i, ur]),
            (JoinType::Full, Some(i), Some(ul), Some(ur)) => Int::add(&[i, ul, ur]),
            (JoinType::LeftAnti, _, Some(ul), _) => ul.clone(),
            (JoinType::RightAnti, _, _, Some(ur)) => ur.clone(),
            _ => return,
        };
        self.assert(o.card.eq(&rows));
    }

    /// Whether `join` is on exactly a declared foreign key's columns, from the
    /// left side's values to every row of the table they reference, and from
    /// the right's.
    fn foreign_key(&self, join: &Join) -> (bool, bool) {
        if join.on.is_empty() || join.filter.is_some() {
            return (false, false);
        }
        let from_left = self.references(&join.left, &join.right, join.on.iter().map(|(a, b)| (a, b)));
        let from_right = self.references(&join.right, &join.left, join.on.iter().map(|(a, b)| (b, a)));
        (from_left, from_right)
    }

    /// True if each pair `(f, t)` compares a column of `from` with one of
    /// `to`, together exactly a foreign key's columns: `from`'s hold one row's
    /// values of the referencing columns, and `to` holds every row of the
    /// referenced table once.
    fn references<'e>(
        &self,
        from: &LogicalPlan,
        to: &LogicalPlan,
        pairs: impl Iterator<Item = (&'e Expr, &'e Expr)>,
    ) -> bool {
        let mut source: Option<(String, String)> = None;
        let mut target: Option<String> = None;
        let mut cols = vec![];
        for (f, t) in pairs {
            let (Some(fc), Some(tc)) = (key_column(from, f), key_column(to, t)) else {
                return false;
            };
            let (Some((ft, row, fname)), Some((tt, tname))) =
                (self.values(from, &fc, String::new()), self.every_row(to, &tc))
            else {
                return false;
            };
            if *source.get_or_insert((ft.clone(), row.clone())) != (ft, row)
                || *target.get_or_insert(tt.clone()) != tt
            {
                return false;
            }
            cols.push((fname, tname));
        }
        let (Some((from_table, _)), Some(to_table)) = (source, target) else {
            return false;
        };
        cols.sort();
        cols.dedup();
        self.foreign_keys.iter().any(|fk| {
            let pairs: Vec<(String, String)> =
                fk.pairs().into_iter().map(|(a, b)| (a.to_string(), b.to_string())).collect();
            fk.table == from_table && fk.references == to_table && pairs == cols
        })
    }

    /// The stored column whose values column `c` of `plan` holds on every
    /// row: `(table, row, column)`, where columns with the same `row` hold
    /// values of one row of the table. `path` names the scan by the join
    /// sides leading to it, so two reads of one table stay apart.
    fn values(&self, plan: &LogicalPlan, c: &Column, path: String) -> Option<(String, String, String)> {
        let i = plan.schema().index_of_column(c).ok()?;
        let through = |child: &LogicalPlan, path: String| self.values(child, &child_column(child, i)?, path);
        match plan {
            LogicalPlan::TableScan(scan) => match (self.resolve)(scan) {
                ScanKind::Base { display, .. } => Some((display, path, c.name.clone())),
                ScanKind::NonBase => None,
            },
            LogicalPlan::Projection(p) => self.values(&p.input, &key_column(&p.input, &p.expr[i])?, path),
            LogicalPlan::Aggregate(a) => {
                let key = a.group_expr.get(i)?;
                self.values(&a.input, &key_column(&a.input, key)?, path)
            }
            LogicalPlan::Filter(_)
            | LogicalPlan::Sort(_)
            | LogicalPlan::Limit(_)
            | LogicalPlan::Repartition(_)
            | LogicalPlan::SubqueryAlias(_)
            | LogicalPlan::Subquery(_)
            | LogicalPlan::Window(_)
            | LogicalPlan::Distinct(Distinct::All(_)) => through(plan.inputs()[0], path),
            // A padded side's columns may be NULL.
            LogicalPlan::Join(join) => {
                let nl = join.left.schema().fields().len();
                match join.join_type {
                    JoinType::Inner | JoinType::Left if i < nl => through(&join.left, path + "L"),
                    JoinType::Inner | JoinType::Right if i >= nl => {
                        let child = &join.right;
                        self.values(child, &child_column(child, i - nl)?, path + "R")
                    }
                    JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => through(&join.left, path),
                    JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => through(&join.right, path),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The stored table and column, if `plan` holds each of the table's rows
    /// exactly once and column `c` holds that column.
    fn every_row(&self, plan: &LogicalPlan, c: &Column) -> Option<(String, String)> {
        let i = plan.schema().index_of_column(c).ok()?;
        let through = |child: &LogicalPlan| self.every_row(child, &child_column(child, i)?);
        match plan {
            LogicalPlan::TableScan(scan) if scan.filters.is_empty() && scan.fetch.is_none() => {
                match (self.resolve)(scan) {
                    ScanKind::Base { display, .. } => Some((display, c.name.clone())),
                    ScanKind::NonBase => None,
                }
            }
            LogicalPlan::Projection(p) => self.every_row(&p.input, &key_column(&p.input, &p.expr[i])?),
            LogicalPlan::Sort(s) if s.fetch.is_none() => through(&s.input),
            LogicalPlan::Repartition(_)
            | LogicalPlan::SubqueryAlias(_)
            | LogicalPlan::Subquery(_)
            | LogicalPlan::Window(_) => through(plan.inputs()[0]),
            _ => None,
        }
    }

    /// A join's output values are its inputs', and matched equi-keys take
    /// values both sides have: on an inner join, the two keys' values are
    /// the same. Disjoint ranges leave no row with a value, so none at all.
    fn join_ranges(&self, plan: &LogicalPlan, join: &Join, o: &Rel, l: &Rel, r: &Rel) {
        let nl = l.min.len();
        let (left, right) = match join.join_type {
            JoinType::Inner | JoinType::Left | JoinType::Right | JoinType::Full => (Some(0), Some(nl)),
            JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => (Some(0), None),
            JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => (None, Some(0)),
        };
        for (side, at) in [(l, left), (r, right)] {
            if let Some(at) = at {
                for i in 0..side.min.len() {
                    self.within(o, at + i, side, i);
                }
            }
        }
        if !matches!(join.join_type, JoinType::Inner | JoinType::LeftSemi | JoinType::RightSemi) {
            return;
        }
        for (a, b) in &join.on {
            let (Some(ia), Some(ib)) = (column_index(&join.left, a), column_index(&join.right, b)) else { continue };
            match join.join_type {
                JoinType::Inner => {
                    self.within(o, ia, r, ib);
                    self.within(o, nl + ib, l, ia);
                    if let (Some(a_lo), Some(a_hi), Some(b_lo), Some(b_hi)) = (&o.min[ia], &o.max[ia], &o.min[nl + ib], &o.max[nl + ib]) {
                        self.assert(a_lo.eq(b_lo));
                        self.assert(a_hi.eq(b_hi));
                    }
                }
                JoinType::LeftSemi => self.within(o, ia, r, ib),
                _ => self.within(o, ib, l, ia),
            }
        }
        if let (JoinType::Inner, Some(f)) = (join.join_type, &join.filter) {
            self.range_pairs(f, plan, o);
        }
    }

    /// NDVs of a join's output columns: values come from the inputs, plus NULL
    /// on a padded side, and equi-key columns only keep values both sides share.
    fn join_ndv(&self, join: &Join, o: &Rel, l: &Rel, r: &Rel) {
        let (nl, nr) = (l.ndv.len(), r.ndv.len());
        // (output position, input rel, input position, padded, exact)
        let mut map: Vec<(usize, &Rel, usize, bool, bool)> = vec![];
        match join.join_type {
            JoinType::Inner | JoinType::Left | JoinType::Right | JoinType::Full => {
                let left_padded = matches!(join.join_type, JoinType::Right | JoinType::Full);
                let right_padded = matches!(join.join_type, JoinType::Left | JoinType::Full);
                let left_exact = join.join_type == JoinType::Left;
                let right_exact = join.join_type == JoinType::Right;
                map.extend((0..nl).map(|i| (i, l, i, left_padded, left_exact)));
                map.extend((0..nr).map(|i| (nl + i, r, i, right_padded, right_exact)));
            }
            JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => {
                map.extend((0..nl).map(|i| (i, l, i, false, join.join_type == JoinType::LeftMark)));
            }
            JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => {
                map.extend(
                    (0..nr).map(|i| (i, r, i, false, join.join_type == JoinType::RightMark)),
                );
            }
        }
        for (out, rel, i, padded, exact) in map {
            let src = &rel.ndv[i];
            if exact {
                // Every row of this side appears (a preserved side, or a mark join).
                self.assert(o.ndv[out].eq(src));
            } else if padded {
                self.assert(o.ndv[out].le(src + int(1)));
            } else {
                self.assert(o.ndv[out].le(src));
            }
        }
        // Matched equi-key values exist on both sides.
        let matches_only = matches!(
            join.join_type,
            JoinType::Inner | JoinType::LeftSemi | JoinType::RightSemi
        );
        if !matches_only {
            return;
        }
        for (a, b) in &join.on {
            let (Some(ca), Some(cb)) = (key_column(&join.left, a), key_column(&join.right, b))
            else {
                continue;
            };
            let (Ok(ia), Ok(ib)) = (
                join.left.schema().index_of_column(&ca),
                join.right.schema().index_of_column(&cb),
            ) else {
                continue;
            };
            if join.left.schema().field(ia).data_type().is_floating()
                || join.right.schema().field(ib).data_type().is_floating()
            {
                continue;
            }
            match join.join_type {
                JoinType::Inner => {
                    self.assert(o.ndv[ia].le(&r.ndv[ib]));
                    self.assert(o.ndv[nl + ib].le(&l.ndv[ia]));
                }
                JoinType::LeftSemi => self.assert(o.ndv[ia].le(&r.ndv[ib])),
                JoinType::RightSemi => self.assert(o.ndv[ib].le(&l.ndv[ia])),
                _ => {}
            }
        }
    }
}

/// `e`, over the output of projection `plan` computing `exprs`, as an
/// expression over its input. `None` if it reads what it can't rewrite.
fn unproject(e: &Expr, plan: &LogicalPlan, exprs: &[Expr]) -> Option<Expr> {
    let mut ok = true;
    let out = e
        .clone()
        .transform_up(|x| match &x {
            Expr::Column(c) => match plan.schema().index_of_column(c) {
                Ok(j) => Ok(Transformed::yes(strip_alias(&exprs[j]).clone())),
                Err(_) => {
                    ok = false;
                    Ok(Transformed::no(x))
                }
            },
            _ => Ok(Transformed::no(x)),
        })
        .ok()?
        .data;
    ok.then_some(out)
}

/// Integers, and dates as days: the columns with min and max variables.
fn integer_like(t: &DataType) -> bool {
    t.is_integer() || *t == DataType::Date32
}

/// The names of `vars`, by column.
fn range_names(vars: &[Option<Int>]) -> Vec<Option<String>> {
    vars.iter().map(|v| v.as_ref().map(|v| v.to_string())).collect()
}

/// The names of the columns that a comparison, equi-join key or grouping
/// key of `plan` reads. Only these get min and max variables, which add
/// constraints at every operator: the others' would carry nothing.
fn ranged_columns(plan: &LogicalPlan) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let _ = plan.apply_with_subqueries(|p| {
        let mut read = |e: &Expr| out.extend(e.column_refs().into_iter().map(|c| c.name.clone()));
        match p {
            LogicalPlan::Join(j) => j.on.iter().for_each(|(a, b)| {
                read(a);
                read(b);
            }),
            LogicalPlan::Aggregate(a) => a.group_expr.iter().for_each(&mut read),
            _ => {}
        }
        for e in p.expressions() {
            let _ = e.apply(|x| {
                match x {
                    Expr::BinaryExpr(BinaryExpr { op, .. }) if op.swap().is_some() => read(x),
                    Expr::Between(_) | Expr::InList(_) => read(x),
                    _ => {}
                }
                Ok(TreeNodeRecursion::Continue)
            });
        }
        Ok(TreeNodeRecursion::Continue)
    });
    out
}

/// Output column `j` of `plan`, as an expression.
fn col(plan: &LogicalPlan, j: usize) -> Expr {
    Expr::Column(Column::from(plan.schema().qualified_field(j)))
}

/// Facts on the output of an operator computing `exprs` over the rows of
/// `input`: each output column takes its expression's values, and facts on
/// input columns passed through unchanged still hold.
fn computed_facts(plan: &LogicalPlan, exprs: &[Expr], input: &LogicalPlan, facts: &Facts) -> Facts {
    let passed = |c: &Column| passed_column(plan, exprs, c);
    let mut out = facts.rename(&passed);
    for (j, e) in exprs.iter().enumerate() {
        if let Some(e) = domain::rename(e, &passed) {
            out.define(&col(plan, j), &e, plan.schema());
        }
        out.add(&col(plan, j), facts.dom(e, input.schema()), plan.schema());
    }
    out
}

/// The output column of `plan`, computing `exprs`, that passes input column
/// `c` through unchanged.
fn passed_column(plan: &LogicalPlan, exprs: &[Expr], c: &Column) -> Option<Column> {
    let j = exprs
        .iter()
        .position(|e| matches!(strip_alias(e), Expr::Column(x) if x == c))?;
    Some(Column::from(plan.schema().qualified_field(j)))
}

/// Positions of `side`'s columns that are never NULL on a row matched by
/// `join`: those never NULL on `side`, and its equi-key columns `keys`
/// (unless NULL keys match).
fn never_null_when_matched(join: &Join, side: &LogicalPlan, facts: &Facts, keys: &[&Expr]) -> Vec<usize> {
    let schema = side.schema();
    let keys_non_null = join.null_equality != NullEquality::NullEqualsNull;
    (0..schema.fields().len())
        .filter(|&i| {
            let c = Expr::Column(Column::from(schema.qualified_field(i)));
            let key = keys_non_null && keys.iter().any(|k| strip_alias(k) == &c);
            key || facts.dom(&c, schema).never_null()
        })
        .collect()
}

fn strip_alias(e: &Expr) -> &Expr {
    match e {
        Expr::Alias(a) => strip_alias(&a.expr),
        e => e,
    }
}

/// Facts on an aggregate's output: each group key takes its expression's
/// values, and MIN or MAX takes one of its argument's values, or NULL.
fn aggregate_facts(plan: &LogicalPlan, agg: &Aggregate, input: &Facts) -> Facts {
    let in_schema = agg.input.schema();
    let groups = agg.group_expr.len();
    let mut out = Facts::default();
    for (j, e) in agg.group_expr.iter().chain(&agg.aggr_expr).enumerate() {
        let dom = if j < groups {
            input.dom(e, in_schema)
        } else {
            match strip_alias(e) {
                Expr::AggregateFunction(f)
                    if matches!(f.func.name(), "min" | "max") && f.params.args.len() == 1 =>
                {
                    input.dom(&f.params.args[0], in_schema).with_null()
                }
                // A group has at least one row, and `count(*)` counts it.
                Expr::AggregateFunction(f) if f.func.name() == "count" => {
                    let counts_all = f.params.filter.is_none()
                        && !f.params.distinct
                        && f.params.args.iter().all(|a| input.dom(a, in_schema).never_null());
                    Dom::at_least(if groups > 0 && counts_all { 1 } else { 0 })
                }
                _ => continue,
            }
        };
        out.add(&col(plan, j), dom, plan.schema());
    }
    out
}

/// Facts on a join's output: each side's facts, NULL on a padded side, and
/// matched equi-keys take values both sides have.
fn join_facts(plan: &LogicalPlan, join: &Join, l: &Facts, r: &Facts) -> Facts {
    let schema = plan.schema();
    let nulls_match = join.null_equality == NullEquality::NullEqualsNull;
    // The values a matched pair of keys takes.
    let matched = |a: &Expr, b: &Expr| {
        let d = l
            .dom(a, join.left.schema())
            .intersect(&r.dom(b, join.right.schema()));
        if nulls_match { d } else { d.without_null() }
    };
    let mut out = match join.join_type {
        JoinType::Inner | JoinType::Left | JoinType::Right | JoinType::Full => {
            let pad_left = matches!(join.join_type, JoinType::Right | JoinType::Full);
            let pad_right = matches!(join.join_type, JoinType::Left | JoinType::Full);
            let mut out = if pad_left { l.nullable() } else { l.clone() };
            out.extend(&if pad_right { r.nullable() } else { r.clone() });
            out
        }
        JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => l.clone(),
        JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => r.clone(),
    };
    match join.join_type {
        JoinType::Inner => {
            for (a, b) in &join.on {
                out.add(a, matched(a, b), schema);
                out.add(b, matched(a, b), schema);
            }
            if let Some(f) = &join.filter {
                out.assume(f, schema);
            }
        }
        JoinType::LeftSemi => {
            for (a, b) in &join.on {
                out.add(a, matched(a, b), schema);
            }
        }
        JoinType::RightSemi => {
            for (a, b) in &join.on {
                out.add(b, matched(a, b), schema);
            }
        }
        _ => {}
    }
    out
}

/// True unless `e` is a deterministic function of the columns it reads: it
/// is volatile, or reads a subquery, an outer query or a parameter.
fn opaque(e: &Expr) -> bool {
    e.is_volatile()
        || e.exists(|x| {
            Ok(matches!(
                x,
                Expr::ScalarSubquery(_)
                    | Expr::Exists(_)
                    | Expr::InSubquery(_)
                    | Expr::SetComparison(_)
                    | Expr::OuterReferenceColumn(..)
                    | Expr::Placeholder(_)
            ))
        })
        .unwrap_or(true)
}

/// True if `e`, over the rows of `input`, takes one value on rows that agree
/// on the columns `determined` (positions in `input`'s output).
fn determined(e: &Expr, input: &LogicalPlan, determined: &BTreeSet<usize>) -> bool {
    !opaque(e)
        && e.column_refs()
            .into_iter()
            .all(|c| input.schema().index_of_column(c).is_ok_and(|i| determined.contains(&i)))
}

/// Pairs of `input`'s output positions that `predicate` holds equal on every
/// row it keeps. Floats are left out: SQL equality identifies values that
/// are distinct as bits (`-0.0 = 0.0`).
fn equalities(predicate: &Expr, input: &LogicalPlan) -> Vec<(usize, usize)> {
    split_conjunction(predicate)
        .into_iter()
        .filter_map(|conj| match conj {
            Expr::BinaryExpr(BinaryExpr { left, op: Operator::Eq, right }) => {
                Some((exact_index(input, left)?, exact_index(input, right)?))
            }
            _ => None,
        })
        .collect()
}

/// [`column_index`], of a column whose type is not a float.
fn exact_index(input: &LogicalPlan, e: &Expr) -> Option<usize> {
    let i = column_index(input, e)?;
    (!input.schema().field(i).data_type().is_floating()).then_some(i)
}

/// The closure `close` gives of `keys`, where each of `pairs` holds two
/// columns equal on every row: a column equal to a determined one is
/// determined too.
fn with_equalities(
    mut keys: Vec<usize>,
    pairs: &[(usize, usize)],
    close: impl Fn(&[usize]) -> BTreeSet<usize>,
) -> BTreeSet<usize> {
    loop {
        let closed = close(&keys);
        let before = keys.len();
        for &(a, b) in pairs {
            for (x, y) in [(a, b), (b, a)] {
                if closed.contains(&x) && !closed.contains(&y) && !keys.contains(&y) {
                    keys.push(y);
                }
            }
        }
        if keys.len() == before {
            return closed;
        }
    }
}

/// An upper bound on the number of distinct values `e` takes over the rows of
/// `input`, or `None` if nothing better than the row count is known. A
/// deterministic function of some columns takes at most as many values as
/// there are combinations of theirs.
fn expr_bound(e: &Expr, input: &LogicalPlan, l: &Rel, cap: usize) -> Option<Int> {
    if let Some(c) = key_column(input, e) {
        let i = input.schema().index_of_column(&c).ok()?;
        return Some(l.ndv[i].clone());
    }
    if opaque(e) {
        return None;
    }
    let factors: Option<Vec<&Int>> = e
        .column_refs()
        .into_iter()
        .map(|c| input.schema().index_of_column(c).ok().map(|i| &l.ndv[i]))
        .collect();
    product(&factors?, cap)
}

/// The column `e` reads from `input`, if `e` is that column possibly wrapped in
/// casts that cannot make two distinct values equal.
fn key_column(input: &LogicalPlan, e: &Expr) -> Option<Column> {
    match e {
        Expr::Column(c) => Some(c.clone()),
        Expr::Alias(a) => key_column(input, &a.expr),
        Expr::Cast(Cast { expr, field }) | Expr::TryCast(TryCast { expr, field }) => {
            let from = expr.get_type(input.schema()).ok()?;
            injective_cast(&from, field.data_type()).then(|| key_column(input, expr))?
        }
        _ => None,
    }
}

/// The position in `input`'s output of the column `e` reads (see
/// [`key_column`]).
fn column_index(input: &LogicalPlan, e: &Expr) -> Option<usize> {
    input.schema().index_of_column(&key_column(input, e)?).ok()
}

/// True if casting `from` to `to` maps distinct values to distinct values.
fn injective_cast(from: &DataType, to: &DataType) -> bool {
    use DataType::*;
    // Decimal digits an integer type's values need.
    let digits = match from {
        Int8 | UInt8 => Some(3),
        Int16 | UInt16 => Some(5),
        Int32 | UInt32 => Some(10),
        Int64 => Some(19),
        UInt64 => Some(20),
        _ => None,
    };
    from == to
        || matches!(
            (from, to),
            (Int8, Int16 | Int32 | Int64)
                | (Int16, Int32 | Int64)
                | (Int32, Int64)
                | (UInt8, UInt16 | UInt32 | UInt64 | Int16 | Int32 | Int64)
                | (UInt16, UInt32 | UInt64 | Int32 | Int64)
                | (UInt32, UInt64 | Int64)
                | (Utf8 | LargeUtf8 | Utf8View, Utf8 | LargeUtf8 | Utf8View)
                // Floats hold integers exactly up to 2^24 and 2^53.
                | (Int8 | Int16 | UInt8 | UInt16, Float32)
                | (Int8 | Int16 | Int32 | UInt8 | UInt16 | UInt32, Float64)
        )
        || match (digits, to) {
            (Some(d), Decimal128(p, s) | Decimal256(p, s)) => i16::from(*p) - i16::from(*s) >= d,
            _ => false,
        }
}

/// The column of `child` feeding output position `i`, for operators whose output
/// columns start with their child's columns unchanged.
fn child_column(child: &LogicalPlan, i: usize) -> Option<Column> {
    let schema = child.schema();
    (i < schema.fields().len()).then(|| Column::from(schema.qualified_field(i)))
}

/// Maps `cols` of `plan`'s output to the child columns at the same positions.
fn same_positions(plan: &LogicalPlan, child: &LogicalPlan, cols: &[Column]) -> Option<Vec<Column>> {
    cols.iter()
        .map(|c| {
            let i = plan.schema().index_of_column(c).ok()?;
            child_column(child, i)
        })
        .collect()
}

/// Columns `predicate` holds equal to a non-NULL constant on every row it keeps.
fn pinned(predicate: &Expr) -> Vec<Column> {
    split_conjunction(predicate)
        .into_iter()
        .filter_map(|e| match e {
            Expr::BinaryExpr(BinaryExpr { left, op: Operator::Eq, right }) => {
                match (strip_alias(left), strip_alias(right)) {
                    (Expr::Column(c), Expr::Literal(v, _)) | (Expr::Literal(v, _), Expr::Column(c)) if !v.is_null() => {
                        Some(c.clone())
                    }
                    _ => None,
                }
            }
            _ => None,
        })
        .collect()
}

/// Positions of `cols` in `plan`'s output.
fn output_indices(plan: &LogicalPlan, cols: &[Column]) -> Option<Vec<usize>> {
    cols.iter()
        .map(|c| plan.schema().index_of_column(c).ok())
        .collect()
}

/// Whether two NULLs count as the same key value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Nulls {
    /// As in a GROUP BY, DISTINCT or NDV, where NULLs form one value.
    Equal,
    /// As in an equi-join, where a NULL key matches nothing.
    Distinct,
}

impl<'a> Analyzer<'a> {
    /// True if each row of the other side of `join` matches at most one row of
    /// `side` on its key expressions `keys` (see `covers_key`): the keys are
    /// columns, possibly under injective casts, unique in `side`'s output. NULL
    /// keys match nothing unless the join compares them as equal.
    fn key_is_unique(&self, join: &Join, side: &LogicalPlan, keys: &[&Expr]) -> bool {
        let Some(cols) = keys
            .iter()
            .map(|e| key_column(side, e))
            .collect::<Option<Vec<Column>>>()
        else {
            return false;
        };
        let nulls = match join.null_equality {
            NullEquality::NullEqualsNothing => Nulls::Distinct,
            NullEquality::NullEqualsNull => Nulls::Equal,
        };
        self.covers_key(side, &cols, nulls)
    }

    /// True if `cols` of `plan`'s output are unique, with NULLs compared as
    /// `nulls` says: they trace back to a declared primary key, a UNIQUE
    /// constraint, a GROUP BY key or a DISTINCT output through operators that
    /// never duplicate rows. A UNIQUE column may hold many NULLs, so it is
    /// unique with NULLs equal only if it is NOT NULL.
    fn covers_key(&self, plan: &LogicalPlan, cols: &[Column], nulls: Nulls) -> bool {
        match plan {
            LogicalPlan::TableScan(scan) => {
                let schema = scan.source.schema();
                let Some(indices) = cols
                    .iter()
                    .map(|c| schema.index_of(&c.name).ok())
                    .collect::<Option<Vec<usize>>>()
                else {
                    return false;
                };
                let unique = |u: &[usize]| {
                    u.iter().all(|i| indices.contains(i))
                        && (nulls == Nulls::Distinct || u.iter().all(|i| !schema.field(*i).is_nullable()))
                };
                let declared = scan.source.constraints().is_some_and(|cs| {
                    cs.iter().any(|c| match c {
                        Constraint::PrimaryKey(pk) => pk.iter().all(|i| indices.contains(i)),
                        Constraint::Unique(u) => unique(u),
                    })
                });
                // A foreign key references a key, so its referenced columns
                // are unique, like a UNIQUE constraint's.
                let ScanKind::Base { display, .. } = (self.resolve)(scan) else {
                    return declared;
                };
                declared
                    || self.foreign_keys.iter().filter(|fk| fk.references == display).any(|fk| {
                        let referenced: Option<Vec<usize>> =
                            fk.referenced.iter().map(|c| schema.index_of(c).ok()).collect();
                        referenced.is_some_and(|r| unique(&r))
                    })
            }
            // A column the filter pins to one value adds nothing to tell its rows
            // apart: if the input is unique on it with `cols`, the filter's rows
            // are unique on `cols` alone, e.g. `rn = 1` over `row_number()`.
            LogicalPlan::Filter(f) => {
                let Some(cs) = same_positions(plan, &f.input, cols) else {
                    return false;
                };
                if self.covers_key(&f.input, &cs, nulls) {
                    return true;
                }
                let mut with = cs.clone();
                for c in pinned(&f.predicate) {
                    if f.input.schema().has_column(&c) && !with.contains(&c) {
                        with.push(c);
                    }
                }
                with.len() > cs.len() && self.covers_key(&f.input, &with, nulls)
            }
            // `row_number()` numbers each partition's rows 1, 2, ...: it is unique
            // with its partition columns. Otherwise the window keeps its input's
            // rows, so the input's keys among `cols` stay unique.
            LogicalPlan::Window(w) => {
                let Some(ix) = output_indices(plan, cols) else {
                    return false;
                };
                let n = w.input.schema().fields().len();
                let numbered = ix.iter().filter(|&&i| i >= n).any(|&i| match strip_alias(&w.window_expr[i - n]) {
                    Expr::WindowFunction(f) if f.fun.name() == "row_number" && f.params.filter.is_none() => {
                        f.params.partition_by.iter().all(|p| match strip_alias(p) {
                            Expr::Column(c) => w.input.schema().index_of_column(c).is_ok_and(|j| ix.contains(&j)),
                            _ => false,
                        })
                    }
                    _ => false,
                });
                let kept: Vec<Column> = ix
                    .iter()
                    .filter(|&&i| i < n)
                    .map(|&i| Column::from(w.input.schema().qualified_field(i)))
                    .collect();
                numbered || (!kept.is_empty() && self.covers_key(&w.input, &kept, nulls))
            }
            // Operators whose output rows are a subset of their input's, with the
            // input's columns first and unchanged.
            LogicalPlan::Sort(_)
            | LogicalPlan::Limit(_)
            | LogicalPlan::Repartition(_)
            | LogicalPlan::SubqueryAlias(_) => {
                let child = plan.inputs()[0];
                same_positions(plan, child, cols).is_some_and(|cs| self.covers_key(child, &cs, nulls))
            }
            // DISTINCT's output is unique on all its columns, and is a subset of its
            // input's rows, so its input's keys stay unique too.
            LogicalPlan::Distinct(Distinct::All(input)) => {
                let all = output_indices(plan, cols)
                    .is_some_and(|ix| (0..plan.schema().fields().len()).all(|i| ix.contains(&i)));
                all || same_positions(plan, input, cols)
                    .is_some_and(|cs| self.covers_key(input, &cs, nulls))
            }
            // DISTINCT ON is unique on its ON expressions, where they are selected
            // as columns; its rows are a subset of its input's.
            LogicalPlan::Distinct(Distinct::On(on)) => {
                let Some(ix) = output_indices(plan, cols) else {
                    return false;
                };
                let on_positions: Option<Vec<usize>> = on
                    .on_expr
                    .iter()
                    .map(|e| {
                        let c = key_column(&on.input, e)?;
                        on.select_expr
                            .iter()
                            .position(|s| key_column(&on.input, s).as_ref() == Some(&c))
                    })
                    .collect();
                let by_on = on_positions.is_some_and(|ps| ps.iter().all(|p| ix.contains(p)));
                let mapped: Option<Vec<Column>> = ix
                    .iter()
                    .map(|&i| key_column(&on.input, &on.select_expr[i]))
                    .collect();
                by_on || mapped.is_some_and(|cs| self.covers_key(&on.input, &cs, nulls))
            }
            // GROUP BY emits one row per distinct combination of its keys (NULLs
            // forming one group), so it is unique on all its key columns, and on any
            // keys that are unique in its input. With no GROUP BY there is exactly
            // one row, unique on anything. ROLLUP / CUBE / GROUPING SETS repeat keys
            // across grouping levels.
            LogicalPlan::Aggregate(agg) => {
                if agg
                    .group_expr
                    .iter()
                    .any(|e| matches!(e, Expr::GroupingSet(_)))
                {
                    return false;
                }
                if agg.group_expr.is_empty() {
                    return true;
                }
                let Some(ix) = output_indices(plan, cols) else {
                    return false;
                };
                let groups = agg.group_expr.len();
                if (0..groups).all(|i| ix.contains(&i)) {
                    return true;
                }
                let mapped: Option<Vec<Column>> = ix
                    .iter()
                    .map(|&i| {
                        if i < groups {
                            key_column(&agg.input, &agg.group_expr[i])
                        } else {
                            None
                        }
                    })
                    .collect();
                if mapped.is_some_and(|cs| self.covers_key(&agg.input, &cs, nulls)) {
                    return true;
                }
                // Columns that determine every key pick out one group.
                let closed = self.fd_closure(plan, &ix);
                (0..groups).all(|i| closed.contains(&i))
            }
            LogicalPlan::Projection(p) => {
                let mapped = cols
                    .iter()
                    .map(|c| {
                        let i = p.schema.index_of_column(c).ok()?;
                        key_column(&p.input, &p.expr[i])
                    })
                    .collect::<Option<Vec<Column>>>();
                mapped.is_some_and(|cs| self.covers_key(&p.input, &cs, nulls))
            }
            LogicalPlan::Join(join) => {
                let left_len = join.left.schema().fields().len();
                let Some(indices) = cols
                    .iter()
                    .map(|c| plan.schema().index_of_column(c).ok())
                    .collect::<Option<Vec<usize>>>()
                else {
                    return false;
                };
                let left_cols = || -> Option<Vec<Column>> {
                    indices
                        .iter()
                        .map(|i| child_column(&join.left, *i))
                        .collect()
                };
                let (lk, rk): (Vec<&Expr>, Vec<&Expr>) = join.on.iter().map(|(a, b)| (a, b)).unzip();
                match join.join_type {
                    // Semi, anti and mark joins emit each row of one side at most once.
                    JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => {
                        left_cols().is_some_and(|cs| self.covers_key(&join.left, &cs, nulls))
                    }
                    // These output the right side's schema (plus a mark column).
                    JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => indices
                        .iter()
                        .map(|i| child_column(&join.right, *i))
                        .collect::<Option<Vec<Column>>>()
                        .is_some_and(|cs| self.covers_key(&join.right, &cs, nulls)),
                    // A row of one side appears at most once if it matches at most one
                    // row of the other side, i.e. the join is on the other side's key.
                    // Rows agreeing on `cols` agree on its columns of that side, so
                    // they are one row if those are unique there. Only the preserved
                    // side of an outer join keeps its key, since the other side gains
                    // NULL-padded rows.
                    JoinType::Inner | JoinType::Left | JoinType::Right => {
                        let mut ix = indices.clone();
                        // An inner join's equi-keys are equal on every row it emits.
                        if join.join_type == JoinType::Inner {
                            for (a, b) in &join.on {
                                let (Some(i), Some(j)) = (column_index(&join.left, a), column_index(&join.right, b))
                                else {
                                    continue;
                                };
                                let j = left_len + j;
                                match (ix.contains(&i), ix.contains(&j)) {
                                    (true, false) => ix.push(j),
                                    (false, true) => ix.push(i),
                                    _ => {}
                                }
                            }
                        }
                        let side = |child: &LogicalPlan, on_side: &dyn Fn(usize) -> Option<usize>| {
                            ix.iter().filter_map(|&i| on_side(i)).map(|i| child_column(child, i)).collect::<Option<Vec<Column>>>()
                        };
                        let left = side(&join.left, &|i| (i < left_len).then_some(i));
                        let right = side(&join.right, &|i| i.checked_sub(left_len));
                        let left_ok = join.join_type != JoinType::Right
                            && left.as_ref().is_some_and(|cs| !cs.is_empty())
                            && self.key_is_unique(join, &join.right, &rk)
                            && left.is_some_and(|cs| self.covers_key(&join.left, &cs, nulls));
                        let right_ok = join.join_type != JoinType::Left
                            && right.as_ref().is_some_and(|cs| !cs.is_empty())
                            && self.key_is_unique(join, &join.left, &lk)
                            && right.is_some_and(|cs| self.covers_key(&join.right, &cs, nulls));
                        left_ok || right_ok
                    }
                    JoinType::Full => false,
                }
            }
            // Unions, scans of non-tables and everything else: no key to rely on.
            _ => false,
        }
    }

    /// Output columns of `plan` that `keys` (output positions) functionally
    /// determine: rows agreeing on `keys`, NULLs equal, agree on them. The
    /// dependencies come from declared keys, and are trusted as they are.
    fn fd_closure(&self, plan: &LogicalPlan, keys: &[usize]) -> BTreeSet<usize> {
        let mut out: BTreeSet<usize> = keys.iter().copied().collect();
        let width = plan.schema().fields().len();
        // The input's closure, for operators whose output columns start with
        // their input's, unchanged.
        let same = |input: &LogicalPlan| {
            let n = input.schema().fields().len();
            let keys: Vec<usize> = keys.iter().copied().filter(|&k| k < n).collect();
            self.fd_closure(input, &keys)
        };
        match plan {
            LogicalPlan::TableScan(_) => {
                let cols: Vec<Column> =
                    keys.iter().map(|&i| Column::from(plan.schema().qualified_field(i))).collect();
                if self.covers_key(plan, &cols, Nulls::Equal) {
                    out.extend(0..width);
                }
            }
            LogicalPlan::Projection(p) => {
                let input: Vec<usize> = keys.iter().filter_map(|&k| column_index(&p.input, &p.expr[k])).collect();
                let closed = self.fd_closure(&p.input, &input);
                out.extend((0..width).filter(|&j| determined(&p.expr[j], &p.input, &closed)));
            }
            // A column the filter pins to one value is the same on every
            // row, and columns it holds equal agree.
            LogicalPlan::Filter(f) => {
                let mut keys = keys.to_vec();
                for c in pinned(&f.predicate) {
                    if let Ok(i) = f.input.schema().index_of_column(&c) {
                        keys.push(i);
                    }
                }
                out.extend(with_equalities(keys, &equalities(&f.predicate, &f.input), |k| self.fd_closure(&f.input, k)));
            }
            // The window's own columns are not determined.
            LogicalPlan::Sort(_)
            | LogicalPlan::Limit(_)
            | LogicalPlan::Repartition(_)
            | LogicalPlan::SubqueryAlias(_)
            | LogicalPlan::Window(_)
            | LogicalPlan::Distinct(Distinct::All(_)) => out.extend(same(plan.inputs()[0])),
            LogicalPlan::Join(join) => {
                let nl = join.left.schema().fields().len();
                // A padded side's columns are NULL on unmatched rows, so its
                // dependencies don't hold on the output: only the preserved
                // side's do.
                let side = |child: &LogicalPlan, keys: &[usize], offset: usize| -> BTreeSet<usize> {
                    let n = child.schema().fields().len();
                    let keys: Vec<usize> =
                        keys.iter().filter_map(|&k| k.checked_sub(offset)).filter(|&k| k < n).collect();
                    self.fd_closure(child, &keys).into_iter().map(|i| i + offset).collect()
                };
                match join.join_type {
                    // Each equi-key pair is equal on every row the join emits.
                    JoinType::Inner => {
                        let pairs: Vec<(usize, usize)> = join
                            .on
                            .iter()
                            .filter_map(|(a, b)| Some((exact_index(&join.left, a)?, nl + exact_index(&join.right, b)?)))
                            .collect();
                        out.extend(with_equalities(keys.to_vec(), &pairs, |k| {
                            let mut closed = side(&join.left, k, 0);
                            closed.extend(side(&join.right, k, nl));
                            closed
                        }));
                    }
                    JoinType::Left | JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => {
                        out.extend(side(&join.left, keys, 0))
                    }
                    JoinType::Right => out.extend(side(&join.right, keys, nl)),
                    // These output the right side's schema (plus a mark column).
                    JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => {
                        out.extend(side(&join.right, keys, 0))
                    }
                    JoinType::Full => {}
                }
            }
            LogicalPlan::Aggregate(agg) if !agg.group_expr.iter().any(|e| matches!(e, Expr::GroupingSet(_))) => {
                let groups = agg.group_expr.len();
                let input: Vec<usize> = keys
                    .iter()
                    .filter(|&&k| k < groups)
                    .filter_map(|&k| column_index(&agg.input, &agg.group_expr[k]))
                    .collect();
                let closed = self.fd_closure(&agg.input, &input);
                out.extend((0..groups).filter(|&j| determined(&agg.group_expr[j], &agg.input, &closed)));
                // The keys pick out one group, aggregates and all.
                if (0..groups).all(|j| out.contains(&j)) {
                    out.extend(0..width);
                }
            }
            _ => {}
        }
        out
    }

    /// A smallest-by-greedy subset of `plan`'s first `n` output positions
    /// that determines all of them ([`Self::fd_closure`]).
    fn determining_keys(&self, plan: &LogicalPlan, n: usize) -> Vec<usize> {
        let mut keys: Vec<usize> = (0..n).collect();
        for k in 0..n {
            let rest: Vec<usize> = keys.iter().copied().filter(|&j| j != k).collect();
            let closed = self.fd_closure(plan, &rest);
            if (0..n).all(|j| closed.contains(&j)) {
                keys = rest;
            }
        }
        keys
    }
}

fn variant_name(plan: &LogicalPlan) -> &'static str {
    match plan {
        LogicalPlan::Unnest(_) => "Unnest",
        LogicalPlan::RecursiveQuery(_) => "RecursiveQuery",
        LogicalPlan::Extension(_) => "Extension",
        LogicalPlan::Explain(_) => "Explain",
        LogicalPlan::Analyze(_) => "Analyze",
        LogicalPlan::Statement(_) => "Statement",
        LogicalPlan::Dml(_) => "Dml",
        LogicalPlan::Ddl(_) => "Ddl",
        LogicalPlan::Copy(_) => "Copy",
        LogicalPlan::DescribeTable(_) => "DescribeTable",
        _ => "Other",
    }
}
