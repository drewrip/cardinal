//! Building one plan's SMT system: a bottom-up walk over a DataFusion
//! `LogicalPlan`.
//!
//! Every operator gets an integer variable for its output cardinality and one per
//! output column bounding that column's number of distinct values (NDV, with NULL
//! counted as one value). The operator's rule ([`crate::rules`]) relates
//! them to its inputs'.

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::panic::Location;

use datafusion::arrow::datatypes::DataType;
use datafusion::common::Column;
use datafusion::common::tree_node::{TreeNode, TreeNodeRecursion};
use datafusion::datasource::source_as_provider;
use datafusion::logical_expr::logical_plan::{LogicalPlan, TableScan};
use datafusion::logical_expr::utils::split_conjunction;
use datafusion::logical_expr::{BinaryExpr, Expr, TableProviderFilterPushDown};
use z3::ast::{Bool, Int};
use z3::{Params, Solver};

use crate::ForeignKey;
use crate::domain::{self, Facts};
use crate::origin::Origin;

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
    pub(crate) sums: Vec<(Expr, Int)>,
    /// Sets of columns that are unique together, beyond declared keys.
    pub(crate) keys: Vec<Vec<Expr>>,
    /// `(column, nulls, values)`: at most `nulls` rows have the column NULL,
    /// and at most `values` rows have it non-NULL, like the padded and
    /// matched rows of an outer join.
    pub(crate) nulls: Vec<(Expr, Int, Int)>,
}

impl Rows {
    /// The facts whose columns all map through `map`, over the new columns.
    pub(crate) fn rename(&self, map: &dyn Fn(&Column) -> Option<Column>) -> Rows {
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
    pub(crate) resolve: &'a dyn Fn(&TableScan) -> ScanKind,
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
    pub(crate) origins: Vec<(Int, Origin)>,
    /// Ids of visited nodes not yet claimed by a parent.
    pub(crate) frontier: Vec<usize>,
    pub(crate) counter: usize,
    /// Most NDV factors multiplied in one constraint.
    pub(crate) max_product: usize,
    /// Declared foreign keys.
    pub(crate) foreign_keys: &'a [ForeignKey],
    /// The last join visited's [`Node::at_most_once`], for its node to take.
    pub(crate) at_most_once: (bool, bool),
    /// Whether to log every assertion, for [`crate::trace`].
    pub(crate) trace: bool,
    /// Every assertion, in order, if `trace` is set.
    pub(crate) log: RefCell<Vec<Logged>>,
    /// Frames of the nodes being visited, innermost last.
    pub(crate) owners: Vec<usize>,
    pub(crate) next_frame: usize,
    /// The node each finished frame became.
    pub(crate) frame_node: HashMap<usize, usize>,
    /// The names of the columns that get min and max variables
    /// ([`ranged_columns`]).
    pub(crate) ranged: BTreeSet<String>,
    /// The last base scan's raw min and max variables, for its node to take.
    pub(crate) raw_ranges: (Vec<Option<String>>, Vec<Option<String>>),
}

/// One assertion: the frame of the node it was made for (none for
/// partitions), and the line of the analyzer that made it.
pub(crate) struct Logged {
    pub(crate) expr: Bool,
    pub(crate) frame: Option<usize>,
    pub(crate) at: &'static Location<'static>,
    /// The axiom it is, for one asserted by name rather than by a function
    /// of its own.
    pub(crate) rule: Option<&'static str>,
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
pub(crate) fn symbol(s: &str) -> String {
    s.chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect()
}

pub(crate) fn int(n: u64) -> Int {
    Int::from_u64(n)
}

pub(crate) fn max(a: &Int, b: &Int) -> Int {
    a.ge(b).ite(a, b)
}

pub(crate) fn min(a: &Int, b: &Int) -> Int {
    a.le(b).ite(a, b)
}

/// Default for `Options::max_product`.
pub(crate) const DEFAULT_MAX_PRODUCT: usize = 3;

/// The product of `factors`, or `None` if there are more than `cap` of them.
/// Products of NDVs are nonlinear, so larger products are dropped (the bound is
/// then just the cardinality), which is sound but weaker.
pub(crate) fn product(factors: &[&Int], cap: usize) -> Option<Int> {
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
    pub(crate) fn range_var(&mut self, name: String) -> Int {
        let v = Int::new_const(name.as_str());
        self.vars.push((name, v.clone()));
        v
    }

    #[track_caller]
    pub(crate) fn new_var(&mut self, name: String) -> Int {
        let v = Int::new_const(name.as_str());
        self.non_negative(&v);
        self.vars.push((name, v.clone()));
        v
    }

    /// Creates a fresh relation for `plan`'s output: a cardinality variable
    /// `op{n}_{kind}` and NDV variables `op{n}_{kind}_c{j}`, with the constraints
    /// every relation satisfies.
    pub(crate) fn fresh(&mut self, kind: &str, plan: &LogicalPlan) -> Rel {
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
                self.ndv_within_rows(&v, &card);
                self.nonempty_ndv(&v, &card);
                if *t == DataType::Boolean {
                    self.boolean_ndv(&v);
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
        self.key_ndv(plan, &rel);
        rel
    }

    /// The unquoted name of a variable created by `new_var`.
    pub(crate) fn name_of(&self, v: &Int) -> String {
        self.vars
            .iter()
            .find(|(_, x)| x == v)
            .map(|(n, _)| n.clone())
            .expect("variable was created by new_var")
    }

    pub(crate) fn names_of(&self, rel: &Rel) -> Vec<String> {
        rel.ndv.iter().map(|v| self.name_of(v)).collect()
    }

    #[track_caller]
    pub(crate) fn assert(&self, b: Bool) {
        if self.trace {
            self.log.borrow_mut().push(Logged {
                expr: b.clone(),
                frame: self.owners.last().copied(),
                at: Location::caller(),
                rule: None,
            });
        }
        self.solver.assert(b);
    }

    /// Asserts `b`, an instance of axiom `rule`, for no node in particular.
    #[track_caller]
    pub(crate) fn assert_named(&self, rule: &'static str, b: Bool) {
        if self.trace {
            self.log.borrow_mut().push(Logged { expr: b.clone(), frame: None, at: Location::caller(), rule: Some(rule) });
        }
        self.solver.assert(b);
    }

    pub(crate) fn table(&mut self, key: &str, display: &str) -> Int {
        if let Some(t) = self.tables.get(key) {
            return t.var.clone();
        }
        // Tables are numbered so their symbols cannot collide with each other or
        // with operator variables (which start with `op`).
        let symbol = format!("T{}_{}", self.tables.len(), symbol(display));
        let var = Int::new_const(symbol.as_str());
        self.non_negative(&var);
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

    /// What `rel`'s value domains and row facts give: the domain axioms,
    /// and the bounds unique columns, summed columns and padded columns put
    /// on its rows.
    pub(crate) fn apply_domains(&self, plan: &LogicalPlan, rel: &Rel) {
        let schema = plan.schema();
        if rel.facts.contradictory() {
            self.empty_domain(&rel.card);
        }
        for (j, v) in rel.ndv.iter().enumerate() {
            let col = Expr::Column(Column::from(schema.qualified_field(j)));
            match rel.facts.dom(&col, schema).size() {
                Some(0) => self.empty_domain(&rel.card),
                Some(n) if n <= u64::MAX as u128 => self.ndv_within_domain(v, n as u64),
                _ => {}
            }
        }
        self.range_within_domain(plan, rel);
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
}

/// Integers, and dates as days: the columns with min and max variables.
pub(crate) fn integer_like(t: &DataType) -> bool {
    t.is_integer() || *t == DataType::Date32
}

/// The names of `vars`, by column.
pub(crate) fn range_names(vars: &[Option<Int>]) -> Vec<Option<String>> {
    vars.iter().map(|v| v.as_ref().map(|v| v.to_string())).collect()
}

/// The names of the columns that a comparison, equi-join key or grouping
/// key of `plan` reads. Only these get min and max variables, which add
/// constraints at every operator: the others' would carry nothing.
pub(crate) fn ranged_columns(plan: &LogicalPlan) -> BTreeSet<String> {
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
