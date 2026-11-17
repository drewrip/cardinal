//! Building one plan's SMT system: a bottom-up walk over a DataFusion
//! `LogicalPlan` by an [`Analyzer`].
//!
//! Every operator gets an [`OpOutput`]: an integer variable for its output
//! cardinality and, per output column, one bounding its number of distinct
//! values (NDV, with NULL counted as one value), and for some its least and
//! greatest value. The operator's rule ([`crate::rules`]) relates them to its
//! inputs' and records the op output in the [`Analyzer`]'s ledger; once the
//! walk is done, the [axioms](crate::axioms) pass asserts what holds of
//! them.

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::panic::Location;
use std::sync::Arc;

use datafusion::arrow::datatypes::{DataType, TimeUnit};
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
use crate::postprocess::Role;
use crate::properties::Claim;

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

/// An operator's output: variables for its rows, and what is known of them.
/// A variable for its cardinality and, per output column, one for its
/// number of distinct values and, for some, its least and greatest value;
/// and what its rows satisfy whatever the data.
#[derive(Clone)]
pub struct OpOutput {
    /// Its record in [`Analyzer::op_outputs`].
    pub(crate) id: OpOutputId,
    pub(crate) card: Int,
    pub(crate) ndv: Vec<Int>,
    /// Per output column, the ends of an interval holding each of its
    /// non-NULL values (empty, `max < min`, if there is none): for columns
    /// with a [`Unit`] that a range, a join or a grouping reads.
    pub(crate) min: Vec<Option<Int>>,
    pub(crate) max: Vec<Option<Int>>,
    /// Per output column, the unit its `min` and `max` count in. Two
    /// columns' ends compare only in one unit.
    pub(crate) unit: Vec<Option<Unit>>,
    /// What every row's values satisfy, whatever the data.
    pub(crate) facts: Facts,
    /// Bounds that also hold of any subset of the rows.
    pub(crate) subset_bounds: SubsetBounds,
    /// The stored table these rows are distinct rows of, if any.
    pub(crate) origin: Option<Origin>,
    /// The frame of the node being visited when it was made, for
    /// [`crate::trace`].
    pub(crate) frame: Option<usize>,
    /// The node it is the output of, once finished ([`Analyzer::finish`]):
    /// none for a scan's raw rows.
    pub(crate) node: Option<usize>,
}

impl OpOutput {
    /// Takes what is known of `l`'s rows, for an operator that keeps some of
    /// them as they are, columns unchanged.
    pub(crate) fn inherit(&mut self, l: &OpOutput) {
        self.facts = l.facts.clone();
        self.subset_bounds = l.subset_bounds.clone();
        self.origin = l.origin.clone();
    }
}

/// An op output's index in [`Analyzer::op_outputs`].
pub(crate) type OpOutputId = usize;

/// Bounds on an output's rows that hold of any subset of them too, so they
/// carry up through operators that keep some rows as they are. Each waits on
/// a domain to apply: a column of counts summing to `b`, a unique key, a
/// column NULL on at most `n` rows.
#[derive(Clone, Default)]
pub(crate) struct SubsetBounds {
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

impl SubsetBounds {
    /// The bounds whose columns all map through `map`, over the new columns.
    pub(crate) fn rename(&self, map: &dyn Fn(&Column) -> Option<Column>) -> SubsetBounds {
        let r = |c: &Expr| domain::rename(c, map);
        SubsetBounds {
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

/// The state of one analysis: the Z3 solver and every variable and
/// assertion so far. Its walk over a plan (`Analyzer::visit`) runs each
/// operator's [rule](crate::rules), which asserts what the operator adds
/// and how its rows are its inputs', and records its op outputs; the
/// [axioms](crate::axioms) pass then asserts what holds of them. Each rule and axiom is one of its
/// methods. Made by [`Analysis`](crate::Analysis).
pub struct Analyzer<'a> {
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
    /// Every op output the rules made, by [`OpOutputId`], as its rule left
    /// it once finished.
    pub(crate) op_outputs: Vec<OpOutput>,
    /// Ids of visited nodes not yet claimed by a parent.
    pub(crate) frontier: Vec<usize>,
    pub(crate) counter: usize,
    /// Most NDV factors multiplied in one constraint.
    pub(crate) max_product: usize,
    /// Declared foreign keys.
    pub(crate) foreign_keys: &'a [ForeignKey],
    /// Whether to log every assertion, for [`crate::trace`].
    pub(crate) trace: bool,
    /// Every assertion, in order, if `trace` is set.
    pub(crate) log: RefCell<Vec<Logged>>,
    /// Every assertion's role, in order ([`crate::postprocess`]).
    pub(crate) roles: RefCell<Vec<Role>>,
    /// Frames of the nodes being visited, innermost last.
    pub(crate) owners: Vec<usize>,
    pub(crate) next_frame: usize,
    /// The node each finished frame became.
    pub(crate) frame_node: HashMap<usize, usize>,
    /// The node each visited plan became, by its address ([`address`]).
    pub(crate) node_at: HashMap<usize, usize>,
    /// Dependencies the rules relied on, by plan address, not yet given to
    /// their node.
    pub(crate) relied: RefCell<Vec<(usize, Dependency)>>,
    /// The names of the columns that get min and max variables
    /// ([`ranged_columns`]).
    pub(crate) ranged: BTreeSet<String>,
    /// Whether to assert [`referenced size`](Self::referenced_size) on each
    /// scan, with reference plans ([`crate::joint`]).
    pub(crate) referenced_sizes: bool,
}

/// One assertion: the frame of the node it was made for (none for
/// partitions), and the line of the analyzer that made it.
pub(crate) struct Logged {
    pub(crate) expr: Bool,
    pub(crate) frame: Option<usize>,
    pub(crate) at: &'static Location<'static>,
    /// The property it is, for one asserted by name rather than by a
    /// function of its own.
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
    /// For a base scan with pushed-down filters: the scan before them.
    pub(crate) raw_scan: Option<RawScan>,
    /// The min and max variable of each output column that has them
    /// ([`OpOutput::min`]), `op{n}_{kind}_c{j}_min` and `_max`.
    pub(crate) min_vars: Vec<Option<String>>,
    pub(crate) max_vars: Vec<Option<String>>,
    /// The functional dependencies the rules relied on among the output
    /// columns, for [`crate::Analysis::validate`] to check.
    pub(crate) dependencies: Vec<Dependency>,
}

/// A base scan before its pushed-down filters and fetch: its cardinality,
/// `ndv`, min and max variables, and the scan without them.
#[derive(Debug, Clone)]
pub struct RawScan {
    pub(crate) var: String,
    pub(crate) ndv_vars: Vec<String>,
    pub(crate) min_vars: Vec<Option<String>>,
    pub(crate) max_vars: Vec<Option<String>>,
    pub(crate) plan: LogicalPlan,
}

/// Rows agreeing on `on` (output positions, NULLs equal) agree on these
/// columns too, or are one row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Dependency {
    pub on: Vec<usize>,
    pub determines: Determines,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Determines {
    Columns(Vec<usize>),
    Row,
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
            op_outputs: Vec::new(),
            max_product,
            foreign_keys,
            trace,
            log: RefCell::new(Vec::new()),
            roles: RefCell::new(Vec::new()),
            owners: Vec::new(),
            next_frame: 0,
            frame_node: HashMap::new(),
            node_at: HashMap::new(),
            relied: RefCell::new(Vec::new()),
            ranged: BTreeSet::new(),
            referenced_sizes: false,
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

    /// A variable counting something, rows or distinct values: never
    /// negative.
    pub(crate) fn new_var(&mut self, name: String) -> Int {
        let v = Int::new_const(name.as_str());
        self.non_negative(&v);
        self.vars.push((name, v.clone()));
        v
    }

    /// Creates a fresh op output for `plan`: a cardinality variable
    /// `op{n}_{kind}` and NDV variables `op{n}_{kind}_c{j}`, recorded in
    /// [`Self::op_outputs`] for the axioms. Asserts what holds of any
    /// columns of any rows.
    pub(crate) fn fresh(&mut self, kind: &str, plan: &LogicalPlan) -> OpOutput {
        let base = format!("op{}_{}", self.counter, symbol(kind));
        self.counter += 1;
        let card = self.new_var(base.clone());
        let fields: Vec<DataType> = plan
            .schema()
            .fields()
            .iter()
            .map(|f| f.data_type().clone())
            .collect();
        let ndv: Vec<Int> = fields
            .iter()
            .enumerate()
            .map(|(j, _)| self.new_var(format!("{base}_c{j}")))
            .collect();
        let schema = plan.schema();
        let (mut min, mut max, mut units) = (vec![], vec![], vec![]);
        for (j, t) in fields.iter().enumerate() {
            let u = unit(t).filter(|_| self.ranged.contains(schema.field(j).name()));
            min.push(u.is_some().then(|| self.range_var(format!("{base}_c{j}_min"))));
            max.push(u.is_some().then(|| self.range_var(format!("{base}_c{j}_max"))));
            units.push(u);
        }
        for (v, t) in ndv.iter().zip(&fields) {
            self.ndv_within_rows(v, &card);
            self.nonempty_ndv(v, &card);
            if t == &DataType::Boolean {
                self.boolean_ndv(v);
            }
        }
        let out = OpOutput {
            id: self.op_outputs.len(),
            card,
            ndv,
            min,
            max,
            unit: units,
            facts: Facts::default(),
            subset_bounds: SubsetBounds::default(),
            origin: None,
            frame: self.owners.last().copied(),
            node: None,
        };
        self.op_outputs.push(out.clone());
        out
    }

    /// Records `out`, the output of `plan`, as its rule leaves it, with
    /// `node` if it is that node's output, and asserts what follows of it
    /// ([`Self::on_op_output`]).
    pub(crate) fn finish(&mut self, out: &OpOutput, plan: &LogicalPlan, node: Option<usize>) {
        let out = OpOutput { node, ..out.clone() };
        self.on_op_output(&out, plan);
        let id = out.id;
        self.op_outputs[id] = out;
    }

    /// The unquoted name of a variable created by `new_var`.
    pub(crate) fn name_of(&self, v: &Int) -> String {
        self.vars
            .iter()
            .find(|(_, x)| x == v)
            .map(|(n, _)| n.clone())
            .expect("variable was created by new_var")
    }

    pub(crate) fn names_of(&self, out: &OpOutput) -> Vec<String> {
        out.ndv.iter().map(|v| self.name_of(v)).collect()
    }

    /// Asserts `b`, a [`Role::Gen`].
    #[track_caller]
    pub(crate) fn assert(&self, b: Bool) {
        self.assert_as(Role::Gen, b);
    }

    /// Asserts `b`, with `role` in [liveness](crate::postprocess).
    #[track_caller]
    pub(crate) fn assert_as(&self, role: Role, b: Bool) {
        self.roles.borrow_mut().push(role);
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

    /// Asserts `b`, with `role`, kept out of the trace's log: the caller
    /// traces it itself.
    pub(crate) fn assert_untraced(&self, role: Role, b: Bool) {
        self.roles.borrow_mut().push(role);
        self.solver.assert(b);
    }

    /// Asserts each of `claims`, the [property](crate::properties) `name`,
    /// for the node being visited, if any.
    #[track_caller]
    pub(crate) fn assert_property(&self, name: &'static str, claims: Vec<Claim>) {
        let at = Location::caller();
        for Claim { role, claim } in claims {
            self.roles.borrow_mut().push(role);
            if self.trace {
                let frame = self.owners.last().copied();
                self.log.borrow_mut().push(Logged { expr: claim.clone(), frame, at, rule: Some(name) });
            }
            self.solver.assert(claim);
        }
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
    pub(crate) fn visit(&mut self, plan: &LogicalPlan) -> OpOutput {
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
            min_vars: range_names(&out.min),
            max_vars: range_names(&out.max),
            dependencies: vec![],
        });
        self.node_at.insert(address(plan), self.nodes.len() - 1);
        self.finish(&out, plan, Some(self.nodes.len() - 1));
        // Those of plans not yet visited wait for them; those of plans never
        // visited (rewritten copies) are dropped at the end.
        for (at, d) in std::mem::take(&mut *self.relied.borrow_mut()) {
            match self.node_at.get(&at) {
                Some(&id) if !self.nodes[id].dependencies.contains(&d) => self.nodes[id].dependencies.push(d),
                Some(_) => {}
                None => self.relied.borrow_mut().push((at, d)),
            }
        }
        self.owners.pop();
        self.frame_node.insert(frame, self.nodes.len() - 1);
        self.frontier.push(self.nodes.len() - 1);
        out
    }
}

/// The address of a plan node, which identifies it while the plan is
/// borrowed.
pub(crate) fn address(plan: &LogicalPlan) -> usize {
    plan as *const LogicalPlan as usize
}

/// What a column's values count in, as integers that order as the values
/// do: the columns with min and max variables. Each is the raw value a
/// literal of the type keys to ([`domain`]): an integer, days, milliseconds
/// (Date64), the timestamp's unit, or a decimal's unscaled value at its
/// scale.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Unit {
    Int,
    Date32,
    Date64,
    Time(TimeUnit, Option<Arc<str>>),
    Decimal(i8),
}

/// The [`Unit`] of a type's values, if they count in one.
pub(crate) fn unit(t: &DataType) -> Option<Unit> {
    Some(match t {
        t if t.is_integer() => Unit::Int,
        DataType::Date32 => Unit::Date32,
        DataType::Date64 => Unit::Date64,
        DataType::Timestamp(u, tz) => Unit::Time(*u, tz.clone()),
        DataType::Decimal128(_, s) => Unit::Decimal(*s),
        _ => return None,
    })
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
