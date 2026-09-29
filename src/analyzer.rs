//! Bottom-up walk over a DataFusion `LogicalPlan` that emits Z3 cardinality
//! constraints, one integer variable per operator.

use std::collections::HashMap;

use datafusion::arrow::datatypes::DataType;
use datafusion::common::tree_node::TreeNodeRecursion;
use datafusion::common::{Column, Constraint, JoinType};
use datafusion::logical_expr::logical_plan::{Distinct, FetchType, Join, LogicalPlan, TableScan};
use datafusion::logical_expr::{Cast, Expr, ExprSchemable, TryCast};
use z3::ast::{Bool, Int};
use z3::{Params, Solver};

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
    pub(crate) var: Int,
}

pub(crate) struct Analyzer<'a> {
    pub(crate) solver: Solver,
    resolve: &'a dyn Fn(&TableScan) -> ScanKind,
    /// One variable per distinct base table, keyed by `ScanKind::Base::key` and
    /// shared by every scan of that table.
    pub(crate) tables: HashMap<String, TableVar>,
    /// Every base-table scan as (scan variable name, table display name), with its variable.
    pub(crate) scans: Vec<(String, String, Int)>,
    /// Every operator variable, by name, so callers can read them from a model.
    pub(crate) vars: Vec<(String, Int)>,
    /// Every plan node, children before parents, so a validator can evaluate
    /// them bottom-up.
    pub(crate) nodes: Vec<Node>,
    /// Ids of visited nodes not yet claimed by a parent.
    frontier: Vec<usize>,
    counter: usize,
}

/// One plan node and the variable holding its output cardinality.
#[derive(Debug, Clone)]
pub(crate) struct Node {
    pub(crate) var: String,
    pub(crate) plan: LogicalPlan,
    /// Node ids of `plan.inputs()`, in order.
    pub(crate) inputs: Vec<usize>,
    /// For a base scan with pushed-down filters: the variable of the raw scan and
    /// the scan without filters or fetch.
    pub(crate) raw_scan: Option<(String, LogicalPlan)>,
}

/// How long Z3 may spend on one check before answering unknown.
pub(crate) const SOLVER_TIMEOUT_MS: u32 = 10_000;

pub(crate) fn new_solver() -> Solver {
    let solver = Solver::new();
    let mut params = Params::new();
    params.set_u32("timeout", SOLVER_TIMEOUT_MS);
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

fn max(a: &Int, b: &Int) -> Int {
    a.ge(b).ite(a, b)
}

fn min(a: &Int, b: &Int) -> Int {
    a.le(b).ite(a, b)
}

impl<'a> Analyzer<'a> {
    pub(crate) fn new(resolve: &'a dyn Fn(&TableScan) -> ScanKind) -> Self {
        Self {
            solver: new_solver(),
            resolve,
            tables: HashMap::new(),
            scans: Vec::new(),
            vars: Vec::new(),
            nodes: Vec::new(),
            frontier: Vec::new(),
            counter: 0,
        }
    }

    /// Creates a fresh non-negative variable named `O{n}_{kind}`.
    fn fresh(&mut self, kind: &str) -> Int {
        let name = format!("O{}_{}", self.counter, symbol(kind));
        self.counter += 1;
        let v = Int::new_const(name.as_str());
        self.solver.assert(v.ge(Int::from_i64(0)));
        self.vars.push((name, v.clone()));
        v
    }

    /// The unquoted name of an operator variable created by `fresh`.
    pub(crate) fn name_of(&self, v: &Int) -> String {
        self.vars
            .iter()
            .find(|(_, x)| x == v)
            .map(|(n, _)| n.clone())
            .expect("variable was created by fresh")
    }

    fn assert(&self, b: Bool) {
        self.solver.assert(b);
    }

    fn table(&mut self, key: &str, display: &str) -> Int {
        if let Some(t) = self.tables.get(key) {
            return t.var.clone();
        }
        // Tables are numbered so their symbols cannot collide with each other or
        // with operator variables (which start with `O`).
        let name = format!("T{}_{}", self.tables.len(), symbol(display));
        let var = Int::new_const(name.as_str());
        self.solver.assert(var.ge(Int::from_i64(0)));
        self.tables.insert(
            key.to_string(),
            TableVar {
                display: display.to_string(),
                var: var.clone(),
            },
        );
        var
    }

    /// Returns the output cardinality variable of `plan`.
    pub(crate) fn visit(&mut self, plan: &LogicalPlan) -> Int {
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
        let (out, raw_scan) = self.visit_node(plan);
        let inputs = self.frontier.split_off(mark);
        debug_assert_eq!(inputs.len(), plan.inputs().len());
        let var = self.name_of(&out);
        self.nodes.push(Node {
            var,
            plan: plan.clone(),
            inputs,
            raw_scan,
        });
        self.frontier.push(self.nodes.len() - 1);
        out
    }

    fn visit_node(&mut self, plan: &LogicalPlan) -> (Int, Option<(String, LogicalPlan)>) {
        if let LogicalPlan::TableScan(scan) = plan {
            return self.scan(scan);
        }
        let out = match plan {
            LogicalPlan::Projection(p) => self.equal("Projection", &p.input),
            LogicalPlan::Subquery(p) => self.equal("Subquery", &p.subquery),
            LogicalPlan::SubqueryAlias(p) => self.equal("SubqueryAlias", &p.input),
            LogicalPlan::Window(p) => self.equal("Window", &p.input),
            LogicalPlan::Repartition(p) => self.equal("Repartition", &p.input),
            LogicalPlan::Filter(p) => self.at_most_input("Filter", &p.input),
            LogicalPlan::Distinct(d) => self.at_most_input("Distinct", d.input()),
            LogicalPlan::Sort(s) => {
                let l = self.visit(&s.input);
                let o = self.fresh("Sort");
                match s.fetch {
                    None => self.assert(o.eq(&l)),
                    Some(n) => {
                        self.assert(o.le(&l));
                        self.assert(o.le(Int::from_u64(n as u64)));
                    }
                }
                o
            }
            LogicalPlan::Limit(lim) => {
                let l = self.visit(&lim.input);
                let o = self.fresh("Limit");
                self.assert(o.le(&l));
                if let Ok(FetchType::Literal(Some(n))) = lim.get_fetch_type() {
                    self.assert(o.le(Int::from_u64(n as u64)));
                }
                o
            }
            LogicalPlan::Aggregate(agg) => {
                let l = self.visit(&agg.input);
                let grouping_sets = agg
                    .group_expr
                    .iter()
                    .any(|e| matches!(e, Expr::GroupingSet(_)));
                if grouping_sets {
                    // ROLLUP / CUBE / GROUPING SETS can emit more rows than they read.
                    self.fresh("GroupingSets")
                } else if agg.group_expr.is_empty() {
                    let o = self.fresh("ScalarAggregate");
                    self.assert(o.eq(Int::from_i64(1)));
                    o
                } else {
                    let o = self.fresh("GroupBy");
                    self.assert(o.le(&l));
                    o
                }
            }
            LogicalPlan::Join(join) => self.join(join),
            LogicalPlan::Union(u) => {
                let inputs: Vec<Int> = u.inputs.iter().map(|i| self.visit(i)).collect();
                let o = self.fresh("Union");
                self.assert(o.eq(Int::add(&inputs)));
                o
            }
            LogicalPlan::Values(v) => {
                let o = self.fresh("Values");
                self.assert(o.eq(Int::from_u64(v.values.len() as u64)));
                o
            }
            LogicalPlan::EmptyRelation(e) => {
                let o = self.fresh("EmptyRelation");
                self.assert(o.eq(Int::from_i64(e.produce_one_row as i64)));
                o
            }
            other => {
                // Unsupported operator: visit children so their scans still count,
                // but say nothing about this operator's output beyond O >= 0.
                for input in other.inputs() {
                    self.visit(input);
                }
                self.fresh(&format!("Unknown_{}", variant_name(other)))
            }
        };
        (out, None)
    }

    fn scan(&mut self, scan: &TableScan) -> (Int, Option<(String, LogicalPlan)>) {
        let mut raw_scan = None;
        let mut out = match (self.resolve)(scan) {
            ScanKind::Base { key, display } => {
                let r = self.table(&key, &display);
                let s = self.fresh(&format!("Scan_{display}"));
                self.assert(s.eq(&r));
                let name = self.name_of(&s);
                self.scans.push((name.clone(), display, s.clone()));
                if !scan.filters.is_empty() {
                    // The raw scan, before pushed-down filters and fetch.
                    let mut raw = scan.clone();
                    raw.filters.clear();
                    raw.fetch = None;
                    raw_scan = Some((name, LogicalPlan::TableScan(raw)));
                }
                s
            }
            ScanKind::NonBase => self.fresh(&format!("NonBaseScan_{}", scan.table_name)),
        };
        // Pushed-down filters behave like a Filter wrapping the scan: whether the
        // provider applies them exactly or not, it cannot add rows. A pushed-down
        // `fetch` is only a hint: providers must return *at least* that many rows
        // and may return more (DataFusion keeps the Limit above), so it bounds
        // nothing.
        if !scan.filters.is_empty() {
            let f = self.fresh("ScanFilter");
            self.assert(f.le(&out));
            out = f;
        }
        (out, raw_scan)
    }

    /// `O == l`
    fn equal(&mut self, kind: &str, input: &LogicalPlan) -> Int {
        let l = self.visit(input);
        let o = self.fresh(kind);
        self.assert(o.eq(&l));
        o
    }

    /// `O <= l`
    fn at_most_input(&mut self, kind: &str, input: &LogicalPlan) -> Int {
        let l = self.visit(input);
        let o = self.fresh(kind);
        self.assert(o.le(&l));
        o
    }

    fn join(&mut self, join: &Join) -> Int {
        let l = self.visit(&join.left);
        let r = self.visit(&join.right);
        let equi = !join.on.is_empty();
        let cross = !equi && join.filter.is_none();
        // `max(l, r)` is only sound when each row of one side matches at most one
        // row of the other, i.e. the join key is unique on at least one side.
        let keyed = equi && {
            let (lk, rk): (Vec<&Expr>, Vec<&Expr>) = join.on.iter().map(|(a, b)| (a, b)).unzip();
            key_is_unique(&join.left, &lk) || key_is_unique(&join.right, &rk)
        };
        let kind = format!(
            "{:?}{}Join",
            join.join_type,
            if keyed {
                "Key"
            } else if equi {
                "Equi"
            } else if cross {
                "Cross"
            } else {
                "Theta"
            }
        );
        let o = self.fresh(&kind);
        let lr = Int::mul(&[&l, &r]);
        // Bound on the rows the join's matching produces. `l * r` always holds;
        // a unique key adds `max(l, r)`, which is tighter unless a side is empty.
        let inner = if keyed {
            min(&max(&l, &r), &lr)
        } else {
            lr.clone()
        };
        match join.join_type {
            JoinType::Inner => {
                if cross {
                    self.assert(o.eq(&lr));
                } else {
                    self.assert(o.le(&inner));
                }
            }
            // An outer join emits its inner join's rows plus each unmatched row of
            // the preserved side(s), so its upper bound is the inner bound plus the
            // preserved input(s). Every preserved row appears at least once.
            JoinType::Left | JoinType::Right => {
                let preserved = if join.join_type == JoinType::Left {
                    &l
                } else {
                    &r
                };
                self.assert(o.ge(preserved));
                self.assert(o.le(Int::add(&[&inner, preserved])));
            }
            JoinType::Full => {
                self.assert(o.ge(&l));
                self.assert(o.ge(&r));
                self.assert(o.le(Int::add(&[&inner, &l, &r])));
            }
            JoinType::LeftSemi | JoinType::LeftAnti => self.assert(o.le(&l)),
            JoinType::RightSemi | JoinType::RightAnti => self.assert(o.le(&r)),
            JoinType::LeftMark => self.assert(o.eq(&l)),
            JoinType::RightMark => self.assert(o.eq(&r)),
        }
        o
    }
}

/// True if the join key expressions `keys` of `side` are unique in `side`'s
/// output, i.e. they cover a declared PRIMARY KEY of a base table and the path
/// from `side` down to that table cannot duplicate rows. Declared primary keys
/// are the only evidence of uniqueness; non-column keys are never unique.
fn key_is_unique(side: &LogicalPlan, keys: &[&Expr]) -> bool {
    let Some(cols) = keys
        .iter()
        .map(|e| key_column(side, e))
        .collect::<Option<Vec<Column>>>()
    else {
        return false;
    };
    covers_primary_key(side, &cols)
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

/// True if casting `from` to `to` maps distinct values to distinct values.
fn injective_cast(from: &DataType, to: &DataType) -> bool {
    use DataType::*;
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
        )
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

/// True if `cols` of `plan`'s output are unique because they trace back to a
/// declared primary key through operators that never duplicate rows.
fn covers_primary_key(plan: &LogicalPlan, cols: &[Column]) -> bool {
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
            scan.source.constraints().is_some_and(|cs| {
                cs.iter().any(|c| match c {
                    Constraint::PrimaryKey(pk) => pk.iter().all(|i| indices.contains(i)),
                    Constraint::Unique(_) => false,
                })
            })
        }
        // Operators whose output rows are a subset of their input's, with the
        // input's columns first and unchanged.
        LogicalPlan::Filter(_)
        | LogicalPlan::Sort(_)
        | LogicalPlan::Limit(_)
        | LogicalPlan::Repartition(_)
        | LogicalPlan::SubqueryAlias(_)
        | LogicalPlan::Window(_)
        | LogicalPlan::Distinct(Distinct::All(_)) => {
            let child = plan.inputs()[0];
            same_positions(plan, child, cols).is_some_and(|cs| covers_primary_key(child, &cs))
        }
        LogicalPlan::Projection(p) => {
            let mapped = cols
                .iter()
                .map(|c| {
                    let i = p.schema.index_of_column(c).ok()?;
                    key_column(&p.input, &p.expr[i])
                })
                .collect::<Option<Vec<Column>>>();
            mapped.is_some_and(|cs| covers_primary_key(&p.input, &cs))
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
            let on_left = indices.iter().all(|i| *i < left_len);
            let on_right = indices.iter().all(|i| *i >= left_len);
            let left_cols = || -> Option<Vec<Column>> {
                indices
                    .iter()
                    .map(|i| child_column(&join.left, *i))
                    .collect()
            };
            let right_cols = || -> Option<Vec<Column>> {
                indices
                    .iter()
                    .map(|i| child_column(&join.right, i - left_len))
                    .collect()
            };
            let (lk, rk): (Vec<&Expr>, Vec<&Expr>) = join.on.iter().map(|(a, b)| (a, b)).unzip();
            match join.join_type {
                // Semi, anti and mark joins emit each row of one side at most once.
                JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => {
                    left_cols().is_some_and(|cs| covers_primary_key(&join.left, &cs))
                }
                // These output the right side's schema (plus a mark column).
                JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => indices
                    .iter()
                    .map(|i| child_column(&join.right, *i))
                    .collect::<Option<Vec<Column>>>()
                    .is_some_and(|cs| covers_primary_key(&join.right, &cs)),
                // A row of one side appears at most once if it matches at most one
                // row of the other side, i.e. the join is on the other side's key.
                // Only the preserved side of an outer join keeps its key, since the
                // other side gains NULL-padded rows.
                JoinType::Inner | JoinType::Left | JoinType::Right => {
                    let left_ok = on_left
                        && join.join_type != JoinType::Right
                        && key_is_unique(&join.right, &rk)
                        && left_cols().is_some_and(|cs| covers_primary_key(&join.left, &cs));
                    let right_ok = on_right
                        && join.join_type != JoinType::Left
                        && key_is_unique(&join.left, &lk)
                        && right_cols().is_some_and(|cs| covers_primary_key(&join.right, &cs));
                    left_ok || right_ok
                }
                JoinType::Full => false,
            }
        }
        // Aggregates, unions, scans of non-tables and everything else: no
        // declared primary key to rely on.
        _ => false,
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
