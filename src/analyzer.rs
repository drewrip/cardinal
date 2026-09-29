//! Bottom-up walk over a DataFusion `LogicalPlan` that emits Z3 constraints.
//!
//! Every operator gets an integer variable for its output cardinality and one per
//! output column bounding that column's number of distinct values (NDV, with NULL
//! counted as one value). Constraints relate each operator's variables to its
//! inputs'.

use std::collections::HashMap;

use datafusion::arrow::datatypes::DataType;
use datafusion::common::tree_node::{TreeNode, TreeNodeRecursion};
use datafusion::common::{Column, Constraint, JoinType, NullEquality};
use datafusion::logical_expr::logical_plan::{
    Aggregate, Distinct, FetchType, Join, LogicalPlan, SkipType, TableScan,
};
use datafusion::logical_expr::utils::split_conjunction;
use datafusion::logical_expr::{BinaryExpr, Cast, Expr, ExprSchemable, Operator, TryCast};
use z3::ast::{Bool, Int};

use crate::domain::{self, Dom, Facts};
use crate::origin::{self, Origin};
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
    pub(crate) symbol: String,
    pub(crate) var: Int,
}

/// The abstract state of a relation: its cardinality and, per output column, a
/// variable bounding its number of distinct values.
#[derive(Clone)]
pub(crate) struct Rel {
    pub(crate) card: Int,
    pub(crate) ndv: Vec<Int>,
    /// What every row's values satisfy, whatever the data.
    pub(crate) facts: Facts,
    /// `(column, bound)`: the column holds non-negative integers summing to at
    /// most `bound` over all rows, like the counts of a GROUP BY.
    pub(crate) sums: Vec<(Expr, Int)>,
    /// The stored table this relation's rows are distinct rows of, if any.
    pub(crate) origin: Option<Origin>,
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
    pub(crate) fn new(resolve: &'a dyn Fn(&TableScan) -> ScanKind, max_product: usize) -> Self {
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
        }
    }

    fn new_var(&mut self, name: String) -> Int {
        let v = Int::new_const(name.as_str());
        self.solver.assert(v.ge(int(0)));
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
        let rel = Rel {
            card,
            ndv,
            facts: Facts::default(),
            sums: vec![],
            origin: None,
        };
        self.unique_columns(plan, &rel);
        rel
    }

    /// A column that traces to a declared primary key takes a distinct value on
    /// every row: its NDV equals the cardinality.
    fn unique_columns(&self, plan: &LogicalPlan, rel: &Rel) {
        let schema = plan.schema();
        for j in 0..schema.fields().len() {
            let col = Column::from(schema.qualified_field(j));
            if covers_primary_key(plan, &[col]) {
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

    fn assert(&self, b: Bool) {
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
        self.solver.assert(var.ge(int(0)));
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
        });
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
        // Rows whose values are each at least `k` and sum to at most `bound`
        // number at most `bound / k`.
        for (c, bound) in &rel.sums {
            if let Some(k) = rel.facts.dom(c, schema).min()
                && k >= 1
                && k <= u64::MAX as i128
            {
                self.assert((&rel.card * int(k as u64)).le(bound));
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
                }
                o.facts = computed_facts(plan, &p.expr, &p.input, &l.facts);
                o.sums = rename_sums(&l.sums, &|c| passed_column(plan, &p.expr, c));
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
            LogicalPlan::Window(p) => self.same_rows("Window", plan, &p.input),
            LogicalPlan::Filter(f) => {
                let l = self.visit(&f.input);
                let mut o = self.fresh("Filter", plan);
                self.assert(o.card.le(&l.card));
                self.subset_ndv(&o, &l);
                self.filter_ndv(&f.predicate, &f.input, &o, &l);
                o.facts = l.facts.clone();
                o.sums = l.sums.clone();
                o.facts.assume(&f.predicate, plan.schema());
                o.origin = l.origin.clone().map(|x| x.narrow(&o.facts, plan.schema()));
                o
            }
            LogicalPlan::Distinct(Distinct::All(input)) => {
                let l = self.visit(input);
                let mut o = self.fresh("Distinct", plan);
                o.facts = l.facts.clone();
                o.sums = l.sums.clone();
                o.origin = l.origin.clone();
                self.assert(o.card.le(&l.card));
                self.assert(l.card.ge(int(1)).implies(o.card.ge(int(1))));
                // DISTINCT keeps every value that occurs.
                self.kept_values(plan, &o, &l);
                let all: Vec<&Int> = l.ndv.iter().collect();
                if let Some(p) = product(&all, self.max_product) {
                    self.assert(o.card.le(p));
                }
                let cols: Vec<Column> = (0..input.schema().fields().len())
                    .map(|i| Column::from(input.schema().qualified_field(i)))
                    .collect();
                if covers_primary_key(input, &cols) {
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
                o.facts = l.facts.clone();
                o.sums = l.sums.clone();
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
                o.facts = l.facts.clone();
                o.sums = l.sums.clone();
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
            f.facts = out.facts.clone();
            for filter in &scan.filters {
                f.facts.assume(filter, plan.schema());
            }
            f.origin = out.origin.clone().map(|x| x.narrow(&f.facts, plan.schema()));
            out = f;
        }
        (out, raw_scan)
    }

    /// A composite primary key is unique as a tuple: the table has at most as
    /// many rows as the product of its key columns' NDVs.
    fn composite_key(&self, scan: &TableScan, rel: &Rel) {
        let Some(constraints) = scan.source.constraints() else {
            return;
        };
        for c in constraints.iter() {
            let Constraint::PrimaryKey(pk) = c else {
                continue;
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

    /// Same rows as the input, whose columns come first and unchanged.
    fn same_rows(&mut self, kind: &str, plan: &LogicalPlan, input: &LogicalPlan) -> Rel {
        let l = self.visit(input);
        let mut o = self.fresh(kind, plan);
        self.assert(o.card.eq(&l.card));
        self.equal_ndv(&o, &l);
        o.facts = l.facts.by_position(input.schema(), plan.schema());
        o.sums = rename_sums(&l.sums, &|c| {
            let i = input.schema().index_of_column(c).ok()?;
            child_column(plan, i)
        });
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
            o.facts = aggregate_facts(plan, agg, &l.facts);
            return o;
        }
        let mut o = self.fresh("GroupBy", plan);
        o.facts = aggregate_facts(plan, agg, &l.facts);
        // Groups split the input's rows, so their counts sum to at most its
        // row count.
        for (i, e) in agg.aggr_expr.iter().enumerate() {
            if let Expr::AggregateFunction(f) = strip_alias(e)
                && f.func.name() == "count"
            {
                o.sums.push((col(plan, agg.group_expr.len() + i), l.card.clone()));
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
        // Grouping by a unique key leaves every row its own group.
        let cols: Option<Vec<Column>> = agg
            .group_expr
            .iter()
            .map(|e| key_column(&agg.input, e))
            .collect();
        if cols.is_some_and(|cols| covers_primary_key(&agg.input, &cols)) {
            self.assert(o.card.eq(&l.card));
        }
        o
    }

    fn join(&mut self, plan: &LogicalPlan, join: &Join) -> Rel {
        let l = self.visit(&join.left);
        let r = self.visit(&join.right);
        let equi = !join.on.is_empty();
        let cross = !equi && join.filter.is_none();
        let (lk, rk): (Vec<&Expr>, Vec<&Expr>) = join.on.iter().map(|(a, b)| (a, b)).unzip();
        // A unique key on one side means each row of the other side matches at
        // most once.
        let ru = equi && key_is_unique(&join.right, &rk);
        let lu = equi && key_is_unique(&join.left, &lk);
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
        if ru {
            inner = min(&inner, &l.card);
        }
        if lu {
            inner = min(&inner, &r.card);
        }
        match join.join_type {
            JoinType::Inner => {
                if cross {
                    self.assert(o.card.eq(&lr));
                } else {
                    self.assert(o.card.le(&inner));
                }
            }
            // An outer join emits its inner join's rows plus each unmatched row of
            // the preserved side. If each preserved row matches at most once, it
            // appears exactly once.
            JoinType::Left if ru => self.assert(o.card.eq(&l.card)),
            JoinType::Right if lu => self.assert(o.card.eq(&r.card)),
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
            JoinType::LeftSemi | JoinType::LeftAnti => self.assert(o.card.le(&l.card)),
            JoinType::RightSemi | JoinType::RightAnti => self.assert(o.card.le(&r.card)),
            JoinType::LeftMark => self.assert(o.card.eq(&l.card)),
            JoinType::RightMark => self.assert(o.card.eq(&r.card)),
        }
        self.join_ndv(join, &o, &l, &r);
        o.facts = join_facts(plan, join, &l.facts, &r.facts);
        // Semi, anti and mark joins keep a subset of one side's rows.
        o.sums = match join.join_type {
            JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => l.sums.clone(),
            JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => r.sums.clone(),
            _ => vec![],
        };
        let width = plan.schema().fields().len();
        o.origin = match join.join_type {
            JoinType::LeftSemi | JoinType::LeftAnti | JoinType::LeftMark => l.origin.as_ref(),
            JoinType::RightSemi | JoinType::RightAnti | JoinType::RightMark => r.origin.as_ref(),
            _ => None,
        }
        .map(|x| x.with_width(width).narrow(&o.facts, plan.schema()));
        o
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

fn rename_sums(sums: &[(Expr, Int)], map: &dyn Fn(&Column) -> Option<Column>) -> Vec<(Expr, Int)> {
    sums.iter()
        .filter_map(|(c, b)| Some((domain::rename(c, map)?, b.clone())))
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

/// An upper bound on the number of distinct values `e` takes over the rows of
/// `input`, or `None` if nothing better than the row count is known. A
/// deterministic function of some columns takes at most as many values as
/// there are combinations of theirs.
fn expr_bound(e: &Expr, input: &LogicalPlan, l: &Rel, cap: usize) -> Option<Int> {
    if let Some(c) = key_column(input, e) {
        let i = input.schema().index_of_column(&c).ok()?;
        return Some(l.ndv[i].clone());
    }
    let opaque = e.is_volatile()
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
        .unwrap_or(true);
    if opaque {
        return None;
    }
    let factors: Option<Vec<&Int>> = e
        .column_refs()
        .into_iter()
        .map(|c| input.schema().index_of_column(c).ok().map(|i| &l.ndv[i]))
        .collect();
    product(&factors?, cap)
}

/// True if the join key expressions `keys` of `side` are unique in `side`'s
/// output (see `covers_primary_key`). Non-column keys are never unique.
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

/// Positions of `cols` in `plan`'s output.
fn output_indices(plan: &LogicalPlan, cols: &[Column]) -> Option<Vec<usize>> {
    cols.iter()
        .map(|c| plan.schema().index_of_column(c).ok())
        .collect()
}

/// True if `cols` of `plan`'s output are unique: they trace back to a declared
/// primary key, a GROUP BY key or a DISTINCT output through operators that
/// never duplicate rows.
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
        | LogicalPlan::Window(_) => {
            let child = plan.inputs()[0];
            same_positions(plan, child, cols).is_some_and(|cs| covers_primary_key(child, &cs))
        }
        // DISTINCT's output is unique on all its columns, and is a subset of its
        // input's rows, so its input's keys stay unique too.
        LogicalPlan::Distinct(Distinct::All(input)) => {
            let all = output_indices(plan, cols)
                .is_some_and(|ix| (0..plan.schema().fields().len()).all(|i| ix.contains(&i)));
            all || same_positions(plan, input, cols)
                .is_some_and(|cs| covers_primary_key(input, &cs))
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
            by_on || mapped.is_some_and(|cs| covers_primary_key(&on.input, &cs))
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
            mapped.is_some_and(|cs| covers_primary_key(&agg.input, &cs))
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
        // Unions, scans of non-tables and everything else: no key to rely on.
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
