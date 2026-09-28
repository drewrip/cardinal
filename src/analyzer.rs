//! Bottom-up walk over a DataFusion `LogicalPlan` that emits Z3 cardinality
//! constraints, one integer variable per operator.

use std::collections::HashMap;

use datafusion::common::JoinType;
use datafusion::common::tree_node::TreeNodeRecursion;
use datafusion::logical_expr::Expr;
use datafusion::logical_expr::logical_plan::{FetchType, Join, LogicalPlan};
use z3::Solver;
use z3::ast::{Bool, Int};

pub(crate) struct Analyzer {
    pub(crate) solver: Solver,
    /// One variable per distinct table name, shared by every scan of it.
    pub(crate) tables: HashMap<String, Int>,
    /// Every scan occurrence as (scan variable name, table name), with its variable.
    pub(crate) scans: Vec<(String, String, Int)>,
    /// Every operator variable, by name, so callers can read them from a model.
    pub(crate) vars: Vec<(String, Int)>,
    counter: usize,
}

fn max(a: &Int, b: &Int) -> Int {
    a.ge(b).ite(a, b)
}

impl Analyzer {
    pub(crate) fn new() -> Self {
        Self {
            solver: Solver::new(),
            tables: HashMap::new(),
            scans: Vec::new(),
            vars: Vec::new(),
            counter: 0,
        }
    }

    /// Creates a fresh non-negative variable named `O{n}_{kind}`.
    fn fresh(&mut self, kind: &str) -> Int {
        let name = format!("O{}_{}", self.counter, kind);
        self.counter += 1;
        let v = Int::new_const(name.as_str());
        self.solver.assert(v.ge(Int::from_i64(0)));
        self.vars.push((name, v.clone()));
        v
    }

    fn assert(&self, b: Bool) {
        self.solver.assert(b);
    }

    fn table(&mut self, name: &str) -> Int {
        if let Some(t) = self.tables.get(name) {
            return t.clone();
        }
        let t = Int::new_const(name);
        self.solver.assert(t.ge(Int::from_i64(0)));
        self.tables.insert(name.to_string(), t.clone());
        t
    }

    /// Returns the output cardinality variable of `plan`.
    pub(crate) fn visit(&mut self, plan: &LogicalPlan) -> Int {
        // Subqueries left inside expressions (e.g. an uncorrelated scalar subquery
        // in a Filter) are not plan inputs, but their scans still read rows, so
        // visit them to register those scans in the sum.
        let _ = plan.apply_subqueries(|sub| {
            self.visit(sub);
            Ok(TreeNodeRecursion::Continue)
        });
        match plan {
            LogicalPlan::TableScan(scan) => {
                let table_name = scan.table_name.to_string();
                let r = self.table(&table_name);
                let s = self.fresh(&format!("Scan_{}", table_name.replace('.', "_")));
                self.assert(s.eq(&r));
                self.scans.push((s.to_string(), table_name, s.clone()));
                let mut out = s;
                // Pushed-down filters behave like a Filter wrapping the scan.
                if !scan.filters.is_empty() {
                    let f = self.fresh("ScanFilter");
                    self.assert(f.le(&out));
                    out = f;
                }
                if let Some(n) = scan.fetch {
                    let f = self.fresh("ScanFetch");
                    self.assert(f.le(&out));
                    self.assert(f.le(Int::from_u64(n as u64)));
                    out = f;
                }
                out
            }
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
        }
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
        let kind = format!(
            "{:?}{}Join",
            join.join_type,
            if equi {
                "Equi"
            } else if cross {
                "Cross"
            } else {
                "Theta"
            }
        );
        let o = self.fresh(&kind);
        let lr = Int::mul(&[&l, &r]);
        match join.join_type {
            JoinType::Inner => {
                if equi {
                    self.assert(o.le(max(&l, &r)));
                } else if cross {
                    self.assert(o.eq(&lr));
                } else {
                    self.assert(o.le(&lr));
                }
            }
            JoinType::Left | JoinType::Right => {
                let (preserved, _) = if join.join_type == JoinType::Left {
                    (&l, &r)
                } else {
                    (&r, &l)
                };
                self.assert(o.ge(preserved));
                if equi {
                    self.assert(o.le(max(&l, &r)));
                } else {
                    self.assert(o.le(Int::add(&[&lr, preserved])));
                }
            }
            JoinType::Full => {
                if equi {
                    self.assert(o.le(Int::add(&[&l, &r])));
                } else {
                    self.assert(o.le(Int::add(&[&lr, &l, &r])));
                }
            }
            JoinType::LeftSemi | JoinType::LeftAnti => self.assert(o.le(&l)),
            JoinType::RightSemi | JoinType::RightAnti => self.assert(o.le(&r)),
            JoinType::LeftMark => self.assert(o.eq(&l)),
            JoinType::RightMark => self.assert(o.eq(&r)),
        }
        o
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
