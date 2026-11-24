//! Snowflake's executed plans, from `GET_QUERY_OPERATOR_STATS`, and its
//! `EXPLAIN USING JSON` plans, as an [`ObservedPlan`].
//!
//! Snowflake has no `EXPLAIN ANALYZE`. Its operator statistics are read
//! through [`snowflake_explain`]'s `QueryPlan`, which the readers take as
//! rows, as a `QueryPlan` (its JSON form, or the value), or as `EXPLAIN`'s
//! output.
//!
//! Snowflake prints every column qualified, by its scan's alias or table
//! (`L1.L_ORDERKEY`, `ORDERS.O_ORDERKEY`), and in upper case: names are
//! matched to the catalog's without regard to case. It inlines derived
//! tables and CTEs read once, printing what reads them by base expression;
//! a CTE read more than once is a `WithClause` that each `WithReference`
//! reads (an [`Op::Reuse`]), under its alias. Operators print no output
//! columns but scans, aggregates and the result: each outputs its inputs'
//! columns, and an aggregate's values are matched by their text, as the
//! operators above print them.
//!
//! A join's first input is its build side, the second its probe side,
//! which it reads first. An inner or outer join's type names the first as
//! its left side (`LEFT OUTER` keeps it): it reads as the probe side joined
//! to it by the mirrored type (`Right`). A semi or anti join may keep either
//! side under one name: the side is told by what the join can have done
//! (see `Builder::keeps_build`), or the join is not read. An anti join is
//! null-aware if the query's are `NOT IN`, not `NOT EXISTS`.
//!
//! Snowflake prunes more than it prints:
//!
//! - A scan's rows are those left by the filters directly above it: a
//!   filter that removed nothing the scan applied in full, and others it
//!   may have applied in part.
//! - A scan under a `JoinFilter` (a bloom filter) may be pruned by the
//!   build side of any join above it on its columns, whichever join the
//!   filter names. A scan under none is not.
//! - A top-n's input is pruned of what cannot be in its rows (an
//!   aggregate's groups, by a key it sorts on), and a limit stops its
//!   input: neither's input is counted.
//! - An aggregate another completes above it may be partial: a group per
//!   worker, or rows passed through. It is read as its input, and nothing
//!   up to the aggregate that completes it is counted.
//!
//! What is not printed is not guessed. A `Limit` prints no count, so its
//! count is the query's (`sql`). An uncorrelated scalar subquery runs as an
//! earlier step, which the plan reads as `Subquery(Step1)`: the query's step
//! is the last, and that value is not read. Neither are the internal
//! functions of an aggregation split in phases (`SUM_INTERNAL`).

use std::collections::{HashMap, HashSet};

use datafusion::arrow::datatypes::{DataType, Field};
use datafusion::common::tree_node::{Transformed, TreeNode};
use datafusion::common::{DFSchema, DataFusionError, JoinType};
use datafusion::logical_expr::Expr;
use datafusion::logical_expr::utils::split_conjunction_owned;
use datafusion::sql::sqlparser::dialect::SnowflakeDialect;
use serde_json::Value;
use snowflake_explain::{Node, OperatorStatsRow, QueryPlan, Step};

use super::duckdb::replace_word;
use super::sql::QueryText;
use super::{Catalog, Lineage, ONode, ObservedPlan, Op, OutCol, Pred, RuntimeFilter, base_table, column_key, qualified, requalify, simplify, type_of};
use crate::{Error, Result};

/// Reads a Snowflake query's executed plan against the tables in `catalog`:
/// `json` is its `GET_QUERY_OPERATOR_STATS` rows, or a serialized
/// [`QueryPlan`] made from them. `name` names the query in provenance.
/// `sql`, the query, gives its `LIMIT` counts, which the plan does not
/// print, and its CTEs' column names; without it, those are not read.
pub fn from_snowflake(catalog: &Catalog, name: &str, json: &str, sql: Option<&str>) -> Result<ObservedPlan> {
    let plan = parse(json)?;
    if plan.query_id.is_none() {
        return Err(Error::Observed("an estimated plan (EXPLAIN) has no counts: read it with from_snowflake_explain".into()));
    }
    from_snowflake_plan(catalog, name, &plan, sql, true)
}

/// Reads the plan Snowflake chose for a query, as printed by `EXPLAIN USING
/// JSON`, or an executed plan ([`from_snowflake`]'s input) with its counts
/// ignored. The plan is not counted: it pins nothing.
pub fn from_snowflake_explain(catalog: &Catalog, name: &str, json: &str, sql: Option<&str>) -> Result<ObservedPlan> {
    from_snowflake_plan(catalog, name, &parse(json)?, sql, false)
}

/// Reads `plan`, counted if `counted` (then it must be an executed plan's).
pub fn from_snowflake_plan(catalog: &Catalog, name: &str, plan: &QueryPlan, sql: Option<&str>, counted: bool) -> Result<ObservedPlan> {
    // A CREATE TABLE AS creates the table in a step of its own.
    let step = plan
        .steps
        .iter()
        .rev()
        .find(|s| !matches!(&s.nodes[..], [only] if only.operator == "CREATE TABLE"))
        .ok_or_else(|| Error::Observed("the plan has no steps".into()))?;
    let roots: Vec<&Node> = step.roots().collect();
    let [root] = roots[..] else {
        return Err(Error::Observed(format!("step {} has {} roots", step.id, roots.len())));
    };
    let text = sql.and_then(|q| QueryText::parse_in(catalog, q, &SnowflakeDialect {}));
    let not_in = sql.and_then(|q| {
        let q = q.to_uppercase().split_whitespace().collect::<Vec<_>>().join(" ").replace("( ", "(");
        match (q.contains("NOT IN (SELECT") || q.contains("NOT IN(SELECT"), q.contains("NOT EXISTS")) {
            (true, true) => None,
            (not_in, _) => Some(not_in),
        }
    });
    let mut b = Builder { catalog, step, text, counted, nodes: vec![], built: HashMap::new(), not_in, partial: Partial::default() };
    b.partial = b.partials();
    let root = b.node(root)?;
    b.limits();
    b.bloom_filters();
    b.top_k();
    Ok(ObservedPlan { name: name.to_string(), nodes: b.nodes, root, counted })
}

/// `json` as a [`QueryPlan`]: from operator stats rows, `EXPLAIN USING
/// JSON`'s output, or the plan's own JSON form, written out as a string or
/// not.
fn parse(json: &str) -> Result<QueryPlan> {
    let v: Value = serde_json::from_str(json).map_err(|e| Error::Observed(e.to_string()))?;
    let invalid = |e: &dyn std::fmt::Display| Error::Observed(format!("not a Snowflake plan: {e}"));
    match v {
        Value::String(s) => parse(&s),
        Value::Array(_) => {
            let rows: Vec<OperatorStatsRow> = serde_json::from_value(v).map_err(|e| invalid(&e))?;
            QueryPlan::from_rows(rows).map_err(|e| invalid(&e))
        }
        Value::Object(ref o) if o.contains_key("Operations") => QueryPlan::from_explain(&v).map_err(|e| invalid(&e)),
        Value::Object(ref o) if o.contains_key("steps") => serde_json::from_value(v).map_err(|e| invalid(&e)),
        _ => Err(invalid(&"expected operator stats rows, EXPLAIN USING JSON output or a QueryPlan")),
    }
}

/// Wrappers with no effect on rows: the result, and the write of a
/// `CREATE TABLE AS` or `INSERT`.
const WRAPPERS: &[&str] = &["Result", "CreateTableAsSelect", "Insert"];

struct Builder<'a> {
    catalog: &'a Catalog,
    step: &'a Step,
    text: Option<QueryText>,
    /// Whether operators report their rows. Without, they read as 0.
    counted: bool,
    nodes: Vec<ONode>,
    /// What each `WithClause` became, by operator id: built once, however
    /// many read it.
    built: HashMap<u32, usize>,
    /// Whether the query's anti joins are `NOT IN` (null-aware), not `NOT
    /// EXISTS`: `None` if it has both, or is not known.
    not_in: Option<bool>,
    partial: Partial,
}

/// The aggregates that may be partial ([`Builder::partials`]), by operator
/// id, and what they leave uncounted.
#[derive(Default)]
struct Partial {
    /// Read as their input.
    spliced: HashSet<u32>,
    /// Operators above one, up to the aggregate that completes it: their
    /// counts are of partial groups.
    uncounted: HashSet<u32>,
    /// The aggregates that complete one: their values are not read.
    completing: HashSet<u32>,
}

impl<'a> Builder<'a> {
    fn get(&self, id: u32) -> Result<&'a Node> {
        let step: &'a Step = self.step;
        step.node(id).ok_or_else(|| Error::Observed(format!("no operator {id} in step {}", step.id)))
    }

    fn children(&self, n: &Node) -> Result<Vec<&'a Node>> {
        n.children.iter().map(|&c| self.get(c)).collect()
    }

    fn node(&mut self, n: &'a Node) -> Result<usize> {
        let kids = self.children(n)?;
        let ty = n.operator.as_str();
        match (ty, &kids[..]) {
            (t, [only]) if WRAPPERS.contains(&t) => return self.node(only),
            ("WithClause", [body]) => {
                if let Some(&i) = self.built.get(&n.id) {
                    return Ok(i);
                }
                let i = self.node(body)?;
                self.built.insert(n.id, i);
                return Ok(i);
            }
            ("WithReference", [clause]) => {
                let of = self.node(clause)?;
                return Ok(self.reuse(of, n, clause));
            }
            // Read into the scan below it, if one.
            ("JoinFilter", [c]) if self.scan_below(c) => return self.node(c),
            ("Aggregate", [c]) if self.partial.spliced.contains(&n.id) => return self.node(c),
            _ => {}
        }
        let ids = kids.iter().map(|k| self.node(k)).collect::<Result<Vec<_>>>()?;
        let (op, columns, ordered, mut children) = self.convert(n, &ids);
        let (op, columns) = match op {
            // A null-aware anti join, as a filter on a mark join.
            Op::Join { kind: JoinType::LeftMark, on } => {
                let probe = &self.nodes[children[0]];
                let mut marked = columns.clone();
                marked.push(unknown("mark".into()));
                let (rows, counted) = (probe.rows, false);
                self.nodes.push(ONode { op: Op::Join { kind: JoinType::LeftMark, on }, rows, counted, children, columns: marked, ordered: false, blocking: false, engine_op: n.operator.clone(), cut_short: false });
                children = vec![self.nodes.len() - 1];
                (Op::MarkFilter { negated: true }, columns)
            }
            op => (op, columns),
        };
        let op = match op {
            Op::Aggregate { keys, values } if self.partial.completing.contains(&n.id) => Op::Aggregate { keys, values: vec![None; values.len()] },
            op => op,
        };
        let blocking = matches!(op, Op::Sort | Op::TopN { .. } | Op::Aggregate { .. });
        let (rows, counted) = self.rows(n);
        let counted = counted && !self.partial.uncounted.contains(&n.id);
        self.nodes.push(ONode { op, rows, counted, children, columns, ordered, blocking, engine_op: n.operator.clone(), cut_short: false });
        Ok(self.nodes.len() - 1)
    }

    /// The rows operator `n` output, and whether they were counted.
    fn rows(&self, n: &Node) -> (u64, bool) {
        match n.stats.output_rows {
            Some(rows) if self.counted => (rows, true),
            _ => (0, false),
        }
    }

    /// The aggregates that may be partial. Snowflake aggregates in phases on
    /// several workers: below the aggregate that completes it, an aggregate
    /// may output a group once per worker, or pass rows through (eager
    /// aggregation below a join, by its key). One is taken as partial where
    /// another aggregate above it, through joins, filters and sorts, reads
    /// its values only in its own aggregates. A partial aggregate keeps its
    /// input's set of keys, so the one above has as many groups over its
    /// input: it is read as its input, and what lies between is not counted.
    fn partials(&self) -> Partial {
        let mut p = Partial::default();
        let aggregate = |n: &Node| n.operator == "Aggregate";
        // The aggregate above `n` through joins, filters and sorts, if one,
        // and the operators on the way.
        let above = |n: &'a Node| -> Option<(&'a Node, Vec<&'a Node>)> {
            let mut path = vec![];
            let mut at = n;
            loop {
                let [parent] = at.parents[..] else { return None };
                let parent = self.get(parent).ok()?;
                match parent.operator.as_str() {
                    "Aggregate" => return Some((parent, path)),
                    "Filter" | "JoinFilter" | "Sort" | "CartesianJoin" => {}
                    t if t.ends_with("Join") => {}
                    _ => return None,
                }
                path.push(parent);
                at = parent;
            }
        };
        for n in self.step.nodes.iter().filter(|n| aggregate(n)) {
            let Some((over, path)) = above(n) else { continue };
            let values = strings(&n.attributes, "functions");
            let mut texts = strings(&over.attributes, "grouping_keys");
            for x in &path {
                texts.extend(x.attributes.keys().flat_map(|k| strings(&x.attributes, k)));
            }
            if !values.iter().any(|v| texts.iter().any(|t| t.contains(v.as_str()))) {
                p.spliced.insert(n.id);
            }
        }
        for &id in &p.spliced {
            let mut at = self.get(id).ok();
            while let Some(n) = at.and_then(&above) {
                p.uncounted.extend(n.1.iter().map(|x| x.id));
                if !p.spliced.contains(&n.0.id) {
                    p.completing.insert(n.0.id);
                    break;
                }
                at = Some(n.0);
            }
        }
        p
    }

    /// Whether only filters lie between `n` and a scan below it.
    fn scan_below(&self, mut n: &'a Node) -> bool {
        loop {
            match (n.operator.as_str(), &n.children[..]) {
                ("TableScan", []) => return true,
                ("Filter" | "JoinFilter", [c]) => match self.get(*c) {
                    Ok(c) => n = c,
                    Err(_) => return false,
                },
                _ => return false,
            }
        }
    }

    /// A read of operator `of`'s output, as an independent copy of it, under
    /// the alias of `n`, a `WithReference` of the CTE `clause`.
    fn reuse(&mut self, of: usize, n: &Node, clause: &Node) -> usize {
        let id = self.nodes.len();
        let suffix = format!("~r{id}");
        let attr = |n: &Node, key: &str| n.attributes.get(key).and_then(Value::as_str).map(str::to_uppercase);
        let cte = attr(clause, "name");
        let alias = attr(n, "alias").or_else(|| cte.clone()).unwrap_or_default();
        let source = &self.nodes[of];
        // The CTE's columns as the query names them, else as their columns.
        let names = cte.as_deref().and_then(|c| self.text.as_ref()?.relation_columns(c)).filter(|n| source.ordered && n.len() == source.columns.len());
        let columns = source
            .columns
            .iter()
            .enumerate()
            .map(|(i, c)| {
                let name = match names {
                    Some(names) => names[i].to_uppercase(),
                    None => c.name.rsplit_once('.').map_or(c.name.as_str(), |(_, n)| n).to_string(),
                };
                OutCol { name: format!("{alias}.{name}"), lineage: rename(&c.lineage, &suffix) }
            })
            .collect();
        let (rows, counted) = self.rows(n);
        let ordered = source.ordered;
        self.nodes.push(ONode {
            op: Op::Reuse { suffix, checked: counted },
            rows: if counted { rows } else { source.rows },
            counted: self.counted,
            children: vec![of],
            columns,
            ordered,
            blocking: false,
            engine_op: n.operator.clone(),
            cut_short: false,
        });
        id
    }

    /// Operator `n` over `kids`: its model, columns, whether they are in
    /// order, and its inputs in the model's order.
    fn convert(&self, n: &'a Node, kids: &[usize]) -> (Op, Vec<OutCol>, bool, Vec<usize>) {
        let attrs = &n.attributes;
        let passthrough = |op| {
            let c = &self.nodes[kids[0]];
            (op, c.columns.clone(), c.ordered, kids.to_vec())
        };
        let ty = n.operator.as_str();
        match (ty, kids) {
            ("TableScan", []) => {
                let (op, columns) = self.scan(n);
                (op, columns, true, vec![])
            }
            ("Filter", [c]) => {
                let c = &self.nodes[*c];
                let predicate = self.pred(text(attrs, "filter_condition").unwrap_or(""), &c.columns, false);
                passthrough(Op::Filter { predicate })
            }
            ("Projection", [c]) => {
                let c = &self.nodes[*c];
                let columns = strings(attrs, "expressions")
                    .into_iter()
                    .map(|e| match lookup(&e, &c.columns) {
                        Some(col) => col.clone(),
                        None => OutCol { lineage: self.read(&e, &c.columns).map_or(Lineage::Unknown, Lineage::Exact), name: e },
                    })
                    .collect();
                (Op::Project, columns, false, kids.to_vec())
            }
            ("Aggregate", [c]) => {
                let (op, columns) = self.aggregate(attrs, &self.nodes[*c]);
                (op, columns, true, kids.to_vec())
            }
            ("Sort", [_]) => passthrough(Op::Sort),
            ("SortWithLimit", [_]) => match number(attrs, "rows") {
                Some(fetch) => passthrough(Op::TopN { fetch, offset: number(attrs, "offset").unwrap_or(0) }),
                None => passthrough(Op::Other),
            },
            // Bounded, if the query says, by `Builder::limits`.
            ("Limit", [_]) => passthrough(Op::Limit { at_most: None }),
            ("WindowFunction", [c]) => {
                let c = &self.nodes[*c];
                let mut columns = c.columns.clone();
                columns.extend(strings(attrs, "functions").into_iter().map(unknown));
                (Op::Window, columns, false, kids.to_vec())
            }
            ("UnionAll", [first, ..]) => {
                let columns = self.nodes[*first].columns.iter().map(|c| unknown(c.name.clone())).collect();
                (Op::Union, columns, false, kids.to_vec())
            }
            (_, [build, probe]) if ty.ends_with("Join") => self.join(n, ty == "CartesianJoin", *build, *probe),
            // What has no model outputs, as it translates, its one input's
            // columns.
            (_, [_]) => passthrough(Op::Other),
            _ => (Op::Other, vec![], false, kids.to_vec()),
        }
    }

    /// A scan, with the filters directly above it, which it may have applied.
    fn scan(&self, n: &'a Node) -> (Op, Vec<OutCol>) {
        let attrs = &n.attributes;
        let printed = text(attrs, "table_name").unwrap_or("");
        let short = unquote(printed.rsplit('.').next().unwrap_or(printed));
        let Some(table) = self.catalog.tables.keys().find(|t| t.eq_ignore_ascii_case(&short)).cloned() else {
            return (Op::Other, vec![]);
        };
        let qualifier = text(attrs, "table_alias").map(unquote).unwrap_or(short).to_uppercase();
        let instance = format!("{table}#{}", self.nodes.len());
        let fields: Vec<String> = self.catalog.tables[&table].fields().iter().map(|f| f.name().clone()).collect();
        let field = |c: &str| fields.iter().find(|f| f.eq_ignore_ascii_case(&unquote(c))).cloned();
        let listed = match attrs.get("columns") {
            Some(_) => strings(attrs, "columns"),
            None => fields.clone(),
        };
        let columns: Vec<OutCol> = listed
            .iter()
            .map(|c| OutCol {
                name: format!("{qualifier}.{}", unquote(c).to_uppercase()),
                lineage: field(c).map_or(Lineage::Unknown, |f| Lineage::Exact(qualified(&instance, &f))),
            })
            .collect();
        // The filters above, from the nearest. A predicate the scan applied
        // in full, where its filter removed nothing, is the scan's own; in a
        // plan that counts nothing, which applies it changes no count read.
        let (mut filters, mut runtime_filters) = (vec![], vec![]);
        let mut below = n;
        let mut at = n.parents.first().and_then(|&p| self.get(p).ok()).filter(|_| n.parents.len() == 1);
        while let Some(f) = at.filter(|f| f.children.len() == 1) {
            match f.operator.as_str() {
                "Filter" => {
                    let whole = !self.counted || (f.stats.output_rows.is_some() && f.stats.output_rows == below.stats.output_rows);
                    filters.extend(self.pred(text(&f.attributes, "filter_condition").unwrap_or(""), &columns, !whole));
                }
                // Which columns it filters, `Builder::bloom_filters` says.
                "JoinFilter" => runtime_filters.push(RuntimeFilter { column: None, text: "JoinFilter".into(), optional: true, expr: None }),
                _ => break,
            }
            below = f;
            at = f.parents.first().and_then(|&p| self.get(p).ok()).filter(|_| f.parents.len() == 1);
        }
        (Op::Scan { table, instance, filters, runtime_filters }, columns)
    }

    fn aggregate(&self, attrs: &serde_json::Map<String, Value>, child: &ONode) -> (Op, Vec<OutCol>) {
        let mut keys = vec![];
        let mut columns = vec![];
        for g in strings(attrs, "grouping_keys") {
            let lineage = match lookup(&g, &child.columns) {
                Some(c) => c.lineage.clone(),
                None => self.read(&g, &child.columns).map_or(Lineage::Unknown, Lineage::Exact),
            };
            keys.push(match &lineage {
                Lineage::Exact(e) | Lineage::Bijective(e) => Some(e.clone()),
                Lineage::Unknown => None,
            });
            columns.push(OutCol { name: g, lineage });
        }
        // Each value is a column of this operator, named as it is printed,
        // which is how the operators above refer to it.
        let me = format!("@{}", self.nodes.len());
        let mut values = vec![];
        for a in strings(attrs, "functions") {
            values.push(self.read(&a, &child.columns).filter(aggregates));
            columns.push(OutCol { lineage: Lineage::Exact(qualified(&me, &a)), name: a });
        }
        (Op::Aggregate { keys, values }, columns)
    }

    /// A join of `build`, the first input, and `probe`: the probe side
    /// first, by the mirrored join type.
    fn join(&self, n: &Node, cartesian: bool, build: usize, probe: usize) -> (Op, Vec<OutCol>, bool, Vec<usize>) {
        let attrs = &n.attributes;
        let children = vec![probe, build];
        let other = || (Op::Other, vec![], false, children.clone());
        let ty = text(attrs, "join_type").map(str::to_uppercase);
        let kind = match ty.as_deref() {
            Some("INNER" | "CARTESIAN") => JoinType::Inner,
            Some("FULL OUTER") => JoinType::Full,
            Some(t @ ("LEFT OUTER" | "SEMI" | "ANTI")) => match (self.keeps_build(n, t), t) {
                (Some(true), "LEFT OUTER") => JoinType::Right,
                (Some(true), "SEMI") => JoinType::RightSemi,
                (Some(true), _) => JoinType::RightAnti,
                (Some(false), "LEFT OUTER") => JoinType::Left,
                (Some(false), "SEMI") => JoinType::LeftSemi,
                (Some(false), _) => JoinType::LeftAnti,
                (None, _) => return other(),
            },
            _ => return other(),
        };
        // NOT IN is a null-aware anti join, which only a mark join keeping
        // its probe side, the first, reads as.
        let null_aware = matches!(kind, JoinType::LeftAnti | JoinType::RightAnti) && self.not_in != Some(false);
        if null_aware && (kind == JoinType::RightAnti || self.not_in.is_none()) {
            return other();
        }
        let (p, b) = (&self.nodes[probe], &self.nodes[build]);
        let both: Vec<OutCol> = p.columns.iter().chain(&b.columns).cloned().collect();
        let mut on = vec![];
        for c in conjuncts(text(attrs, "equality_join_condition").unwrap_or("")) {
            match self.read(&c, &both).or_else(|| self.key(&c, p, b)) {
                Some(e) => on.push(Pred { text: e.to_string(), expr: Some(e), optional: false }),
                None => on.push(Pred { expr: None, text: c, optional: false }),
            }
        }
        on.extend(self.pred(text(attrs, "additional_join_condition").unwrap_or(""), &both, false));
        // EXPLAIN's, which snowflake-explain keeps as it is.
        for e in strings(attrs, "expressions") {
            if let Some(c) = e.strip_prefix("joinFilter:") {
                on.extend(self.pred(c.trim(), &both, false));
            }
        }
        // A join that printed no condition has one, but a cartesian join.
        if on.is_empty() && !cartesian {
            on.push(Pred { expr: None, text: "an unprinted condition".into(), optional: false });
        }
        if null_aware {
            // Read by `Builder::node` as a mark join and a filter on it.
            return (Op::Join { kind: JoinType::LeftMark, on }, p.columns.clone(), false, children);
        }
        let columns = match kind {
            JoinType::RightSemi | JoinType::RightAnti => b.columns.clone(),
            JoinType::LeftSemi | JoinType::LeftAnti => p.columns.clone(),
            _ => both,
        };
        (Op::Join { kind, on }, columns, false, children)
    }

    /// Whether join `n` of type `ty` (`LEFT OUTER`, `SEMI` or `ANTI`) keeps
    /// its build side, the first, rather than its probe side, if that can
    /// be told. Snowflake joins either way under one name. A join's
    /// `JoinFilter` drops rows of the probe side that match nothing, which
    /// an outer or anti join keeping that side keeps; a semi or anti join
    /// outputs at most the rows of the side it keeps, an outer join at
    /// least; and the operators above read only the columns of the side a
    /// semi or anti join keeps.
    fn keeps_build(&self, n: &Node, ty: &str) -> Option<bool> {
        let [build, probe] = n.children[..] else { return None };
        let (build, probe) = (self.get(build).ok()?, self.get(probe).ok()?);
        let filtered = |side: &Node| self.subtree(side).iter().any(|f| self.filters_for(f, n));
        if ty != "SEMI" && filtered(probe) {
            return Some(true);
        }
        if ty != "SEMI" && filtered(build) {
            return Some(false);
        }
        // Counts, where no limit stopped what it read.
        let limited = self.step.nodes.iter().any(|n| n.operator == "Limit");
        if let (true, false, Some(out), Some(b), Some(p)) = (self.counted, limited, n.stats.output_rows, build.stats.output_rows, probe.stats.output_rows) {
            let fits = |side: u64| if ty == "LEFT OUTER" { out >= side } else { out <= side };
            match (fits(b), fits(p)) {
                (true, false) => return Some(true),
                (false, true) => return Some(false),
                _ => {}
            }
        }
        if ty == "LEFT OUTER" {
            return None;
        }
        // The qualifiers only one side has, read above.
        let (qb, qp) = (self.qualifiers(build), self.qualifiers(probe));
        let inside: Vec<u32> = self.subtree(n).iter().map(|x| x.id).collect();
        let outside: Vec<String> = self.step.nodes.iter().filter(|x| !inside.contains(&x.id)).flat_map(|x| self.qualifiers_of(x)).collect();
        let only = |q: &[String], not: &[String]| q.iter().filter(|x| !not.contains(x) && !outside.contains(x)).cloned().collect::<Vec<_>>();
        let (qb, qp) = (only(&qb, &qp), only(&qp, &qb));
        let above = self.above(n);
        let read = |qs: &[String]| qs.iter().any(|q| above.iter().any(|t| find_word(t, &format!("{q}.")).is_some()));
        match (read(&qb), read(&qp)) {
            (true, false) => Some(true),
            (false, true) => Some(false),
            _ => None,
        }
    }

    /// Whether `f` is a `JoinFilter` of join `n`'s.
    fn filters_for(&self, f: &Node, n: &Node) -> bool {
        if f.operator != "JoinFilter" {
            return false;
        }
        match text(&f.attributes, "join_id") {
            Some(j) => j.trim().parse() == Ok(n.id),
            // EXPLAIN prints the join's condition.
            None => text(&f.attributes, "equality_join_condition").is_some() && text(&f.attributes, "equality_join_condition") == text(&n.attributes, "equality_join_condition"),
        }
    }

    /// `n` and every operator below it.
    fn subtree(&self, n: &'a Node) -> Vec<&'a Node> {
        let mut out = vec![n];
        let mut i = 0;
        while i < out.len() {
            out.extend(self.children(out[i]).unwrap_or_default());
            i += 1;
        }
        out
    }

    /// The qualifiers of the columns of the scans and CTE reads at or below `n`.
    fn qualifiers(&self, n: &'a Node) -> Vec<String> {
        self.subtree(n).into_iter().flat_map(|x| self.qualifiers_of(x)).collect()
    }

    /// The qualifier of the columns `n` reads in, if a scan or CTE read.
    fn qualifiers_of(&self, n: &Node) -> Option<String> {
        let attr = |k| text(&n.attributes, k).map(unquote);
        match n.operator.as_str() {
            "TableScan" => attr("table_alias").or_else(|| attr("table_name").map(|t| unquote(t.rsplit('.').next().unwrap_or(&t)))),
            "WithReference" => attr("alias"),
            _ => None,
        }
        .map(|q| q.to_uppercase())
    }

    /// The text of every attribute of the operators above `n`.
    fn above(&self, n: &Node) -> Vec<String> {
        fn texts(v: &Value, out: &mut Vec<String>) {
            match v {
                Value::String(s) => out.push(s.clone()),
                Value::Array(a) => a.iter().for_each(|v| texts(v, out)),
                Value::Object(o) => o.values().for_each(|v| texts(v, out)),
                _ => {}
            }
        }
        let mut out = vec![];
        let mut todo: Vec<u32> = n.parents.clone();
        let mut seen = vec![];
        while let Some(id) = todo.pop() {
            let Ok(p) = self.get(id) else { continue };
            if seen.contains(&id) {
                continue;
            }
            seen.push(id);
            p.attributes.values().for_each(|v| texts(v, &mut out));
            todo.extend(&p.parents);
        }
        out
    }

    /// An equality of a join's keys, `a = b`, read with one side over each
    /// input: where a name both inputs have (a table read twice, without an
    /// alias) is the one input's, the other side's being only the other's.
    fn key(&self, text: &str, p: &ONode, b: &ONode) -> Option<Expr> {
        let [l, r] = split_top_level(text, " = ")[..] else { return None };
        let (l, r) = (strip_parens(l), strip_parens(r));
        let read = |x: &str, side: &ONode| self.read(x, &side.columns);
        let mut found = vec![];
        for (x, y) in [(p, b), (b, p)] {
            if let (Some(l), Some(r)) = (read(l, x), read(r, y)) {
                found.push(l.eq(r));
            }
        }
        match &found[..] {
            [e] => Some(e.clone()),
            _ => None,
        }
    }

    /// A `JoinFilter` names one join, but the scan under it may have been
    /// filtered by the build side of any join above it on one of the scan's
    /// columns: each scan under one has a runtime filter on each column a
    /// join above compares, which only the highest such join makes moot. (A
    /// scan under none read every row its filters keep.) Above a CTE's read,
    /// and above a join on a condition not read, the columns are not known.
    fn bloom_filters(&mut self) {
        let mut parents = vec![vec![]; self.nodes.len()];
        for (i, n) in self.nodes.iter().enumerate() {
            for &c in &n.children {
                parents[c].push(i);
            }
        }
        for i in 0..self.nodes.len() {
            let Op::Scan { runtime_filters, .. } = &self.nodes[i].op else { continue };
            if runtime_filters.is_empty() {
                continue;
            }
            let (mut above, mut todo) = (vec![], parents[i].clone());
            while let Some(a) = todo.pop() {
                if !above.contains(&a) {
                    above.push(a);
                    todo.extend(&parents[a]);
                }
            }
            let mut pairs = vec![];
            let mut unknown = false;
            for &a in &above {
                match &self.nodes[a].op {
                    Op::Reuse { .. } => unknown = true,
                    Op::Join { on, .. } => {
                        for p in on {
                            match &p.expr {
                                Some(Expr::BinaryExpr(b)) if b.op == datafusion::logical_expr::Operator::Eq => {
                                    if let (Expr::Column(l), Expr::Column(r)) = (b.left.as_ref(), b.right.as_ref()) {
                                        pairs.push((column_key(l), column_key(r)));
                                    }
                                }
                                None if p.text.contains(" = ") => unknown = true,
                                _ => {}
                            }
                        }
                    }
                    _ => {}
                }
            }
            let compared = |c: &String| pairs.iter().any(|(l, r)| l == c || r == c);
            let mut filters: Vec<RuntimeFilter> = self.nodes[i]
                .columns
                .iter()
                .filter_map(|c| match &c.lineage {
                    Lineage::Exact(Expr::Column(col)) => Some(column_key(col)),
                    _ => None,
                })
                .filter(compared)
                .map(|c| RuntimeFilter { text: format!("a bloom filter on {c}"), column: Some(c), optional: true, expr: None })
                .collect();
            if unknown || filters.is_empty() {
                filters.push(RuntimeFilter { column: None, text: "a bloom filter of a join above".into(), optional: true, expr: None });
            }
            if let Op::Scan { runtime_filters, .. } = &mut self.nodes[i].op {
                *runtime_filters = filters;
            }
        }
    }

    /// A top-n's input stops early, or prunes what cannot be in its first
    /// rows (an aggregate's groups by a key it sorts on, a scan's
    /// partitions): nothing below one is counted.
    fn top_k(&mut self) {
        let mut below: Vec<usize> = vec![];
        for n in &self.nodes {
            if let Op::TopN { .. } = n.op {
                below.extend(&n.children);
            }
        }
        while let Some(i) = below.pop() {
            self.nodes[i].counted = false;
            below.extend(self.nodes[i].children.clone());
        }
    }

    /// Bounds each limit by the query's `LIMIT` clauses, which Snowflake
    /// does not print. With as many limit and top-n operators as clauses,
    /// all with a constant count, each limit is one of the clauses, so
    /// outputs at most the largest count.
    fn limits(&mut self) {
        let Some(text) = &self.text else { return };
        let Some(counts) = text.limits().iter().copied().collect::<Option<Vec<u64>>>() else { return };
        let operators = self.nodes.iter().filter(|n| matches!(n.engine_op.as_str(), "Limit" | "SortWithLimit")).count();
        if operators != counts.len() {
            return;
        }
        let at_most = counts.into_iter().max();
        for n in self.nodes.iter_mut().filter(|n| n.engine_op == "Limit") {
            n.op = Op::Limit { at_most };
        }
    }

    /// `text`'s conjuncts over `cols`, each unresolved where it does not read.
    fn pred(&self, text: &str, cols: &[OutCol], optional: bool) -> Vec<Pred> {
        conjuncts(text)
            .into_iter()
            .flat_map(|c| match self.read(&c, cols) {
                Some(e) => split_conjunction_owned(e).into_iter().map(|e| Pred { text: e.to_string(), expr: Some(e), optional }).collect(),
                None => vec![Pred { expr: None, text: c, optional }],
            })
            .collect()
    }

    /// Reads `text`, an expression over `cols`, as an expression over base
    /// columns. A column is referred to by its name, which only it has, and
    /// must hold an exact value: a qualified column (`ORDERS.O_ORDERKEY`), or
    /// an aggregate's value, by its text.
    fn read(&self, text: &str, cols: &[OutCol]) -> Option<Expr> {
        let mut count = HashMap::<&str, usize>::new();
        for c in cols {
            *count.entry(c.name.as_str()).or_default() += 1;
        }
        let mut unique: Vec<&OutCol> = cols.iter().filter(|c| count[c.name.as_str()] == 1).collect();
        unique.sort_by_key(|c| std::cmp::Reverse(c.name.len()));
        let mut text = text.to_string();
        let (mut fields, mut lineage) = (vec![], HashMap::new());
        for (i, c) in unique.into_iter().enumerate() {
            if !text.contains(&c.name) {
                continue;
            }
            let placeholder = format!("__name_{i}");
            text = replace_word(&text, &c.name, &placeholder);
            let ty = match &c.lineage {
                Lineage::Exact(e) | Lineage::Bijective(e) => type_of(self.catalog, e),
                Lineage::Unknown => None,
            };
            fields.push(Field::new(&placeholder, ty.unwrap_or(DataType::Null), true));
            lineage.insert(placeholder, &c.lineage);
        }
        let schema = DFSchema::from_unqualified_fields(fields.into(), HashMap::new()).ok()?;
        let expr = self.catalog.state.create_logical_expr(&rewrite(&text), &schema).ok()?;
        let expr = expr
            .transform_up(|e| match e {
                Expr::Column(c) if c.relation.is_none() => match lineage.get(&c.name) {
                    Some(Lineage::Exact(e)) => Ok(Transformed::yes(e.clone())),
                    _ => Err(DataFusionError::Plan(format!("unresolved column {}", c.name))),
                },
                Expr::Alias(a) => Ok(Transformed::yes(*a.expr)),
                e => Ok(Transformed::no(e)),
            })
            .ok()?
            .data;
        Some(simplify(self.catalog, &self.nodes, expr))
    }
}

/// Whether `e` computes an aggregate: a value that does not is no
/// aggregate's (`COUNT(*)` of a `COUNT(*)` is printed as the lower's text).
fn aggregates(e: &Expr) -> bool {
    e.exists(|x| Ok(matches!(x, Expr::AggregateFunction(_)))).unwrap_or(false)
}

/// The column of `cols` named `name`, if only one is.
fn lookup<'c>(name: &str, cols: &'c [OutCol]) -> Option<&'c OutCol> {
    let mut named = cols.iter().filter(|c| c.name == name);
    match (named.next(), named.next()) {
        (Some(c), None) => Some(c),
        _ => None,
    }
}

fn unknown(name: String) -> OutCol {
    OutCol { name, lineage: Lineage::Unknown }
}

/// `l` over a copy of its instances, each renamed with `suffix`.
fn rename(l: &Lineage, suffix: &str) -> Lineage {
    let f = |r: &str| base_table(r).map(|_| format!("{r}{suffix}"));
    match l {
        Lineage::Exact(e) => Lineage::Exact(requalify(e, &f)),
        Lineage::Bijective(e) => Lineage::Bijective(requalify(e, &f)),
        Lineage::Unknown => Lineage::Unknown,
    }
}

fn text<'v>(attrs: &'v serde_json::Map<String, Value>, key: &str) -> Option<&'v str> {
    attrs.get(key).and_then(Value::as_str)
}

/// An attribute that is a list of strings, or one.
fn strings(attrs: &serde_json::Map<String, Value>, key: &str) -> Vec<String> {
    match attrs.get(key) {
        Some(Value::String(s)) if !s.is_empty() => vec![s.clone()],
        Some(Value::Array(a)) => a.iter().filter_map(Value::as_str).map(str::to_string).collect(),
        _ => vec![],
    }
}

/// A whole, non-negative number, which Snowflake prints as a float (`10.0`).
fn number(attrs: &serde_json::Map<String, Value>, key: &str) -> Option<u64> {
    let n = attrs.get(key)?;
    let f = n.as_f64().or_else(|| n.as_str()?.trim().parse().ok())?;
    (f >= 0.0 && f.fract() == 0.0).then_some(f as u64)
}

/// An identifier as written, without its double quotes.
fn unquote(s: &str) -> String {
    s.trim().trim_matches('"').to_string()
}

/// The top-level conjuncts of `text`, each without its outer parentheses.
fn conjuncts(text: &str) -> Vec<String> {
    let text = strip_parens(text.trim());
    if text.is_empty() {
        return vec![];
    }
    let parts = split_top_level(text, " AND ");
    if parts.len() == 1 {
        return vec![text.to_string()];
    }
    parts.into_iter().flat_map(conjuncts).collect()
}

/// `text` without parentheses around all of it.
fn strip_parens(mut text: &str) -> &str {
    loop {
        let t = text.trim();
        let Some(inner) = t.strip_prefix('(').and_then(|r| r.strip_suffix(')')) else { return t };
        if closing(t, 0) != Some(t.len() - 1) {
            return t;
        }
        text = inner;
    }
}

/// The index of the parenthesis closing the one at `open`, outside string
/// literals.
fn closing(text: &str, open: usize) -> Option<usize> {
    let mut depth = 0usize;
    let mut quoted = false;
    for (i, c) in text.char_indices().skip_while(|(i, _)| *i < open) {
        match c {
            '\'' => quoted = !quoted,
            '(' if !quoted => depth += 1,
            ')' if !quoted => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// `text` split at each `separator` outside parentheses and string literals.
fn split_top_level<'t>(text: &'t str, separator: &str) -> Vec<&'t str> {
    let mut parts = vec![];
    let (mut depth, mut quoted, mut start) = (0i32, false, 0);
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'\'' => quoted = !quoted,
            b'(' if !quoted => depth += 1,
            b')' if !quoted => depth -= 1,
            _ if !quoted && depth == 0 && text[i..].starts_with(separator) => {
                parts.push(&text[start..i]);
                i += separator.len();
                start = i;
                continue;
            }
            _ => {}
        }
        i += 1;
    }
    parts.push(&text[start..]);
    parts
}

/// Snowflake's printed SQL in a form DataFusion parses: IN lists, which it
/// prints `x IN 'a' IN 'b'`, and its own functions. String literals are left
/// alone.
fn rewrite(text: &str) -> String {
    let mut s = in_lists(text);
    for (from, to) in [("STARTSWITH(", "starts_with("), ("ENDSWITH(", "ends_with("), ("CONTAINS(", "contains("), ("NVL(", "coalesce("), ("IFNULL(", "coalesce(")] {
        s = outside_literals(&s, |part| replace_word(part, from, to));
    }
    s = calls(&s, "TO_TIMESTAMP_NTZ", &|args| match args {
        [x] => Some(format!("CAST({x} AS TIMESTAMP)")),
        _ => None,
    });
    for name in ["CASE_FLATTENED", "IFF"] {
        s = calls(&s, name, &|args| match args {
            [c, a, b] => Some(format!("(CASE WHEN {c} THEN {a} ELSE {b} END)")),
            _ => None,
        });
    }
    // A timestamp literal in UTC (`'1998-09-02 00:00:00.000000000Z'`), of a
    // time-zone-free timestamp.
    let parts: Vec<&str> = s.split('\'').collect();
    parts
        .iter()
        .enumerate()
        .map(|(i, p)| match i % 2 == 1 && p.len() > 10 && p.as_bytes()[4] == b'-' && p.ends_with('Z') {
            true => &p[..p.len() - 1],
            false => p,
        })
        .collect::<Vec<_>>()
        .join("'")
}

/// `f` applied to the parts of `s` outside string literals.
fn outside_literals(s: &str, f: impl Fn(&str) -> String) -> String {
    s.split('\'').enumerate().map(|(i, p)| if i % 2 == 0 { f(p) } else { p.to_string() }).collect::<Vec<_>>().join("'")
}

/// Each call of the function `name` in `s` as `f` writes it from its
/// (rewritten) arguments, where it does.
fn calls(s: &str, name: &str, f: &dyn Fn(&[String]) -> Option<String>) -> String {
    let mut out = String::new();
    let mut rest = s;
    let call = format!("{name}(");
    loop {
        let Some(at) = find_word(rest, &call) else {
            out.push_str(rest);
            return out;
        };
        let open = at + name.len();
        let Some(close) = closing(rest, open) else {
            out.push_str(rest);
            return out;
        };
        let args: Vec<String> = split_top_level(&rest[open + 1..close], ",").iter().map(|a| calls(a.trim(), name, f)).collect();
        out.push_str(&rest[..at]);
        match f(&args) {
            Some(written) => out.push_str(&written),
            None => out.push_str(&rest[at..=close]),
        }
        rest = &rest[close + 1..];
    }
}

/// The first `word` in `s` outside string literals, not preceded by a word
/// character.
fn find_word(s: &str, word: &str) -> Option<usize> {
    let mut quoted = false;
    for (i, c) in s.char_indices() {
        if c == '\'' {
            quoted = !quoted;
        }
        if !quoted && s[i..].starts_with(word) && !s[..i].chars().next_back().is_some_and(|c| c.is_alphanumeric() || c == '_') {
            return Some(i);
        }
    }
    None
}

/// `x IN a IN b` as `x IN (a, b)`, in every parenthesized part of `text`.
fn in_lists(text: &str) -> String {
    // The parenthesized parts first, innermost first.
    let mut inner = String::new();
    let mut rest = text;
    while let Some(open) = find_open(rest) {
        let Some(close) = closing(rest, open) else { break };
        inner.push_str(&rest[..=open]);
        inner.push_str(&in_lists(&rest[open + 1..close]));
        inner.push(')');
        rest = &rest[close + 1..];
    }
    inner.push_str(rest);
    let parts = split_top_level(&inner, " IN ");
    let joined = |p: &str| split_top_level(p, " AND ").len() > 1 || split_top_level(p, " OR ").len() > 1;
    match &parts[..] {
        [x, items @ ..] if !items.is_empty() && !parts.iter().any(|p| joined(p)) && !items[0].trim_start().starts_with('(') => {
            format!("{x} IN ({})", items.iter().map(|i| i.trim()).collect::<Vec<_>>().join(", "))
        }
        _ => inner,
    }
}

/// The first `(` outside string literals.
fn find_open(s: &str) -> Option<usize> {
    let mut quoted = false;
    for (i, c) in s.char_indices() {
        match c {
            '\'' => quoted = !quoted,
            '(' if !quoted => return Some(i),
            _ => {}
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rewrites() {
        assert_eq!(rewrite("N1.N_NAME IN 'FRANCE' IN 'GERMANY'"), "N1.N_NAME IN ('FRANCE', 'GERMANY')");
        assert_eq!(
            rewrite("(P.P_SIZE IN 49 IN 14) AND (NOT(STARTSWITH(P.P_TYPE, 'MEDIUM')))"),
            "(P.P_SIZE IN (49, 14)) AND (NOT(starts_with(P.P_TYPE, 'MEDIUM')))"
        );
        assert_eq!(rewrite("(SUBSTRING(C, 1, 2)) IN '13' IN '31'"), "(SUBSTRING(C, 1, 2)) IN ('13', '31')");
        assert_eq!(
            rewrite("(TO_TIMESTAMP_NTZ(L.D)) <= '1998-09-02 00:00:00.000000000Z'"),
            "(CAST(L.D AS TIMESTAMP)) <= '1998-09-02 00:00:00.000000000'"
        );
        assert_eq!(rewrite("SUM(CASE_FLATTENED(A = 'x', B, 0))"), "SUM((CASE WHEN A = 'x' THEN B ELSE 0 END))");
        assert_eq!(rewrite("X = 'a IN b IN c'"), "X = 'a IN b IN c'");
    }

    #[test]
    fn splits_conjuncts() {
        assert_eq!(conjuncts("(A = 1) AND ((B = 2) OR (C = 3)) AND (D IN 'x' IN 'y')"), ["A = 1", "(B = 2) OR (C = 3)", "D IN 'x' IN 'y'"]);
        assert_eq!(conjuncts("(A = 1) OR (B = 2)"), ["(A = 1) OR (B = 2)"]);
    }
}
