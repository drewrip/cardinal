//! PostgreSQL's `EXPLAIN (ANALYZE, VERBOSE, FORMAT JSON)` profile, or its
//! plain `EXPLAIN (VERBOSE, FORMAT JSON)` plan, as an [`ObservedPlan`].
//!
//! `VERBOSE` is required: with it every operator lists its output, and every
//! column is printed with the alias of the relation it is read from, which
//! PostgreSQL keeps unique in a plan. So a column reads the same wherever it
//! is printed, and an operator's expressions are read on their own, with what
//! its inputs computed (`(sum(x))`, in parentheses) matched to their outputs.
//!
//! PostgreSQL's operators do more than one thing each, and run more than
//! once. A scan, a join or an aggregate applies its own filter, and reports
//! the rows left: each becomes the operator and a filter, the rows between
//! them being those left plus those the filter removed. A condition that
//! reads the outer side of a nested loop (an index lookup of the join key)
//! is the join's, not the scan's it is printed on.
//!
//! An operator that ran several times reports an average. Where each run
//! output the same rows (the inner side of a nested loop that binds nothing
//! in it), that is their count. Where the processes of a parallel plan
//! split its rows, version 18 prints the average to two decimals, which
//! times the runs is their sum, for fewer than 100 runs. Any other average
//! is no count, and neither are the rows of an operator a join or a limit
//! stopped reading early. One that outputs its input's rows (a sort, a
//! `Hash`, which reports only the rows it stored) has as many as were
//! counted there.
//!
//! What a plan does not print is not guessed. A scan of a partial index
//! keeps rows by a predicate the plan leaves out, so the catalog gives the
//! partial indexes' predicates ([`Catalog::with_partial_indexes`]), which a
//! scan of one applies too: until it does, a scan of any index has a
//! predicate that does not resolve. An `EXISTS` subquery reports the one
//! row it needed: no count.

use std::collections::{BTreeSet, HashMap};
use std::ops::ControlFlow;

use datafusion::arrow::datatypes::{DataType, Field};
use datafusion::common::tree_node::{Transformed, TreeNode};
use datafusion::common::{DFSchema, DataFusionError, JoinType};
use datafusion::logical_expr::{BinaryExpr, Expr, Operator};
use datafusion::sql::sqlparser::ast::{self, VisitMut, VisitorMut};
use datafusion::sql::sqlparser::dialect::PostgreSqlDialect;
use datafusion::sql::sqlparser::parser::Parser;
use serde_json::Value;

use super::sql::QueryText;
use super::{Catalog, Lineage, ONode, ObservedPlan, Op, OutCol, Pred, base_table, qualified, requalify, simplify, type_of};
use crate::{Error, Result};

/// Reads a PostgreSQL profile, as printed by `EXPLAIN (ANALYZE, VERBOSE,
/// FORMAT JSON)`, against the tables in `catalog`. `name` names the query in
/// provenance. `sql`, the query, names the columns of its CTEs and derived
/// tables, which the profile reads by name and prints by position, and gives
/// its `LIMIT` counts, which the profile does not print; without it, what
/// needs them is left unresolved.
///
/// Under a `Gather`, rows are averages over the processes that ran the
/// operator: counts, as far as version 18's two decimals tell them, but for
/// the rows a filter removed. Run the query with
/// `max_parallel_workers_per_gather = 0` for a profile that counts those.
pub fn from_postgres(catalog: &Catalog, name: &str, json: &str, sql: Option<&str>) -> Result<ObservedPlan> {
    read(catalog, name, json, sql, true)
}

/// Reads the plan PostgreSQL chose for a query, as printed by `EXPLAIN
/// (VERBOSE, FORMAT JSON)`, or by `EXPLAIN (ANALYZE, VERBOSE, FORMAT JSON)`
/// with its counts ignored. The plan is not counted: it gives no facts.
pub fn from_postgres_explain(catalog: &Catalog, name: &str, json: &str, sql: Option<&str>) -> Result<ObservedPlan> {
    read(catalog, name, json, sql, false)
}

fn read(catalog: &Catalog, name: &str, json: &str, sql: Option<&str>, counted: bool) -> Result<ObservedPlan> {
    let v: Value = serde_json::from_str(json).map_err(|e| Error::Observed(e.to_string()))?;
    // A list of one statement's plan.
    let top = match &v {
        Value::Array(a) => a.first(),
        v => Some(v),
    };
    let plan = top.and_then(|t| t.get("Plan")).ok_or_else(|| Error::Observed("no Plan: not EXPLAIN (FORMAT JSON) output".into()))?;
    // Some operators (an append) list no output even so: one that does
    // says the plan is verbose.
    fn verbose(v: &Value) -> bool {
        v.get("Output").is_some() || plans(v).iter().any(verbose)
    }
    if !verbose(plan) {
        return Err(Error::Observed("no operator lists its Output: the plan must be printed with EXPLAIN (VERBOSE)".into()));
    }
    if counted && plan.get("Actual Rows").is_none() {
        return Err(Error::Observed("no Actual Rows: the plan must be printed with EXPLAIN (ANALYZE)".into()));
    }
    let mut aliases = BTreeSet::new();
    scan_aliases(plan, &mut aliases);
    let text = sql.and_then(|q| QueryText::parse_in(catalog, q, &PostgreSqlDialect {}));
    let mut b = Builder {
        catalog,
        text,
        counted,
        gathered: false,
        single: (aliases.len() == 1).then(|| aliases.pop_first().unwrap()),
        nodes: vec![],
        keys: vec![],
        aliases: HashMap::new(),
        ctes: HashMap::new(),
        inits: HashMap::new(),
        params: HashMap::new(),
        subplans: HashMap::new(),
        windows: HashMap::new(),
        unnamed: HashMap::new(),
    };
    b.unnamed_windows(plan);
    let root = b.node(plan, true)?.id;
    b.limits();
    Ok(ObservedPlan { name: name.to_string(), nodes: b.nodes, root, counted })
}

/// Every relation alias in the plan under `v`.
fn scan_aliases(v: &Value, out: &mut BTreeSet<String>) {
    if let Some(a) = v.get("Alias").and_then(Value::as_str) {
        out.insert(a.to_string());
    }
    for c in plans(v) {
        scan_aliases(c, out);
    }
}

/// The indexes the scan `v` reads: its own, or those of the bitmap scans
/// under it.
fn index_names(v: &Value, out: &mut Vec<String>) {
    out.extend(text(v, "Index Name").map(str::to_string));
    for c in plans(v) {
        index_names(c, out);
    }
}

fn plans(v: &Value) -> &[Value] {
    v.get("Plans").and_then(Value::as_array).map_or(&[], |c| c)
}

fn text<'v>(v: &'v Value, key: &str) -> Option<&'v str> {
    v.get(key).and_then(Value::as_str)
}

fn texts(v: &Value, key: &str) -> Vec<String> {
    v.get(key).and_then(Value::as_array).map(|a| a.iter().filter_map(Value::as_str).map(str::to_string).collect()).unwrap_or_default()
}

/// A count PostgreSQL printed as a whole number (`10`, or `10.00` since 18).
/// Whether the processes of a parallel plan share operator `v`'s work: each
/// outputs a part of its rows, where one that they do not share is run in
/// full by each. They share a parallel-aware scan, and what reads one.
fn shared(v: &Value) -> bool {
    // A `Gather` collects what its processes output: it runs once.
    let gathers = text(v, "Node Type").is_some_and(|t| t.starts_with("Gather"));
    !gathers && (v.get("Parallel Aware").and_then(Value::as_bool).unwrap_or(false) || plans(v).iter().any(shared))
}

fn whole(v: &Value, key: &str) -> Option<u64> {
    let n = v.get(key)?;
    n.as_u64().or_else(|| n.as_f64().filter(|f| *f >= 0.0 && f.fract() == 0.0).map(|f| f as u64))
}

struct Builder<'a> {
    catalog: &'a Catalog,
    text: Option<QueryText>,
    /// Whether the plan was run. Without, no operator is counted.
    counted: bool,
    /// Whether the operators being built run once in each process of a
    /// parallel plan: under a `Gather` that ran once, and under nothing
    /// that runs its input again. Then what the processes share ran as
    /// often as there were processes, and its rows sum to all of them.
    gathered: bool,
    /// The plan's one relation alias, if it reads only one relation: then
    /// PostgreSQL prints output columns without it.
    single: Option<String>,
    nodes: Vec<ONode>,
    /// Each operator's columns as [`Builder::key`] writes them, to match
    /// what operators above print in parentheses.
    keys: Vec<Vec<String>>,
    /// What each relation alias names.
    aliases: HashMap<String, Alias>,
    /// A CTE's definition, by name.
    ctes: HashMap<String, usize>,
    /// The InitPlans (uncorrelated subqueries, run once), by name.
    inits: HashMap<String, Init>,
    /// The InitPlan output each parameter `$n` is, as versions before 17
    /// print a reference to one.
    params: HashMap<String, (String, usize)>,
    /// The SubPlans of the operators being built, by name.
    subplans: HashMap<String, &'a Value>,
    /// Each window's definition (`PARTITION BY ... ORDER BY ...`), by name:
    /// or, where a version before 18 prints no window (`OVER (?)`), by its
    /// function's call, as `?row_number()`.
    windows: HashMap<String, String>,
    /// How many window operators compute each such call.
    unnamed: HashMap<String, usize>,
}

enum Alias {
    /// A scan of a table of the catalog.
    Base { table: String, instance: String },
    /// A subquery or a CTE: its columns by name.
    Derived(HashMap<String, Lineage>),
    /// A relation whose columns cannot be read.
    Opaque,
}

struct Init {
    root: usize,
    /// Whether it outputs exactly one row: an aggregate without groups.
    one_row: bool,
    /// Whether an operator already reads it. A second reads a copy.
    used: bool,
}

/// A built operator, and what its subtree leaves open.
struct Sub {
    id: usize,
    /// The relation aliases scanned beneath.
    aliases: BTreeSet<String>,
    /// Conditions printed beneath that read relations not beneath: applied
    /// by the nested loop that binds them.
    hoisted: Vec<Hoisted>,
    /// The relations not beneath that something else beneath reads (an
    /// output, or a condition under an operator no join's condition passes
    /// through): what binds one runs the subtree once per row of it, and has
    /// no model here.
    free: BTreeSet<String>,
    /// Whether its rows are groups aggregated in part, one for each process
    /// that met the group: the aggregate above that finishes them reads the
    /// rows beneath, and until it does, a count is of no rows of the query.
    partial: bool,
}

impl Sub {
    /// Whether the subtree's rows are its own: nothing in it depends on a
    /// row from outside, and each is a row of the query.
    fn closed(&self) -> bool {
        self.hoisted.is_empty() && self.free.is_empty() && !self.partial
    }

    /// Notes that something beneath reads the relations `reads`.
    fn read(&mut self, reads: &BTreeSet<String>) {
        self.free.extend(reads.difference(&self.aliases).cloned());
    }
}

struct Hoisted {
    pred: Pred,
    reads: BTreeSet<String>,
}

/// An expression as read: `None` if it did not resolve.
struct Read {
    expr: Option<Expr>,
    /// The relation aliases it reads.
    reads: BTreeSet<String>,
    /// The InitPlans it reads.
    inits: BTreeSet<String>,
}

/// What an expression may compute itself, beyond values of single rows.
#[derive(Clone, Copy, PartialEq)]
enum Mode {
    Row,
    /// An aggregate's own outputs: its aggregates.
    Aggregate,
    /// A window operator's own outputs: its window functions.
    Window,
}

/// A reference PostgreSQL prints to something computed elsewhere.
enum Ref {
    /// `(InitPlan 1).col1`.
    Init(String, usize),
    /// `$0`.
    Param(String),
    /// `(SubPlan 1)`, whose value depends on the row.
    Sub,
}

impl<'a> Builder<'a> {
    fn node(&mut self, v: &'a Value, exact: bool) -> Result<Sub> {
        let ty = text(v, "Node Type").ok_or_else(|| Error::Observed("an operator has no Node Type".into()))?;
        // The processes of a parallel plan split the rows of a scan, and so
        // of what keeps or joins each row on its own. Anything else they
        // share (a limit, a `DISTINCT`) each computes of its own part: no
        // rows of the query, until what is above their `Gather` finishes it.
        let apart = [" Scan", " Join", "Sort", "Append"].iter().any(|t| ty.ends_with(t))
            || matches!(ty, "Nested Loop" | "Hash" | "Materialize" | "Memoize" | "Result" | "Aggregate" | "Group" | "Unique");
        if !apart && shared(v) {
            let mut sub = self.operator(v, ty, false)?;
            sub.partial = true;
            return Ok(sub);
        }
        self.operator(v, ty, exact)
    }

    fn operator(&mut self, v: &'a Value, ty: &'a str, exact: bool) -> Result<Sub> {
        // Its CTEs and InitPlans come first: what follows may read them.
        let mut inputs = vec![];
        for p in plans(v) {
            let name = text(p, "Subplan Name").unwrap_or_default();
            match text(p, "Parent Relationship") {
                Some("InitPlan") => self.init_plan(p, name)?,
                Some("SubPlan") => {
                    self.subplans.insert(name.strip_prefix("SubPlan ").unwrap_or(name).to_string(), p);
                }
                _ => inputs.push(p),
            }
        }
        if let Some((name, definition)) = text(v, "Window").and_then(|w| w.split_once(" AS ")) {
            // Its order is printed without directions: the sort that feeds
            // it prints them.
            let sorted = inputs.first().filter(|i| text(i, "Node Type").is_some_and(|t| t.ends_with("Sort")));
            let keys = sorted.map(|i| texts(i, "Sort Key")).unwrap_or_default();
            let definition = window_order(strip_parens(definition.trim()), &keys);
            self.windows.insert(name.trim().to_string(), definition);
        }
        match (ty, &inputs[..]) {
            ("Seq Scan" | "Index Scan" | "Index Only Scan" | "Bitmap Heap Scan" | "Tid Scan" | "Tid Range Scan", _) => self.scan(v, ty, exact),
            ("Subquery Scan", [input]) => self.subquery_scan(v, ty, input, exact),
            ("CTE Scan", []) => self.cte_scan(v, ty, exact),
            ("Hash Join" | "Merge Join" | "Nested Loop", [_, _]) => self.join(v, ty, &inputs, exact),
            ("Aggregate" | "Group" | "Unique", [input]) => self.aggregate(v, ty, input, exact),
            ("WindowAgg", [input]) => self.window(v, ty, input, exact),
            ("Limit", [input]) => {
                // Bounded, if the query says, by `Builder::limits`.
                let k = self.node(input, false)?;
                let columns = self.outputs(v, &[k.id], Mode::Row).0;
                let rows = self.count(v, exact && k.closed());
                let id = self.push(Op::Limit { at_most: None }, rows, vec![k.id], columns, ty);
                Ok(self.over(k, id, false))
            }
            // A sort reads all of its input first, as a hash table's build
            // does: a wrapper with no effect on rows.
            ("Sort", [input]) => self.pass(v, ty, Op::Sort, input, true, exact, true),
            ("Incremental Sort", [input]) => self.pass(v, ty, Op::Sort, input, exact, exact, false),
            // It reports the rows it put in its table: not those with a
            // NULL key, which match nothing. So its rows are no count of
            // its input's, which the join reads through it all the same.
            ("Hash", [input]) => self.pass(v, ty, Op::Project, input, true, false, true),
            ("Materialize", [input]) => self.pass(v, ty, Op::Project, input, exact, exact, false),
            // It runs its input again for each key it has not kept.
            ("Memoize", [input]) => {
                let outside = std::mem::replace(&mut self.gathered, false);
                let sub = self.pass(v, ty, Op::Project, input, exact, exact, false);
                self.gathered = outside;
                sub
            }
            // Its processes' rows sum to its input's, if it ran once: run
            // again, their sum over the runs counts each row as often.
            ("Gather" | "Gather Merge", [input]) => {
                let once = whole(v, "Actual Loops") == Some(1);
                let outside = std::mem::replace(&mut self.gathered, once);
                let sub = self.pass(v, ty, Op::Project, input, exact && once, exact, false);
                self.gathered = outside;
                sub
            }
            ("Result", [input]) => {
                let k = self.pass(v, ty, Op::Project, input, exact, exact, false)?;
                // A filter that reads no row: it keeps all of them, or none.
                let conds = text(v, "One-Time Filter").map(conjuncts).unwrap_or_default();
                let rows = self.count(v, exact && k.closed());
                self.filter(k, &conds, Mode::Row, rows, ty)
            }
            ("Append" | "Merge Append", [_, ..]) => {
                let mut kids = vec![];
                for input in &inputs {
                    kids.push(self.node(input, exact)?);
                }
                // An append lists no output: its inputs' columns, in order.
                let columns = self.nodes[kids[0].id].columns.iter().map(|c| unknown(c.name.clone())).collect();
                let closed = kids.iter().all(Sub::closed);
                let rows = self.count(v, exact && closed);
                let id = self.push(Op::Union, rows, kids.iter().map(|k| k.id).collect(), columns, ty);
                Ok(self.merge(kids, id, false))
            }
            _ => {
                let mut kids = vec![];
                for input in &inputs {
                    kids.push(self.node(input, false)?);
                }
                let ids: Vec<usize> = kids.iter().map(|k| k.id).collect();
                let columns = self.outputs(v, &ids, Mode::Row).0;
                let id = self.push(Op::Other, self.count(v, exact), ids, columns, ty);
                Ok(self.merge(kids, id, false))
            }
        }
    }

    /// Operator `v`, built where [`Builder::gathered`] is `gathered`.
    fn node_where(&mut self, v: &'a Value, exact: bool, gathered: bool) -> Result<Sub> {
        let outside = std::mem::replace(&mut self.gathered, gathered);
        let sub = self.node(v, exact);
        self.gathered = outside;
        sub
    }

    fn push(&mut self, op: Op, rows: Option<u64>, children: Vec<usize>, columns: Vec<OutCol>, engine_op: &str) -> usize {
        let id = self.nodes.len();
        self.keys.push(columns.iter().map(|c| self.key(&c.name)).collect());
        self.nodes.push(ONode {
            op,
            rows: rows.unwrap_or(0),
            counted: rows.is_some(),
            children,
            columns,
            ordered: true,
            blocking: false,
            engine_op: engine_op.to_string(),
            cut_short: false,
        });
        id
    }

    /// The rows operator `v` output, if it output them all: `exact` says
    /// whether what reads it read all of them, each time it ran, and that
    /// nothing it reads changes between runs. One that ran several times
    /// reports an average. Of the same rows each time (the inner side of a
    /// nested loop that binds nothing in it), the average is their count.
    /// Of rows split between processes, it is their sum over the runs, as
    /// far as two decimals tell it: for fewer than 100 runs.
    fn count(&self, v: &Value, exact: bool) -> Option<u64> {
        if !self.counted || !exact {
            return None;
        }
        let loops = whole(v, "Actual Loops")?;
        match loops {
            0 => None,
            1 => whole(v, "Actual Rows"),
            _ if !shared(v) => whole(v, "Actual Rows"),
            // Versions before 18 round the average to a whole number.
            _ => v.get("Actual Rows").filter(|n| n.is_f64() && loops < 100 && self.gathered).and_then(Value::as_f64).map(|avg| (avg * loops as f64).round() as u64),
        }
    }

    /// `rows` and those operator `v` removed with the filter whose removed
    /// rows it reports as `key`: an average rounded to a whole number, so no
    /// count of rows split between processes.
    fn before(&self, v: &Value, rows: Option<u64>, key: &str) -> Option<u64> {
        if whole(v, "Actual Loops") != Some(1) && shared(v) {
            return None;
        }
        rows?.checked_add(whole(v, key)?)
    }

    /// `kid`, seen through operator `id` above it. `free` if the operator
    /// cannot leave its conditions to a join above.
    fn over(&mut self, mut kid: Sub, id: usize, hoists: bool) -> Sub {
        kid.id = id;
        if !hoists {
            for h in std::mem::take(&mut kid.hoisted) {
                kid.read(&h.reads);
            }
        }
        kid
    }

    fn merge(&mut self, kids: Vec<Sub>, id: usize, hoists: bool) -> Sub {
        let mut out = Sub { id, aliases: BTreeSet::new(), hoisted: vec![], free: BTreeSet::new(), partial: false };
        for k in kids {
            let k = self.over(k, id, hoists);
            out.aliases.extend(k.aliases);
            out.hoisted.extend(k.hoisted);
            out.free.extend(k.free);
            out.partial |= k.partial;
        }
        // What one input reads of another is bound here.
        out.free.retain(|a| !out.aliases.contains(a));
        out
    }

    /// An operator that outputs its input's rows. `blocking` if it reads
    /// them all first.
    #[allow(clippy::too_many_arguments)]
    fn pass(&mut self, v: &'a Value, ty: &str, op: Op, input: &'a Value, input_exact: bool, exact: bool, blocking: bool) -> Result<Sub> {
        let k = self.node(input, input_exact)?;
        let (columns, reads) = self.outputs(v, &[k.id], Mode::Row);
        // It outputs its input's rows, as many as were counted there where
        // its own were not: read short (a sort), or not all reported (a
        // hash table's).
        let input = &self.nodes[k.id];
        let rows = self.count(v, exact && k.closed()).or(input.counted.then_some(input.rows));
        let id = self.push(op, rows, vec![k.id], columns, ty);
        self.nodes[id].blocking = blocking;
        let mut out = self.over(k, id, true);
        out.read(&reads);
        Ok(out)
    }

    /// A CTE's definition, or an InitPlan.
    fn init_plan(&mut self, p: &'a Value, name: &str) -> Result<()> {
        let (nodes, aliases) = (self.nodes.len(), self.aliases.keys().cloned().collect::<BTreeSet<_>>());
        // A CTE is read as its scans read it, and a scalar subquery to its
        // end. An `EXISTS` is read to its first row, and the plan does not
        // say which an InitPlan is: one whose top is an aggregate without
        // groups read all of its input either way.
        let whole = name.starts_with("CTE ")
            || (text(p, "Node Type") == Some("Aggregate") && text(p, "Strategy") == Some("Plain") && p.get("Group Key").is_none());
        let sub = self.node_where(p, whole, false)?;
        if !sub.closed() {
            self.forget(nodes, &aliases);
            return Ok(());
        }
        if let Some(cte) = name.strip_prefix("CTE ") {
            self.ctes.insert(cte.to_string(), sub.id);
            return Ok(());
        }
        // `InitPlan 1`, or before 17 `InitPlan 1 (returns $0,$1)`.
        let Some(rest) = name.strip_prefix("InitPlan ") else { return Ok(()) };
        let (init, returns) = match rest.split_once(" (returns ") {
            Some((n, r)) => (n.trim(), r.trim_end_matches(')')),
            None => (rest.trim(), ""),
        };
        for (i, param) in returns.split(',').map(str::trim).filter(|p| !p.is_empty()).enumerate() {
            self.params.insert(param.to_string(), (init.to_string(), i));
        }
        let mut top = sub.id;
        while let (Op::Project | Op::Sort, [c]) = (&self.nodes[top].op, &self.nodes[top].children[..]) {
            top = *c;
        }
        let one_row = matches!(&self.nodes[top].op, Op::Aggregate { keys, .. } if keys.is_empty());
        self.inits.insert(init.to_string(), Init { root: sub.id, one_row, used: false });
        Ok(())
    }

    /// Drops the operators built since there were `nodes`, and the aliases
    /// not among `aliases`: a subplan that reads the rows of what runs it.
    fn forget(&mut self, nodes: usize, aliases: &BTreeSet<String>) {
        self.nodes.truncate(nodes);
        self.keys.truncate(nodes);
        self.aliases.retain(|a, _| aliases.contains(a));
        self.ctes.retain(|_, d| *d < nodes);
        self.inits.retain(|_, i| i.root < nodes);
    }

    fn scan(&mut self, v: &'a Value, ty: &str, exact: bool) -> Result<Sub> {
        let alias = text(v, "Alias").unwrap_or_default().to_string();
        let name = text(v, "Relation Name").unwrap_or_default();
        let table = [name.to_string(), name.to_lowercase()].into_iter().find(|t| self.catalog.tables.contains_key(t));
        let Some(table) = table else {
            self.aliases.insert(alias.clone(), Alias::Opaque);
            let columns = texts(v, "Output").into_iter().map(unknown).collect();
            let id = self.push(Op::Other, self.count(v, exact), vec![], columns, ty);
            return Ok(Sub { id, aliases: [alias].into(), hoisted: vec![], free: BTreeSet::new(), partial: false });
        };
        let instance = format!("{table}#{}", self.nodes.len());
        // An alias scanned twice names no one scan.
        let known = match self.aliases.contains_key(&alias) {
            true => Alias::Opaque,
            false => Alias::Base { table: table.clone(), instance: instance.clone() },
        };
        self.aliases.insert(alias.clone(), known);
        let own: BTreeSet<String> = [alias].into();
        let (columns, reads) = self.outputs(v, &[], Mode::Row);
        let free: BTreeSet<String> = reads.difference(&own).cloned().collect();

        // What an index looked up, exactly: what a bitmap may have fetched
        // more of, the scan rechecked.
        let index: Vec<String> = ["Index Cond", "Recheck Cond", "TID Cond"].iter().filter_map(|k| text(v, k)).flat_map(conjuncts).collect();
        let filter = text(v, "Filter").map(conjuncts).unwrap_or_default();
        let depends = |b: &Builder, conds: &[String]| conds.iter().any(|c| !b.reads(c).is_subset(&own));
        let closed = free.is_empty() && !depends(self, &index) && !depends(self, &filter);
        let rows = self.count(v, exact && closed);
        let filtered = match filter.is_empty() {
            true => rows,
            false => self.before(v, rows, "Rows Removed by Filter"),
        };
        // A partial index holds the rows its predicate keeps, which the
        // plan does not print: the catalog's, read over this scan's
        // columns. Without one, a filter that does not resolve: as of the
        // rows of several indexes, which a bitmap may have joined either way.
        let mut indexes = vec![];
        index_names(v, &mut indexes);
        let unseen = |text: String| Pred { expr: None, text, optional: false };
        let (partial, known): (Vec<(String, String)>, bool) = match self.catalog.index_predicates(&indexes) {
            Some(p) => (p.into_iter().map(|(i, p)| (i.to_string(), p.to_string())).collect(), true),
            None => (vec![], false),
        };
        // Every row of the table, with no condition on what is read.
        let whole = index.is_empty() && known && partial.is_empty();
        let op = Op::Scan { table, instance, filters: vec![], runtime_filters: vec![] };
        let id = self.push(op, filtered.filter(|_| whole), vec![], columns, ty);
        let mut preds = vec![];
        if !known {
            preds.extend(indexes.first().map(|i| unseen(format!("the predicate of index {i}, if it is partial"))));
        } else if !partial.is_empty() && indexes.len() > 1 {
            preds.push(unseen(format!("the predicates of indexes {}", indexes.join(", "))));
        } else {
            // As the catalog prints it, a predicate names its table's
            // columns alone.
            let single = std::mem::replace(&mut self.single, own.first().cloned());
            for (i, text) in &partial {
                let expr = conjuncts(text).iter().map(|c| self.read(c, &[id], Mode::Row).expr).collect::<Option<Vec<Expr>>>();
                match expr {
                    Some(exprs) => preds.extend(exprs.into_iter().map(|e| Pred { text: e.to_string(), expr: Some(e), optional: false })),
                    None => preds.push(unseen(format!("the predicate of index {i}: {text}"))),
                }
            }
            self.single = single;
        }
        let mut sub = Sub { id, aliases: own, hoisted: vec![], free, partial: false };
        if !preds.is_empty() {
            let columns = self.nodes[sub.id].columns.clone();
            // With no condition of its own, the scan read the whole index.
            let kept = filtered.filter(|_| index.is_empty() && preds.iter().all(|p| p.expr.is_some()));
            sub.id = self.push(Op::Filter { predicate: preds }, kept, vec![sub.id], columns, ty);
        }
        let sub = self.filter(sub, &index, Mode::Row, filtered, ty)?;
        self.filter(sub, &filter, Mode::Row, rows, ty)
    }

    /// Keeps the rows of `input` satisfying `conds`, of which `rows` are
    /// left. A condition that reads a relation not beneath is left to the
    /// join that binds it. An InitPlan a condition reads is joined in first,
    /// as its one row. `x IN (SubPlan)` is a mark join against the subplan,
    /// and a filter on its mark.
    fn filter(&mut self, input: Sub, conds: &[String], mode: Mode, rows: Option<u64>, ty: &str) -> Result<Sub> {
        if conds.is_empty() {
            return Ok(input);
        }
        let mut sub = input;
        let mut preds = vec![];
        let mut marks = vec![];
        let mut inits = BTreeSet::new();
        let kids = [sub.id];
        for c in conds {
            if let Some(mark) = mark_condition(c).filter(|m| self.subplans.contains_key(&m.subplan)) {
                marks.push((mark, c));
                continue;
            }
            let r = self.read(c, &kids, mode);
            let pred = Pred { text: r.expr.as_ref().map_or_else(|| c.clone(), Expr::to_string), expr: r.expr, optional: false };
            if !r.reads.is_subset(&sub.aliases) {
                sub.hoisted.push(Hoisted { pred, reads: r.reads });
                continue;
            }
            inits.extend(r.inits);
            preds.push(pred);
        }
        let rows = rows.filter(|_| sub.closed());
        // Each InitPlan's row, beside every row of the input.
        for init in inits {
            let Some(i) = self.inits.get_mut(&init).filter(|i| i.one_row) else { continue };
            let (root, used) = (i.root, std::mem::replace(&mut i.used, true));
            let right = if used { self.reuse(root, None, "InitPlan") } else { root };
            let columns = self.nodes[sub.id].columns.iter().chain(&self.nodes[right].columns).cloned().collect();
            let n = &self.nodes[sub.id];
            let all = n.counted.then_some(n.rows);
            sub.id = self.push(Op::Join { kind: JoinType::Inner, on: vec![] }, all, vec![sub.id, right], columns, "InitPlan");
        }
        if !preds.is_empty() {
            let columns = self.nodes[sub.id].columns.clone();
            let left = rows.filter(|_| marks.is_empty());
            sub.id = self.push(Op::Filter { predicate: preds }, left, vec![sub.id], columns, ty);
        }
        let last = marks.len();
        for (i, (mark, cond)) in marks.into_iter().enumerate() {
            let left = rows.filter(|_| i + 1 == last);
            sub = self.mark(sub, &mark, cond, left, ty)?;
        }
        Ok(sub)
    }

    /// `input`'s rows whose `mark.keys` are (or with `negated`, are not) IN
    /// the subplan's: a mark join against it, and a filter on the mark.
    fn mark(&mut self, mut sub: Sub, mark: &Mark, cond: &str, rows: Option<u64>, ty: &str) -> Result<Sub> {
        let unresolved = |b: &mut Builder<'a>, mut sub: Sub| {
            let columns = b.nodes[sub.id].columns.clone();
            let pred = Pred { expr: None, text: cond.to_string(), optional: false };
            sub.id = b.push(Op::Filter { predicate: vec![pred] }, rows, vec![sub.id], columns, ty);
            Ok(sub)
        };
        let Some(plan) = self.subplans.remove(&mark.subplan) else { return unresolved(self, sub) };
        let (nodes, aliases) = (self.nodes.len(), self.aliases.keys().cloned().collect::<BTreeSet<_>>());
        // A hashed subplan is read whole, into its table. One that is not
        // is read, for each row, to its first match.
        let right = self.node_where(plan, mark.hashed, false)?;
        if !right.closed() {
            self.forget(nodes, &aliases);
            return unresolved(self, sub);
        }
        let on = mark
            .keys
            .iter()
            .map(|(left, col)| {
                let x = self.read(left, &[sub.id], Mode::Row).expr;
                let y = self.nodes[right.id].columns.get(*col).and_then(|c| expr_of(&c.lineage));
                let expr = x.zip(y).map(|(x, y)| {
                    self.simplify(Expr::BinaryExpr(BinaryExpr::new(Box::new(x), Operator::Eq, Box::new(y))))
                });
                Pred { text: expr.as_ref().map_or_else(|| cond.to_string(), Expr::to_string), expr, optional: false }
            })
            .collect();
        let left = &self.nodes[sub.id];
        let all = left.counted.then_some(left.rows);
        let kept = left.columns.clone();
        let columns = kept.iter().cloned().chain([unknown(MARK.into())]).collect();
        let join = self.push(Op::Join { kind: JoinType::LeftMark, on }, all, vec![sub.id, right.id], columns, "SubPlan");
        sub.id = self.push(Op::MarkFilter { negated: mark.negated }, rows, vec![join], kept, ty);
        sub.aliases.extend(right.aliases);
        Ok(sub)
    }

    /// A read of operator `of`'s output, as an independent copy of it.
    fn reuse(&mut self, of: usize, rows: Option<u64>, engine_op: &str) -> usize {
        let suffix = format!("~r{}", self.nodes.len());
        let columns = self.nodes[of]
            .columns
            .iter()
            .map(|c| OutCol { name: c.name.clone(), lineage: rename(&c.lineage, &suffix) })
            .collect();
        self.push(Op::Reuse { suffix, checked: rows.is_some() }, rows, vec![of], columns, engine_op)
    }

    /// Marks `id`'s rows as not counted, and those of what it reads as it
    /// outputs: a read cut short leaves them short too.
    fn uncount(&mut self, id: usize) {
        self.nodes[id].counted = false;
        if self.nodes[id].blocking || matches!(self.nodes[id].op, Op::Reuse { .. }) {
            return;
        }
        for c in self.nodes[id].children.clone() {
            self.uncount(c);
        }
    }

    fn cte_scan(&mut self, v: &'a Value, ty: &str, exact: bool) -> Result<Sub> {
        let alias = text(v, "Alias").unwrap_or_default().to_string();
        let name = text(v, "CTE Name").unwrap_or_default();
        let Some(&definition) = self.ctes.get(name) else {
            self.aliases.insert(alias.clone(), Alias::Opaque);
            let columns = texts(v, "Output").into_iter().map(unknown).collect();
            let id = self.push(Op::Other, self.count(v, exact), vec![], columns, ty);
            return Ok(Sub { id, aliases: [alias].into(), hoisted: vec![], free: BTreeSet::new(), partial: false });
        };
        let filter = text(v, "Filter").map(conjuncts).unwrap_or_default();
        let own: BTreeSet<String> = [alias.clone()].into();
        let closed = filter.iter().all(|c| self.reads(c).is_subset(&own));
        let rows = self.count(v, exact && closed);
        let all = match filter.is_empty() {
            true => rows,
            false => self.before(v, rows, "Rows Removed by Filter"),
        };
        // A CTE is computed as it is read: only as far as its readers went.
        if all.is_none() && self.counted {
            self.uncount(definition);
        }
        let id = self.reuse(definition, all, ty);
        let derived = self.derived(&[name, &alias], &self.nodes[id].columns);
        self.aliases.insert(alias, Alias::Derived(derived));
        let mut sub = self.filter(Sub { id, aliases: own, hoisted: vec![], free: BTreeSet::new(), partial: false }, &filter, Mode::Row, rows, ty)?;
        let (columns, reads) = self.outputs(v, &[sub.id], Mode::Row);
        sub.read(&reads);
        let left = self.nodes[sub.id].counted.then_some(self.nodes[sub.id].rows).filter(|_| sub.closed());
        sub.id = self.push(Op::Project, left, vec![sub.id], columns, ty);
        Ok(sub)
    }

    fn subquery_scan(&mut self, v: &'a Value, ty: &str, input: &'a Value, exact: bool) -> Result<Sub> {
        let alias = text(v, "Alias").unwrap_or_default().to_string();
        let k = self.node(input, exact)?;
        // PostgreSQL numbers an alias used before (`s_1`).
        let plain = alias.rsplit_once('_').filter(|(_, n)| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit())).map(|(a, _)| a);
        let names: Vec<&str> = [Some(alias.as_str()), plain].into_iter().flatten().collect();
        let derived = self.derived(&names, &self.nodes[k.id].columns);
        self.aliases.insert(alias.clone(), Alias::Derived(derived));
        let mut sub = self.over(k, 0, true);
        sub.id = self.nodes.len() - 1;
        sub.aliases.insert(alias);
        let filter = text(v, "Filter").map(conjuncts).unwrap_or_default();
        let rows = self.count(v, exact);
        let mut sub = self.filter(sub, &filter, Mode::Row, rows, ty)?;
        let (columns, reads) = self.outputs(v, &[sub.id], Mode::Row);
        sub.read(&reads);
        let left = rows.filter(|_| sub.closed());
        sub.id = self.push(Op::Project, left, vec![sub.id], columns, ty);
        Ok(sub)
    }

    /// The columns of a subquery or CTE called one of `names`, which
    /// outputs `columns`: named by the query, by position (what it sorts by
    /// and does not select comes after); or else as PostgreSQL names a
    /// column that the query did not, after the column it is.
    fn derived(&self, names: &[&str], columns: &[OutCol]) -> HashMap<String, Lineage> {
        let listed = names
            .iter()
            .filter_map(|n| self.text.as_ref()?.relation_columns(n))
            .find(|listed| !listed.is_empty() && listed.len() <= columns.len());
        if let Some(listed) = listed {
            return listed.iter().cloned().zip(columns.iter().map(|c| c.lineage.clone())).collect();
        }
        let mut out = HashMap::new();
        let mut seen = HashMap::<String, usize>::new();
        let named: Vec<(String, &OutCol)> = columns
            .iter()
            .filter_map(|c| {
                let key = self.key(&c.name);
                let name = key.rsplit('.').next()?.trim_matches('"').to_string();
                let identifier = !name.is_empty() && name.chars().all(|ch| ch.is_alphanumeric() || ch == '_');
                (identifier && key.matches('.').count() <= 1).then_some((name, c))
            })
            .collect();
        for (name, _) in &named {
            *seen.entry(name.clone()).or_default() += 1;
        }
        for (name, c) in named {
            if seen[&name] == 1 {
                out.insert(name, c.lineage.clone());
            }
        }
        out
    }

    fn join(&mut self, v: &'a Value, ty: &str, inputs: &[&'a Value], exact: bool) -> Result<Sub> {
        let side = |rel: &str| inputs.iter().copied().find(|p| text(p, "Parent Relationship") == Some(rel));
        let (Some(outer), Some(inner)) = (side("Outer"), side("Inner")) else {
            return Err(Error::Observed(format!("{ty} has no outer and inner input")));
        };
        let kind = text(v, "Join Type").and_then(join_type);
        let unique = v.get("Inner Unique").and_then(Value::as_bool).unwrap_or(false);
        // Whether each side is read to its end. A merge join stops at the
        // end of either side; a nested loop rereads its inner side, and
        // stops reading it at the first match where one is enough.
        // A hash join whose table is empty reads no more than a first row of
        // its outer side, unless it outputs that side's unmatched rows.
        let empty = whole(inner, "Actual Rows") == Some(0) && whole(inner, "Actual Loops") == Some(1);
        let fills_outer = matches!(kind, Some(JoinType::Left | JoinType::Full | JoinType::LeftAnti));
        let (exact_outer, exact_inner) = match ty {
            "Hash Join" => (exact && (fills_outer || !empty), true),
            "Merge Join" => (false, false),
            _ => (exact, exact && matches!(kind, Some(JoinType::Inner | JoinType::Left)) && !unique && !shared(inner)),
        };
        let l = self.node(outer, exact_outer)?;
        // A nested loop runs its inner side for each outer row.
        let r = self.node_where(inner, exact_inner, self.gathered && ty != "Nested Loop")?;
        let kids = [l.id, r.id];
        let (columns, reads) = self.outputs(v, &kids, Mode::Row);
        let Some(kind) = kind else {
            let id = self.push(Op::Other, self.count(v, exact), kids.to_vec(), columns, ty);
            return Ok(self.merge(vec![l, r], id, false));
        };
        let aliases: BTreeSet<String> = l.aliases.union(&r.aliases).cloned().collect();
        let (l_aliases, r_aliases) = (l.aliases.clone(), r.aliases.clone());
        // What a side reads of the other, other than in a condition this
        // join can apply, runs that side once per row: no join of the two.
        let dependent = l.free.iter().chain(&r.free).any(|a| aliases.contains(a));
        let partial = l.partial || r.partial;
        let mut sub = Sub { id: 0, aliases: aliases.clone(), hoisted: vec![], free: l.free.union(&r.free).cloned().collect(), partial };
        sub.read(&reads);
        sub.free.retain(|a| !aliases.contains(a));
        if dependent {
            for h in l.hoisted.iter().chain(&r.hoisted) {
                sub.read(&h.reads);
            }
            sub.id = self.push(Op::Other, self.count(v, exact), kids.to_vec(), columns, ty);
            return Ok(sub);
        }
        let mut on = vec![];
        // A condition that reads only this join's sides is its own, as one
        // printed on its inner side is: that side's lookup of this join's
        // outer rows. Another goes on up, where the join keeps the rows of
        // a filter above it: an inner join, or the side an outer, semi or
        // anti join keeps every row of.
        let keeps_left = matches!(kind, JoinType::Inner | JoinType::Left | JoinType::LeftSemi | JoinType::LeftAnti);
        let keeps_right = matches!(kind, JoinType::Inner | JoinType::Right | JoinType::RightSemi | JoinType::RightAnti);
        let mut place = |sub: &mut Sub, pred: Pred, reads: BTreeSet<String>, own: bool, passes: bool| {
            if reads.is_subset(&aliases) && own {
                on.push(pred);
            } else if passes && !reads.is_subset(&aliases) {
                sub.hoisted.push(Hoisted { pred, reads });
            } else {
                sub.read(&reads);
                // Bound here, yet not this join's: it has no model.
                on.push(Pred { expr: None, text: pred.text, optional: false });
            }
        };
        for c in ["Hash Cond", "Merge Cond", "Join Filter"].iter().filter_map(|k| text(v, k)).flat_map(conjuncts) {
            let r = self.read(&c, &kids, Mode::Row);
            let pred = Pred { text: r.expr.as_ref().map_or(c, Expr::to_string), expr: r.expr, optional: false };
            place(&mut sub, pred, r.reads, true, kind == JoinType::Inner);
        }
        for h in l.hoisted {
            place(&mut sub, h.pred, h.reads, false, keeps_left);
        }
        for h in r.hoisted {
            place(&mut sub, h.pred, h.reads, true, keeps_right);
        }
        let closed = sub.closed();
        let rows = self.count(v, exact && closed);
        let filter = text(v, "Filter").map(conjuncts).unwrap_or_default();
        let joined = match filter.is_empty() {
            true => rows,
            false => self.before(v, rows, "Rows Removed by Filter"),
        };
        let id = self.push(Op::Join { kind, on }, joined, kids.to_vec(), columns, ty);
        // A semi or anti join outputs one side's rows. PostgreSQL still
        // prints the other's columns above an anti join it made of an outer
        // join (`LEFT JOIN ... WHERE b.key IS NULL`), where all are NULL:
        // above, they are no scan's columns.
        let dropped = match kind {
            JoinType::LeftSemi | JoinType::LeftAnti => Some(&r_aliases),
            JoinType::RightSemi | JoinType::RightAnti => Some(&l_aliases),
            _ => None,
        };
        for a in dropped.into_iter().flatten() {
            self.aliases.insert(a.clone(), Alias::Opaque);
        }
        sub.id = id;
        self.filter(sub, &filter, Mode::Row, rows, ty)
    }

    /// A GROUP BY, a DISTINCT, or an aggregate without groups: the
    /// aggregate, a projection computing what it outputs from its keys and
    /// aggregates, and its `HAVING` filter.
    fn aggregate(&mut self, v: &'a Value, ty: &str, input: &'a Value, exact: bool) -> Result<Sub> {
        let strategy = text(v, "Strategy").unwrap_or("Sorted");
        let partial = text(v, "Partial Mode").unwrap_or("Simple");
        // A hash or plain aggregate reads all of its input first.
        let blocking = ty == "Aggregate" && matches!(strategy, "Hashed" | "Plain" | "Mixed");
        // Each process's share of the groups: the aggregate above finishes
        // them, and reads the columns below.
        // As is a `DISTINCT` each process of a parallel plan computes of its
        // own part of the rows, which is not marked so.
        if partial == "Partial" || shared(v) {
            let mut sub = self.pass(v, ty, Op::Project, input, blocking || exact, false, blocking)?;
            self.nodes[sub.id].counted = false;
            sub.partial = true;
            return Ok(sub);
        }
        let mut k = self.node(input, blocking || exact)?;
        k.partial = false;
        // Which columns a `DISTINCT ON` compares is not printed.
        let distinct = ty != "Unique" || self.text.as_ref().is_some_and(|t| !t.distinct_on());
        if v.get("Grouping Sets").is_some() || strategy == "Mixed" || !distinct {
            let columns = texts(v, "Output").into_iter().map(unknown).collect();
            let id = self.push(Op::Other, self.count(v, exact), vec![k.id], columns, ty);
            return Ok(self.over(k, id, false));
        }
        let id = self.nodes.len();
        let me = format!("@{id}");
        // A key is printed as the input prints the column it is.
        let key_texts = match ty {
            "Unique" => self.nodes[k.id].columns.iter().map(|c| c.name.clone()).collect(),
            _ => texts(v, "Group Key"),
        };
        let mut columns: Vec<OutCol> = key_texts
            .into_iter()
            .map(|g| match self.find(&g, &[k.id]) {
                Some(c) => c,
                None => {
                    let lineage = self.read(&g, &[k.id], Mode::Row).expr.map_or(Lineage::Unknown, Lineage::Exact);
                    OutCol { name: g, lineage }
                }
            })
            .collect();
        let keys: Vec<Option<Expr>> = columns.iter().map(|c| expr_of(&c.lineage)).collect();

        // Each aggregate is a column of this operator, by its text.
        let mut values: Vec<(String, Expr)> = vec![];
        let mut value = |e: Expr| {
            e.transform_down(|x| match x {
                Expr::AggregateFunction(_) => {
                    let name = x.to_string();
                    if !values.iter().any(|(n, _)| *n == name) {
                        values.push((name.clone(), x));
                    }
                    Ok(Transformed::new(qualified(&me, &name), true, datafusion::common::tree_node::TreeNodeRecursion::Jump))
                }
                x => Ok(Transformed::no(x)),
            })
            .map(|t| t.data)
            .ok()
        };
        let kids = [k.id];
        let mut reads = BTreeSet::new();
        let outputs: Vec<OutCol> = texts(v, "Output")
            .into_iter()
            .map(|item| {
                let r = self.read(&item, &kids, Mode::Aggregate);
                reads.extend(r.reads);
                OutCol { name: item, lineage: r.expr.and_then(&mut value).map_or(Lineage::Unknown, Lineage::Exact) }
            })
            .collect();
        let having = text(v, "Filter").map(conjuncts).unwrap_or_default();
        let mut inits = BTreeSet::new();
        let preds: Vec<Pred> = having
            .iter()
            .map(|c| {
                let r = self.read(c, &kids, Mode::Aggregate);
                reads.extend(r.reads);
                inits.extend(r.inits);
                let expr = r.expr.and_then(&mut value);
                Pred { text: expr.as_ref().map_or_else(|| c.clone(), Expr::to_string), expr, optional: false }
            })
            .collect();
        columns.extend(values.iter().map(|(name, _)| OutCol { name: name.clone(), lineage: Lineage::Exact(qualified(&me, name)) }));
        let values = values.into_iter().map(|(_, e)| Some(e)).collect();

        let closed = k.closed() && reads.is_subset(&k.aliases);
        let rows = self.count(v, exact && closed);
        let groups = match having.is_empty() {
            true => rows,
            false => self.before(v, rows, "Rows Removed by Filter"),
        };
        let aggregate = self.push(Op::Aggregate { keys, values }, groups, vec![k.id], columns, ty);
        debug_assert_eq!(aggregate, id);
        self.nodes[aggregate].blocking = blocking;
        let project = self.push(Op::Project, groups, vec![aggregate], outputs, ty);
        let mut sub = self.over(k, project, false);
        sub.read(&reads);
        if preds.is_empty() {
            return Ok(sub);
        }
        // Its InitPlans' rows, then the filter, which reads what the
        // projection outputs.
        for init in inits {
            let Some(i) = self.inits.get_mut(&init).filter(|i| i.one_row) else { continue };
            let (root, used) = (i.root, std::mem::replace(&mut i.used, true));
            let right = if used { self.reuse(root, None, "InitPlan") } else { root };
            let columns = self.nodes[sub.id].columns.iter().chain(&self.nodes[right].columns).cloned().collect();
            sub.id = self.push(Op::Join { kind: JoinType::Inner, on: vec![] }, groups, vec![sub.id, right], columns, "InitPlan");
        }
        let columns = self.nodes[project].columns.clone();
        sub.id = self.push(Op::Filter { predicate: preds }, rows, vec![sub.id], columns, ty);
        Ok(sub)
    }

    /// Counts the window operators under `v` that compute each window
    /// function printed without its window.
    fn unnamed_windows(&mut self, v: &Value) {
        for call in unnamed_calls(v) {
            if let Some(key) = call_key(&call) {
                *self.unnamed.entry(key).or_default() += 1;
            }
        }
        for c in plans(v) {
            self.unnamed_windows(c);
        }
    }

    /// The definition of the window that `call` (`row_number()`), a window
    /// function printed without it, runs over: the query's, if it and the
    /// plan each have one window function so called, with each column as
    /// operator `kid`, the window's input, prints it.
    fn query_window(&self, call: &str, kid: usize) -> Option<(String, String)> {
        let key = call_key(call)?;
        if self.unnamed.get(&key) != Some(&1) {
            return None;
        }
        let parsed = Parser::new(&PostgreSqlDialect {}).try_with_sql(call).and_then(|mut p| p.parse_expr()).ok()?;
        let mut spec = self.text.as_ref()?.window_of(&parsed)?;
        let mut resolved = true;
        let mut column = |e: &mut ast::Expr| {
            let name = match e {
                ast::Expr::Identifier(i) => i.value.to_lowercase(),
                ast::Expr::CompoundIdentifier(parts) => parts.last().unwrap().value.to_lowercase(),
                _ => return ControlFlow::<()>::Continue(()),
            };
            // The input's one column of that name, as it prints it.
            let mut named = self.nodes[kid].columns.iter().filter_map(|c| {
                let printed = Parser::new(&PostgreSqlDialect {}).try_with_sql(&c.name).and_then(|mut p| p.parse_expr()).ok()?;
                let last = match &printed {
                    ast::Expr::Identifier(i) => i.value.to_lowercase(),
                    ast::Expr::CompoundIdentifier(parts) => parts.last().unwrap().value.to_lowercase(),
                    _ => return None,
                };
                (last == name).then_some(printed)
            });
            match (named.next(), named.next()) {
                (Some(printed), None) => *e = printed,
                _ => resolved = false,
            }
            ControlFlow::Continue(())
        };
        for e in spec.partition_by.iter_mut().chain(spec.order_by.iter_mut().map(|o| &mut o.expr)) {
            let _ = ast::visit_expressions_mut(e, &mut column);
        }
        resolved.then(|| (format!("?{key}"), spec.to_string()))
    }

    /// A window operator: its input's columns, and its window functions'
    /// values. A run condition stops it once a function passes a bound: a
    /// filter on the function.
    fn window(&mut self, v: &'a Value, ty: &str, input: &'a Value, exact: bool) -> Result<Sub> {
        let run = text(v, "Run Condition").map(conjuncts).unwrap_or_default();
        let filter = text(v, "Filter").map(conjuncts).unwrap_or_default();
        let k = self.node(input, exact && run.is_empty())?;
        for call in unnamed_calls(v) {
            if let Some((name, definition)) = self.query_window(&call, k.id) {
                self.windows.insert(name, definition);
            }
        }
        let (columns, reads) = self.outputs(v, &[k.id], Mode::Window);
        let closed = k.closed() && reads.is_subset(&k.aliases);
        let rows = self.count(v, exact && closed);
        let all = if run.is_empty() && filter.is_empty() { rows } else { None };
        let id = self.push(Op::Window, all, vec![k.id], columns, ty);
        let mut sub = self.over(k, id, false);
        sub.read(&reads);
        let conds: Vec<String> = run.into_iter().chain(filter).collect();
        self.filter(sub, &conds, Mode::Window, rows, ty)
    }

    /// Bounds each limit by the query's `LIMIT` clauses, which PostgreSQL
    /// does not print. With as many limits as clauses, all with a constant
    /// count, each limit is one of the clauses, so outputs at most the
    /// largest count: its offset, if any, only drops rows. The one limit of
    /// a query with one clause is that clause: over a sort, the first rows
    /// in its order, after those the clause skips.
    fn limits(&mut self) {
        let Some(text) = &self.text else { return };
        let Some(counts) = text.limits().iter().copied().collect::<Option<Vec<u64>>>() else { return };
        let limit = |n: &ONode| matches!(n.op, Op::Limit { .. });
        let limits: Vec<usize> = (0..self.nodes.len()).filter(|&i| limit(&self.nodes[i])).collect();
        if limits.len() != counts.len() {
            return;
        }
        if let ([i], [fetch], [Some(offset)]) = (&limits[..], &counts[..], text.offsets())
            && let [sort] = self.nodes[*i].children[..]
            && matches!(self.nodes[sort].op, Op::Sort)
        {
            self.nodes[*i].op = Op::TopN { fetch: *fetch, offset: *offset };
            return;
        }
        let at_most = counts.into_iter().max();
        for i in limits {
            self.nodes[i].op = Op::Limit { at_most };
        }
    }

    /// The columns operator `v` outputs, read over `kids`' columns, and the
    /// relation aliases they read.
    fn outputs(&self, v: &Value, kids: &[usize], mode: Mode) -> (Vec<OutCol>, BTreeSet<String>) {
        let mut reads = BTreeSet::new();
        let columns = texts(v, "Output")
            .into_iter()
            .map(|item| {
                if let Some(c) = self.find(&item, kids).filter(|_| item.trim_start().starts_with('(')) {
                    return OutCol { name: item, lineage: c.lineage };
                }
                let r = self.read(&item, kids, mode);
                reads.extend(r.reads);
                OutCol { name: item, lineage: r.expr.map_or(Lineage::Unknown, Lineage::Exact) }
            })
            .collect();
        (columns, reads)
    }

    /// The column of `kids` printed as `item`.
    fn find(&self, item: &str, kids: &[usize]) -> Option<OutCol> {
        let key = self.key(item);
        kids.iter().find_map(|&k| {
            let i = self.keys[k].iter().position(|c| *c == key)?;
            Some(self.nodes[k].columns[i].clone())
        })
    }

    /// An output column's text in one form, to compare: without the
    /// parentheses around it, and without relation aliases where the plan
    /// reads one relation (PostgreSQL then prints them in some places only).
    fn key(&self, item: &str) -> String {
        let item = self.windowed(strip_all_parens(item.trim()));
        match Parser::new(&PostgreSqlDialect {}).try_with_sql(&item).and_then(|mut p| p.parse_expr()) {
            Ok(e) => self.key_of(&e),
            Err(_) => item,
        }
    }

    /// `text` with each window's name (`OVER w1`, or `OVER (?)`) as its
    /// definition, where known. String literals are left alone.
    fn windowed(&self, text: &str) -> String {
        let mut out = String::new();
        for (i, part) in text.split('\'').enumerate() {
            if i > 0 {
                out.push('\'');
            }
            let mut rest = part;
            while let Some(at) = rest.find("OVER ").filter(|_| i % 2 == 0) {
                out.push_str(&rest[..at]);
                rest = &rest[at..];
                match self.window_at(rest, &out) {
                    Some((definition, len)) => {
                        out.push_str(&format!("OVER ({definition})"));
                        rest = &rest[len..];
                    }
                    None => {
                        out.push_str("OVER ");
                        rest = &rest["OVER ".len()..];
                    }
                }
            }
            out.push_str(rest);
        }
        out
    }

    /// `OVER w1` or `OVER (?)` at the start of `text`, after `before`: the
    /// window's definition, and the length of the reference.
    fn window_at(&self, text: &str, before: &str) -> Option<(&str, usize)> {
        let rest = text.strip_prefix("OVER ")?;
        if rest.starts_with("(?)") {
            let key = call_key(trailing_call(before)?)?;
            return Some((self.windows.get(&format!("?{key}"))?.as_str(), "OVER (?)".len()));
        }
        let name: String = rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
        let definition = self.windows.get(&name)?.as_str();
        // A function that reads no frame is given the cheapest one, which
        // the query did not write.
        let frameless = ["row_number() ", "rank() ", "dense_rank() ", "percent_rank() ", "cume_dist() "].iter().any(|f| before.ends_with(f));
        let definition = match frameless {
            true => definition.strip_suffix(" ROWS UNBOUNDED PRECEDING").unwrap_or(definition),
            false => definition,
        };
        Some((definition, "OVER ".len() + name.len()))
    }

    fn key_of(&self, e: &ast::Expr) -> String {
        let mut e = e;
        while let ast::Expr::Nested(inner) = e {
            e = inner;
        }
        if self.single.is_none() {
            return e.to_string();
        }
        let mut e = e.clone();
        let _ = ast::visit_expressions_mut(&mut e, |x| {
            if let ast::Expr::CompoundIdentifier(parts) = x {
                *x = ast::Expr::Identifier(parts.last().unwrap().clone());
            }
            ControlFlow::<()>::Continue(())
        });
        e.to_string()
    }

    /// The column `name` of the relation aliased `alias`: `None` if no such
    /// relation is known.
    fn column(&self, alias: &str, name: &str) -> Option<Lineage> {
        Some(match self.aliases.get(alias)? {
            Alias::Base { table, instance } => match self.catalog.has_column(table, name) {
                true => Lineage::Exact(qualified(instance, name)),
                false => Lineage::Unknown,
            },
            Alias::Derived(columns) => columns.get(name).or_else(|| columns.get(&name.to_lowercase())).cloned().unwrap_or(Lineage::Unknown),
            Alias::Opaque => Lineage::Unknown,
        })
    }

    /// The known relation aliases `text` reads.
    fn reads(&self, text: &str) -> BTreeSet<String> {
        qualifiers(text).into_iter().filter(|q| self.aliases.contains_key(q)).collect()
    }

    /// Reads `text`, an expression PostgreSQL printed for an operator over
    /// `kids`, as an expression over base columns. A column is read by its
    /// relation's alias, and what an input computed, printed in
    /// parentheses, as that input's column.
    fn read(&self, text: &str, kids: &[usize], mode: Mode) -> Read {
        let reads = self.reads(text);
        let mut r = Reader { b: self, kids, refs: vec![], columns: vec![], inits: BTreeSet::new(), failed: false };
        let prepared = r.prepare(text);
        let expr = Parser::new(&PostgreSqlDialect {})
            .try_with_sql(&prepared)
            .and_then(|mut p| p.parse_expr())
            .ok()
            .and_then(|mut e| {
                let _ = e.visit(&mut r);
                (!r.failed).then_some(e)
            })
            .and_then(|e| self.plan(&e.to_string(), &r.columns, mode));
        Read { expr, reads, inits: r.inits }
    }

    /// `sql`, an expression over the placeholder columns `__c{i}`, each
    /// standing for `columns[i]`, as an expression over base columns.
    fn plan(&self, sql: &str, columns: &[Lineage], mode: Mode) -> Option<Expr> {
        let fields: Vec<Field> = columns
            .iter()
            .enumerate()
            .map(|(i, l)| {
                let ty = expr_of(l).and_then(|e| self.type_of(&e));
                Field::new(format!("__c{i}"), ty.unwrap_or(DataType::Null), true)
            })
            .collect();
        let schema = DFSchema::from_unqualified_fields(fields.into(), HashMap::new()).ok()?;
        let expr = self.catalog.state.create_logical_expr(sql, &schema).ok()?;
        // What the operator computes itself, before what its inputs did.
        let aggregates = expr.exists(|x| Ok(matches!(x, Expr::AggregateFunction(_)))).unwrap_or(true);
        let windows = expr.exists(|x| Ok(matches!(x, Expr::WindowFunction(_)))).unwrap_or(true);
        if (aggregates && mode != Mode::Aggregate) || (windows && mode != Mode::Window) {
            return None;
        }
        let expr = expr
            .transform_up(|e| match e {
                Expr::Column(c) if c.relation.is_none() => {
                    let i: Option<usize> = c.name.strip_prefix("__c").and_then(|i| i.parse().ok());
                    match i.and_then(|i| columns.get(i)) {
                        Some(Lineage::Exact(e)) => Ok(Transformed::yes(e.clone())),
                        _ => Err(DataFusionError::Plan(format!("unresolved column {}", c.name))),
                    }
                }
                Expr::Alias(a) => Ok(Transformed::yes(*a.expr)),
                e => Ok(Transformed::no(e)),
            })
            .ok()?
            .data;
        // Casts PostgreSQL adds where the query has none: a string to
        // `text`, and an exact number to `numeric`, both of the same value.
        let expr = expr
            .transform_up(|e| match &e {
                Expr::Cast(c) => {
                    let (to, from) = (c.field.data_type(), self.type_of(&c.expr));
                    let string = |t: &DataType| matches!(t, DataType::Utf8 | DataType::LargeUtf8 | DataType::Utf8View);
                    let same = match from {
                        Some(from) => {
                            (string(to) && string(&from))
                                || (*to == DataType::Decimal128(38, 10) && (from.is_integer() || matches!(from, DataType::Decimal128(..))))
                        }
                        None => false,
                    };
                    Ok(if same { Transformed::yes((*c.expr).clone()) } else { Transformed::no(e) })
                }
                _ => Ok(Transformed::no(e)),
            })
            .ok()?
            .data;
        Some(self.simplify(expr))
    }

    fn type_of(&self, e: &Expr) -> Option<DataType> {
        type_of(self.catalog, e)
    }

    fn simplify(&self, e: Expr) -> Expr {
        simplify(self.catalog, &self.nodes, e)
    }
}

/// Rewrites one expression PostgreSQL printed into one DataFusion parses,
/// over placeholder columns.
struct Reader<'b, 'a> {
    b: &'b Builder<'a>,
    kids: &'b [usize],
    /// What each `__ref{i}` in the prepared text refers to.
    refs: Vec<Ref>,
    /// What each placeholder column `__c{i}` holds.
    columns: Vec<Lineage>,
    inits: BTreeSet<String>,
    /// Whether it reads a relation no scan gave.
    failed: bool,
}

impl Reader<'_, '_> {
    /// `text` with each reference to a subplan's or InitPlan's output as
    /// the identifier `__ref{i}`, and each window's name as its definition.
    /// String literals are left alone.
    fn prepare(&mut self, text: &str) -> String {
        let mut out = String::new();
        for (i, part) in text.split('\'').enumerate() {
            if i > 0 {
                out.push('\'');
            }
            if i % 2 == 1 {
                out.push_str(part);
                continue;
            }
            let mut rest = part;
            while let Some(at) = rest.find(['(', '$', 'O']) {
                out.push_str(&rest[..at]);
                rest = &rest[at..];
                if let Some((r, len)) = reference(rest) {
                    out.push_str(&format!("__ref{}", self.refs.len()));
                    self.refs.push(r);
                    rest = &rest[len..];
                } else if let Some((definition, len)) = self.b.window_at(rest, &out) {
                    out.push_str(&format!("OVER ({definition})"));
                    rest = &rest[len..];
                } else {
                    let c = rest.chars().next().unwrap();
                    out.push(c);
                    rest = &rest[c.len_utf8()..];
                }
            }
            out.push_str(rest);
        }
        out
    }

    fn placeholder(&mut self, lineage: Lineage) -> ast::Expr {
        self.columns.push(lineage);
        ast::Expr::Identifier(ast::Ident::new(format!("__c{}", self.columns.len() - 1)))
    }

    /// What `__ref{i}` holds: an InitPlan's output column.
    fn reference(&mut self, i: usize) -> Lineage {
        let (init, column) = match self.refs.get(i) {
            Some(Ref::Init(init, column)) => (init.clone(), *column),
            Some(Ref::Param(p)) => match self.b.params.get(p) {
                Some((init, column)) => (init.clone(), *column),
                None => return Lineage::Unknown,
            },
            _ => return Lineage::Unknown,
        };
        let Some(i) = self.b.inits.get(&init).filter(|i| i.one_row) else { return Lineage::Unknown };
        self.inits.insert(init);
        self.b.nodes[i.root].columns.get(column).map_or(Lineage::Unknown, |c| c.lineage.clone())
    }
}

impl VisitorMut for Reader<'_, '_> {
    type Break = ();

    /// References, each to a placeholder column.
    fn pre_visit_expr(&mut self, e: &mut ast::Expr) -> ControlFlow<()> {
        let lineage = match e {
            ast::Expr::Nested(inner) => {
                let key = self.b.key_of(inner);
                let found = self.kids.iter().find_map(|&k| {
                    let i = self.b.keys[k].iter().position(|c| *c == key)?;
                    Some(self.b.nodes[k].columns[i].lineage.clone())
                });
                match found {
                    Some(l) => l,
                    None => return ControlFlow::Continue(()),
                }
            }
            ast::Expr::CompoundIdentifier(parts) if parts.len() >= 2 => {
                let (alias, name) = (&parts[parts.len() - 2].value, &parts[parts.len() - 1].value);
                match self.b.column(alias, name) {
                    Some(l) => l,
                    None => {
                        self.failed = true;
                        Lineage::Unknown
                    }
                }
            }
            ast::Expr::Identifier(i) if i.value.starts_with("__c") => return ControlFlow::Continue(()),
            ast::Expr::Identifier(i) => match i.value.strip_prefix("__ref").and_then(|k| k.parse().ok()) {
                Some(k) => self.reference(k),
                // A column printed without its relation: the plan's only one.
                None => match self.b.single.as_ref().and_then(|a| self.b.column(a, &i.value)) {
                    Some(l) => l,
                    None => {
                        self.failed = true;
                        Lineage::Unknown
                    }
                },
            },
            _ => return ControlFlow::Continue(()),
        };
        *e = self.placeholder(lineage);
        ControlFlow::Continue(())
    }

    /// PostgreSQL's spellings, in DataFusion's.
    fn post_visit_expr(&mut self, e: &mut ast::Expr) -> ControlFlow<()> {
        let literal = |e: &ast::Expr| match e {
            ast::Expr::Value(v) => match &v.value {
                ast::Value::SingleQuotedString(s) => Some(s.clone()),
                _ => None,
            },
            _ => None,
        };
        let replacement = match e {
            // `'1'::numeric` is the number the query wrote, and `'a'::text`
            // the string.
            ast::Expr::Cast { expr, data_type, .. } => match (literal(expr), kind(data_type)) {
                (Some(s), Kind::Number) if s.trim().parse::<f64>().is_ok_and(f64::is_finite) => Some(number(&s)),
                (Some(_), Kind::String) => Some((**expr).clone()),
                (None, Kind::String) => {
                    *data_type = ast::DataType::Text;
                    None
                }
                _ => None,
            },
            ast::Expr::BinaryOp { left, op, right } => {
                use ast::BinaryOperator as B;
                let like = |negated, insensitive| {
                    let (expr, pattern) = (left.clone(), right.clone());
                    Some(match insensitive {
                        false => ast::Expr::Like { negated, any: false, expr, pattern, escape_char: None },
                        true => ast::Expr::ILike { negated, any: false, expr, pattern, escape_char: None },
                    })
                };
                match op {
                    B::PGLikeMatch => like(false, false),
                    B::PGNotLikeMatch => like(true, false),
                    B::PGILikeMatch => like(false, true),
                    B::PGNotILikeMatch => like(true, true),
                    _ => None,
                }
            }
            // `x = ANY ('{a,b}'::text[])` is `x IN ('a', 'b')`.
            ast::Expr::AnyOp { left, compare_op: ast::BinaryOperator::Eq, right, .. } => {
                array(right).map(|list| ast::Expr::InList { expr: left.clone(), list, negated: false })
            }
            ast::Expr::AllOp { left, compare_op: ast::BinaryOperator::NotEq, right } => {
                array(right).map(|list| ast::Expr::InList { expr: left.clone(), list, negated: true })
            }
            // `"substring"(x, 1, 2)`: a function named by a keyword.
            ast::Expr::Function(f) => {
                for part in &mut f.name.0 {
                    if let ast::ObjectNamePart::Identifier(i) = part {
                        i.quote_style = None;
                    }
                }
                None
            }
            _ => None,
        };
        if let Some(r) = replacement {
            *e = r;
        }
        ControlFlow::Continue(())
    }
}

/// What a cast's target type holds, as far as a literal cast to it reads.
enum Kind {
    Number,
    String,
    Other,
}

fn kind(t: &ast::DataType) -> Kind {
    use ast::DataType as T;
    match t {
        T::Numeric(_) | T::Decimal(_) | T::Dec(_) | T::Int(_) | T::Integer(_) | T::BigInt(_) | T::SmallInt(_) | T::Int2(_) | T::Int4(_) | T::Int8(_) => Kind::Number,
        T::Real | T::Float4 | T::Float8 | T::Double(_) | T::DoublePrecision | T::Float(_) => Kind::Number,
        T::Text | T::Varchar(_) | T::CharacterVarying(_) | T::Char(_) | T::Character(_) => Kind::String,
        T::Custom(name, _) if matches!(name.to_string().to_lowercase().as_str(), "bpchar" | "name" | "\"char\"") => Kind::String,
        _ => Kind::Other,
    }
}

fn number(s: &str) -> ast::Expr {
    ast::Expr::Value(ast::Value::Number(s.trim().parse().unwrap_or_default(), false).into())
}

fn string(s: &str) -> ast::Expr {
    ast::Expr::Value(ast::Value::SingleQuotedString(s.to_string()).into())
}

/// The elements of `'{a,b}'::type[]`, an array literal, as literals of
/// `type`.
fn array(e: &ast::Expr) -> Option<Vec<ast::Expr>> {
    let ast::Expr::Cast { expr, data_type: ast::DataType::Array(element), .. } = e else { return None };
    let (ast::ArrayElemTypeDef::SquareBracket(element, _) | ast::ArrayElemTypeDef::AngleBracket(element)) = element else { return None };
    let ast::Expr::Value(v) = expr.as_ref() else { return None };
    let ast::Value::SingleQuotedString(s) = &v.value else { return None };
    let inner = s.trim().strip_prefix('{')?.strip_suffix('}')?;
    let mut elements = vec![];
    let mut chars = inner.chars().peekable();
    while chars.peek().is_some() {
        let mut item = String::new();
        let mut quoted = false;
        if chars.peek() == Some(&'"') {
            chars.next();
            quoted = true;
            while let Some(c) = chars.next() {
                match c {
                    '\\' => item.extend(chars.next()),
                    '"' => break,
                    c => item.push(c),
                }
            }
        }
        for c in chars.by_ref() {
            if c == ',' {
                break;
            }
            item.push(c);
        }
        // An unquoted NULL is no value: `IN` over it is not a list of
        // literals.
        if !quoted && item.eq_ignore_ascii_case("null") {
            return None;
        }
        elements.push(item);
    }
    elements
        .iter()
        .map(|item| match kind(element) {
            Kind::Number => item.trim().parse::<f64>().is_ok_and(f64::is_finite).then(|| number(item)),
            Kind::String => Some(string(item)),
            Kind::Other => Some(ast::Expr::Cast {
                kind: ast::CastKind::DoubleColon,
                expr: Box::new(string(item)),
                data_type: (**element).clone(),
                array: false,
                format: None,
            }),
        })
        .collect()
}

/// A reference at the start of `text` to an InitPlan's or SubPlan's output,
/// or a parameter, and its length.
fn reference(text: &str) -> Option<(Ref, usize)> {
    if let Some(rest) = text.strip_prefix('$') {
        let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
        return (!digits.is_empty()).then(|| (Ref::Param(format!("${digits}")), 1 + digits.len()));
    }
    let rest = text.strip_prefix('(')?;
    let (init, rest) = if let Some(r) = rest.strip_prefix("InitPlan ") {
        (true, r)
    } else if let Some(r) = rest.strip_prefix("hashed SubPlan ").or_else(|| rest.strip_prefix("SubPlan ")) {
        (false, r)
    } else {
        return None;
    };
    let name: String = rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
    let after = rest[name.len()..].strip_prefix(')')?;
    let mut len = text.len() - after.len();
    // `.col1`: its first output column.
    let mut column = 0;
    if let Some(digits) = after.strip_prefix(".col") {
        let digits: String = digits.chars().take_while(char::is_ascii_digit).collect();
        if let Ok(n) = digits.parse::<usize>() {
            column = n.checked_sub(1)?;
            len += ".col".len() + digits.len();
        }
    }
    Some((if init { Ref::Init(name, column) } else { Ref::Sub }, len))
}

/// `[NOT] (ANY (x = (hashed SubPlan 1).col1))`: `x [NOT] IN` an
/// uncorrelated subquery, which PostgreSQL runs once.
struct Mark {
    subplan: String,
    negated: bool,
    hashed: bool,
    /// Each compared expression, and the subplan's output column it is
    /// compared with.
    keys: Vec<(String, usize)>,
}

fn mark_condition(cond: &str) -> Option<Mark> {
    let mut t = strip_all_parens(cond.trim());
    let negated = t.starts_with("NOT ");
    if negated {
        t = strip_all_parens(t["NOT ".len()..].trim());
    }
    let inner = t.strip_prefix("ANY ")?.trim();
    if !inner.starts_with('(') || strip_parens(inner).len() == inner.len() {
        return None;
    }
    let mut subplan = None;
    let mut keys = vec![];
    let mut hashed = true;
    for part in conjuncts(inner) {
        let part = strip_all_parens(part.trim());
        let (at, len) = ["= (hashed SubPlan ", "= (SubPlan "].iter().find_map(|p| part.rfind(p).map(|at| (at, p.len())))?;
        hashed &= part[at..].starts_with("= (hashed ");
        let (left, right) = (part[..at].trim(), &part[at + len..]);
        let (name, column) = right.strip_suffix(|c: char| c.is_ascii_digit()).map_or((right, right), |_| {
            right.rsplit_once(").col").unwrap_or((right, ""))
        });
        let column: usize = column.parse::<usize>().ok()?.checked_sub(1)?;
        if subplan.get_or_insert_with(|| name.to_string()) != name {
            return None;
        }
        keys.push((left.to_string(), column));
    }
    Some(Mark { subplan: subplan?, negated, hashed, keys })
}

/// The window functions operator `v`, a window, computes and prints
/// without their window (`row_number() OVER (?)`, before version 18): each
/// one's call.
fn unnamed_calls(v: &Value) -> Vec<String> {
    if text(v, "Node Type") != Some("WindowAgg") {
        return vec![];
    }
    let below: BTreeSet<String> = plans(v).iter().flat_map(|c| texts(c, "Output")).collect();
    texts(v, "Output")
        .into_iter()
        .filter(|item| !below.contains(item))
        .filter_map(|item| item.strip_suffix(" OVER (?)").map(str::to_string))
        .collect()
}

/// A function call in one form, to compare a plan's with a query's.
fn call_key(call: &str) -> Option<String> {
    let e = Parser::new(&PostgreSqlDialect {}).try_with_sql(call.trim()).and_then(|mut p| p.parse_expr()).ok()?;
    matches!(e, ast::Expr::Function(_)).then(|| super::sql::plain(&e).to_lowercase())
}

/// The function call `text` ends with: `rank()` in `(rank() `.
fn trailing_call(text: &str) -> Option<&str> {
    let text = text.trim_end();
    let mut depth = 0i32;
    let mut open = None;
    for (i, c) in text.char_indices().rev() {
        match c {
            ')' => depth += 1,
            '(' => {
                depth -= 1;
                if depth == 0 {
                    open = Some(i);
                    break;
                }
            }
            _ => {}
        }
    }
    let open = open.filter(|_| text.ends_with(')'))?;
    let name = text[..open].rfind(|c: char| !(c.is_alphanumeric() || c == '_' || c == '"')).map_or(0, |i| i + 1);
    (name < open).then(|| &text[name..])
}

/// `definition`, a window's (`PARTITION BY a ORDER BY b, c ROWS ...`), with
/// each expression it orders by as `keys`, the sort keys of its input,
/// print it: with its direction (`b DESC NULLS LAST`).
fn window_order(definition: &str, keys: &[String]) -> String {
    let Some(at) = top_level(definition, "ORDER BY ") else { return definition.to_string() };
    let (head, rest) = definition.split_at(at + "ORDER BY ".len());
    let end = [" ROWS ", " RANGE ", " GROUPS "].iter().filter_map(|f| top_level(rest, f)).min().unwrap_or(rest.len());
    let (order, frame) = rest.split_at(end);
    let items: Vec<String> = split_top_level(order, ',')
        .into_iter()
        .map(|item| {
            let item = item.trim();
            let sorted = keys.iter().find(|k| k.strip_prefix(item).is_some_and(|d| d.is_empty() || d.starts_with(' ')));
            sorted.map_or(item, |k| k.as_str()).to_string()
        })
        .collect();
    format!("{head}{}{frame}", items.join(", "))
}

/// Where `what` first occurs in `text` outside parentheses and quotes.
fn top_level(text: &str, what: &str) -> Option<usize> {
    let mut depth = 0i32;
    let mut quote = None;
    for (i, c) in text.char_indices() {
        match (quote, c) {
            (Some(q), c) if c == q => quote = None,
            (Some(_), _) => {}
            (None, '\'' | '"') => quote = Some(c),
            (None, '(') => depth += 1,
            (None, ')') => depth -= 1,
            _ if depth == 0 && text[i..].starts_with(what) => return Some(i),
            _ => {}
        }
    }
    None
}

/// `text` split at each `separator` outside parentheses and quotes.
fn split_top_level(text: &str, separator: char) -> Vec<&str> {
    let mut parts = vec![];
    let mut rest = text;
    let pattern = separator.to_string();
    while let Some(at) = top_level(rest, &pattern) {
        parts.push(&rest[..at]);
        rest = &rest[at + separator.len_utf8()..];
    }
    parts.push(rest);
    parts
}

/// The name of a mark join's mark column.
const MARK: &str = "mark";

/// `text` without one pair of parentheses around all of it.
fn strip_parens(text: &str) -> &str {
    let Some(inner) = text.strip_prefix('(').and_then(|t| t.strip_suffix(')')) else { return text };
    // The first parenthesis closes at the end, not before.
    let mut depth = 0i32;
    let mut quote = None;
    for c in inner.chars() {
        match (quote, c) {
            (Some(q), c) if c == q => quote = None,
            (Some(_), _) => {}
            (None, '\'' | '"') => quote = Some(c),
            (None, '(') => depth += 1,
            (None, ')') => {
                depth -= 1;
                if depth < 0 {
                    return text;
                }
            }
            _ => {}
        }
    }
    inner
}

fn strip_all_parens(mut text: &str) -> &str {
    loop {
        let inner = strip_parens(text).trim();
        if inner.len() == text.len() {
            return text;
        }
        text = inner;
    }
}

/// The conjuncts of `text`, a condition as PostgreSQL prints one: `((a) AND
/// (b))`, with every nested condition in parentheses of its own.
fn conjuncts(text: &str) -> Vec<String> {
    let inner = strip_parens(text.trim());
    let mut parts = vec![];
    let mut depth = 0i32;
    let mut quote = None;
    let mut start = 0;
    let bytes = inner.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i] as char;
        match (quote, c) {
            (Some(q), c) if c == q => quote = None,
            (Some(_), _) => {}
            (None, '\'' | '"') => quote = Some(c),
            (None, '(') => depth += 1,
            (None, ')') => depth -= 1,
            (None, ' ') if depth == 0 && inner[i..].starts_with(" AND ") => {
                parts.push(inner[start..i].to_string());
                start = i + " AND ".len();
                i = start;
                continue;
            }
            _ => {}
        }
        i += 1;
    }
    if parts.is_empty() {
        return vec![text.trim().to_string()];
    }
    parts.push(inner[start..].to_string());
    parts
}

/// The identifiers `text` uses to qualify a column: `a` in `a.x`.
fn qualifiers(text: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for (i, part) in text.split('\'').enumerate() {
        if i % 2 == 1 {
            continue;
        }
        let chars: Vec<char> = part.chars().collect();
        let word = |c: char| c.is_alphanumeric() || c == '_';
        let mut k = 0;
        while k < chars.len() {
            let start = k;
            if chars[k] == '"' {
                k += 1;
                while k < chars.len() && chars[k] != '"' {
                    k += 1;
                }
                k += 1;
                if chars.get(k) == Some(&'.') && k > start + 2 {
                    out.insert(chars[start + 1..k - 1].iter().collect());
                }
            } else if word(chars[k]) {
                while k < chars.len() && word(chars[k]) {
                    k += 1;
                }
                if chars.get(k) == Some(&'.') && !chars[start].is_ascii_digit() {
                    out.insert(chars[start..k].iter().collect());
                }
            } else {
                k += 1;
            }
        }
    }
    out
}

fn expr_of(l: &Lineage) -> Option<Expr> {
    match l {
        Lineage::Exact(e) | Lineage::Bijective(e) => Some(e.clone()),
        Lineage::Unknown => None,
    }
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

fn unknown(name: String) -> OutCol {
    OutCol { name, lineage: Lineage::Unknown }
}

fn join_type(t: &str) -> Option<JoinType> {
    Some(match t {
        "Inner" => JoinType::Inner,
        "Left" => JoinType::Left,
        "Right" => JoinType::Right,
        "Full" => JoinType::Full,
        "Semi" => JoinType::LeftSemi,
        "Anti" => JoinType::LeftAnti,
        "Right Semi" => JoinType::RightSemi,
        "Right Anti" => JoinType::RightAnti,
        _ => return None,
    })
}
