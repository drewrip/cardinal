//! DuckDB's `EXPLAIN (ANALYZE, FORMAT JSON)` profile, as an [`ObservedPlan`].
//!
//! DuckDB prints a physical plan: columns are referred to by unqualified name
//! or by position (`#2`), joins may drop and reorder columns without saying,
//! and projections wrap columns in internal compression functions. Each
//! operator's output columns are tracked back to base-table expressions, and
//! a reference is resolved only when that is unambiguous. The query text, which
//! the profile includes, names what projections print only by alias, and
//! vouches for each join condition's columns.

use std::collections::{BTreeSet, HashMap};

use datafusion::arrow::datatypes::{DataType, Field};
use datafusion::common::tree_node::{Transformed, TreeNode};
use datafusion::common::{DFSchema, DataFusionError, JoinType};
use datafusion::logical_expr::simplify::SimplifyContext;
use datafusion::logical_expr::utils::split_conjunction_owned;
use datafusion::logical_expr::{BinaryExpr, Expr, ExprSchemable, Operator};
use datafusion::optimizer::simplify_expressions::ExprSimplifier;
use datafusion::sql::sqlparser::ast;
use datafusion::sql::sqlparser::dialect::GenericDialect;
use datafusion::sql::sqlparser::parser::Parser;
use serde_json::Value;

use super::sql::QueryText;
use super::{
    Catalog, Lineage, ONode, ObservedPlan, Op, OutCol, Pred, RuntimeFilter, base_table, qualified, relation,
    requalify,
};
use crate::{Error, Result};

/// Reads a DuckDB profile, as printed by `EXPLAIN (ANALYZE, FORMAT JSON)`,
/// against the tables in `catalog`. `name` names the query in provenance.
pub fn from_duckdb(catalog: &Catalog, name: &str, json: &str) -> Result<ObservedPlan> {
    let v: Value = serde_json::from_str(json).map_err(|e| Error::Observed(e.to_string()))?;
    let text = v.get("query_name").and_then(Value::as_str).and_then(|q| QueryText::parse(catalog, q));
    let mut b = Builder { catalog, text, nodes: vec![], ctes: HashMap::new(), delims: vec![] };
    let root = b.node(&v)?;
    Ok(ObservedPlan { name: name.to_string(), nodes: b.nodes, root })
}

/// Wrappers with no effect on rows.
const WRAPPERS: &[&str] = &["EXPLAIN_ANALYZE", "RESULT_COLLECTOR"];

struct Builder<'a> {
    catalog: &'a Catalog,
    text: Option<QueryText>,
    nodes: Vec<ONode>,
    /// A materialized CTE's definition, by its `Table Index`.
    ctes: HashMap<String, usize>,
    /// The delim joins being built, innermost last.
    delims: Vec<Delim>,
}

/// A delim join: its input `A`, read by the join below it through a
/// `COLUMN_DATA_SCAN` or `DUMMY_SCAN`, and the distinct join keys of `A`,
/// read by the subquery through `DELIM_SCAN`s.
struct Delim {
    index: String,
    /// The scan that stands for the input, by address in the profile.
    data: *const Value,
    input: usize,
    keys: usize,
}

impl Builder<'_> {
    fn node(&mut self, v: &Value) -> Result<usize> {
        let ty = v.get("operator_type").and_then(Value::as_str);
        let children: &[Value] = v.get("children").and_then(Value::as_array).map_or(&[], |c| c);
        if ty.is_none_or(|t| WRAPPERS.contains(&t)) {
            return match children {
                [only] => self.node(only),
                _ => Err(Error::Observed(format!("{} has {} children", ty.unwrap_or("the profile"), children.len()))),
            };
        }
        let ty = ty.unwrap();
        let info = v.get("extra_info").unwrap_or(&Value::Null);
        let rows = rows(v, ty)?;
        let index = |key| strings(info, key).into_iter().next();
        match (ty, children) {
            // A materialized CTE: its definition, then the query reading it.
            ("CTE", [definition, consumer]) => {
                let d = self.node(definition)?;
                if let Some(i) = index("Table Index") {
                    self.ctes.insert(i, d);
                }
                return self.node(consumer);
            }
            ("CTE_SCAN", []) => {
                if let Some(&d) = index("CTE Index").and_then(|i| self.ctes.get(&i)) {
                    return Ok(self.reuse(d, Some(rows), ty));
                }
            }
            ("LEFT_DELIM_JOIN" | "RIGHT_DELIM_JOIN", [input, join, distinct]) => {
                return self.delim_join(ty, info, input, join, distinct);
            }
            ("COLUMN_DATA_SCAN" | "DUMMY_SCAN", []) => {
                if let Some(d) = self.delims.iter().rev().find(|d| std::ptr::eq(d.data, v)) {
                    // A DUMMY_SCAN reports no rows of its own.
                    let reported = (ty == "COLUMN_DATA_SCAN").then_some(rows);
                    return Ok(self.reuse(d.input, reported, ty));
                }
            }
            ("DELIM_SCAN", []) => {
                // Reports 0 rows, whatever it read.
                let i = index("Delim Index");
                if let Some(d) = self.delims.iter().rev().find(|d| Some(&d.index) == i.as_ref()) {
                    return Ok(self.reuse(d.keys, None, ty));
                }
            }
            _ => {}
        }
        let mut kids = children.iter().map(|c| self.node(c)).collect::<Result<Vec<_>>>()?;
        let (op, columns, ordered) = self.convert(ty, info, &kids);
        // A filter that replaced a mark join reads the join's probe side.
        if let (Op::Filter { .. }, [c]) = (&op, &kids[..])
            && let Op::Join { kind: JoinType::LeftMark, .. } = self.nodes[*c].op
        {
            kids = vec![self.nodes[*c].children[0]];
        }
        self.nodes.push(ONode { op, rows, children: kids, columns, ordered, engine_op: ty.to_string() });
        Ok(self.nodes.len() - 1)
    }

    /// A read of operator `of`'s output, as an independent copy of it.
    fn reuse(&mut self, of: usize, reported: Option<u64>, engine_op: &str) -> usize {
        let id = self.nodes.len();
        let suffix = format!("~r{id}");
        let columns = self.nodes[of]
            .columns
            .iter()
            .map(|c| OutCol { name: c.name.clone(), lineage: rename(&c.lineage, &suffix) })
            .collect();
        let node = ONode {
            op: Op::Reuse { suffix, checked: reported.is_some() },
            rows: reported.unwrap_or(self.nodes[of].rows),
            children: vec![of],
            columns,
            ordered: self.nodes[of].ordered,
            engine_op: engine_op.to_string(),
        };
        self.nodes.push(node);
        id
    }

    /// A delim join, DuckDB's plan for a correlated subquery: `join` joins
    /// the input to the subquery, which reads the distinct join keys of the
    /// input (computed by `distinct`). It is `join`'s output.
    fn delim_join(&mut self, ty: &str, info: &Value, input: &Value, join: &Value, distinct: &Value) -> Result<usize> {
        let a = self.node(input)?;
        let copy = self.reuse(a, None, "DELIM_INPUT");
        // The keys are the conditions' left sides, over the input; the
        // grouping's own positions are into a column order not printed.
        let keys: Vec<OutCol> = strings(info, "Conditions")
            .iter()
            .map(|c| {
                let left = split_condition(c).map(|(l, _, _)| l.to_string());
                let node = &self.nodes[copy];
                match left.as_deref().and_then(|l| lookup(l, &node.columns, node.ordered)) {
                    Some(col) => col.clone(),
                    None => unknown(left.unwrap_or_else(|| c.clone())),
                }
            })
            .collect();
        let g = ONode {
            op: Op::Aggregate {
                keys: keys.iter().map(|k| exact(&k.lineage)).collect(),
                values: vec![],
            },
            rows: rows(distinct, "delim distinct")?,
            children: vec![copy],
            columns: keys.clone(),
            ordered: true,
            engine_op: distinct.get("operator_type").and_then(Value::as_str).unwrap_or("HASH_GROUP_BY").to_string(),
        };
        self.nodes.push(g);
        let g = self.nodes.len() - 1;

        let left = ty == "LEFT_DELIM_JOIN";
        let (position, scan) = if left { (0, "COLUMN_DATA_SCAN") } else { (1, "DUMMY_SCAN") };
        let data = join
            .get("children")
            .and_then(|c| c.get(position))
            .filter(|c| c.get("operator_type").and_then(Value::as_str) == Some(scan))
            .map_or(std::ptr::null(), |c| c as *const Value);
        let index = strings(info, "Delim Index").into_iter().next().unwrap_or_default();
        self.delims.push(Delim { index, data, input: a, keys: g });
        let j = self.node(join);
        self.delims.pop();
        let j = j?;

        // A correlated scalar subquery's value is referred to as SUBQUERY:
        // the subquery side's one column besides the keys.
        if let Op::Join { kind: JoinType::Inner | JoinType::Left | JoinType::Right | JoinType::Full, .. } = self.nodes[j].op {
            let (data, sub) = match left {
                true => (self.nodes[j].children[0], self.nodes[j].children[1]),
                false => (self.nodes[j].children[1], self.nodes[j].children[0]),
            };
            let offset = if left { self.nodes[data].columns.len() } else { 0 };
            let key_names: BTreeSet<&str> = keys.iter().map(|k| k.name.as_str()).collect();
            let others: Vec<usize> = (0..self.nodes[sub].columns.len())
                .filter(|&i| !key_names.contains(self.nodes[sub].columns[i].name.as_str()))
                .collect();
            if let [i] = others[..] {
                self.nodes[j].columns[offset + i].name = "SUBQUERY".into();
            }
        }
        Ok(j)
    }

    fn convert(&self, ty: &str, info: &Value, kids: &[usize]) -> (Op, Vec<OutCol>, bool) {
        let passthrough = |op| {
            let c = &self.nodes[kids[0]];
            (op, c.columns.clone(), c.ordered)
        };
        match (ty, kids) {
            ("TABLE_SCAN" | "SEQ_SCAN", []) => self.scan(info),
            ("FILTER", [c]) => {
                let c = &self.nodes[*c];
                let text = strings(info, "Expression");
                let marks = c.columns.iter().filter(|c| c.name == MARK).count();
                if let (Op::Join { kind: JoinType::LeftMark, .. }, [t], 1) = (&c.op, &text[..], marks)
                    && let Some(negated) = mark_filter(t)
                {
                    if let Some(f) = (!negated).then(|| self.constant_in(c)).flatten() {
                        return f;
                    }
                    let columns = c.columns.iter().filter(|c| c.name != MARK).cloned().collect();
                    return (Op::MarkFilter { negated }, columns, false);
                }
                let predicate = text.iter().flat_map(|t| self.pred(t, &c.columns, c.ordered, false)).collect();
                (Op::Filter { predicate }, c.columns.clone(), c.ordered)
            }
            ("PROJECTION", [c]) => {
                let (columns, ordered) = self.projection(&strings(info, "Projections"), &self.nodes[*c]);
                (Op::Project, columns, ordered)
            }
            ("HASH_GROUP_BY" | "PERFECT_HASH_GROUP_BY", [c]) if info.get("Grouping Sets").is_none() => {
                self.aggregate(info, &self.nodes[*c])
            }
            ("UNGROUPED_AGGREGATE", [c]) => self.aggregate(info, &self.nodes[*c]),
            ("HASH_JOIN" | "NESTED_LOOP_JOIN" | "PIECEWISE_MERGE_JOIN" | "BLOCKWISE_NL_JOIN", [l, r]) => {
                self.join(info, &self.nodes[*l], &self.nodes[*r])
            }
            ("CROSS_PRODUCT", [l, r]) => {
                let (l, r) = (&self.nodes[*l], &self.nodes[*r]);
                let columns = l.columns.iter().chain(&r.columns).cloned().collect();
                (Op::Join { kind: JoinType::Inner, on: vec![] }, columns, false)
            }
            ("ORDER_BY", [_]) => passthrough(Op::Sort),
            ("TOP_N", [_]) => match strings(info, "Top").first().and_then(|t| t.trim().parse().ok()) {
                Some(fetch) => passthrough(Op::TopN { fetch }),
                None => passthrough(Op::Other),
            },
            ("STREAMING_LIMIT" | "LIMIT" | "LIMIT_PERCENT", [_]) => passthrough(Op::Limit),
            ("WINDOW" | "STREAMING_WINDOW", [c]) => {
                let mut columns = self.nodes[*c].columns.clone();
                columns.extend(strings(info, "Projections").into_iter().map(unknown));
                (Op::Window, columns, false)
            }
            ("UNION", [first, ..]) => {
                let columns = self.nodes[*first].columns.iter().map(|c| unknown(c.name.clone())).collect();
                (Op::Union, columns, true)
            }
            _ => (Op::Other, vec![], false),
        }
    }

    /// `x IN (constants)`, which DuckDB plans as a mark join against a table
    /// of the constants (`x = #0`), and also pushes into `x`'s scan as an
    /// optional filter, where the list can be read. The filter replaces the
    /// join, over the scan.
    fn constant_in(&self, mark: &ONode) -> Option<(Op, Vec<OutCol>, bool)> {
        let [probe, build] = mark.children[..] else { return None };
        let (probe, build) = (&self.nodes[probe], &self.nodes[build]);
        let (Op::Scan { filters, .. }, "COLUMN_DATA_SCAN") = (&probe.op, build.engine_op.as_str()) else { return None };
        let Op::Join { on, .. } = &mark.op else { return None };
        let [cond] = &on[..] else { return None };
        let (x, Operator::Eq, k) = split_condition(&cond.text)? else { return None };
        if k.to_string() != "__pos_0" {
            return None;
        }
        let x = self.read(&x.to_string(), &probe.columns, probe.ordered)?;
        let pred = filters.iter().find(|p| {
            p.optional && matches!(&p.expr, Some(Expr::InList(l)) if !l.negated && *l.expr == x && l.list.iter().all(|v| matches!(v, Expr::Literal(..))))
        })?;
        // Rewired by the caller: see `Builder::node`.
        let filter = Pred { optional: false, ..pred.clone() };
        Some((Op::Filter { predicate: vec![filter] }, probe.columns.clone(), probe.ordered))
    }

    fn scan(&self, info: &Value) -> (Op, Vec<OutCol>, bool) {
        let Some(table) = strings(info, "Table").first().map(|t| t.rsplit('.').next().unwrap().to_string()) else {
            return (Op::Other, vec![], false);
        };
        let instance = format!("{table}#{}", self.nodes.len());
        let base = |name: &str| match self.catalog.has_column(&table, name) {
            true => Lineage::Exact(qualified(&instance, name)),
            false => Lineage::Unknown,
        };
        let columns = strings(info, "Projections")
            .into_iter()
            .map(|n| OutCol { lineage: base(&n), name: n })
            .collect();
        // Filters may read columns the scan does not output.
        let all: Vec<OutCol> = self
            .catalog
            .tables
            .get(&table)
            .map(|s| s.fields().iter().map(|f| OutCol { name: f.name().clone(), lineage: base(f.name()) }).collect())
            .unwrap_or_default();
        let filters = strings(info, "Filters")
            .iter()
            .flat_map(|t| {
                let optional = t.contains("optional: ");
                self.pred(&t.replace("optional: ", ""), &all, false, optional)
            })
            .collect();
        let runtime_filters = strings(info, "Dynamic Filters")
            .iter()
            .flat_map(|t| t.split(" AND ").map(|t| t.trim().trim_start_matches("optional: ").to_string()).collect::<Vec<_>>())
            .map(|text| {
                let name: String = text.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
                let column = matches!(base(&name), Lineage::Exact(_)).then(|| format!("{instance}.{name}"));
                RuntimeFilter { column, text }
            })
            .collect();
        (Op::Scan { table, instance, filters, runtime_filters }, columns, true)
    }

    fn projection(&self, items: &[String], child: &ONode) -> (Vec<OutCol>, bool) {
        let items = &merge_guards(items);
        // Over a join, whose column order is unknown, DuckDB (de)compresses
        // columns by position. Such a projection keeps the columns, under
        // their names, but only the distinct counts of those it may have
        // compressed are certain. DuckDB compresses only integers
        // (`__internal_compress_integral_*`) and strings
        // (`__internal_compress_string_*`).
        if !child.ordered && !items.is_empty() && items.iter().all(|i| internal(i).is_some()) {
            let integers = items.iter().any(|i| i.starts_with("__internal_compress_integral_"));
            let strings = items.iter().any(|i| i.starts_with("__internal_compress_string_"));
            let compressible = |e: &Expr| match self.type_of(e) {
                Some(t) => (integers && t.is_integer()) || (strings && matches!(t, DataType::Utf8 | DataType::LargeUtf8 | DataType::Utf8View)),
                None => integers || strings,
            };
            let columns = child
                .columns
                .iter()
                .map(|c| OutCol {
                    name: c.name.clone(),
                    lineage: match &c.lineage {
                        Lineage::Exact(e) if compressible(e) => Lineage::Bijective(e.clone()),
                        l => l.clone(),
                    },
                })
                .collect();
            return (columns, false);
        }
        let columns = items
            .iter()
            .map(|item| {
                if let Some((compress, i)) = internal(item) {
                    let Some(c) = child.ordered.then(|| child.columns.get(i)).flatten() else {
                        return unknown(item.clone());
                    };
                    let lineage = match (&c.lineage, compress) {
                        (Lineage::Exact(e), Some(true)) => Lineage::Bijective(e.clone()),
                        // Decompressing what DuckDB compressed restores it.
                        (Lineage::Bijective(e), Some(false)) => Lineage::Exact(e.clone()),
                        (l, _) => l.clone(),
                    };
                    return OutCol { name: c.name.clone(), lineage };
                }
                // DuckDB's guard on a scalar subquery's single row, which
                // otherwise passes its value through.
                if is_guard(item) && item.trim_end().ends_with("ELSE #0 END") {
                    return match child.ordered.then(|| child.columns.first()).flatten() {
                        Some(c) => OutCol { name: "SUBQUERY".into(), lineage: c.lineage.clone() },
                        None => unknown("SUBQUERY".into()),
                    };
                }
                if let Some(c) = lookup(item, &child.columns, child.ordered) {
                    return c.clone();
                }
                // An expression, or an alias the query defines.
                let read = |text: &str| self.read(text, &child.columns, child.ordered);
                let alias = || self.text.as_ref().and_then(|t| t.alias(item)).and_then(read);
                match read(item).or_else(alias) {
                    Some(e) => OutCol { name: item.clone(), lineage: Lineage::Exact(e) },
                    None => unknown(item.clone()),
                }
            })
            .collect();
        (columns, true)
    }

    fn aggregate(&self, info: &Value, child: &ONode) -> (Op, Vec<OutCol>, bool) {
        let mut keys = vec![];
        let mut columns = vec![];
        for g in strings(info, "Groups") {
            let col = match lookup(&g, &child.columns, child.ordered) {
                Some(c) => c.clone(),
                None => match self.read(&g, &child.columns, child.ordered) {
                    Some(e) => OutCol { name: g.clone(), lineage: Lineage::Exact(e) },
                    None => unknown(g.clone()),
                },
            };
            keys.push(match &col.lineage {
                Lineage::Exact(e) | Lineage::Bijective(e) => Some(e.clone()),
                Lineage::Unknown => None,
            });
            columns.push(col);
        }
        // Each aggregate is a column of this operator, named as DuckDB refers
        // to it above: with its arguments' names in place of positions.
        let me = format!("@{}", self.nodes.len());
        let mut values = vec![];
        for a in strings(info, "Aggregates") {
            let value = self.read(&aggregate_sql(&a), &child.columns, child.ordered);
            values.push(value);
            columns.push(match named(&a.replace("sum_no_overflow(", "sum("), child) {
                Some(name) => OutCol { lineage: Lineage::Exact(qualified(&me, &name)), name },
                None => unknown(a),
            });
        }
        (Op::Aggregate { keys, values }, columns, true)
    }

    fn join(&self, info: &Value, l: &ONode, r: &ONode) -> (Op, Vec<OutCol>, bool) {
        let Some(kind) = strings(info, "Join Type").first().and_then(|t| join_type(t)) else {
            return (Op::Other, vec![], false);
        };
        let on = strings(info, "Conditions").iter().map(|c| self.condition(c, l, r)).collect();
        let columns = match kind {
            JoinType::LeftSemi | JoinType::LeftAnti => l.columns.clone(),
            JoinType::RightSemi | JoinType::RightAnti => r.columns.clone(),
            JoinType::LeftMark => l.columns.iter().cloned().chain([unknown(MARK.into())]).collect(),
            _ => l.columns.iter().chain(&r.columns).cloned().collect(),
        };
        (Op::Join { kind, on }, columns, false)
    }

    /// A join condition `a op b`: `a` reads the probe side, `b` the build
    /// side. DuckDB may name a column after the other side's (as in some
    /// decorrelated subqueries), so the query must compare the columns read.
    fn condition(&self, text: &str, l: &ONode, r: &ONode) -> Pred {
        let expr = split_condition(text).and_then(|(a, op, b)| {
            let a = self.read(&a.to_string(), &l.columns, l.ordered)?;
            let b = self.read(&b.to_string(), &r.columns, r.ordered)?;
            self.vouched(&a, op, &b).then(|| Expr::BinaryExpr(BinaryExpr::new(Box::new(a), op, Box::new(b))))
        });
        Pred { expr, text: text.to_string(), optional: false }
    }

    /// Whether the query compares what `a op b` reads: the same base
    /// columns, or columns some comparison reads together. Without the query
    /// text, any condition is.
    fn vouched(&self, a: &Expr, op: Operator, b: &Expr) -> bool {
        let Some(text) = &self.text else { return true };
        let base = |e: &Expr| -> BTreeSet<String> {
            e.column_refs()
                .into_iter()
                .filter_map(|c| relation(c).and_then(base_table).map(|t| format!("{t}.{}", c.name)))
                .collect()
        };
        let op_text = match op {
            Operator::IsNotDistinctFrom => "IS NOT DISTINCT FROM".to_string(),
            Operator::NotEq => "<>".to_string(),
            op => op.to_string(),
        };
        match (a, b) {
            (Expr::Column(x), Expr::Column(y)) if relation(x).and_then(base_table).is_some() && relation(y).and_then(base_table).is_some() => {
                let (x, y) = (base(a).pop_first().unwrap(), base(b).pop_first().unwrap());
                text.compares(&x, &op_text, &y)
            }
            _ => text.relates(&base(a).union(&base(b)).cloned().collect()),
        }
    }

    /// `text` as conjuncts over `cols`, or one unresolved predicate.
    fn pred(&self, text: &str, cols: &[OutCol], ordered: bool, optional: bool) -> Vec<Pred> {
        match self.read(text, cols, ordered) {
            Some(e) => split_conjunction_owned(e)
                .into_iter()
                .map(|e| Pred { text: e.to_string(), expr: Some(e), optional })
                .collect(),
            None => vec![Pred { expr: None, text: text.to_string(), optional }],
        }
    }

    /// Reads `text`, an expression over `cols`, as an expression over base
    /// columns. A column referenced by name must be the only one so named,
    /// by position needs `ordered` columns, and must hold an exact value.
    /// Names that read as expressions (`sum(l_quantity)`) match as written.
    fn read(&self, text: &str, cols: &[OutCol], ordered: bool) -> Option<Expr> {
        let mut fields = vec![];
        let mut lineage = HashMap::new();
        let mut count = HashMap::<&str, usize>::new();
        for c in cols {
            *count.entry(c.name.as_str()).or_default() += 1;
        }
        let mut text = text.to_string();
        let mut unique: Vec<&OutCol> = cols.iter().filter(|c| count[c.name.as_str()] == 1).collect();
        unique.sort_by_key(|c| std::cmp::Reverse(c.name.len()));
        let mut names = vec![];
        for (i, c) in unique.into_iter().enumerate() {
            let identifier = c.name.chars().all(|ch| ch.is_alphanumeric() || ch == '_');
            // DataFusion lowercases identifiers; other names are matched as
            // written (`SUBQUERY`, `sum(l_quantity)`).
            let name = if identifier && c.name.chars().all(|ch| !ch.is_uppercase()) {
                c.name.clone()
            } else if text.contains(&c.name) {
                let placeholder = format!("__name_{i}");
                text = match identifier {
                    true => replace_word(&text, &c.name, &placeholder),
                    false => text.replace(&c.name, &placeholder),
                };
                placeholder
            } else {
                continue;
            };
            names.push((name, c));
        }
        let positions = cols.iter().enumerate().filter(|_| ordered).map(|(i, c)| (format!("__pos_{i}"), c));
        for (name, c) in names.into_iter().chain(positions) {
            let ty = match &c.lineage {
                Lineage::Exact(e) | Lineage::Bijective(e) => self.type_of(e),
                Lineage::Unknown => None,
            };
            fields.push(Field::new(&name, ty.unwrap_or(DataType::Null), true));
            lineage.insert(name, &c.lineage);
        }
        let schema = DFSchema::from_unqualified_fields(fields.into(), HashMap::new()).ok()?;
        let Ok(expr) = self.catalog.state.create_logical_expr(&rewrite(&text), &schema) else {
            // A bare alias the query defines (`supplier_no`), not a column.
            let alias = self.text.as_ref().and_then(|t| t.alias(text.trim()));
            return alias.filter(|a| *a != text.trim()).and_then(|a| self.read(a, cols, ordered));
        };
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
        Some(self.simplify(expr))
    }

    /// The type of `e`, an expression over scan instances.
    fn type_of(&self, e: &Expr) -> Option<DataType> {
        requalify(e, &|r| base_table(r).map(str::to_string)).get_type(self.catalog.all.as_ref()).ok()
    }

    /// `e` simplified (constants folded), against the schemas of the
    /// instances it reads.
    fn simplify(&self, e: Expr) -> Expr {
        let mut schema = DFSchema::empty();
        let instances: BTreeSet<String> =
            e.column_refs().into_iter().filter_map(relation).filter(|r| base_table(r).is_some()).map(str::to_string).collect();
        for i in &instances {
            let Some(t) = self.catalog.tables.get(base_table(i).unwrap()) else { return e };
            match DFSchema::try_from_qualified_schema(i.as_str(), t) {
                Ok(s) => schema.merge(&s),
                Err(_) => return e,
            }
        }
        let context = SimplifyContext::builder().with_schema(schema.into()).build();
        ExprSimplifier::new(context).simplify(e.clone()).unwrap_or(e)
    }
}

/// Whether `item` is (the start of) DuckDB's guard on a scalar subquery's
/// single row.
fn is_guard(item: &str) -> bool {
    item.starts_with("CASE") && item.contains("\"error\"(")
}

/// Projection items, with a guard that DuckDB printed over several (its
/// error message has a line break) put back together.
fn merge_guards(items: &[String]) -> Vec<String> {
    let mut out: Vec<String> = vec![];
    let mut open = false;
    for item in items {
        match out.last_mut() {
            Some(last) if open => {
                last.push('\n');
                last.push_str(item);
            }
            _ => out.push(item.clone()),
        }
        let last = out.last().unwrap();
        open = is_guard(last) && !last.trim_end().ends_with("END");
    }
    out
}

/// The name of a mark join's mark column.
const MARK: &str = "mark";

/// A filter on a mark join's mark alone: `Some(false)` keeps marked rows,
/// `Some(true)` the rest.
fn mark_filter(text: &str) -> Option<bool> {
    let mut t = text.trim();
    while let Some(inner) = t.strip_prefix('(').and_then(|r| r.strip_suffix(')')) {
        t = inner.trim();
    }
    match t {
        "SUBQUERY" | "IN (...)" => Some(false),
        "NOT SUBQUERY" | "NOT IN (...)" | "NOT (SUBQUERY)" | "NOT (IN (...))" => Some(true),
        _ => None,
    }
}

fn rows(v: &Value, ty: &str) -> Result<u64> {
    v.get("operator_cardinality")
        .and_then(Value::as_u64)
        .ok_or_else(|| Error::Observed(format!("{ty} has no operator_cardinality")))
}

fn exact(l: &Lineage) -> Option<Expr> {
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

/// A join condition's sides and comparison.
fn split_condition(text: &str) -> Option<(ast::Expr, Operator, ast::Expr)> {
    let e = Parser::new(&GenericDialect {}).try_with_sql(&rewrite(text)).and_then(|mut p| p.parse_expr()).ok()?;
    match e {
        ast::Expr::BinaryOp { left, op, right } => Some((*left, comparison(&op)?, *right)),
        ast::Expr::IsNotDistinctFrom(left, right) => Some((*left, Operator::IsNotDistinctFrom, *right)),
        _ => None,
    }
}

/// An aggregate as DuckDB prints it, in DataFusion's spelling.
fn aggregate_sql(text: &str) -> String {
    text.replace("count_star()", "count(*)")
        .replace("sum_no_overflow(", "sum(")
        .replace("\"first\"(", "first_value(")
}

/// An aggregate's printed text with each `#i` replaced by the name of the
/// input's column `i`, as DuckDB names it above; `None` if a position does
/// not resolve.
fn named(text: &str, child: &ONode) -> Option<String> {
    let mut out = String::new();
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '#' || !chars.peek().is_some_and(char::is_ascii_digit) {
            out.push(c);
            continue;
        }
        let mut digits = String::new();
        while let Some(d) = chars.peek().copied().filter(char::is_ascii_digit) {
            digits.push(d);
            chars.next();
        }
        let col = child.ordered.then(|| child.columns.get(digits.parse::<usize>().ok()?)).flatten()?;
        out.push_str(&col.name);
    }
    Some(out)
}

/// The column `item` names: `#i`, or a name only one column has.
fn lookup<'c>(item: &str, cols: &'c [OutCol], ordered: bool) -> Option<&'c OutCol> {
    if let Some(i) = position(item) {
        return ordered.then(|| cols.get(i)).flatten();
    }
    let mut named = cols.iter().filter(|c| c.name == item);
    match (named.next(), named.next()) {
        (Some(c), None) => Some(c),
        _ => None,
    }
}

fn position(item: &str) -> Option<usize> {
    item.trim().strip_prefix('#')?.parse().ok()
}

/// DuckDB's internal (de)compression of column `#i`: `Some(true)` for
/// compress, `Some(false)` for decompress, `None` for a bare `#i`.
fn internal(item: &str) -> Option<(Option<bool>, usize)> {
    if let Some(i) = position(item) {
        return Some((None, i));
    }
    let compress = if item.starts_with("__internal_compress_") {
        true
    } else if item.starts_with("__internal_decompress_") {
        false
    } else {
        return None;
    };
    let args = item.split_once('(')?.1.trim_end_matches(')');
    Some((Some(compress), position(args.split(',').next()?)?))
}

fn unknown(name: String) -> OutCol {
    OutCol { name, lineage: Lineage::Unknown }
}

/// A field of `extra_info` that may be a string or a list of strings.
fn strings(info: &Value, key: &str) -> Vec<String> {
    match info.get(key) {
        Some(Value::String(s)) if !s.is_empty() => vec![s.clone()],
        Some(Value::Array(a)) => a.iter().filter_map(Value::as_str).map(str::to_string).collect(),
        _ => vec![],
    }
}

fn join_type(t: &str) -> Option<JoinType> {
    Some(match t {
        "INNER" => JoinType::Inner,
        "LEFT" => JoinType::Left,
        "RIGHT" => JoinType::Right,
        "OUTER" | "FULL" => JoinType::Full,
        "SEMI" => JoinType::LeftSemi,
        "ANTI" => JoinType::LeftAnti,
        "RIGHT_SEMI" => JoinType::RightSemi,
        "RIGHT_ANTI" => JoinType::RightAnti,
        "MARK" => JoinType::LeftMark,
        // SINGLE (a scalar subquery's join, which errors on a second match)
        // has no DataFusion counterpart.
        _ => return None,
    })
}

fn comparison(op: &ast::BinaryOperator) -> Option<Operator> {
    use ast::BinaryOperator as B;
    Some(match op {
        B::Eq => Operator::Eq,
        B::NotEq => Operator::NotEq,
        B::Lt => Operator::Lt,
        B::LtEq => Operator::LtEq,
        B::Gt => Operator::Gt,
        B::GtEq => Operator::GtEq,
        _ => return None,
    })
}

/// DuckDB's printed SQL in a form DataFusion parses: `~~` is LIKE,
/// `prefix`/`suffix` are `starts_with`/`ends_with`, and `#i` becomes the
/// field name `__pos_i`. String literals are left alone.
fn rewrite(text: &str) -> String {
    let mut out = String::new();
    for (i, part) in text.split('\'').enumerate() {
        if i > 0 {
            out.push('\'');
        }
        if i % 2 == 1 {
            out.push_str(part);
            continue;
        }
        let mut s = part
            .replace("!~~*", " NOT ILIKE ")
            .replace("~~*", " ILIKE ")
            .replace("!~~", " NOT LIKE ")
            .replace("~~", " LIKE ");
        for (from, to) in [("prefix(", "starts_with("), ("suffix(", "ends_with(")] {
            s = replace_word(&s, from, to);
        }
        let mut chars = s.chars().peekable();
        while let Some(c) = chars.next() {
            if c == '#' && chars.peek().is_some_and(char::is_ascii_digit) {
                out.push_str("__pos_");
            } else {
                out.push(c);
            }
        }
    }
    out
}

/// Replaces `from` where it is a whole word: not preceded, nor (if it ends
/// in a word character) followed, by a word character.
fn replace_word(s: &str, from: &str, to: &str) -> String {
    let word = |c: char| c.is_alphanumeric() || c == '_';
    let mut out = String::new();
    let mut rest = s;
    while let Some(i) = rest.find(from) {
        let after = &rest[i + from.len()..];
        let starts = !rest[..i].chars().next_back().is_some_and(word);
        let ends = !from.ends_with(word) || !after.chars().next().is_some_and(word);
        out.push_str(&rest[..i]);
        out.push_str(if starts && ends { to } else { from });
        rest = after;
    }
    out.push_str(rest);
    out
}
