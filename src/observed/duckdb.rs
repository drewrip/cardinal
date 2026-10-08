//! DuckDB's `EXPLAIN (ANALYZE, FORMAT JSON)` profile, as an [`ObservedPlan`].
//!
//! DuckDB prints a physical plan: columns are referred to by unqualified name
//! or by position (`#2`), joins may drop and reorder columns without saying,
//! and projections wrap columns in internal compression functions. Each
//! operator's output columns are tracked back to base-table expressions, and
//! a reference is resolved only when that is unambiguous.

use std::collections::HashMap;

use datafusion::arrow::datatypes::{DataType, Field};
use datafusion::common::tree_node::{Transformed, TreeNode};
use datafusion::common::{Column, DFSchema, DataFusionError, JoinType};
use datafusion::logical_expr::simplify::SimplifyContext;
use datafusion::logical_expr::utils::split_conjunction_owned;
use datafusion::logical_expr::{BinaryExpr, Expr, ExprSchemable, Operator};
use datafusion::optimizer::simplify_expressions::ExprSimplifier;
use datafusion::sql::sqlparser::ast;
use datafusion::sql::sqlparser::dialect::GenericDialect;
use datafusion::sql::sqlparser::parser::Parser;
use serde_json::Value;

use super::{Catalog, Lineage, ONode, ObservedPlan, Op, OutCol, Pred, RuntimeFilter};
use crate::{Error, Result};

/// Reads a DuckDB profile, as printed by `EXPLAIN (ANALYZE, FORMAT JSON)`,
/// against the tables in `catalog`. `name` names the query in provenance.
pub fn from_duckdb(catalog: &Catalog, name: &str, json: &str) -> Result<ObservedPlan> {
    let v: Value = serde_json::from_str(json).map_err(|e| Error::Observed(e.to_string()))?;
    let mut b = Builder { catalog, nodes: vec![] };
    let root = b.node(&v)?;
    Ok(ObservedPlan { name: name.to_string(), nodes: b.nodes, root })
}

/// Wrappers with no effect on rows.
const WRAPPERS: &[&str] = &["EXPLAIN_ANALYZE", "RESULT_COLLECTOR"];

struct Builder<'a> {
    catalog: &'a Catalog,
    nodes: Vec<ONode>,
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
        let kids = children.iter().map(|c| self.node(c)).collect::<Result<Vec<_>>>()?;
        let rows = v
            .get("operator_cardinality")
            .and_then(Value::as_u64)
            .ok_or_else(|| Error::Observed(format!("{ty} has no operator_cardinality")))?;
        let info = v.get("extra_info").unwrap_or(&Value::Null);
        let (op, columns, ordered) = self.convert(ty, info, &kids);
        self.nodes.push(ONode { op, rows, children: kids, columns, ordered, engine_op: ty.to_string() });
        Ok(self.nodes.len() - 1)
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
                let predicate = strings(info, "Expression")
                    .iter()
                    .flat_map(|t| self.pred(t, &c.columns, c.ordered, false))
                    .collect();
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

    fn scan(&self, info: &Value) -> (Op, Vec<OutCol>, bool) {
        let Some(table) = strings(info, "Table").first().map(|t| t.rsplit('.').next().unwrap().to_string()) else {
            return (Op::Other, vec![], false);
        };
        let schema = self.catalog.tables.get(&table);
        let base = |name: &str| match schema.is_some_and(|s| s.field_with_name(name).is_ok()) {
            true => Lineage::Exact(Expr::Column(Column::new(Some(table.as_str()), name))),
            false => Lineage::Unknown,
        };
        let columns = strings(info, "Projections")
            .into_iter()
            .map(|n| OutCol { lineage: base(&n), name: n })
            .collect();
        // Filters may read columns the scan does not output.
        let all: Vec<OutCol> = schema
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
                let column = matches!(base(&name), Lineage::Exact(_)).then(|| format!("{table}.{name}"));
                RuntimeFilter { column, text }
            })
            .collect();
        (Op::Scan { table, filters, runtime_filters }, columns, true)
    }

    fn projection(&self, items: &[String], child: &ONode) -> (Vec<OutCol>, bool) {
        // Over a join, whose column order is unknown, DuckDB (de)compresses
        // columns by position. Such a projection keeps the columns, under
        // their names, but only their distinct counts are certain.
        if !child.ordered && !items.is_empty() && items.iter().all(|i| internal(i).is_some()) {
            let any_compress = items.iter().any(|i| internal(i).is_some_and(|(compress, _)| compress == Some(true)));
            let columns = child
                .columns
                .iter()
                .map(|c| OutCol {
                    name: c.name.clone(),
                    lineage: match &c.lineage {
                        Lineage::Exact(e) if any_compress => Lineage::Bijective(e.clone()),
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
                if let Some(c) = lookup(item, &child.columns, child.ordered) {
                    return c.clone();
                }
                match self.read(item, &child.columns, child.ordered) {
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
        columns.extend(strings(info, "Aggregates").into_iter().map(unknown));
        (Op::Aggregate { keys }, columns, true)
    }

    fn join(&self, info: &Value, l: &ONode, r: &ONode) -> (Op, Vec<OutCol>, bool) {
        let Some(kind) = strings(info, "Join Type").first().and_then(|t| join_type(t)) else {
            return (Op::Other, vec![], false);
        };
        let on = strings(info, "Conditions").iter().map(|c| self.condition(c, l, r)).collect();
        let columns = match kind {
            JoinType::LeftSemi | JoinType::LeftAnti => l.columns.clone(),
            JoinType::RightSemi | JoinType::RightAnti => r.columns.clone(),
            JoinType::LeftMark => l.columns.iter().cloned().chain([unknown("mark".into())]).collect(),
            _ => l.columns.iter().chain(&r.columns).cloned().collect(),
        };
        (Op::Join { kind, on }, columns, false)
    }

    /// A join condition `a op b`: `a` reads the probe side, `b` the build side.
    fn condition(&self, text: &str, l: &ONode, r: &ONode) -> Pred {
        let sides = Parser::new(&GenericDialect {})
            .try_with_sql(&rewrite(text))
            .and_then(|mut p| p.parse_expr())
            .ok()
            .and_then(|e| match e {
                ast::Expr::BinaryOp { left, op, right } => Some((left, comparison(&op)?, right)),
                ast::Expr::IsNotDistinctFrom(left, right) => Some((left, Operator::IsNotDistinctFrom, right)),
                _ => None,
            });
        let expr = sides.and_then(|(a, op, b)| {
            let a = self.read(&a.to_string(), &l.columns, l.ordered)?;
            let b = self.read(&b.to_string(), &r.columns, r.ordered)?;
            Some(Expr::BinaryExpr(BinaryExpr::new(Box::new(a), op, Box::new(b))))
        });
        Pred { expr, text: text.to_string(), optional: false }
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
    fn read(&self, text: &str, cols: &[OutCol], ordered: bool) -> Option<Expr> {
        let mut fields = vec![];
        let mut lineage = HashMap::new();
        let mut count = HashMap::<&str, usize>::new();
        for c in cols {
            *count.entry(c.name.as_str()).or_default() += 1;
        }
        let names = cols.iter().filter(|c| count[c.name.as_str()] == 1).map(|c| (c.name.clone(), c));
        let positions = cols.iter().enumerate().filter(|_| ordered).map(|(i, c)| (format!("__pos_{i}"), c));
        for (name, c) in names.chain(positions) {
            let ty = match &c.lineage {
                Lineage::Exact(e) | Lineage::Bijective(e) => e.get_type(self.catalog.all.as_ref()).ok(),
                Lineage::Unknown => None,
            };
            fields.push(Field::new(&name, ty.unwrap_or(DataType::Null), true));
            lineage.insert(name, &c.lineage);
        }
        let schema = DFSchema::from_unqualified_fields(fields.into(), HashMap::new()).ok()?;
        let expr = self.catalog.state.create_logical_expr(&rewrite(text), &schema).ok()?;
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
        let context = SimplifyContext::builder().with_schema(self.catalog.all.clone()).build();
        Some(ExprSimplifier::new(context).simplify(expr.clone()).unwrap_or(expr))
    }
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

/// Replaces `from` where it starts a word.
fn replace_word(s: &str, from: &str, to: &str) -> String {
    let mut out = String::new();
    let mut rest = s;
    while let Some(i) = rest.find(from) {
        let starts_word = !rest[..i].chars().next_back().is_some_and(|c| c.is_alphanumeric() || c == '_');
        out.push_str(&rest[..i]);
        out.push_str(if starts_word { to } else { from });
        rest = &rest[i + from.len()..];
    }
    out.push_str(rest);
    out
}
