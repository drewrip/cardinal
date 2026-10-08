//! What a plan's query text says, to check and complete what its profile
//! prints.
//!
//! Engines print operators' expressions by alias (`nation`, `o_year`) and
//! sometimes name a join condition's columns after the wrong side. The query
//! itself fills the first gap and guards against the second: an alias read
//! as the expression it names, and a join condition kept only if the query
//! compares those columns.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::ops::ControlFlow;

use datafusion::sql::sqlparser::ast::{
    self, BinaryOperator, Expr, Query, SelectItem, SetExpr, TableFactor, Visit, Visitor, visit_expressions,
};
use datafusion::sql::sqlparser::dialect::DuckDbDialect;
use datafusion::sql::sqlparser::parser::Parser;

use super::Catalog;

/// Functions whose value is over many rows, not one.
const AGGREGATES: &[&str] = &[
    "sum", "avg", "count", "count_star", "min", "max", "first", "last", "any_value", "stddev", "stddev_pop",
    "stddev_samp", "variance", "var_pop", "var_samp", "median", "mode", "string_agg", "list", "array_agg",
];

/// Facts about a query's text.
#[derive(Debug, Default)]
pub struct QueryText {
    /// Row-level SELECT aliases, as their expressions with qualifiers dropped.
    aliases: HashMap<String, String>,
    /// For each column (`table.column`), its class under the query's
    /// equalities: columns compared with `=` share one.
    class: HashMap<String, usize>,
    /// Every other comparison between columns, as (left, operator, right).
    comparisons: HashSet<(String, String, String)>,
    /// Every comparison's columns, for conditions over expressions.
    compared: Vec<BTreeSet<String>>,
}

impl QueryText {
    /// Reads `sql`, with any leading `EXPLAIN (...)` dropped. `None` if it
    /// does not parse.
    pub fn parse(catalog: &Catalog, sql: &str) -> Option<QueryText> {
        let statements = Parser::parse_sql(&DuckDbDialect {}, strip_explain(sql)).ok()?;
        let mut scan = Scan::default();
        let _ = statements.visit(&mut scan);
        let tables: HashSet<&String> = scan.tables.values().collect();
        // Tables read more than once, whose columns are ambiguous without
        // knowing which instance a qualifier names.
        let mut seen = HashMap::<&String, usize>::new();
        for (alias, table) in &scan.tables {
            if alias != table {
                *seen.entry(table).or_default() += 1;
            }
        }
        // Aliases of a plain column, which comparisons may use in its place.
        let renamed: HashMap<String, &Expr> = scan
            .aliases
            .iter()
            .filter(|(_, e)| matches!(e, Expr::Identifier(_) | Expr::CompoundIdentifier(_)))
            .map(|(a, e)| (a.clone(), e))
            .collect();
        let column = |e: &Expr| -> Option<String> {
            let (qualifier, name) = match e {
                Expr::Identifier(i) => (None, i.value.to_lowercase()),
                Expr::CompoundIdentifier(parts) if parts.len() >= 2 => {
                    let n = parts.len();
                    (Some(parts[n - 2].value.to_lowercase()), parts[n - 1].value.to_lowercase())
                }
                _ => return None,
            };
            // A qualifier naming a CTE or subquery says nothing of the table.
            let qualified = qualifier.and_then(|q| scan.tables.get(&q)).filter(|t| catalog.has_column(t, &name));
            let table = match qualified {
                Some(t) => t.clone(),
                None => {
                    let mut having = tables.iter().filter(|t| catalog.has_column(t, &name));
                    match (having.next(), having.next()) {
                        (Some(t), None) => (*t).clone(),
                        _ => return None,
                    }
                }
            };
            catalog.has_column(&table, &name).then(|| format!("{table}.{name}"))
        };
        let resolve = |e: &Expr| -> Option<String> {
            column(e).or_else(|| match e {
                Expr::Identifier(i) => renamed.get(&i.value.to_lowercase()).and_then(|e| column(e)),
                _ => None,
            })
        };

        let mut q = QueryText::default();
        let mut classes = UnionFind::default();
        for (l, op, r) in &scan.comparisons {
            let columns = |e: &Expr| {
                let mut out = BTreeSet::new();
                let _ = visit_expressions(e, |e| {
                    if let Some(c) = resolve(e) {
                        out.insert(c);
                    }
                    ControlFlow::<()>::Continue(())
                });
                out
            };
            q.compared.push(columns(l).union(&columns(r)).cloned().collect());
            let (Some(a), Some(b)) = (resolve(l), resolve(r)) else { continue };
            match op {
                BinaryOperator::Eq => classes.union(&a, &b),
                op => {
                    let op = op.to_string();
                    q.comparisons.insert((a, op, b));
                }
            }
        }
        q.class = classes.classes();

        let mut bound = HashMap::<String, HashSet<String>>::new();
        for (alias, e) in &scan.aliases {
            if !row_level(e) {
                bound.entry(alias.clone()).or_default().insert(String::new());
                continue;
            }
            let mut ambiguous = false;
            let _ = visit_expressions(e, |c| {
                if let Expr::CompoundIdentifier(parts) = c
                    && parts.len() >= 2
                    && scan.tables.get(&parts[parts.len() - 2].value.to_lowercase()).is_some_and(|t| seen.get(t).copied().unwrap_or(0) > 1)
                {
                    ambiguous = true;
                }
                ControlFlow::<()>::Continue(())
            });
            let text = if ambiguous { String::new() } else { unqualified(e) };
            bound.entry(alias.clone()).or_default().insert(text);
        }
        q.aliases = bound
            .into_iter()
            .filter_map(|(alias, exprs)| match exprs.into_iter().collect::<Vec<_>>()[..] {
                [ref e] if !e.is_empty() => Some((alias, e.clone())),
                _ => None,
            })
            .collect();
        Some(q)
    }

    /// The expression `alias` names, if it names one row-level expression.
    pub fn alias(&self, alias: &str) -> Option<&str> {
        self.aliases.get(&alias.to_lowercase()).map(String::as_str)
    }

    /// Whether the query compares base columns `a` and `b` (`table.column`)
    /// with `op`: for an equality, whether they are equal under its
    /// equalities, which engines extend transitively.
    pub fn compares(&self, a: &str, op: &str, b: &str) -> bool {
        match op {
            "=" | "IS NOT DISTINCT FROM" => a == b || self.class.get(a).is_some_and(|c| self.class.get(b) == Some(c)),
            op => {
                let mirror = mirror(op);
                self.comparisons.contains(&(a.into(), op.into(), b.into()))
                    || mirror.is_some_and(|m| self.comparisons.contains(&(b.into(), m.into(), a.into())))
            }
        }
    }

    /// Whether some comparison in the query reads every column in `columns`.
    pub fn relates(&self, columns: &BTreeSet<String>) -> bool {
        self.compared.iter().any(|c| columns.is_subset(c))
    }
}

fn mirror(op: &str) -> Option<&'static str> {
    Some(match op {
        "<" => ">",
        ">" => "<",
        "<=" => ">=",
        ">=" => "<=",
        "<>" | "!=" => "<>",
        _ => return None,
    })
}

fn strip_explain(sql: &str) -> &str {
    let s = sql.trim_start();
    if !s.get(..7).is_some_and(|p| p.eq_ignore_ascii_case("explain")) {
        return s;
    }
    let rest = s[7..].trim_start();
    match rest.strip_prefix('(') {
        Some(r) => r.split_once(')').map_or(rest, |(_, q)| q),
        None => rest,
    }
}

/// Whether `e` is a value of one row: no aggregate, window or subquery.
fn row_level(e: &Expr) -> bool {
    let mut ok = true;
    let _ = visit_expressions(e, |e| {
        match e {
            Expr::Function(f) => {
                let name = f.name.to_string().to_lowercase();
                if f.over.is_some() || AGGREGATES.contains(&name.as_str()) {
                    ok = false;
                }
            }
            Expr::Subquery(_) | Expr::Exists { .. } | Expr::InSubquery { .. } => ok = false,
            _ => {}
        }
        ControlFlow::<()>::Continue(())
    });
    ok
}

/// `e` with column qualifiers dropped.
fn unqualified(e: &Expr) -> String {
    let mut e = e.clone();
    let _ = ast::visit_expressions_mut(&mut e, |e| {
        if let Expr::CompoundIdentifier(parts) = e {
            *e = Expr::Identifier(parts.last().unwrap().clone());
        }
        ControlFlow::<()>::Continue(())
    });
    e.to_string()
}

/// Walks a query for its tables, aliases and comparisons.
#[derive(Default)]
struct Scan {
    /// Table alias (or name) → table, lowercased.
    tables: HashMap<String, String>,
    aliases: Vec<(String, Expr)>,
    comparisons: Vec<(Expr, BinaryOperator, Expr)>,
}

impl Visitor for Scan {
    type Break = ();

    fn pre_visit_query(&mut self, query: &Query) -> ControlFlow<()> {
        fn selects<'a>(s: &'a SetExpr, out: &mut Vec<&'a ast::Select>) {
            match s {
                SetExpr::Select(s) => out.push(s),
                SetExpr::SetOperation { left, right, .. } => {
                    selects(left, out);
                    selects(right, out);
                }
                _ => {}
            }
        }
        let mut found = vec![];
        selects(&query.body, &mut found);
        for s in found {
            for item in &s.projection {
                if let SelectItem::ExprWithAlias { expr, alias } = item {
                    self.aliases.push((alias.value.to_lowercase(), expr.clone()));
                }
            }
        }
        // `WITH t (a, b) AS (SELECT x, y ...)` names x and y.
        for cte in query.with.iter().flat_map(|w| &w.cte_tables) {
            let mut body = vec![];
            selects(&cte.query.body, &mut body);
            if let [s] = body[..] {
                for (name, item) in cte.alias.columns.iter().zip(&s.projection) {
                    if let SelectItem::UnnamedExpr(e) | SelectItem::ExprWithAlias { expr: e, .. } = item {
                        self.aliases.push((name.name.value.to_lowercase(), e.clone()));
                    }
                }
            }
        }
        ControlFlow::Continue(())
    }

    fn pre_visit_table_factor(&mut self, factor: &TableFactor) -> ControlFlow<()> {
        if let TableFactor::Table { name, alias, .. } = factor {
            let table = name.0.last().map(|p| p.to_string().to_lowercase()).unwrap_or_default();
            self.tables.insert(table.clone(), table.clone());
            if let Some(a) = alias {
                self.tables.insert(a.name.value.to_lowercase(), table);
            }
        }
        ControlFlow::Continue(())
    }

    fn pre_visit_expr(&mut self, e: &Expr) -> ControlFlow<()> {
        match e {
            Expr::BinaryOp { left, op, right } if is_comparison(op) => {
                self.comparisons.push((*left.clone(), op.clone(), *right.clone()));
            }
            Expr::IsNotDistinctFrom(l, r) => self.comparisons.push((*l.clone(), BinaryOperator::Eq, *r.clone())),
            Expr::InSubquery { expr, subquery, .. } => {
                // `x IN (SELECT y ...)` compares x with y.
                if let SetExpr::Select(s) = subquery.body.as_ref()
                    && let [SelectItem::UnnamedExpr(y) | SelectItem::ExprWithAlias { expr: y, .. }] = &s.projection[..]
                {
                    self.comparisons.push((*expr.clone(), BinaryOperator::Eq, y.clone()));
                }
            }
            _ => {}
        }
        ControlFlow::Continue(())
    }
}

fn is_comparison(op: &BinaryOperator) -> bool {
    use BinaryOperator as B;
    matches!(op, B::Eq | B::NotEq | B::Lt | B::LtEq | B::Gt | B::GtEq)
}

#[derive(Default)]
struct UnionFind {
    ids: HashMap<String, usize>,
    parent: Vec<usize>,
}

impl UnionFind {
    fn id(&mut self, k: &str) -> usize {
        if let Some(&i) = self.ids.get(k) {
            return i;
        }
        let i = self.parent.len();
        self.parent.push(i);
        self.ids.insert(k.to_string(), i);
        i
    }

    fn find(&mut self, mut i: usize) -> usize {
        while self.parent[i] != i {
            self.parent[i] = self.parent[self.parent[i]];
            i = self.parent[i];
        }
        i
    }

    fn union(&mut self, a: &str, b: &str) {
        let (a, b) = (self.id(a), self.id(b));
        let (a, b) = (self.find(a), self.find(b));
        self.parent[a] = b;
    }

    fn classes(mut self) -> HashMap<String, usize> {
        let keys: Vec<(String, usize)> = self.ids.iter().map(|(k, &i)| (k.clone(), i)).collect();
        keys.into_iter().map(|(k, i)| (k, self.find(i))).collect()
    }
}
