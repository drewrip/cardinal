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
use datafusion::sql::sqlparser::dialect::{Dialect, DuckDbDialect};
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
    /// Each `LIMIT` (or `FETCH`) clause's row count, `None` if not a
    /// constant (`LIMIT ALL`, an expression, a percentage).
    limits: Vec<Option<u64>>,
    /// The rows each of those clauses skips first (its `OFFSET`), `None` if
    /// not a constant.
    offsets: Vec<Option<u64>>,
    /// Each alias of a table the query reads more than once: the table, and
    /// the columns of tables read once its columns equal, as (its column,
    /// `table.column`). What tells its instance in a plan apart.
    twice: HashMap<String, (String, BTreeSet<(String, String)>)>,
    /// Expressions that read an alias in `twice`, by their text without
    /// qualifiers, which is how an engine prints them.
    qualified: Vec<(String, Expr)>,
    /// SELECT aliases of such expressions.
    qualified_aliases: HashMap<String, Vec<Expr>>,
    /// SELECT aliases of window functions, as [`QueryText::window_text`]
    /// writes them.
    windows: HashMap<String, BTreeSet<String>>,
    /// For each base column, the least column equal to it on every row the
    /// query keeps: by an equality of a `WHERE` or an inner join's condition,
    /// not an outer join's, which pads rows where it does not hold.
    inner: HashMap<String, String>,
    /// Every comparison the query makes between base columns, as (column,
    /// operator, column), each column as `inner` names it.
    direct: HashSet<(String, String, String)>,
    /// The column names of each CTE and derived table, in order, by its
    /// name: of those every relation so named agrees on.
    relations: HashMap<String, Vec<String>>,
    /// Whether some `SELECT` is `DISTINCT ON`.
    distinct_on: bool,
    /// Every window function the query calls.
    window_functions: Vec<Expr>,
}

impl QueryText {
    /// Reads `sql`, with any leading `EXPLAIN (...)` dropped. `None` if it
    /// does not parse.
    pub fn parse(catalog: &Catalog, sql: &str) -> Option<QueryText> {
        QueryText::parse_in(catalog, sql, &DuckDbDialect {})
    }

    /// [`QueryText::parse`], for a query in `dialect`.
    pub fn parse_in(catalog: &Catalog, sql: &str, dialect: &dyn Dialect) -> Option<QueryText> {
        let statements = Parser::parse_sql(dialect, strip_explain(sql)).ok()?;
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

        let mut q = QueryText {
            limits: scan.limits.clone(),
            offsets: scan.offsets.clone(),
            distinct_on: scan.distinct_on,
            ..Default::default()
        };
        for e in &scan.exprs {
            if matches!(e, Expr::Function(f) if f.over.is_some()) && !q.window_functions.contains(e) {
                q.window_functions.push(e.clone());
            }
        }
        // Aliases of tables read more than once, and their equalities with
        // columns of tables read once.
        for (alias, table) in &scan.tables {
            if alias != table && seen.get(table).copied().unwrap_or(0) > 1 {
                q.twice.insert(alias.clone(), (table.clone(), BTreeSet::new()));
            }
        }
        let twice_column = |e: &Expr| match e {
            Expr::CompoundIdentifier(parts) if parts.len() >= 2 => {
                let alias = parts[parts.len() - 2].value.to_lowercase();
                q.twice.contains_key(&alias).then(|| (alias, parts[parts.len() - 1].value.to_lowercase()))
            }
            _ => None,
        };
        let mut signatures: Vec<(String, (String, String))> = vec![];
        for (l, op, r) in &scan.comparisons {
            if *op != BinaryOperator::Eq {
                continue;
            }
            for (own, other) in [(l, r), (r, l)] {
                let (Some((alias, c)), Some(o)) = (twice_column(own), column(other)) else { continue };
                let once = o.split_once('.').is_some_and(|(t, _)| seen.get(&t.to_string()).copied().unwrap_or(0) <= 1);
                if once && twice_column(other).is_none() {
                    signatures.push((alias, (c, o)));
                }
            }
        }
        let reads_twice = |e: &Expr| {
            let mut found = false;
            let _ = visit_expressions(e, |x| {
                found |= twice_column(x).is_some();
                ControlFlow::<()>::Continue(())
            });
            found
        };
        let qualified: Vec<(String, Expr)> =
            scan.exprs.iter().filter(|e| reads_twice(e)).map(|e| (plain(e), unnested(e).clone())).collect();
        let mut qualified_aliases = HashMap::<String, Vec<Expr>>::new();
        for (alias, e) in &scan.aliases {
            if row_level(e) && reads_twice(e) {
                qualified_aliases.entry(alias.clone()).or_default().push(e.clone());
            }
        }
        for (alias, pair) in signatures {
            q.twice.get_mut(&alias).unwrap().1.insert(pair);
        }
        q.qualified = qualified;
        q.qualified_aliases = qualified_aliases;
        for (alias, e) in &scan.aliases {
            if let Expr::Function(f) = e
                && f.over.is_some()
            {
                q.windows.entry(alias.clone()).or_default().insert(window(e));
            }
        }
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
        // The same comparisons, each name resolved in its own scope: through
        // derived tables and CTEs, and `USING` joins.
        let mut scoped = Scoped::new(catalog);
        for st in &statements {
            if let ast::Statement::Query(query) = st {
                scoped.query(query);
            }
        }
        let mut inner = UnionFind::default();
        for c in &scoped.comparisons {
            if c.op == BinaryOperator::Eq && !c.outer {
                inner.union(&c.a, &c.b);
            }
        }
        let inner = inner.classes();
        let mut least: HashMap<usize, String> = HashMap::new();
        for (c, k) in &inner {
            let l = least.entry(*k).or_insert_with(|| c.clone());
            if c < l {
                *l = c.clone();
            }
        }
        q.inner = inner.iter().map(|(c, k)| (c.clone(), least[k].clone())).collect();
        for c in &scoped.comparisons {
            let rep = |x: &String| q.inner.get(x).cloned().unwrap_or_else(|| x.clone());
            let op = c.op.to_string();
            q.direct.insert((rep(&c.a), op.clone(), rep(&c.b)));
            if let Some(m) = mirror(&op).or((op == "=").then_some("=")) {
                q.direct.insert((rep(&c.b), m.to_string(), rep(&c.a)));
            }
        }
        for c in scoped.comparisons {
            match c.op {
                BinaryOperator::Eq => classes.union(&c.a, &c.b),
                op => {
                    q.comparisons.insert((c.a, op.to_string(), c.b));
                }
            }
        }
        q.compared.extend(scoped.compared);
        q.class = classes.classes();
        q.relations = scoped
            .named
            .into_iter()
            .filter_map(|(name, mut columns)| {
                let first = columns.pop()?;
                columns.iter().all(|c| *c == first).then_some((name, first))
            })
            .collect();

        let mut bound = HashMap::<String, HashSet<String>>::new();
        for (alias, e) in &scan.aliases {
            // An alias of an aggregate's value (`round(avg(score), 3)`)
            // reads above the aggregate, where `avg(score)` is a column: the
            // reader takes no aggregate it would compute itself.
            if !per_row(e) {
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

    /// Each alias of a table read more than once: its table, and the
    /// columns of tables read once that its columns equal, as (its column,
    /// `table.column`).
    pub fn twice(&self) -> &HashMap<String, (String, BTreeSet<(String, String)>)> {
        &self.twice
    }

    /// The query's expression that an engine printed as `printed`, without
    /// qualifiers, if it reads a table read more than once: so its columns
    /// are the aliases'. `None` unless exactly one reads so.
    pub fn qualified(&self, printed: &str) -> Option<&Expr> {
        let printed = Parser::new(&DuckDbDialect {}).try_with_sql(printed).and_then(|mut p| p.parse_expr()).ok()?;
        let printed = plain(&printed);
        unique(self.qualified.iter().filter(|(p, _)| *p == printed).map(|(_, e)| e))
    }

    /// The expression a SELECT alias names, if it reads a table read more
    /// than once, and the alias names one expression.
    pub fn qualified_alias(&self, alias: &str) -> Option<&Expr> {
        unique(self.qualified_aliases.get(&alias.to_lowercase())?.iter())
    }

    /// The window function a SELECT alias names, as [`QueryText::window_text`]
    /// writes it, if it names one.
    pub fn window_alias(&self, alias: &str) -> Option<&str> {
        match self.windows.get(&alias.to_lowercase())?.iter().collect::<Vec<_>>()[..] {
            [w] => Some(w.as_str()),
            _ => None,
        }
    }

    /// Every SELECT alias of a window function.
    pub fn window_aliases(&self) -> impl Iterator<Item = &str> {
        self.windows.keys().map(String::as_str)
    }

    /// A window function, as DuckDB prints it or as a query writes it, in
    /// one form: DuckDB's default orders (`ASC`, `NULLS LAST`) written out,
    /// without qualifiers, parentheses or case in names.
    pub fn window_text(text: &str) -> Option<String> {
        let e = Parser::new(&DuckDbDialect {}).try_with_sql(text).and_then(|mut p| p.parse_expr()).ok()?;
        matches!(&e, Expr::Function(f) if f.over.is_some()).then(|| window(&e))
    }

    /// The column names of the CTE or derived table `name`, in order, if
    /// every relation the query so names has the same.
    pub fn relation_columns(&self, name: &str) -> Option<&[String]> {
        self.relations.get(&name.to_lowercase()).map(Vec::as_slice)
    }

    /// The definition (`PARTITION BY ... ORDER BY ...`) of the window the
    /// query's one call of the window function `call` (`row_number()`) runs
    /// over, if it calls one so, and defines its window there.
    pub fn window_of(&self, call: &Expr) -> Option<ast::WindowSpec> {
        let call = plain(call).to_lowercase();
        let mut found = self.window_functions.iter().filter_map(|e| {
            let Expr::Function(f) = e else { return None };
            let Some(ast::WindowType::WindowSpec(spec)) = &f.over else { return None };
            let mut bare = f.clone();
            bare.over = None;
            (plain(&Expr::Function(bare)).to_lowercase() == call && spec.window_name.is_none()).then_some(spec)
        });
        match (found.next(), found.next()) {
            (Some(spec), None) => Some(spec.clone()),
            _ => None,
        }
    }

    /// Whether some `SELECT` of the query is `DISTINCT ON`.
    pub fn distinct_on(&self) -> bool {
        self.distinct_on
    }

    /// The query's `LIMIT` (and `FETCH`) clauses: each one's row count, or
    /// `None` for one that is not a constant.
    pub fn limits(&self) -> &[Option<u64>] {
        &self.limits
    }

    /// The rows each clause of [`QueryText::limits`] skips first: its
    /// `OFFSET`, 0 without one, or `None` for one that is not a constant.
    pub fn offsets(&self) -> &[Option<u64>] {
        &self.offsets
    }

    /// Whether the query itself compares base columns `a` and `b` with
    /// `op`, columns its equalities make equal on every row counted as one;
    /// not by the transitivity of its equalities.
    pub fn directly_compares(&self, a: &str, op: &str, b: &str) -> bool {
        let rep = |x: &str| self.inner.get(x).cloned().unwrap_or_else(|| x.to_string());
        let op = if op == "IS NOT DISTINCT FROM" { "=" } else { op };
        self.direct.contains(&(rep(a), op.to_string(), rep(b)))
    }

    /// Whether some comparison in the query reads every column in `columns`.
    pub fn relates(&self, columns: &BTreeSet<String>) -> bool {
        self.compared.iter().any(|c| columns.is_subset(c))
    }
}

/// The one expression `exprs` holds, however often.
fn unique<'e>(exprs: impl Iterator<Item = &'e Expr>) -> Option<&'e Expr> {
    let mut found: Option<&Expr> = None;
    for e in exprs {
        match found {
            Some(f) if f != e => return None,
            _ => found = Some(e),
        }
    }
    found
}

/// Window function `e` as [`QueryText::window_text`] writes it.
fn window(e: &Expr) -> String {
    let mut e = e.clone();
    let _ = ast::visit_expressions_mut(&mut e, |e| {
        if let Expr::Function(f) = e {
            f.name = ast::ObjectName::from(vec![ast::Ident::new(f.name.to_string().to_lowercase())]);
            if let Some(ast::WindowType::WindowSpec(spec)) = &mut f.over {
                for o in &mut spec.order_by {
                    o.options.asc.get_or_insert(true);
                    o.options.nulls_first.get_or_insert(false);
                }
            }
        }
        ControlFlow::<()>::Continue(())
    });
    plain(&e)
}

/// `e` without the parentheses around it.
fn unnested(mut e: &Expr) -> &Expr {
    while let Expr::Nested(inner) = e {
        e = inner;
    }
    e
}

/// `e` as an engine prints it, compared: without qualifiers, parentheses or
/// case in names.
pub(super) fn plain(e: &Expr) -> String {
    let mut e = e.clone();
    let _ = ast::visit_expressions_mut(&mut e, |e| {
        match e {
            Expr::Nested(inner) => *e = *inner.clone(),
            Expr::CompoundIdentifier(parts) => *e = Expr::Identifier(ast::Ident::new(parts.last().unwrap().value.to_lowercase())),
            Expr::Identifier(i) => i.value = i.value.to_lowercase(),
            _ => {}
        }
        ControlFlow::<()>::Continue(())
    });
    e.to_string()
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

/// Whether `e` is a value of one row of its input: no window or subquery.
fn per_row(e: &Expr) -> bool {
    let mut ok = true;
    let _ = visit_expressions(e, |e| {
        match e {
            Expr::Function(f) if f.over.is_some() => ok = false,
            Expr::Subquery(_) | Expr::Exists { .. } | Expr::InSubquery { .. } => ok = false,
            _ => {}
        }
        ControlFlow::<()>::Continue(())
    });
    ok
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
    limits: Vec<Option<u64>>,
    offsets: Vec<Option<u64>>,
    distinct_on: bool,
    /// Every expression.
    exprs: Vec<Expr>,
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
        let count = |e: &Expr| match e {
            Expr::Value(v) => match &v.value {
                ast::Value::Number(n, _) => n.parse::<u64>().ok(),
                _ => None,
            },
            _ => None,
        };
        let skipped = |offset: &Option<ast::Offset>| offset.as_ref().map_or(Some(0), |o| count(&o.value));
        match &query.limit_clause {
            Some(ast::LimitClause::LimitOffset { limit: Some(l), limit_by, offset }) if limit_by.is_empty() => {
                self.limits.push(count(l));
                self.offsets.push(skipped(offset));
            }
            // `LIMIT ALL`, with only an offset, keeps every row after it.
            Some(ast::LimitClause::LimitOffset { limit: None, limit_by, .. }) if limit_by.is_empty() => {}
            Some(ast::LimitClause::OffsetCommaLimit { limit, offset }) => {
                self.limits.push(count(limit));
                self.offsets.push(count(offset));
            }
            Some(_) => {
                self.limits.push(None);
                self.offsets.push(None);
            }
            None => {}
        }
        if let Some(f) = &query.fetch {
            self.limits.push(f.quantity.as_ref().filter(|_| !f.percent && !f.with_ties).and_then(count));
            // `OFFSET k FETCH FIRST n ROWS ONLY`.
            self.offsets.push(match &query.limit_clause {
                Some(ast::LimitClause::LimitOffset { limit: None, offset, .. }) => skipped(offset),
                None => Some(0),
                Some(_) => None,
            });
        }
        let mut found = vec![];
        selects(&query.body, &mut found);
        for s in found {
            self.distinct_on |= matches!(s.distinct, Some(ast::Distinct::On(_)));
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
        self.exprs.push(e.clone());
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

/// A relation a query reads, as a scope sees it: its output columns by
/// name, each the base column (`table.column`) it is, if one.
#[derive(Debug, Clone, Default)]
struct Rel {
    columns: Vec<(String, Option<String>)>,
    /// Whether it has columns not listed: those of a relation whose columns
    /// are not known, which a `*` reads.
    open: bool,
}

impl Rel {
    /// Column `name`'s base column: `None` if there is no such column,
    /// `Some(None)` if it is no one base column.
    fn get(&self, name: &str) -> Option<Option<String>> {
        let mut found = self.columns.iter().filter(|(n, _)| n == name).map(|(_, l)| l);
        let first = found.next()?.clone();
        // A name repeated (as `SELECT *` over a join `USING` it does) is one
        // column only if every one is the same.
        Some(match found.all(|l| *l == first) {
            true => first,
            false => None,
        })
    }
}

/// A relation in a `FROM`: its name, its columns, and the names a `USING`
/// merged into another relation's column, which name that one unqualified.
#[derive(Debug, Clone)]
struct InScope {
    name: String,
    rel: Rel,
    hidden: HashSet<String>,
}

/// A comparison between base columns, and whether an outer join's condition
/// makes it, which leaves rows where it does not hold.
#[derive(Debug, Clone)]
struct Comparison {
    a: String,
    op: BinaryOperator,
    b: String,
    outer: bool,
}

/// Reads a query's comparisons with each name resolved in its own scope:
/// through derived tables, CTEs and subqueries to the base columns they
/// are, and with `JOIN ... USING (c)` as the equality it is. A view's query
/// inlined (each view read as its definition) reads all the way to the
/// stored tables an engine's plan reads.
struct Scoped<'a> {
    catalog: &'a Catalog,
    /// The CTEs in scope, innermost last.
    ctes: Vec<HashMap<String, Rel>>,
    /// The relations of each enclosing `FROM`, innermost last, for
    /// correlated references.
    scopes: Vec<Vec<InScope>>,
    comparisons: Vec<Comparison>,
    /// The base columns each comparison reads.
    compared: Vec<BTreeSet<String>>,
    /// The column names of every CTE and derived table, by its name.
    named: HashMap<String, Vec<Vec<String>>>,
}

impl<'a> Scoped<'a> {
    fn new(catalog: &'a Catalog) -> Self {
        Scoped { catalog, ctes: vec![], scopes: vec![], comparisons: vec![], compared: vec![], named: HashMap::new() }
    }

    /// Notes the columns of the CTE or derived table `name`: none, so that
    /// it has no known list, if not all are known.
    fn name(&mut self, name: &str, rel: &Rel) {
        let columns = if rel.open { vec![] } else { rel.columns.iter().map(|(n, _)| n.clone()).collect() };
        self.named.entry(name.to_string()).or_default().push(columns);
    }

    fn query(&mut self, q: &Query) -> Rel {
        self.ctes.push(HashMap::new());
        for cte in q.with.iter().flat_map(|w| &w.cte_tables) {
            let rel = renamed(self.query(&cte.query), &cte.alias);
            self.name(&cte.alias.name.value.to_lowercase(), &rel);
            self.ctes.last_mut().unwrap().insert(cte.alias.name.value.to_lowercase(), rel);
        }
        let rel = self.set_expr(&q.body);
        self.ctes.pop();
        rel
    }

    fn set_expr(&mut self, s: &SetExpr) -> Rel {
        match s {
            SetExpr::Select(s) => self.select(s),
            SetExpr::Query(q) => self.query(q),
            // A set operation's columns are named as its first input's, and
            // are each several inputs' columns.
            SetExpr::SetOperation { left, right, .. } => {
                let l = self.set_expr(left);
                self.set_expr(right);
                Rel { columns: l.columns.into_iter().map(|(n, _)| (n, None)).collect(), open: l.open }
            }
            _ => Rel { columns: vec![], open: true },
        }
    }

    fn select(&mut self, s: &ast::Select) -> Rel {
        let mut scope: Vec<InScope> = vec![];
        let mut on: Vec<(&Expr, bool)> = vec![];
        for twj in &s.from {
            self.from(twj, &mut scope, &mut on);
        }
        self.scopes.push(scope);
        for (e, outer) in on {
            self.expr(e, outer);
        }
        let mut exprs: Vec<&Expr> = s.selection.iter().chain(&s.having).chain(&s.qualify).collect();
        for item in &s.projection {
            if let SelectItem::UnnamedExpr(e) | SelectItem::ExprWithAlias { expr: e, .. } = item {
                exprs.push(e);
            }
        }
        for e in exprs {
            self.expr(e, false);
        }
        let mut columns = vec![];
        let mut open = false;
        for item in &s.projection {
            match item {
                SelectItem::UnnamedExpr(e) => {
                    let name = match e {
                        Expr::Identifier(i) => i.value.to_lowercase(),
                        Expr::CompoundIdentifier(p) => p.last().unwrap().value.to_lowercase(),
                        e => e.to_string().to_lowercase(),
                    };
                    columns.push((name, self.resolve(e)));
                }
                SelectItem::ExprWithAlias { expr, alias } => columns.push((alias.value.to_lowercase(), self.resolve(expr))),
                // A `USING` column once, as the relation it names.
                SelectItem::Wildcard(_) => {
                    for r in self.scopes.last().unwrap() {
                        open |= r.rel.open;
                        columns.extend(r.rel.columns.iter().filter(|(n, _)| !r.hidden.contains(n)).cloned());
                    }
                }
                SelectItem::QualifiedWildcard(ast::SelectItemQualifiedWildcardKind::ObjectName(n), _) => {
                    let q = n.0.last().map(|p| p.to_string().trim_matches('"').to_lowercase()).unwrap_or_default();
                    let mut found = false;
                    for r in self.scopes.last().unwrap() {
                        if r.name == q {
                            found = true;
                            open |= r.rel.open;
                            columns.extend(r.rel.columns.iter().cloned());
                        }
                    }
                    open |= !found;
                }
                _ => open = true,
            }
        }
        self.scopes.pop();
        Rel { columns, open }
    }

    /// Adds the relations of `twj` to `scope`, its `ON` conditions to `on`
    /// (with whether an outer join's), and its `USING` columns' equalities
    /// to the comparisons.
    fn from<'q>(&mut self, twj: &'q ast::TableWithJoins, scope: &mut Vec<InScope>, on: &mut Vec<(&'q Expr, bool)>) {
        use ast::JoinOperator as J;
        self.factor(&twj.relation, scope, on);
        for j in &twj.joins {
            let before = scope.len();
            self.factor(&j.relation, scope, on);
            // Which sides an outer join pads, and its condition.
            let (constraint, pads_left, pads_right) = match &j.join_operator {
                J::Join(c) | J::Inner(c) | J::Semi(c) | J::LeftSemi(c) | J::RightSemi(c) | J::Anti(c) | J::LeftAnti(c) | J::RightAnti(c) => {
                    (Some(c), false, false)
                }
                J::Left(c) | J::LeftOuter(c) => (Some(c), false, true),
                J::Right(c) | J::RightOuter(c) => (Some(c), true, false),
                J::FullOuter(c) => (Some(c), true, true),
                _ => (None, false, false),
            };
            let outer = pads_left || pads_right;
            match constraint {
                Some(ast::JoinConstraint::On(e)) => on.push((e, outer)),
                Some(ast::JoinConstraint::Using(cols)) => {
                    for c in cols {
                        let c = c.0.last().map(|p| p.to_string().trim_matches('"').to_lowercase()).unwrap_or_default();
                        let visible = |r: &InScope| !r.hidden.contains(&c);
                        let lefts: Vec<String> = scope[..before].iter().filter(|r| visible(r)).filter_map(|r| r.rel.get(&c).flatten()).collect();
                        let rights: Vec<String> = scope[before..].iter().filter(|r| visible(r)).filter_map(|r| r.rel.get(&c).flatten()).collect();
                        for l in &lefts {
                            for r in &rights {
                                self.comparisons.push(Comparison { a: l.clone(), op: BinaryOperator::Eq, b: r.clone(), outer });
                                self.compared.push([l.clone(), r.clone()].into());
                            }
                        }
                        // The merged column is the side never padded's (either
                        // of an inner join's): the other's name now names it.
                        let hide = match (pads_left, pads_right) {
                            (true, false) => 0..before,
                            (_, true) if !pads_left => before..scope.len(),
                            (false, false) => before..scope.len(),
                            _ => 0..0,
                        };
                        for r in &mut scope[hide] {
                            r.hidden.insert(c.clone());
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn factor<'q>(&mut self, f: &'q TableFactor, scope: &mut Vec<InScope>, on: &mut Vec<(&'q Expr, bool)>) {
        let entry = |name: String, rel: Rel| InScope { name, rel, hidden: HashSet::new() };
        match f {
            TableFactor::Table { name, alias, .. } => {
                let table = name.0.last().map(|p| p.to_string().trim_matches('"').to_lowercase()).unwrap_or_default();
                let cte = self.ctes.iter().rev().find_map(|c| c.get(&table)).cloned();
                let rel = match (cte, self.catalog.columns(&table)) {
                    (Some(rel), _) => rel,
                    (None, Some(cols)) => Rel {
                        columns: cols.into_iter().map(|c| (c.to_lowercase(), Some(format!("{table}.{}", c.to_lowercase())))).collect(),
                        open: false,
                    },
                    (None, None) => Rel { columns: vec![], open: true },
                };
                scope.push(match alias {
                    Some(a) => entry(a.name.value.to_lowercase(), renamed(rel, a)),
                    None => entry(table, rel),
                });
            }
            TableFactor::Derived { subquery, alias, .. } => {
                // A derived table sees the enclosing scopes, not its siblings.
                let rel = self.query(subquery);
                if let Some(a) = alias {
                    self.name(&a.name.value.to_lowercase(), &renamed(rel.clone(), a));
                }
                scope.push(match alias {
                    Some(a) => entry(a.name.value.to_lowercase(), renamed(rel, a)),
                    None => entry(String::new(), rel),
                });
            }
            TableFactor::NestedJoin { table_with_joins, .. } => self.from(table_with_joins, scope, on),
            // A relation whose columns are not known (a table function).
            _ => scope.push(entry(String::new(), Rel { columns: vec![], open: true })),
        }
    }

    /// The base column `e` is, in the innermost scope that names it.
    fn resolve(&self, e: &Expr) -> Option<String> {
        let (qualifier, name) = match e {
            Expr::Nested(e) => return self.resolve(e),
            Expr::Identifier(i) => (None, i.value.to_lowercase()),
            Expr::CompoundIdentifier(p) if p.len() >= 2 => {
                (Some(p[p.len() - 2].value.to_lowercase()), p[p.len() - 1].value.to_lowercase())
            }
            _ => return None,
        };
        for scope in self.scopes.iter().rev() {
            let named: Vec<Option<String>> = scope
                .iter()
                .filter(|r| match &qualifier {
                    Some(q) => *q == r.name,
                    None => !r.hidden.contains(&name),
                })
                .filter_map(|r| r.rel.get(&name))
                .collect();
            match &named[..] {
                [] => continue,
                [only] => return only.clone(),
                // Several relations with the column: the same one only if
                // all are, else ambiguous.
                [first, rest @ ..] => return rest.iter().all(|l| l == first).then(|| first.clone()).flatten(),
            }
        }
        None
    }

    /// Records the comparisons `e` makes in the current scope (`outer` if
    /// an outer join's condition), and reads its subqueries in theirs.
    fn expr(&mut self, e: &Expr, outer: bool) {
        #[derive(Default)]
        struct Local {
            depth: usize,
            comparisons: Vec<(Expr, BinaryOperator, Expr)>,
            subqueries: Vec<Query>,
            in_subqueries: Vec<(Expr, Query)>,
        }
        impl Visitor for Local {
            type Break = ();
            fn pre_visit_query(&mut self, _: &Query) -> ControlFlow<()> {
                self.depth += 1;
                ControlFlow::Continue(())
            }
            fn post_visit_query(&mut self, _: &Query) -> ControlFlow<()> {
                self.depth -= 1;
                ControlFlow::Continue(())
            }
            fn pre_visit_expr(&mut self, e: &Expr) -> ControlFlow<()> {
                if self.depth > 0 {
                    return ControlFlow::Continue(());
                }
                match e {
                    Expr::BinaryOp { left, op, right } if is_comparison(op) => {
                        self.comparisons.push((*left.clone(), op.clone(), *right.clone()))
                    }
                    Expr::IsNotDistinctFrom(l, r) => self.comparisons.push((*l.clone(), BinaryOperator::Eq, *r.clone())),
                    Expr::InSubquery { expr, subquery, .. } => self.in_subqueries.push((*expr.clone(), *subquery.clone())),
                    Expr::Subquery(q) | Expr::Exists { subquery: q, .. } => self.subqueries.push(*q.clone()),
                    _ => {}
                }
                ControlFlow::Continue(())
            }
        }
        let mut local = Local::default();
        let _ = e.visit(&mut local);
        for (l, op, r) in local.comparisons {
            let columns = |side: &Expr| {
                let mut out = BTreeSet::new();
                let _ = visit_expressions(side, |x| {
                    if let Some(c) = self.resolve(x) {
                        out.insert(c);
                    }
                    ControlFlow::<()>::Continue(())
                });
                out
            };
            self.compared.push(columns(&l).union(&columns(&r)).cloned().collect());
            if let (Some(a), Some(b)) = (self.resolve(&l), self.resolve(&r)) {
                self.comparisons.push(Comparison { a, op, b, outer });
            }
        }
        for q in local.subqueries {
            self.query(&q);
        }
        // `x IN (SELECT y ...)` compares x with y.
        for (x, q) in local.in_subqueries {
            let rel = self.query(&q);
            if let ([(_, Some(y))], Some(x)) = (&rel.columns[..], self.resolve(&x)) {
                self.comparisons.push(Comparison { a: x.clone(), op: BinaryOperator::Eq, b: y.clone(), outer });
                self.compared.push([x, y.clone()].into());
            }
        }
    }
}

/// `rel` with its columns renamed by `alias`'s column list, if it has one.
fn renamed(mut rel: Rel, alias: &ast::TableAlias) -> Rel {
    for (c, name) in rel.columns.iter_mut().zip(&alias.columns) {
        c.0 = name.name.value.to_lowercase();
    }
    rel
}
