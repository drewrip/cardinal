//! Queries counting what a fact counts, to check it against an engine.
//!
//! A context is written as SQL from what it means, not from how any plan
//! computed it: every table instance a subquery whose columns are named
//! `"instance.column"`, so that each is unique across the whole query, an
//! SPJ a cross product of its inputs with its predicates, a semi or anti
//! condition an `EXISTS`, and so on. A wrong rewrite into the normal form
//! names rows other than the plan's, and its count differs from the fact.
//!
//! An aggregate's value, read as `"value"."sum(x) of group[k](X)"`, is
//! computed by the GROUP BY (or aggregate) that the fact's rows draw on and
//! whose context is `group[k](X)` up to the names of its instances: its
//! query gives the value too, by the definition the [`FactSet`] recorded.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap};

use datafusion::common::Column;
use datafusion::common::tree_node::{Transformed, TreeNode};
use datafusion::logical_expr::{BinaryExpr, Expr, Operator};
use datafusion::sql::unparser::Unparser;

use super::{Context, ExistsKind, FactKind, FactSet, Term};
use crate::observed::Catalog;

/// The queries for a fact's value: a count, and for a share or a
/// uniqueness, the count it is a share of (a fact of uniqueness holds when
/// the two are equal).
#[derive(Debug, Clone)]
pub struct Counts {
    pub value: String,
    pub of: Option<String>,
}

impl FactKind {
    /// Queries counting this fact's value, with tables' columns from
    /// `catalog` and aggregate values' definitions from `facts`. `None` if it
    /// reads what no query can name: a value no GROUP BY of its rows
    /// computes, a grouping key that is not a column, the first rows of a
    /// sort.
    pub fn count_sql(&self, catalog: &Catalog, facts: &FactSet) -> Option<Counts> {
        let r = Render {
            catalog,
            facts,
            wanted: wanted(self, facts),
            next: Cell::new(0),
            aliases: RefCell::new(HashMap::new()),
            computed: RefCell::new(BTreeSet::new()),
        };
        let counts = r.counts(self)?;
        // Every value read must be computed where it is read.
        let read: BTreeSet<String> = r.aliases.borrow().values().cloned().collect();
        (read.is_subset(&r.computed.borrow())).then_some(counts)
    }
}

/// Every value `kind` reads, and every value those are computed from.
fn wanted(kind: &FactKind, facts: &FactSet) -> BTreeSet<String> {
    let mut terms: Vec<&Term> = vec![];
    fn context<'a>(c: &'a Context, out: &mut Vec<&'a Term>) {
        match c {
            Context::Spj { atoms, preds, exists, .. } => {
                out.extend(preds);
                for a in atoms {
                    context(a, out);
                }
                for e in exists {
                    out.extend(&e.on);
                    context(&e.other, out);
                }
            }
            Context::Derived { args, inputs, .. } => {
                out.extend(args);
                for i in inputs {
                    context(i, out);
                }
            }
        }
    }
    match kind {
        FactKind::Cardinality(c) => context(c, &mut terms),
        FactKind::Selectivity { pred, over } => {
            terms.extend(pred);
            context(over, &mut terms);
        }
        FactKind::Match { on, kept, other } => {
            terms.extend(on);
            context(kept, &mut terms);
            context(other, &mut terms);
        }
        FactKind::Distinct { keys, over } | FactKind::Unique { keys, over } => {
            terms.extend(keys);
            context(over, &mut terms);
        }
    }
    let mut out = BTreeSet::new();
    let mut todo: Vec<String> = terms.iter().flat_map(|t| values_read(&t.expr)).collect();
    while let Some(name) = todo.pop() {
        if out.insert(name.clone())
            && let Some(v) = facts.value(&name)
        {
            todo.extend(values_read(&v.aggregate.expr));
            let mut inner = vec![];
            context(&v.over, &mut inner);
            todo.extend(inner.iter().flat_map(|t| values_read(&t.expr)));
        }
    }
    out
}

/// The names of the values `e` reads.
fn values_read(e: &Expr) -> Vec<String> {
    e.column_refs()
        .into_iter()
        .filter(|c| c.relation.as_ref().is_some_and(|r| r.table() == "value"))
        .map(|c| c.name.clone())
        .collect()
}

struct Render<'a> {
    catalog: &'a Catalog,
    facts: &'a FactSet,
    /// The values the fact reads, by name.
    wanted: BTreeSet<String>,
    /// The next subquery alias.
    next: Cell<usize>,
    /// Each value read, by name, with the column it reads as.
    aliases: RefCell<HashMap<String, String>>,
    /// The columns of values some GROUP BY computes.
    computed: RefCell<BTreeSet<String>>,
}

impl Render<'_> {
    /// The queries counting `kind`'s value.
    fn counts(&self, kind: &FactKind) -> Option<Counts> {
        let r = self;
        let count = |c: &Context| r.count(c);
        let distinct = |keys: &BTreeSet<Term>, over: &Context| {
            let keys = keys.iter().map(|k| r.expr(k)).collect::<Option<Vec<_>>>()?.join(", ");
            Some(format!("SELECT count(*) FROM (SELECT DISTINCT {keys} FROM {})", r.from(over)?))
        };
        Some(match kind {
            FactKind::Cardinality(c) => Counts { value: count(c)?, of: None },
            FactKind::Distinct { keys, over } => Counts { value: distinct(keys, over)?, of: None },
            FactKind::Unique { keys, over } => Counts { value: distinct(keys, over)?, of: Some(count(over)?) },
            FactKind::Selectivity { pred, over } => Counts {
                value: format!("SELECT count(*) FROM {} WHERE {}", r.from(over)?, r.conjunction(pred)?),
                of: Some(count(over)?),
            },
            FactKind::Match { on, kept, other } => Counts {
                value: format!(
                    "SELECT count(*) FROM {} WHERE EXISTS (SELECT 1 FROM {} WHERE {})",
                    r.from(kept)?,
                    r.from(other)?,
                    r.conjunction(on)?
                ),
                of: Some(count(kept)?),
            },
        })
    }

    /// A query counting the rows of `c`. An SPJ's inputs that no condition
    /// relates are counted apart, their counts multiplied: a cross product
    /// of large tables is not enumerated.
    fn count(&self, c: &Context) -> Option<String> {
        let Context::Spj { tables, atoms, preds, exists } = c else {
            return Some(format!("SELECT count(*) FROM {}", self.from(c)?));
        };
        // Each input, by the instances it draws on.
        let inputs: Vec<(Context, BTreeSet<String>)> = tables
            .iter()
            .map(|t| (Context::table(t), [t.clone()].into()))
            .chain(atoms.iter().map(|a| (a.clone(), a.tables())))
            .collect();
        let mut part: Vec<usize> = (0..inputs.len()).collect();
        fn root(part: &mut [usize], i: usize) -> usize {
            if part[i] == i { i } else { let r = root(part, part[i]); part[i] = r; r }
        }
        // An input reads a value its rows carry: one a GROUP BY in it computes.
        let reads = |e: &Expr| -> Vec<usize> {
            let rels: BTreeSet<String> = e.column_refs().iter().filter_map(|c| c.relation.as_ref().map(|r| r.table().to_string())).collect();
            let values = values_read(e);
            (0..inputs.len())
                .filter(|&i| !inputs[i].1.is_disjoint(&rels) || values.iter().any(|v| self.carries(&inputs[i].0, v)))
                .collect()
        };
        let exprs: Vec<Vec<usize>> = preds
            .iter()
            .map(|p| reads(&p.expr))
            .chain(exists.iter().map(|e| e.on.iter().flat_map(|t| reads(&t.expr)).collect()))
            .collect();
        for used in &exprs {
            // A condition reading no input (a constant) goes with the first.
            let used = if used.is_empty() { vec![0] } else { used.clone() };
            for w in used.windows(2) {
                let (a, b) = (root(&mut part, w[0]), root(&mut part, w[1]));
                part[a] = b;
            }
        }
        let mut groups: std::collections::BTreeMap<usize, Vec<usize>> = Default::default();
        for i in 0..inputs.len() {
            groups.entry(root(&mut part, i)).or_default().push(i);
        }
        if groups.len() < 2 {
            return Some(format!("SELECT count(*) FROM {}", self.from(c)?));
        }
        let mut counts = vec![];
        let conds: Vec<(Vec<usize>, Option<&Term>, Option<&super::Exists>)> = preds
            .iter()
            .map(|p| (reads(&p.expr), Some(p), None))
            .chain(exists.iter().map(|e| (e.on.iter().flat_map(|t| reads(&t.expr)).collect(), None, Some(e))))
            .collect();
        for members in groups.values() {
            let mut sub = Context::Spj { tables: BTreeSet::new(), atoms: BTreeSet::new(), preds: BTreeSet::new(), exists: BTreeSet::new() };
            let Context::Spj { tables: st, atoms: sa, preds: sp, exists: se } = &mut sub else { unreachable!() };
            for &i in members {
                match &inputs[i].0 {
                    Context::Spj { tables, .. } => st.extend(tables.iter().cloned()),
                    a => {
                        sa.insert(a.clone());
                    }
                }
            }
            for (used, p, e) in &conds {
                let first = used.first().copied().unwrap_or(0);
                if root(&mut part, first) == root(&mut part, members[0]) {
                    sp.extend(p.cloned());
                    se.extend(e.cloned());
                }
            }
            counts.push(format!("({})", self.count(&sub)?));
        }
        Some(format!("SELECT {}", counts.join(" * ")))
    }

    /// `c` as a subquery in a FROM clause.
    fn from(&self, c: &Context) -> Option<String> {
        Some(format!("({}) AS {}", self.query(c)?, self.alias()))
    }

    fn alias(&self) -> String {
        let n = self.next.get();
        self.next.set(n + 1);
        format!("\"_t{n}\"")
    }

    /// A query giving the rows of `c`, with every instance's columns.
    fn query(&self, c: &Context) -> Option<String> {
        match c {
            Context::Spj { tables, atoms, preds, exists } => {
                let mut from = vec![];
                for t in tables {
                    let table = t.split(['@', '#']).next()?;
                    let columns = self.catalog.columns(table)?;
                    let columns: Vec<String> = columns.iter().map(|col| format!("{} AS {}", quote(col), quote(&format!("{t}.{col}")))).collect();
                    from.push(format!("(SELECT {} FROM {table}) AS {}", columns.join(", "), self.alias()));
                }
                for a in atoms {
                    from.push(self.from(a)?);
                }
                if from.is_empty() {
                    return None;
                }
                let mut conds = vec![];
                for p in preds {
                    conds.push(format!("({})", self.expr(p)?));
                }
                for e in exists {
                    let other = self.from(&e.other)?;
                    conds.push(match e.kind {
                        ExistsKind::Semi => format!("EXISTS (SELECT 1 FROM {other} WHERE {})", self.conjunction(&e.on)?),
                        ExistsKind::Anti => format!("NOT EXISTS (SELECT 1 FROM {other} WHERE {})", self.conjunction(&e.on)?),
                        ExistsKind::NotIn => {
                            // `outer NOT IN (SELECT inner ...)`: one equality,
                            // one side of each.
                            let [t] = e.on.iter().collect::<Vec<_>>()[..] else { return None };
                            let Expr::BinaryExpr(BinaryExpr { left, op: Operator::Eq, right }) = &t.expr else { return None };
                            let inner = e.other.tables();
                            let reads_inner = |x: &Expr| x.column_refs().iter().all(|c| c.relation.as_ref().is_some_and(|r| inner.contains(r.table())));
                            let (outer, inside) = match (reads_inner(left), reads_inner(right)) {
                                (false, true) => (left, right),
                                (true, false) => (right, left),
                                _ => return None,
                            };
                            let (outer, inside) = (self.raw(outer)?, self.raw(inside)?);
                            format!("{outer} NOT IN (SELECT {inside} FROM {other})")
                        }
                    });
                }
                let filter = if conds.is_empty() { String::new() } else { format!(" WHERE {}", conds.join(" AND ")) };
                Some(format!("SELECT * FROM {}{filter}", from.join(", ")))
            }
            Context::Derived { op, args, inputs } => match op.as_str() {
                "group" if args.iter().all(|k| matches!(k.expr, Expr::Column(_))) => {
                    let keys = args.iter().map(|k| self.expr(k)).collect::<Option<Vec<_>>>()?;
                    let values = self.computes(c)?;
                    let columns: Vec<String> = keys.iter().cloned().chain(values).collect();
                    Some(format!("SELECT {} FROM {} GROUP BY {}", columns.join(", "), self.from(&inputs[0])?, keys.join(", ")))
                }
                "aggregate" => {
                    let mut values = self.computes(c)?;
                    if values.is_empty() {
                        values.push(format!("count(*) AS {}", self.alias()));
                    }
                    Some(format!("SELECT {} FROM {}", values.join(", "), self.from(&inputs[0])?))
                }
                // Each row of the left side, with whether it has a partner.
                "LeftMark join" => Some(format!("SELECT * FROM {}", self.from(&inputs[0])?)),
                "Left join" | "Full join" => {
                    let kind = if op == "Left join" { "LEFT" } else { "FULL" };
                    let on = if args.is_empty() {
                        "true".to_string()
                    } else {
                        args.iter().map(|a| self.expr(a).map(|e| format!("({e})"))).collect::<Option<Vec<_>>>()?.join(" AND ")
                    };
                    Some(format!("SELECT * FROM {} {kind} JOIN {} ON {on}", self.from(&inputs[0])?, self.from(&inputs[1])?))
                }
                _ => None,
            },
        }
    }

    /// The values the fact reads that `g`, a GROUP BY or aggregate,
    /// computes: each `aggregate AS column`. A value is `g`'s if its rows are
    /// `g`'s under some names of `g`'s instances.
    fn computes(&self, g: &Context) -> Option<Vec<String>> {
        let mut out = vec![];
        for name in &self.wanted {
            let Some(v) = self.facts.value(name) else { continue };
            let Some(names) = renaming(g, &v.over) else { continue };
            // The aggregate, read over `g`'s instances.
            let back: HashMap<&str, &str> = names.iter().map(|(a, b)| (b.as_str(), a.as_str())).collect();
            let aggregate = v.aggregate.rename(&|r| back.get(r).map(|s| s.to_string()));
            let column = self.column(name);
            out.push(format!("{} AS {column}", self.raw(&aggregate.expr)?));
            self.computed.borrow_mut().insert(column);
        }
        Some(out)
    }

    /// Whether the rows of `c` carry value `name`: a GROUP BY in it, not
    /// below another, computes it.
    fn carries(&self, c: &Context, name: &str) -> bool {
        let Some(v) = self.facts.value(name) else { return false };
        match c {
            Context::Spj { atoms, .. } => atoms.iter().any(|a| self.carries(a, name)),
            Context::Derived { op, .. } if op == "group" || op == "aggregate" => renaming(c, &v.over).is_some(),
            Context::Derived { op, inputs, .. } if op == "Left join" || op == "Full join" => inputs.iter().any(|i| self.carries(i, name)),
            _ => false,
        }
    }

    /// The column value `name` reads as.
    fn column(&self, name: &str) -> String {
        let mut aliases = self.aliases.borrow_mut();
        let n = aliases.len();
        aliases.entry(name.to_string()).or_insert_with(|| format!("\"_v{n}\"")).clone()
    }

    fn conjunction(&self, terms: &BTreeSet<Term>) -> Option<String> {
        if terms.is_empty() {
            return Some("true".into());
        }
        Some(terms.iter().map(|t| self.expr(t).map(|e| format!("({e})"))).collect::<Option<Vec<_>>>()?.join(" AND "))
    }

    fn expr(&self, t: &Term) -> Option<String> {
        self.raw(&t.expr)
    }

    /// `e` with each instance column `r.c` as the column `"r.c"`. `None` if
    /// it reads an aggregate's value, or a column of no instance.
    fn raw(&self, e: &Expr) -> Option<String> {
        let e = e
            .clone()
            .transform_up(|e| match e {
                Expr::Column(c) => match c.relation.as_ref().map(|r| r.table().to_string()) {
                    Some(r) if r == "value" => {
                        let column = self.column(&c.name);
                        let name = column.trim_matches('"').to_string();
                        Ok(Transformed::yes(Expr::Column(Column::new_unqualified(name))))
                    }
                    Some(r) => Ok(Transformed::yes(Expr::Column(Column::new_unqualified(format!("{r}.{}", c.name))))),
                    None => Err(datafusion::error::DataFusionError::Plan("unqualified column".into())),
                },
                e => Ok(Transformed::no(e)),
            })
            .ok()?
            .data;
        let sql = Unparser::default().expr_to_sql(&e).ok()?.to_string();
        // Aggregates DuckDB names otherwise.
        Some(sql.replace("first_value(", "first(").replace("last_value(", "last(").replace("btrim(", "trim("))
    }
}

/// Names for `from`'s instances under which it is `to`, if there are any:
/// each table's instances, matched in every order.
fn renaming(from: &Context, to: &Context) -> Option<HashMap<String, String>> {
    let by_table = |c: &Context| {
        let mut m: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for t in c.tables() {
            m.entry(t.split(['@', '#']).next().unwrap_or(&t).to_string()).or_default().push(t);
        }
        m
    };
    let (a, b) = (by_table(from), by_table(to));
    if a.len() != b.len() || a.iter().any(|(t, xs)| b.get(t).is_none_or(|ys| ys.len() != xs.len())) {
        return None;
    }
    let groups: Vec<(&Vec<String>, &Vec<String>)> = a.iter().map(|(t, xs)| (xs, &b[t])).collect();
    let mut choice: Vec<usize> = vec![0; groups.len()];
    let orders: Vec<Vec<Vec<usize>>> = groups.iter().map(|(xs, _)| permutations(xs.len())).collect();
    if orders.iter().map(Vec::len).try_fold(1usize, |n, k| n.checked_mul(k)).is_none_or(|n| n > 5040) {
        return None;
    }
    loop {
        let mut names = HashMap::new();
        for (g, (xs, ys)) in groups.iter().enumerate() {
            for (i, &j) in orders[g][choice[g]].iter().enumerate() {
                names.insert(xs[i].clone(), ys[j].clone());
            }
        }
        if from.rename(&|r| names.get(r).cloned()) == *to {
            return Some(names);
        }
        // The next choice of orders.
        let mut g = 0;
        loop {
            if g == groups.len() {
                return None;
            }
            choice[g] += 1;
            if choice[g] < orders[g].len() {
                break;
            }
            choice[g] = 0;
            g += 1;
        }
    }
}

fn permutations(n: usize) -> Vec<Vec<usize>> {
    if n == 0 {
        return vec![vec![]];
    }
    let mut out = vec![];
    for p in permutations(n - 1) {
        for i in 0..=p.len() {
            let mut q = p.clone();
            q.insert(i, n - 1);
            out.push(q);
        }
    }
    out
}

fn quote(name: &str) -> String {
    format!("\"{}\"", name.replace('"', "\"\""))
}
