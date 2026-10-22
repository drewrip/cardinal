//! Dumps what cardinal tells Z3 about a query, and renders it.
//!
//! A [`Dump`] holds an analysis's verdict and bounds, its [`Trace`] (every
//! constraint with the plan node and analyzer line it comes from) and a
//! [`Proof`] of each bound naming the constraints it needs. [`ascii`] and
//! [`html`] render one.

pub mod ascii;
pub mod html;

use std::collections::BTreeMap;

use cardinal::{Analysis, ForeignKey, Options, Proof, Trace, Verdict};
use datafusion::prelude::SessionContext;
use serde::{Deserialize, Serialize};

/// An analysis, as a file the viewers read.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Dump {
    /// The query: its SQL, or the plan file it was read from.
    pub query: String,
    /// The optimized plan that was analyzed.
    pub plan: String,
    /// `Reduces`, `MightGrow` or `Unknown: {reason}`.
    pub verdict: String,
    /// For `MightGrow`: values of the tables and variables that satisfy every
    /// constraint yet output more rows than the scans read.
    pub counterexample: Option<BTreeMap<String, i64>>,
    /// The proven bounds, if computed.
    pub bounds: Option<String>,
    pub trace: Trace,
    pub proofs: Vec<Proof>,
}

/// Where the query to analyze comes from.
pub enum Source {
    Sql(String),
    /// DuckDB's `EXPLAIN (FORMAT JSON)`, and the query's SQL if known.
    DuckDb { json: String, sql: Option<String> },
    /// PostgreSQL's `EXPLAIN (VERBOSE, FORMAT JSON)`, and the query's SQL if known.
    Postgres { json: String, sql: Option<String> },
}

/// A context with the tables `ddl` creates: `CREATE TABLE` statements
/// separated by `;` (`PRIMARY KEY` constraints are kept).
pub async fn context(ddl: &str) -> Result<SessionContext, String> {
    let ctx = SessionContext::new();
    for statement in ddl.split(';').map(str::trim).filter(|s| !s.is_empty()) {
        ctx.sql(statement).await.map_err(|e| format!("{statement}: {e}"))?;
    }
    Ok(ctx)
}

/// Parses a foreign key written `orders(cust)->customers(id)`, with columns
/// separated by commas.
pub fn foreign_key(s: &str) -> Result<ForeignKey, String> {
    let bad = || format!("expected table(columns)->table(columns), got {s:?}");
    let (from, to) = s.split_once("->").ok_or_else(bad)?;
    let side = |t: &str| -> Result<(String, Vec<String>), String> {
        let (table, rest) = t.trim().split_once('(').ok_or_else(bad)?;
        let columns = rest.strip_suffix(')').ok_or_else(bad)?;
        let columns: Vec<String> = columns.split(',').map(|c| c.trim().to_string()).collect();
        Ok((table.trim().to_string(), columns))
    };
    let ((table, columns), (references, referenced)) = (side(from)?, side(to)?);
    if columns.len() != referenced.len() {
        return Err(format!("{s:?} pairs {} columns with {}", columns.len(), referenced.len()));
    }
    Ok(ForeignKey { table, columns, references, referenced })
}

/// Analyzes `source` against `ctx` with `options` (traced), proves bounds
/// unless `bounds` is false, and explains each.
pub async fn dump(ctx: &SessionContext, source: &Source, options: Options, bounds: bool) -> Result<Dump, String> {
    let options = Options { trace: true, ..options };
    let err = |e: cardinal::Error| e.to_string();
    let (query, analysis): (String, Analysis) = match source {
        Source::Sql(sql) => (sql.clone(), cardinal::analyze_sql_with(ctx, sql, options).await.map_err(err)?),
        Source::DuckDb { json, sql } | Source::Postgres { json, sql } => {
            let catalog = cardinal::observed::Catalog::from_context(ctx).await.map_err(err)?;
            let a = match source {
                Source::DuckDb { .. } => cardinal::analyze_duckdb(&catalog, json, sql.as_deref(), options),
                _ => cardinal::analyze_postgres(&catalog, json, sql.as_deref(), options),
            }
            .map_err(err)?;
            (sql.clone().unwrap_or_else(|| "(from an EXPLAIN plan)".into()), a)
        }
    };
    let proven = if bounds { Some(analysis.bounds().map_err(err)?) } else { None };
    let proofs = analysis.explain(proven.as_ref()).map_err(err)?;
    let (verdict, counterexample) = match &analysis.verdict {
        Verdict::Reduces => ("Reduces".to_string(), None),
        Verdict::MightGrow(c) => {
            let values = c.tables.iter().map(|(t, v)| (format!("|{t}|"), *v)).chain(c.vars.clone()).collect();
            ("MightGrow".to_string(), Some(values))
        }
        Verdict::Unknown(reason) => (format!("Unknown: {reason}"), None),
    };
    Ok(Dump {
        query,
        plan: analysis.plan.clone(),
        verdict,
        counterexample,
        bounds: proven.map(|b| b.to_string()),
        trace: analysis.trace.expect("traced"),
        proofs,
    })
}

/// `text` with each NDV variable named by its column, e.g. `op3_Filter_c1`
/// as `op3_Filter[age]`.
pub fn readable(trace: &Trace, text: &str) -> String {
    let names = column_names(trace);
    let mut out = String::with_capacity(text.len());
    let mut word = String::new();
    let flush = |word: &mut String, out: &mut String| {
        match names.get(word.as_str()) {
            Some(n) => out.push_str(n),
            None => out.push_str(word),
        }
        word.clear();
    };
    for c in text.chars() {
        if c.is_ascii_alphanumeric() || c == '_' {
            word.push(c);
        } else {
            flush(&mut word, &mut out);
            out.push(c);
        }
    }
    flush(&mut word, &mut out);
    out
}

/// Each NDV variable's readable name.
pub fn column_names(trace: &Trace) -> BTreeMap<&str, String> {
    let mut names = BTreeMap::new();
    for n in &trace.nodes {
        for (j, (column, var)) in n.columns.iter().enumerate() {
            // A column named by an expression goes by its position.
            let simple = column.split('.').all(|p| !p.is_empty() && p.chars().all(|c| c.is_alphanumeric() || c == '_'));
            let short = match column.rsplit('.').next() {
                Some(s) if simple => s.to_string(),
                _ => format!("c{j}"),
            };
            let base = var.strip_suffix(&format!("_c{j}")).unwrap_or(&n.var);
            names.insert(var.as_str(), format!("{base}[{short}]"));
        }
    }
    names
}

/// The node ids of `trace` that no other node takes as input, root last:
/// the root and any subqueries left inside expressions.
pub fn roots(trace: &Trace) -> Vec<usize> {
    let used: std::collections::HashSet<usize> = trace.nodes.iter().flat_map(|n| n.inputs.iter().copied()).collect();
    (0..trace.nodes.len()).filter(|i| !used.contains(i)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_foreign_keys() {
        let fk = foreign_key("orders(cust, region) -> customers(id,region)").unwrap();
        assert_eq!(fk, ForeignKey::new("orders", &["cust", "region"], "customers", &["id", "region"]));
        assert!(foreign_key("orders(cust)").is_err());
        assert!(foreign_key("orders(a,b)->c(id)").is_err());
    }
}
