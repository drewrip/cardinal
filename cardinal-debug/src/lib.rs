//! Dumps what cardinal tells Z3 about a query, and renders it.
//!
//! A [`Dump`] holds an analysis's verdict and bounds, its [`Trace`] (every
//! constraint with the plan node and analyzer line it comes from) and a
//! [`Proof`] of each bound naming the constraints it needs, and, informed by
//! facts, the same again with the facts' constraints among them
//! ([`FactsDump`]). [`ascii`] and [`html`] render one.

pub mod ascii;
pub mod html;

use std::collections::BTreeMap;

use cardinal::facts::FactSet;
use cardinal::observed::ObservedPlan;
use cardinal::{Analysis, FactMode, FactReport, ForeignKey, Options, Proof, Trace, Verdict};
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
    /// The analysis informed by facts, if any were given.
    #[serde(default)]
    pub facts: Option<FactsDump>,
}

/// An analysis informed by facts ([`cardinal::Informed`]).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FactsDump {
    /// `ratios` or `pinned`.
    pub mode: String,
    /// What the facts gave and left.
    pub report: FactReport,
    /// The bounds proven with the facts, if computed.
    pub bounds: Option<String>,
    /// The base constraints, then the facts'.
    pub trace: Trace,
    /// The claims of the bounds with facts, proven with the facts' constraints.
    pub proofs: Vec<Proof>,
    /// The same claims, proven without them, in the same order.
    pub base_proofs: Vec<Proof>,
    /// Whether the proofs were attempted (not skipped by `--no-explain`).
    pub explained: bool,
    /// Facts two plans disagree on, which are left out.
    pub conflicts: Vec<String>,
}

/// Facts to inform an analysis with.
pub struct FactInput {
    pub facts: FactSet,
    pub mode: FactMode,
    /// Whether to prove the bounds with facts again, with minimal cores.
    pub explain: bool,
}

/// A plan profile (`EXPLAIN ANALYZE`) to read facts from.
pub struct Profile {
    /// The name its facts' origins give, e.g. its file's stem.
    pub name: String,
    pub json: String,
    /// PostgreSQL's `EXPLAIN (ANALYZE, VERBOSE, FORMAT JSON)`, else DuckDB's
    /// `EXPLAIN (ANALYZE, FORMAT JSON)`.
    pub postgres: bool,
}

/// `facts` (or none) with the facts of each of `profiles` added, over the
/// tables of `ctx`, and closed.
pub async fn read_facts(ctx: &SessionContext, facts: Option<FactSet>, profiles: &[Profile]) -> Result<FactSet, String> {
    let mut set = facts.unwrap_or_default();
    if !profiles.is_empty() {
        let catalog = cardinal::observed::Catalog::from_context(ctx).await.map_err(|e| e.to_string())?;
        for p in profiles {
            let plan: ObservedPlan = if p.postgres {
                cardinal::observed::from_postgres(&catalog, &p.name, &p.json, None)
            } else {
                cardinal::observed::from_duckdb(&catalog, &p.name, &p.json, None)
            }
            .map_err(|e| format!("{}: {e}", p.name))?;
            set.observe(&plan);
        }
    }
    set.close();
    Ok(set)
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
/// unless `bounds` is false, and explains each; with `facts`, does the same
/// again informed by them.
pub async fn dump(
    ctx: &SessionContext,
    source: &Source,
    options: Options,
    bounds: bool,
    facts: Option<&FactInput>,
) -> Result<Dump, String> {
    let options = Options { trace: true, selectivity: options.selectivity || facts.is_some(), ..options };
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
    let facts = match facts {
        Some(f) => Some(inform(&analysis, f, bounds)?),
        None => None,
    };
    Ok(Dump {
        query,
        plan: analysis.plan.clone(),
        verdict,
        counterexample,
        bounds: proven.map(|b| b.to_string()),
        trace: analysis.trace.expect("traced"),
        proofs,
        facts,
    })
}

fn inform(analysis: &Analysis, input: &FactInput, bounds: bool) -> Result<FactsDump, String> {
    let err = |e: cardinal::Error| e.to_string();
    let informed = analysis.with_facts(&input.facts, input.mode).map_err(err)?;
    let proven = if bounds { Some(informed.bounds().map_err(err)?) } else { None };
    let (proofs, base_proofs) = if input.explain {
        (informed.explain(proven.as_ref()).map_err(err)?, informed.explain_without_facts(proven.as_ref()).map_err(err)?)
    } else {
        (vec![], vec![])
    };
    let origins = |os: &[cardinal::facts::Origin]| os.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", ");
    let conflicts = input
        .facts
        .conflicts
        .iter()
        .map(|c| {
            let (a, b) = &c.values;
            format!("{} = {a} ({}) vs {b} ({})", c.kind, origins(&c.origins.0), origins(&c.origins.1))
        })
        .collect();
    Ok(FactsDump {
        mode: input.mode.to_string(),
        report: informed.report(),
        bounds: proven.map(|b| b.to_string()),
        trace: informed.trace.clone().expect("traced"),
        proofs,
        base_proofs,
        explained: input.explain,
        conflicts,
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
