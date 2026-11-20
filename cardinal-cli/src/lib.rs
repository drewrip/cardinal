//! Dumps what cardinal tells Z3 about a query, and renders it.
//!
//! A [`Dump`] holds an analysis's bounds (of the root, and of every
//! operator: [`PlanDump`]), its [`Trace`] (every
//! constraint with the plan node and analyzer line it comes from), a
//! [`Proof`] of each bound naming the constraints it needs; and, with
//! reference plans or tables' row counts, the same again with them
//! ([`InformedDump`]). [`derivation`] orders a proof's constraints from its
//! claim down to what it rests on. [`ascii`] and [`html`] render one.

pub mod ascii;
pub mod html;

use std::collections::BTreeMap;

use cardinal::observed::{Catalog, ObservedPlan};
use cardinal::{Analysis, Builder, ForeignKey, Options, Proof, Trace};
use datafusion::prelude::SessionContext;
use serde::{Deserialize, Serialize};

/// An analysis, as a file the viewers read.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Dump {
    /// The query: its SQL, or the plan file it was read from.
    pub query: String,
    /// The optimized plan that was analyzed.
    pub plan: String,
    /// The proven bounds, if computed.
    pub bounds: Option<String>,
    pub trace: Trace,
    pub proofs: Vec<Proof>,
    /// The analysis with reference plans and row counts, if any were given.
    #[serde(default, alias = "facts")]
    pub informed: Option<InformedDump>,
    /// Every operator's proven bounds, if computed.
    #[serde(default)]
    pub plan_bounds: Option<PlanDump>,
}

impl Dump {
    /// The proofs a view shows, the result's then every operator's, each with
    /// a core into the view's trace. `informed`: those proven with the
    /// reference plans and row counts (none if skipped). Plain: the informed
    /// bounds proven without them if those were proven, else the plain
    /// bounds' own.
    pub fn proofs_of(&self, informed: bool) -> Vec<&Proof> {
        let (root, plan) = match (&self.informed, informed) {
            (Some(f), true) => (&f.proofs[..], f.plan_bounds.as_ref()),
            (Some(f), false) if f.explained => (&f.base_proofs[..], self.plan_bounds.as_ref()),
            _ => (&self.proofs[..], self.plan_bounds.as_ref()),
        };
        root.iter().chain(plan.iter().flat_map(|p| p.proofs.iter().flatten())).collect()
    }

    /// The proof named `name` of [`Dump::proofs_of`].
    pub fn proof(&self, name: &str, informed: bool) -> Option<&Proof> {
        self.proofs_of(informed).into_iter().find(|p| p.name == name)
    }
}

/// Every operator's proven bounds, and their sum's
/// ([`cardinal::Analysis::plan_bounds`]).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PlanDump {
    /// Each node's, by node id: the query's.
    pub nodes: Vec<String>,
    /// The sum of every node's output cardinality.
    pub total: String,
    /// Each node's proofs of its bounds, by node id
    /// ([`cardinal::Analysis::explain_plan`]); empty if not computed.
    #[serde(default)]
    pub proofs: Vec<Vec<Proof>>,
}

impl PlanDump {
    /// `a`'s operators' bounds, each with its proofs if `explain`.
    fn of(a: &Analysis, explain: bool) -> Result<PlanDump, String> {
        let p = a.plan_bounds().map_err(|e| e.to_string())?;
        let proofs = if explain { a.explain_plan(&p).map_err(|e| e.to_string())? } else { vec![] };
        Ok(PlanDump { nodes: p.nodes.iter().map(|n| n.bounds.to_string()).collect(), total: p.total.to_string(), proofs })
    }

    /// The proof named `name` (`n{id}.lower` or `n{id}.upper`).
    pub fn proof(&self, name: &str) -> Option<&Proof> {
        self.proofs.iter().flatten().find(|p| p.name == name)
    }
}

/// An analysis with reference plans ([`cardinal::Builder::with_plans`]) and
/// tables' row counts ([`cardinal::Builder::with_cardinalities`]).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct InformedDump {
    /// The reference plans' names.
    #[serde(default)]
    pub plans: Vec<String>,
    /// The bounds proven with them, if computed.
    pub bounds: Option<String>,
    /// Its constraints: the query's, the reference plans' nodes', each pin
    /// and each row count, saying what it is read from.
    pub trace: Trace,
    /// The claims of the bounds with them, proven with its constraints.
    pub proofs: Vec<Proof>,
    /// The same claims, proven without reference plans or row counts, in the same
    /// order. Their cores index [`Dump::trace`].
    pub base_proofs: Vec<Proof>,
    /// Whether the proofs were attempted (not skipped by `--no-explain`).
    pub explained: bool,
    /// Every operator's bounds proven with them, if computed.
    #[serde(default)]
    pub plan_bounds: Option<PlanDump>,
}

/// Reference plans and tables' row counts to put in an analysis.
pub struct Informed {
    pub plans: Vec<ObservedPlan>,
    pub cardinalities: Vec<(String, u64)>,
    /// Whether to prove the bounds with them again, with minimal cores.
    pub explain: bool,
}

/// A plan profile (`EXPLAIN ANALYZE`) to use as a reference plan.
pub struct Profile {
    /// Its name, e.g. its file's stem.
    pub name: String,
    pub json: String,
    /// PostgreSQL's `EXPLAIN (ANALYZE, VERBOSE, FORMAT JSON)`, else DuckDB's
    /// `EXPLAIN (ANALYZE, FORMAT JSON)`.
    pub postgres: bool,
}

/// Each of `profiles`, read against the tables of `ctx`.
pub async fn read_plans(ctx: &SessionContext, profiles: &[Profile]) -> Result<Vec<ObservedPlan>, String> {
    if profiles.is_empty() {
        return Ok(vec![]);
    }
    let catalog = Catalog::from_context(ctx).await.map_err(|e| e.to_string())?;
    profiles
        .iter()
        .map(|p| {
            if p.postgres {
                cardinal::observed::from_postgres(&catalog, &p.name, &p.json, None)
            } else {
                cardinal::observed::from_duckdb(&catalog, &p.name, &p.json, None)
            }
            .map_err(|e| format!("{}: {e}", p.name))
        })
        .collect()
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

/// What bounds a [`dump`] proves.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Prove {
    /// The root's, with a proof of each.
    pub bounds: bool,
    /// Every operator's ([`PlanDump`]).
    pub plan_bounds: bool,
    /// A proof of every operator's bounds, too.
    pub node_cores: bool,
}

/// Analyzes `source` against `ctx` with `options` (traced), proves the
/// bounds `prove` asks for, and explains the root's; with `informed`, does
/// the same again with its reference plans and row counts.
pub async fn dump(
    ctx: &SessionContext,
    source: &Source,
    options: Options,
    prove: Prove,
    informed: Option<&Informed>,
) -> Result<Dump, String> {
    let options = Options { trace: true, ..options };
    let err = |e: cardinal::Error| e.to_string();
    let catalog = Catalog::from_context(ctx).await.map_err(err)?;
    let (query, builder): (String, Builder) = match source {
        Source::Sql(sql) => (sql.clone(), Analysis::sql(ctx, sql).await.map_err(err)?),
        Source::DuckDb { json, sql } | Source::Postgres { json, sql } => {
            let b = match source {
                Source::DuckDb { .. } => Analysis::duckdb(&catalog, json, sql.as_deref()),
                _ => Analysis::postgres(&catalog, json, sql.as_deref()),
            }
            .map_err(err)?;
            (sql.clone().unwrap_or_else(|| "(from an EXPLAIN plan)".into()), b)
        }
    };
    let builder = builder.options(options);
    let analysis = builder.clone().build().map_err(err)?;
    let proven = if prove.bounds { Some(analysis.bounds().map_err(err)?) } else { None };
    let proofs = explain(&analysis, proven.as_ref())?;
    let plan_bounds = if prove.plan_bounds { Some(PlanDump::of(&analysis, prove.node_cores)?) } else { None };
    let informed = match informed {
        Some(i) => Some(inform(&analysis, builder, i, prove)?),
        None => None,
    };
    Ok(Dump {
        query,
        plan: analysis.plan.clone(),
        bounds: proven.map(|b| b.to_string()),
        trace: analysis.trace.clone().expect("traced"),
        proofs,
        informed,
        plan_bounds,
    })
}

/// `builder` with `input`'s plans and row counts, against `analysis`, its
/// analysis without them.
fn inform(analysis: &Analysis, builder: Builder, input: &Informed, prove: Prove) -> Result<InformedDump, String> {
    let err = |e: cardinal::Error| e.to_string();
    let builder = builder.with_plans(&input.plans).with_cardinalities(input.cardinalities.iter().cloned());
    let informed = builder.build().map_err(err)?;
    let proven = if prove.bounds { Some(informed.bounds().map_err(err)?) } else { None };
    let plan_bounds =
        if prove.plan_bounds { Some(PlanDump::of(&informed, prove.node_cores && input.explain)?) } else { None };
    let (proofs, base_proofs) = if input.explain {
        (explain(&informed, proven.as_ref())?, explain(analysis, proven.as_ref())?)
    } else {
        (vec![], vec![])
    };
    Ok(InformedDump {
        plans: input.plans.iter().map(|p| p.name.clone()).collect(),
        bounds: proven.map(|b| b.to_string()),
        trace: informed.trace.clone().expect("traced"),
        proofs,
        base_proofs,
        explained: input.explain,
        plan_bounds,
    })
}

/// `a`'s proofs of `bounds`, none if they were not computed.
fn explain(a: &Analysis, bounds: Option<&cardinal::Bounds>) -> Result<Vec<Proof>, String> {
    bounds.map_or(Ok(vec![]), |b| a.explain(b).map_err(|e| e.to_string()))
}

/// One constraint of a proof's core, in the order [`derivation`] reads it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Step {
    /// The constraint's id.
    pub constraint: usize,
    /// How many steps it is from the claim: 0 for one over the claim's own
    /// variable. Steps of one depth together explain the variables of the
    /// steps before them.
    pub depth: usize,
    /// The variables it shares with the steps one depth up (with the claim,
    /// at depth 0): why it is needed there.
    pub via: Vec<String>,
}

/// `proof`'s core (over `trace`) as a chain from the claim down to what it
/// rests on: first the constraints over the claim's variable, then those
/// over the variables they bring in, and so on, ending at table sizes,
/// pins and row counts. Within a depth, constraints of nodes nearer the root
/// come first. Constraints sharing no variable with the chain come last, at
/// depth 0.
pub fn derivation(trace: &Trace, proof: &Proof) -> Vec<Step> {
    use std::collections::HashSet;
    let core: Vec<&cardinal::Constraint> = proof.core.iter().filter_map(|&i| trace.constraints.get(i)).collect();
    let mut seen: HashSet<&str> = HashSet::new();
    let mut frontier: HashSet<&str> = proof
        .smt
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .filter(|a| core.iter().any(|c| c.vars.iter().any(|v| v == a)))
        .collect();
    let mut used = vec![false; core.len()];
    let mut steps = vec![];
    let mut depth = 0;
    while !frontier.is_empty() {
        seen.extend(frontier.iter().copied());
        let mut level: Vec<usize> = (0..core.len())
            .filter(|&i| !used[i] && core[i].vars.iter().any(|v| frontier.contains(v.as_str())))
            .collect();
        level.sort_by_key(|&i| (std::cmp::Reverse(core[i].node), core[i].id));
        let mut next = HashSet::new();
        for &i in &level {
            used[i] = true;
            let c = core[i];
            let via = c.vars.iter().filter(|v| frontier.contains(v.as_str())).cloned().collect();
            next.extend(c.vars.iter().map(String::as_str).filter(|v| !seen.contains(v)));
            steps.push(Step { constraint: c.id, depth, via });
        }
        frontier = next;
        depth += 1;
    }
    for (i, c) in core.iter().enumerate() {
        if !used[i] {
            steps.push(Step { constraint: c.id, depth: 0, via: vec![] });
        }
    }
    steps
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

/// The node ids of `trace` that no other node takes as input, root last,
/// by the reference plan they are of (`None` first, for the query's): the
/// root and any subqueries left inside expressions, and each part of a
/// reference plan analyzed with the query.
pub fn roots(trace: &Trace) -> Vec<(Option<&str>, Vec<usize>)> {
    let used: std::collections::HashSet<usize> = trace.nodes.iter().flat_map(|n| n.inputs.iter().copied()).collect();
    let mut out: Vec<(Option<&str>, Vec<usize>)> = vec![];
    for n in trace.nodes.iter().filter(|n| !used.contains(&n.id)) {
        let plan = n.plan.as_deref();
        match out.iter_mut().find(|(p, _)| *p == plan) {
            Some((_, ids)) => ids.push(n.id),
            None => out.push((plan, vec![n.id])),
        }
    }
    out.sort_by_key(|(p, _)| p.is_some());
    out
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
