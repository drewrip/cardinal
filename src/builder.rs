//! Making an [`Analysis`]: the query to bound, then what is known of the
//! data it runs on.

use std::collections::HashMap;
use std::panic::Location;
use std::sync::{Arc, OnceLock};
use std::time::Instant;

use datafusion::catalog::TableProvider;
use datafusion::common::TableReference;
use datafusion::common::tree_node::TreeNodeRecursion;
use datafusion::datasource::cte_worktable::CteWorkTable;
use datafusion::datasource::source_as_provider;
use datafusion::logical_expr::LogicalPlan;
use datafusion::logical_expr::logical_plan::TableScan;
use datafusion::prelude::SessionContext;
use z3::PrepareSynchronized;
use z3::ast::Int;

use crate::analysis::{Analyzer, ScanKind};
use crate::observed::{self, Catalog, ObservedPlan};
use crate::trace::{FactClaim, FactInfo, FactRef, Trace};
use crate::{Analysis, BuildStats, Options, Result, in_own_context, joint, link};

/// An [`Analysis`] being made: the query to bound, the [`Options`], the
/// executed plans of other queries to analyze it with
/// ([`Builder::with_plans`]) and tables' row counts
/// ([`Builder::with_cardinalities`]). Made by [`Analysis::sql`], [`Analysis::plan`],
/// [`Analysis::duckdb`], [`Analysis::postgres`], [`Analysis::snowflake`] or
/// [`Analysis::logical`], each with the [`Catalog`] reference plans are read
/// against.
///
/// ```ignore
/// let a = Analysis::plan(&catalog, &plan)
///     .options(options)
///     .with_plans(&profiles)
///     .with_cardinalities([("lineitem", 6001215)])
///     .build()?;
/// a.bounds()?;
/// ```
#[derive(Clone)]
pub struct Builder<'c> {
    query: Query<'c>,
    catalog: CatalogRef<'c>,
    options: Options,
    plans: Vec<&'c ObservedPlan>,
    cardinalities: Vec<(String, u64)>,
}

#[derive(Clone)]
enum Query<'c> {
    /// A plan DataFusion made, its base tables told by their providers'
    /// identities, and the default catalog and schema it names them in.
    DataFusion { plan: LogicalPlan, base: Option<HashMap<usize, ScanKind>>, defaults: (String, String) },
    /// The plan an engine chose.
    Observed(std::borrow::Cow<'c, ObservedPlan>),
}

#[derive(Clone)]
enum CatalogRef<'c> {
    Borrowed(&'c Catalog),
    Owned(Arc<Catalog>),
}

impl CatalogRef<'_> {
    fn get(&self) -> &Catalog {
        match self {
            CatalogRef::Borrowed(c) => c,
            CatalogRef::Owned(c) => c,
        }
    }
}

impl Analysis {
    /// `sql`, parsed and optimized with `ctx`.
    ///
    /// A scan counts as a base table only if its provider is the one
    /// registered in `ctx`'s catalog under that name. Every spelling of a
    /// table's name (`users`, `public.users`, ...) therefore maps to one
    /// variable, and work tables and table functions such as
    /// `generate_series` are not counted as input. Reference plans are read
    /// against `ctx`'s tables.
    pub async fn sql(ctx: &SessionContext, sql: &str) -> Result<Builder<'static>> {
        let query = plan_sql(ctx, sql).await?;
        let catalog = Catalog::from_context(ctx).await?;
        Ok(Builder::new(query, CatalogRef::Owned(Arc::new(catalog))))
    }

    /// `plan`, the plan an engine chose for a query, in place of the plan
    /// DataFusion would choose. Its operators keep the engine's order, so
    /// their rows are the ones the engine's profiles count: see
    /// [`Catalog::to_logical`]. The plan's row counts, if any, are not
    /// read. Reference plans are read against `catalog`.
    pub fn plan<'c>(catalog: &'c Catalog, plan: &'c ObservedPlan) -> Builder<'c> {
        Builder::new(Query::Observed(std::borrow::Cow::Borrowed(plan)), CatalogRef::Borrowed(catalog))
    }

    /// [`Analysis::plan`] on DuckDB's plan for `sql`, as printed by `EXPLAIN
    /// (FORMAT JSON)` (or by `EXPLAIN (ANALYZE, FORMAT JSON)`).
    pub fn duckdb<'c>(catalog: &'c Catalog, json: &str, sql: Option<&str>) -> Result<Builder<'c>> {
        let plan = observed::from_duckdb_explain(catalog, "", json, sql)?;
        Ok(Builder::new(Query::Observed(std::borrow::Cow::Owned(plan)), CatalogRef::Borrowed(catalog)))
    }

    /// [`Analysis::plan`] on PostgreSQL's plan for `sql`, as printed by
    /// `EXPLAIN (VERBOSE, FORMAT JSON)` (or with `ANALYZE`, too).
    pub fn postgres<'c>(catalog: &'c Catalog, json: &str, sql: Option<&str>) -> Result<Builder<'c>> {
        let plan = observed::from_postgres_explain(catalog, "", json, sql)?;
        Ok(Builder::new(Query::Observed(std::borrow::Cow::Owned(plan)), CatalogRef::Borrowed(catalog)))
    }

    /// [`Analysis::plan`] on Snowflake's plan for `sql`, as printed by
    /// `EXPLAIN USING JSON` (or its operator stats, or a
    /// [`snowflake_explain::QueryPlan`]): see [`observed::from_snowflake`].
    pub fn snowflake<'c>(catalog: &'c Catalog, json: &str, sql: Option<&str>) -> Result<Builder<'c>> {
        let plan = observed::from_snowflake_explain(catalog, "", json, sql)?;
        Ok(Builder::new(Query::Observed(std::borrow::Cow::Owned(plan)), CatalogRef::Borrowed(catalog)))
    }

    /// An already-built logical plan, reading reference plans against
    /// `catalog`.
    ///
    /// Every scan except a recursive CTE's work table counts as a base
    /// table, and names resolve in DataFusion's default catalog and schema
    /// (`datafusion.public`), as reference plans' scans do. A plan with
    /// bare table names therefore matches reference plans' tables.
    /// `catalog` reads reference plans; it does not decide which scans
    /// count as base tables.
    pub fn logical<'c>(catalog: &'c Catalog, plan: LogicalPlan) -> Builder<'c> {
        Builder::new(Query::DataFusion { plan, base: None, defaults: default_names() }, CatalogRef::Borrowed(catalog))
    }
}

/// `sql` parsed and optimized with `ctx`, as [`Analysis::sql`] does: its
/// base tables are the scans of `ctx`'s registered providers.
async fn plan_sql(ctx: &SessionContext, sql: &str) -> Result<Query<'static>> {
    let state = ctx.state();
    let plan = state.create_logical_plan(sql).await?;
    let plan = state.optimize(&plan)?;
    let catalog = state.config().options().catalog.clone();
    let defaults = (catalog.default_catalog, catalog.default_schema);

    let mut scans = Vec::new();
    plan.apply_with_subqueries(|p| {
        if let LogicalPlan::TableScan(scan) = p {
            scans.push(scan.clone());
        }
        Ok(TreeNodeRecursion::Continue)
    })?;
    let mut base = HashMap::new();
    for scan in scans {
        let Ok(registered) = ctx.table_provider(scan.table_name.clone()).await else {
            continue;
        };
        let Ok(scanned) = source_as_provider(&scan.source) else {
            continue;
        };
        if provider_ptr(&registered) == provider_ptr(&scanned) {
            base.insert(provider_ptr(&scanned), base_kind(&scan.table_name, &defaults.0, &defaults.1));
        }
    }
    Ok(Query::DataFusion { plan, base: Some(base), defaults })
}

impl<'c> Builder<'c> {
    /// `sql`, planned with `ctx` as [`Analysis::sql`] plans it, reading
    /// reference plans against `catalog`, `ctx`'s.
    pub(crate) async fn sql(ctx: &SessionContext, sql: &str, catalog: Arc<Catalog>) -> Result<Builder<'static>> {
        Ok(Builder::new(plan_sql(ctx, sql).await?, CatalogRef::Owned(catalog)))
    }

    fn new(query: Query<'c>, catalog: CatalogRef<'c>) -> Builder<'c> {
        Builder { query, catalog, options: Options::default(), plans: vec![], cardinalities: vec![] }
    }

    /// Analyze with `options` (by default, [`Options::default`]).
    pub fn options(mut self, options: Options) -> Self {
        self.options = options;
        self
    }

    /// Analyze the query together with `plans`, executed plans of other
    /// queries over the data the bounds are for ([`crate::joint`]): each
    /// operator they counted is held to its rows, and [link](crate::link)
    /// relates their operators to the query's. Plans that were not run, or do not
    /// translate, are left out. Adds to any plans given before.
    pub fn with_plans(mut self, plans: impl IntoIterator<Item = &'c ObservedPlan>) -> Self {
        self.plans.extend(plans);
        self
    }

    /// Hold each table to its row count: `(name, rows)` asserts `|name| =
    /// rows`. A name resolves as the query's scans do (bare names in the
    /// default catalog and schema); one that names no table the analysis
    /// scans is ignored. The counts must be of the data the bounds are for:
    /// wrong ones make the constraints unsatisfiable, which proves any
    /// bound. Adds to any counts given before.
    pub fn with_cardinalities<S: Into<String>>(mut self, tables: impl IntoIterator<Item = (S, u64)>) -> Self {
        self.cardinalities.extend(tables.into_iter().map(|(t, n)| (t.into(), n)));
        self
    }

    /// The analysis: the query's constraints, the reference plans', and the
    /// tables' row counts. It runs in a Z3 context of its own
    /// ([`in_own_context`]), so a query gives the same constraints built
    /// alone or in a [`Batch`](crate::Batch).
    pub fn build(self) -> Result<Analysis> {
        let start = Instant::now();
        let mut a = in_own_context(|| self.analyze())?;
        a.stats.total = start.elapsed();
        Ok(a)
    }

    /// Whether `joint` would select any subtree of `plan` for this query:
    /// if not, giving it adds no constraint. False for a plan that was not
    /// run or does not translate, which is left out.
    #[doc(hidden)]
    pub fn relevant(&self, plan: &ObservedPlan) -> bool {
        let catalog = self.catalog.get();
        let Ok((query, _, _)) = self.query_plan() else { return false };
        joint::relevant(catalog, &query, plan, &self.options)
    }

    /// The query's plan, the default catalog and schema it names tables
    /// in, and its base tables by provider, if told by them.
    #[allow(clippy::type_complexity)]
    fn query_plan(&self) -> Result<(LogicalPlan, (String, String), Option<&HashMap<usize, ScanKind>>)> {
        Ok(match &self.query {
            Query::DataFusion { plan, base, defaults } => (plan.clone(), defaults.clone(), base.as_ref()),
            Query::Observed(p) => (self.catalog.get().to_logical(p)?, default_names(), None),
        })
    }

    fn analyze(&self) -> Result<Analysis> {
        let options = &self.options;
        let catalog = self.catalog.get();
        let (plan, defaults, base) = self.query_plan()?;
        // An engine's plan, and a reference plan, scan the catalog's tables
        // by their bare names.
        let referenced = |scan: &TableScan| base_kind(&scan.table_name, &defaults.0, &defaults.1);
        let resolve = |scan: &TableScan| match (&self.query, base) {
            (Query::Observed(_), _) => referenced(scan),
            (_, Some(base)) => source_as_provider(&scan.source)
                .ok()
                .and_then(|p| base.get(&provider_ptr(&p)).cloned())
                .unwrap_or(ScanKind::NonBase),
            (_, None) => {
                let work = source_as_provider(&scan.source).is_ok_and(|p| p.downcast_ref::<CteWorkTable>().is_some());
                if work { ScanKind::NonBase } else { referenced(scan) }
            }
        };
        let start = Instant::now();
        let plans = match self.plans.is_empty() {
            true => vec![],
            false => joint::translate(catalog, &self.plans),
        };
        let translating = start.elapsed();
        let sizes: Vec<(String, u64)> = self
            .cardinalities
            .iter()
            .filter_map(|(name, n)| match base_kind(&TableReference::from(name.as_str()), &defaults.0, &defaults.1) {
                ScanKind::Base { key, .. } => Some((key, *n)),
                ScanKind::NonBase => None,
            })
            .collect();
        let mut a = analyze(&plan, &resolve, &referenced, &plans, &sizes, options);
        a.stats.rules += translating;
        a.stats.plans_given = self.plans.len();
        Ok(a)
    }
}

/// `plan` analyzed with `plans`: rules, link, pins, the tables' `sizes`
/// (by [`ScanKind::Base`] key), and the reduction if there are plans
/// ([`crate::joint`]); `referenced` resolves the plans' scans.
fn analyze(
    plan: &LogicalPlan,
    resolve: &dyn Fn(&TableScan) -> ScanKind,
    referenced: &dyn Fn(&TableScan) -> ScanKind,
    plans: &[joint::Translated],
    sizes: &[(String, u64)],
    options: &Options,
) -> Analysis {
    let mut stats = BuildStats::default();
    let start = Instant::now();
    let mut a = Analyzer::new(resolve, options.max_product, &options.foreign_keys, options.trace).with_ranges(plan);
    a.limits = options.limits;
    let joint = !plans.is_empty();
    if joint {
        a.referenced_sizes = true;
        a.ranged.extend(joint::ranged(plan, plans, options));
    }
    let root = a.visit(plan).card;
    let (own, own_scans, own_vars) = (a.nodes.len(), a.scans.len(), a.vars.len());
    a.resolve = referenced;
    let (pins, owners) = joint::visit(&mut a, plan, plans, options);
    stats.rules = start.elapsed();
    let start = Instant::now();
    let linked = link::link_all(&a);
    stats.link = start.elapsed();
    let start = Instant::now();
    let mut pinned = joint::assert_pins(&a, &pins);
    pinned.extend(assert_sizes(&a, sizes));
    let mut pins_time = start.elapsed();

    let root_name = a.name_of(&root);
    let asserted = a.solver.get_assertions();
    let n = asserted.len();
    let mut tables: Vec<(String, String)> = a.tables.values().map(|t| (t.display.clone(), t.symbol.clone())).collect();
    tables.sort();
    let scans: Vec<(String, String)> = a.scans[..own_scans].iter().map(|(s, t, _)| (s.clone(), t.clone())).collect();
    // The constraints are kept as terms: printing is slow, and serializes
    // threads on Z3's symbol table. Only the trace prints them here.
    let traced = options.trace.then(|| {
        let full = a.solver.to_string();
        let t = Trace::build(&a, &full, &root_name, &scans, &tables, &owners).with_facts(&pinned);
        assert_eq!(t.constraints.len(), n, "every assertion is traced");
        (t, full)
    });
    let (trace, full) = traced.unzip();
    let start = Instant::now();
    let (constraints, text) = match joint {
        false => (asserted, full),
        true => (joint::reduce(&asserted, &joint::kept(&a, own_vars)), None),
    };
    pins_time += start.elapsed();
    let floors = pins.iter().filter(|p| p.floor).count();
    let stats = BuildStats {
        pins: pins_time,
        nodes: own,
        plans_selected: owners.len(),
        plan_nodes: a.nodes.len() - own,
        pinned: pins.len() - floors,
        floors,
        assertions_before: n,
        assertions: constraints.len(),
        link_classes: linked.classes,
        links: linked.links,
        link_checks: linked.checks,
        ..stats
    };
    let mut nodes = a.nodes;
    nodes.truncate(own);
    Analysis {
        root: root_name,
        scans,
        plan: plan.display_indent().to_string(),
        trace,
        assertions: constraints.len(),
        constraints: constraints.synchronized(),
        text: text.map(OnceLock::from).unwrap_or_default(),
        nodes,
        limits: options.limits,
        stats,
    }
}

/// Asserts `|T| = rows` for each `(key, rows)` of `sizes` whose table the
/// analysis has, and gives each as a fact for the trace (`given rows`).
fn assert_sizes(a: &Analyzer, sizes: &[(String, u64)]) -> Vec<FactClaim> {
    let mut out = vec![];
    for (key, rows) in sizes {
        let Some(t) = a.tables.get(key) else { continue };
        let claim = t.var.eq(Int::from_u64(*rows));
        a.assert_untraced(claim.clone());
        let fact = FactRef { text: format!("|{}|", t.display), origins: vec!["given".to_string()] };
        out.push(FactClaim {
            claim,
            node: None,
            info: FactInfo { source: "given rows".to_string(), facts: vec![fact], value: format!("= {rows}") },
            at: Location::caller(),
        });
    }
    out
}

/// Identity of a provider object. An address, not a pointer, so futures holding
/// it stay `Send`.
fn provider_ptr(p: &Arc<dyn TableProvider>) -> usize {
    Arc::as_ptr(p) as *const () as usize
}

/// DataFusion's default catalog and schema, which names without a catalog
/// of their own resolve in.
fn default_names() -> (String, String) {
    ("datafusion".to_string(), "public".to_string())
}

/// The scan kind of a table by its bare name, in the default catalog and
/// schema.
pub(crate) fn bare_kind(table: &str) -> ScanKind {
    let (catalog, schema) = default_names();
    base_kind(&TableReference::bare(table), &catalog, &schema)
}

/// Canonical identity and display name for a base table reference.
pub(crate) fn base_kind(name: &TableReference, default_catalog: &str, default_schema: &str) -> ScanKind {
    let r = name.clone().resolve(default_catalog, default_schema);
    let key = format!("{}\0{}\0{}", r.catalog, r.schema, r.table);
    let display = if *r.catalog == *default_catalog && *r.schema == *default_schema {
        r.table.to_string()
    } else {
        r.to_string()
    };
    ScanKind::Base { key, display }
}
