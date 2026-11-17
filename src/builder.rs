//! Making an [`Analysis`]: the query to bound, then what is known of the
//! data it runs on.

use std::collections::HashMap;
use std::sync::Arc;

use datafusion::catalog::TableProvider;
use datafusion::common::TableReference;
use datafusion::common::tree_node::TreeNodeRecursion;
use datafusion::datasource::cte_worktable::CteWorkTable;
use datafusion::datasource::source_as_provider;
use datafusion::logical_expr::LogicalPlan;
use datafusion::logical_expr::logical_plan::TableScan;
use datafusion::prelude::SessionContext;

use crate::analysis::{Analyzer, ScanKind};
use crate::observed::{self, Catalog, ObservedPlan};
use crate::trace::Trace;
use crate::{Analysis, Error, Facts, Options, Result, axioms, joint, postprocess};

/// An [`Analysis`] being made: the query to bound, the [`Options`], the
/// executed plans of other queries to analyze it with
/// ([`Builder::with_plans`]) and facts given by hand
/// ([`Builder::with_facts`]). Made by [`Analysis::sql`], [`Analysis::plan`],
/// [`Analysis::duckdb`], [`Analysis::postgres`] or [`Analysis::logical`].
///
/// ```ignore
/// let a = Analysis::plan(&catalog, &plan)
///     .options(options)
///     .with_plans(&profiles)
///     .with_facts(&facts)
///     .build()?;
/// a.bounds()?;
/// ```
#[derive(Clone)]
pub struct Builder<'c> {
    query: Query<'c>,
    catalog: Option<CatalogRef<'c>>,
    options: Options,
    plans: Vec<&'c ObservedPlan>,
    facts: Vec<Facts>,
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
        let catalog = Catalog::from_context(ctx).await?;
        let query = Query::DataFusion { plan, base: Some(base), defaults };
        Ok(Builder::new(query, Some(CatalogRef::Owned(Arc::new(catalog)))))
    }

    /// `plan`, the plan an engine chose for a query, in place of the plan
    /// DataFusion would choose. Its operators keep the engine's order, so
    /// their rows are the ones the engine's profiles count: see
    /// [`Catalog::to_logical`]. The plan's row counts, if any, are not
    /// read. Reference plans are read against `catalog`.
    pub fn plan<'c>(catalog: &'c Catalog, plan: &'c ObservedPlan) -> Builder<'c> {
        Builder::new(Query::Observed(std::borrow::Cow::Borrowed(plan)), Some(CatalogRef::Borrowed(catalog)))
    }

    /// [`Analysis::plan`] on DuckDB's plan for `sql`, as printed by `EXPLAIN
    /// (FORMAT JSON)` (or by `EXPLAIN (ANALYZE, FORMAT JSON)`).
    pub fn duckdb<'c>(catalog: &'c Catalog, json: &str, sql: Option<&str>) -> Result<Builder<'c>> {
        let plan = observed::from_duckdb_explain(catalog, "", json, sql)?;
        Ok(Builder::new(Query::Observed(std::borrow::Cow::Owned(plan)), Some(CatalogRef::Borrowed(catalog))))
    }

    /// [`Analysis::plan`] on PostgreSQL's plan for `sql`, as printed by
    /// `EXPLAIN (VERBOSE, FORMAT JSON)` (or with `ANALYZE`, too).
    pub fn postgres<'c>(catalog: &'c Catalog, json: &str, sql: Option<&str>) -> Result<Builder<'c>> {
        let plan = observed::from_postgres_explain(catalog, "", json, sql)?;
        Ok(Builder::new(Query::Observed(std::borrow::Cow::Owned(plan)), Some(CatalogRef::Borrowed(catalog))))
    }

    /// An already-built logical plan.
    ///
    /// With no catalog to consult, every scan except a recursive CTE's work
    /// table counts as a base table, and names are resolved against
    /// DataFusion's default catalog and schema (`datafusion.public`). It
    /// takes no reference plans.
    pub fn logical(plan: LogicalPlan) -> Builder<'static> {
        Builder::new(Query::DataFusion { plan, base: None, defaults: default_names() }, None)
    }
}

impl<'c> Builder<'c> {
    fn new(query: Query<'c>, catalog: Option<CatalogRef<'c>>) -> Builder<'c> {
        Builder { query, catalog, options: Options::default(), plans: vec![], facts: vec![] }
    }

    /// Analyze with `options` (by default, [`Options::default`]).
    pub fn options(mut self, options: Options) -> Self {
        self.options = options;
        self
    }

    /// Analyze the query together with `plans`, executed plans of other
    /// queries over the data the bounds are for ([`crate::joint`]): each
    /// operator they counted is held to its rows, and the axioms relate
    /// their operators to the query's. Plans that were not run, or do not
    /// translate, are left out. Adds to any plans given before.
    pub fn with_plans(mut self, plans: impl IntoIterator<Item = &'c ObservedPlan>) -> Self {
        self.plans.extend(plans);
        self
    }

    /// Add what `facts` know, as given by hand: every row count, distinct
    /// count and least or greatest value they give of an operator's rows,
    /// exact or a bound, as a claim on its variable.
    ///
    /// The facts must describe the data the bounds are for. Claims are
    /// assumed consistent with the constraints; an inconsistent set proves
    /// any bound. With [`Options::check_facts`], a claim that contradicts
    /// them, or whose consistency Z3 cannot decide, is left out instead.
    /// Adds to any facts given before.
    pub fn with_facts(mut self, facts: &Facts) -> Self {
        self.facts.push(facts.clone());
        self
    }

    /// The analysis: the query's constraints, the reference plans', and the
    /// facts' claims.
    pub fn build(self) -> Result<Analysis> {
        let options = &self.options;
        let catalog = self.catalog.as_ref().map(CatalogRef::get);
        let (plan, defaults, base) = match &self.query {
            Query::DataFusion { plan, base, defaults } => (plan.clone(), defaults.clone(), base.as_ref()),
            Query::Observed(p) => {
                let catalog = catalog.expect("an engine's plan comes with its catalog");
                (catalog.to_logical(p)?, default_names(), None)
            }
        };
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
        let plans = match (self.plans.is_empty(), catalog) {
            (true, _) => vec![],
            (false, Some(c)) => joint::translate(c, &self.plans),
            (false, None) => return Err(Error::NoCatalog),
        };
        let mut a = analyze(&plan, &resolve, &referenced, &plans, options);
        for f in &self.facts {
            a = crate::facts::apply::apply(&a, f)?;
        }
        Ok(a)
    }
}

/// `plan` analyzed with `plans`: rules, axioms, pins, and the reduction if
/// there are plans ([`crate::joint`]); `referenced` resolves the plans'
/// scans.
fn analyze(
    plan: &LogicalPlan,
    resolve: &dyn Fn(&TableScan) -> ScanKind,
    referenced: &dyn Fn(&TableScan) -> ScanKind,
    plans: &[joint::Translated],
    options: &Options,
) -> Analysis {
    let mut a = Analyzer::new(resolve, options.max_product, &options.foreign_keys, options.trace).with_ranges(plan);
    let joint = !plans.is_empty();
    if joint {
        a.referenced_sizes = true;
        a.ranged.extend(joint::ranged(plans));
    }
    let root = a.visit(plan).card;
    let (own, own_scans, own_vars) = (a.nodes.len(), a.scans.len(), a.vars.len());
    a.resolve = referenced;
    let (pins, owners) = joint::visit(&mut a, plan, plans, options);
    axioms::assert_all(&mut a);
    let pinned = joint::assert_pins(&a, &pins);

    let root_name = a.name_of(&root);
    let full = a.solver.to_string();
    let n = a.solver.get_assertions().len();
    let mut tables: Vec<(String, String)> = a.tables.values().map(|t| (t.display.clone(), t.symbol.clone())).collect();
    tables.sort();
    let scans: Vec<(String, String)> = a.scans[..own_scans].iter().map(|(s, t, _)| (s.clone(), t.clone())).collect();
    let trace = options.trace.then(|| {
        let t = Trace::build(&a, &full, &root_name, &scans, &tables, &owners).with_facts(&pinned);
        assert_eq!(t.constraints.len(), n, "every assertion is traced");
        t
    });
    let (constraints, assertions, parts) = if joint {
        let reduced = joint::reduce(&a, own_vars, options.postprocess.dead_columns);
        (reduced.to_string(), reduced.get_assertions().len(), None)
    } else {
        let parts = postprocess::Assertions::new(&a, &full);
        (full, n, Some(parts))
    };
    let mut nodes = a.nodes;
    nodes.truncate(own);
    Analysis {
        root: root_name,
        scans,
        plan: plan.display_indent().to_string(),
        trace,
        constraints,
        assertions,
        nodes,
        check_facts: options.check_facts,
        postprocess: options.postprocess.clone(),
        // With plans, `solve-eqs` rewrote the assertions: their roles no
        // longer apply.
        parts,
    }
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
