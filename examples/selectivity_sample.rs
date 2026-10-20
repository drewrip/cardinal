//! Estimates the simple selectivities of the query of the `selectivity`
//! example over real TPC-H tables, and plugs them into its equation:
//!
//! ```sql
//! SELECT * FROM lineitem JOIN orders ON l_orderkey = o_orderkey
//! WHERE l_discount < 0.01
//! ```
//!
//! The tables' sizes are taken as known. A filter's share of a table is
//! measured on a 1% `TABLESAMPLE SYSTEM` of it, and a distinct count per row
//! of a table with `approx_distinct` over the table. Each is counted by a
//! query built as a plan over the fact's expressions and written as SQL by
//! `sqlser`.
//!
//! Run with `cargo run --release --example selectivity_sample -- <dir>`,
//! where `<dir>` holds `lineitem.parquet` and `orders.parquet`.

use std::collections::{BTreeSet, HashMap};
use std::fmt::{self, Formatter};
use std::hash::{DefaultHasher, Hash, Hasher};
use std::sync::Arc;

use async_trait::async_trait;
use cardinal::facts::{Context, FactKind};
use cardinal::{Card, ForeignKey, Options, SimpleKind, SimpleSelectivity, analyze_sql_with};
use datafusion::arrow::array::{AsArray, RecordBatch};
use datafusion::arrow::compute::cast;
use datafusion::arrow::datatypes::{DataType, Int64Type};
use datafusion::catalog::Session;
use datafusion::common::tree_node::TreeNodeRecursion;
use datafusion::common::{DFSchemaRef, Result, ScalarValue, not_impl_err, plan_datafusion_err};
use datafusion::execution::context::QueryPlanner;
use datafusion::execution::{SendableRecordBatchStream, SessionStateBuilder, TaskContext};
use datafusion::functions_aggregate::count::count_all;
use datafusion::functions_aggregate::expr_fn::approx_distinct;
use datafusion::logical_expr::physical_planning_context::PhysicalPlanningContext;
use datafusion::logical_expr::planner::{PlannedRelation, RelationPlanner, RelationPlannerContext, RelationPlanning};
use datafusion::logical_expr::utils::conjunction;
use datafusion::logical_expr::{Expr, Extension, LogicalPlan, UserDefinedLogicalNode, UserDefinedLogicalNodeCore};
use datafusion::physical_expr::{EquivalenceProperties, PhysicalExpr};
use datafusion::physical_plan::stream::RecordBatchStreamAdapter;
use datafusion::physical_plan::{DisplayAs, DisplayFormatType, ExecutionPlan, PlanProperties};
use datafusion::physical_planner::{DefaultPhysicalPlanner, ExtensionPlanner, PhysicalPlanner};
use datafusion::prelude::SessionContext;
use datafusion::sql::sqlparser::ast::{TableFactor, TableSampleKind, TableSampleMethod, TableSampleUnit};
use futures::StreamExt;
use sqlser::Unparser;
use sqlser::dialect::DefaultDialect;

const SQL: &str = "SELECT * FROM lineitem JOIN orders ON l_orderkey = o_orderkey \
                   WHERE l_discount < 0.01";

/// The sample each filtered table is measured on.
const SAMPLE: &str = "TABLESAMPLE SYSTEM (1 PERCENT) REPEATABLE (42)";

#[tokio::main]
async fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let dir = std::env::args().nth(1).ok_or("usage: selectivity_sample <dir with lineitem.parquet and orders.parquet>")?;
    let ctx = sampling_context()?;
    for t in ["lineitem", "orders"] {
        ctx.register_parquet(t, format!("{dir}/{t}.parquet"), Default::default()).await?;
    }

    // The source cardinalities are known.
    let mut sizes = HashMap::new();
    for t in ["lineitem", "orders"] {
        sizes.insert(t.to_string(), count(&ctx, &format!("SELECT count(*) FROM {t}")).await?);
    }

    let options = Options {
        selectivity: true,
        foreign_keys: vec![ForeignKey::new("lineitem", &["l_orderkey"], "orders", &["o_orderkey"])],
        ..Default::default()
    };
    let a = analyze_sql_with(&ctx, SQL, options).await?;
    let report = a.selectivity.as_ref().expect("asked for selectivities");
    println!("{SQL}\n\n{report}");
    for (t, n) in &sizes {
        println!("  |{t}| = {n}");
    }

    // Filters first, then distinct counts, then the rest.
    let mut simple = a.simple_selectivities()?;
    simple.sort_by_key(|s| (rank(s), s.name[1..].parse::<usize>().unwrap_or(usize::MAX)));
    println!("\nSimple selectivities:");
    for s in &simple {
        println!("  {s}");
    }

    // A sample of each table a filter is a share of.
    let filtered: BTreeSet<&str> = simple
        .iter()
        .filter_map(|s| s.simple.as_ref().ok().filter(|s| s.kind == SimpleKind::Filter))
        .map(|s| s.tables[0].as_str())
        .collect();
    let mut sampled = HashMap::new();
    if !filtered.is_empty() {
        println!("\nSamples:");
    }
    for t in filtered {
        let sql = format!("CREATE TABLE {t}_sample AS SELECT * FROM {t} {SAMPLE}");
        ctx.sql(&sql).await?.collect().await?;
        let n = count(&ctx, &format!("SELECT count(*) FROM {t}_sample")).await?;
        println!("  {sql}\n    {n} of {} rows", sizes[t]);
        sampled.insert(t, n);
    }

    // Each simple selectivity's value, in [0, 1].
    println!("\nValues:");
    let dialect = DefaultDialect::new();
    let unparser = Unparser::new(&dialect);
    let mut values = HashMap::new();
    for s in &simple {
        let Ok(simple) = &s.simple else { continue };
        let table = simple.tables[0].as_str();
        let (sql, of, of_sql) = match &simple.fact {
            // The share of the sample's rows, or of those satisfying the
            // filters below it, satisfying the predicate.
            FactKind::Selectivity { pred, over } => {
                let sample = format!("{table}_sample");
                let given = conditions(over);
                let (of, of_sql) = if given.is_empty() {
                    (sampled[table], None)
                } else {
                    let sql = counted(&ctx, &unparser, &sample, over, given.clone()).await?;
                    (count(&ctx, &sql).await?, Some(sql))
                };
                if of == 0 {
                    println!("  {}: no row of the sample of {table} to measure it on", s.name);
                    continue;
                }
                let all = given.into_iter().chain(pred.iter().map(|t| t.expr.clone())).collect();
                (counted(&ctx, &unparser, &sample, over, all).await?, of, of_sql)
            }
            // The table's distinct keys per row.
            FactKind::Distinct { keys, over } => {
                let key = match keys.iter().map(|t| t.expr.clone()).collect::<Vec<_>>()[..] {
                    [ref key] => key.clone(),
                    _ => {
                        println!("  {}: approx_distinct takes one key", s.name);
                        continue;
                    }
                };
                let plan = ctx
                    .table(table)
                    .await?
                    .alias(instance(over))?
                    .aggregate(vec![], vec![approx_distinct(key)])?
                    .into_unoptimized_plan();
                (unparser.plan_to_sql(&plan)?, sizes[table], None)
            }
            _ => continue,
        };
        let n = count(&ctx, &sql).await?;
        let value = n as f64 / of as f64;
        let range = report.required.iter().find(|r| r.name == s.name).map(|r| r.range);
        println!("  {} = {} ≈ {n} / {of} = {value:.6}", s.name, simple.fact);
        println!("    {sql}");
        if let Some(of_sql) = of_sql {
            println!("    over {of_sql}");
        }
        if let Some(range) = range {
            println!("    proven to lie in {range}");
        }
        values.insert(s.name.clone(), value);
    }

    // The values multiplied into the equation.
    let x = report.evaluate(&sizes, &values)?;
    println!("\nX = {}", report.output);
    println!("  = {}", plugged(&report.output, &sizes, &values));
    match x.exact() {
        Some(x) => println!("  ≈ {x:.0}"),
        None => println!("  in {x}: a selectivity has no value"),
    }
    let actual = count(&ctx, &format!("SELECT count(*) FROM ({SQL})")).await?;
    println!("Actual: {actual}");
    Ok(())
}

/// Where `s` sorts: filters, then distinct counts, then the rest.
fn rank(s: &SimpleSelectivity) -> u8 {
    match s.simple.as_ref().map(|s| s.kind) {
        Ok(SimpleKind::Filter) => 0,
        Ok(SimpleKind::Distinct) => 1,
        Err(_) => 2,
    }
}

/// The instance a simple fact's expressions qualify their columns by.
fn instance(over: &Context) -> &str {
    match over {
        Context::Spj { tables, .. } => tables.first().expect("a table"),
        Context::Derived { .. } => unreachable!("a simple fact is over a table"),
    }
}

/// The predicates of the filters `over` is a table's rows under.
fn conditions(over: &Context) -> Vec<Expr> {
    match over {
        Context::Spj { preds, .. } => preds.iter().map(|t| t.expr.clone()).collect(),
        Context::Derived { .. } => unreachable!("a simple fact is over a table"),
    }
}

/// A query counting the rows of `table`, read as `over`'s instance, that
/// satisfy `preds`, written by `sqlser`.
async fn counted(
    ctx: &SessionContext,
    unparser: &Unparser<'_>,
    table: &str,
    over: &Context,
    preds: Vec<Expr>,
) -> std::result::Result<String, Box<dyn std::error::Error>> {
    let mut rows = ctx.table(table).await?.alias(instance(over))?;
    if let Some(p) = conjunction(preds) {
        rows = rows.filter(p)?;
    }
    let plan = rows.aggregate(vec![], vec![count_all()])?.into_unoptimized_plan();
    Ok(unparser.plan_to_sql(&plan)?)
}

/// The single count `sql` returns.
async fn count(ctx: &SessionContext, sql: &str) -> Result<u64> {
    let batches = ctx.sql(sql).await?.collect().await?;
    let column = cast(batches[0].column(0), &DataType::Int64)?;
    Ok(column.as_primitive::<Int64Type>().value(0) as u64)
}

/// `card` with each table's size and each selectivity's value in place.
fn plugged(card: &Card, sizes: &HashMap<String, u64>, values: &HashMap<String, f64>) -> String {
    let join = |ps: &[Card], sep: &str| {
        let parts: Vec<String> = ps
            .iter()
            .map(|p| match p {
                Card::Add(_) => format!("({})", plugged(p, sizes, values)),
                _ => plugged(p, sizes, values),
            })
            .collect();
        parts.join(sep)
    };
    match card {
        Card::Table(t) => sizes.get(t).map_or(card.to_string(), u64::to_string),
        Card::Sel(s) => values.get(s).map_or(card.to_string(), |v| format!("{v:.6}")),
        Card::Mul(ps) => join(ps, " · "),
        Card::Add(ps) => join(ps, " + "),
        Card::Not(c) => format!("(1 - {})", plugged(c, sizes, values)),
        Card::Min(a, b) => format!("min({}, {})", plugged(a, sizes, values), plugged(b, sizes, values)),
        Card::Max(a, b) => format!("max({}, {})", plugged(a, sizes, values), plugged(b, sizes, values)),
        Card::Sub(c, k) => format!("{} - {k}", plugged(c, sizes, values)),
        Card::Const(_) | Card::Ratio(..) | Card::Operator(_) => card.to_string(),
    }
}

// `TABLESAMPLE SYSTEM`, after DataFusion's `relation_planner/table_sample.rs`
// example: a relation planner turns the clause into a `TableSample` node, and
// an extension planner runs it as a `SampleExec`. SYSTEM sampling keeps whole
// blocks, here each batch the scan reads, with the given probability.

/// A session that plans `TABLESAMPLE SYSTEM`.
fn sampling_context() -> Result<SessionContext> {
    let state = SessionStateBuilder::new()
        .with_default_features()
        .with_query_planner(Arc::new(SampleQueryPlanner))
        .build();
    let ctx = SessionContext::new_with_state(state);
    ctx.register_relation_planner(Arc::new(SamplePlanner))?;
    Ok(ctx)
}

/// Plans `t TABLESAMPLE SYSTEM (p [PERCENT]) [REPEATABLE (seed)]` as a
/// [`SampleNode`] over `t`. As in PostgreSQL, `p` is a percentage.
#[derive(Debug)]
struct SamplePlanner;

impl RelationPlanner for SamplePlanner {
    fn plan_relation(
        &self,
        mut relation: TableFactor,
        context: &mut dyn RelationPlannerContext,
    ) -> Result<RelationPlanning> {
        let TableFactor::Table { sample, alias, .. } = &mut relation else {
            return Ok(RelationPlanning::Original(Box::new(relation)));
        };
        let Some(sample) = sample.take() else {
            return Ok(RelationPlanning::Original(Box::new(relation)));
        };
        let alias = alias.clone();
        let (TableSampleKind::BeforeTableAlias(sample) | TableSampleKind::AfterTableAlias(sample)) = sample;
        if !matches!(sample.name, Some(TableSampleMethod::System | TableSampleMethod::Block)) {
            return not_impl_err!("only TABLESAMPLE SYSTEM is supported");
        }
        let Some(quantity) = sample.quantity.filter(|q| q.unit != Some(TableSampleUnit::Rows)) else {
            return not_impl_err!("TABLESAMPLE SYSTEM takes a percentage");
        };
        let percent: f64 = quantity.value.to_string().parse().map_err(|_| plan_datafusion_err!("invalid percentage"))?;
        if !(0.0..=100.0).contains(&percent) {
            return Err(plan_datafusion_err!("a percentage is in [0, 100], got {percent}"));
        }
        let seed = match sample.seed {
            Some(s) => s.value.to_string().parse().map_err(|_| plan_datafusion_err!("REPEATABLE takes an integer"))?,
            None => 0,
        };
        let node = SampleNode { input: context.plan(relation)?, fraction: Fraction(percent / 100.0), seed };
        let plan = LogicalPlan::Extension(Extension { node: Arc::new(node) });
        Ok(RelationPlanning::Planned(Box::new(PlannedRelation::new(plan, alias))))
    }
}

/// A fraction, compared and hashed by its bits.
#[derive(Debug, Clone, Copy, PartialOrd)]
struct Fraction(f64);

impl PartialEq for Fraction {
    fn eq(&self, other: &Self) -> bool {
        self.0.to_bits() == other.0.to_bits()
    }
}

impl Eq for Fraction {}

impl Hash for Fraction {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

/// Keeps each block of `input` with probability `fraction`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Hash)]
struct SampleNode {
    input: LogicalPlan,
    fraction: Fraction,
    seed: u64,
}

impl UserDefinedLogicalNodeCore for SampleNode {
    fn name(&self) -> &str {
        "TableSample"
    }

    fn inputs(&self) -> Vec<&LogicalPlan> {
        vec![&self.input]
    }

    fn schema(&self) -> &DFSchemaRef {
        self.input.schema()
    }

    fn expressions(&self) -> Vec<Expr> {
        vec![]
    }

    fn fmt_for_explain(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "TableSample: system={}, seed={}", self.fraction.0, self.seed)
    }

    fn with_exprs_and_inputs(&self, _exprs: Vec<Expr>, mut inputs: Vec<LogicalPlan>) -> Result<Self> {
        Ok(SampleNode { input: inputs.swap_remove(0), ..self.clone() })
    }
}

/// Plans with [`SampleExtensionPlanner`].
#[derive(Debug)]
struct SampleQueryPlanner;

#[async_trait]
impl QueryPlanner for SampleQueryPlanner {
    async fn create_physical_plan(&self, plan: &LogicalPlan, session: &dyn Session) -> Result<Arc<dyn ExecutionPlan>> {
        let planner = DefaultPhysicalPlanner::with_extension_planners(vec![Arc::new(SampleExtensionPlanner)]);
        planner.create_physical_plan(plan, session).await
    }
}

/// Runs a [`SampleNode`] as a [`SampleExec`].
struct SampleExtensionPlanner;

#[async_trait]
impl ExtensionPlanner for SampleExtensionPlanner {
    async fn plan_extension(
        &self,
        _planner: &dyn PhysicalPlanner,
        node: &dyn UserDefinedLogicalNode,
        _logical_inputs: &[&LogicalPlan],
        physical_inputs: &[Arc<dyn ExecutionPlan>],
        _session: &dyn Session,
        _planning_ctx: &PhysicalPlanningContext,
    ) -> Result<Option<Arc<dyn ExecutionPlan>>> {
        let Some(node) = node.as_any().downcast_ref::<SampleNode>() else {
            return Ok(None);
        };
        Ok(Some(Arc::new(SampleExec::new(physical_inputs[0].clone(), node.fraction.0, node.seed))))
    }
}

/// Keeps each batch of `input` with probability `fraction`.
#[derive(Debug)]
struct SampleExec {
    input: Arc<dyn ExecutionPlan>,
    fraction: f64,
    seed: u64,
    properties: Arc<PlanProperties>,
}

impl SampleExec {
    fn new(input: Arc<dyn ExecutionPlan>, fraction: f64, seed: u64) -> SampleExec {
        let p = input.properties();
        let properties = Arc::new(PlanProperties::new(
            EquivalenceProperties::new(input.schema()),
            p.partitioning.clone(),
            p.emission_type,
            p.boundedness,
        ));
        SampleExec { input, fraction, seed, properties }
    }
}

impl DisplayAs for SampleExec {
    fn fmt_as(&self, _t: DisplayFormatType, f: &mut Formatter) -> fmt::Result {
        write!(f, "SampleExec: system={}, seed={}", self.fraction, self.seed)
    }
}

impl ExecutionPlan for SampleExec {
    fn name(&self) -> &'static str {
        "SampleExec"
    }

    fn properties(&self) -> &Arc<PlanProperties> {
        &self.properties
    }

    fn maintains_input_order(&self) -> Vec<bool> {
        vec![true]
    }

    fn children(&self) -> Vec<&Arc<dyn ExecutionPlan>> {
        vec![&self.input]
    }

    fn apply_expressions(
        &self,
        _f: &mut dyn FnMut(&Arc<dyn PhysicalExpr>) -> Result<TreeNodeRecursion>,
    ) -> Result<TreeNodeRecursion> {
        Ok(TreeNodeRecursion::Continue)
    }

    fn with_new_children(self: Arc<Self>, mut children: Vec<Arc<dyn ExecutionPlan>>) -> Result<Arc<dyn ExecutionPlan>> {
        Ok(Arc::new(SampleExec::new(children.swap_remove(0), self.fraction, self.seed)))
    }

    fn execute(&self, partition: usize, context: Arc<TaskContext>) -> Result<SendableRecordBatchStream> {
        let input = self.input.execute(partition, context)?;
        let schema = input.schema();
        let (fraction, seed) = (self.fraction, self.seed);
        let kept = input.filter(move |batch| {
            std::future::ready(batch.as_ref().map_or(true, |b| keep(b, seed) < fraction))
        });
        Ok(Box::pin(RecordBatchStreamAdapter::new(schema, kept)))
    }
}

/// A value in [0, 1) drawn for `batch` from `seed` and its first row, so
/// that a seed keeps the same blocks whichever partition reads them.
fn keep(batch: &RecordBatch, seed: u64) -> f64 {
    let mut h = DefaultHasher::new();
    seed.hash(&mut h);
    for column in batch.columns().iter().filter(|_| batch.num_rows() > 0) {
        ScalarValue::try_from_array(column, 0).ok().hash(&mut h);
    }
    (h.finish() >> 11) as f64 / (1u64 << 53) as f64
}
