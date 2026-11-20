//! Analyzing several base queries alike: the same options, reference plans
//! and row counts.

use std::sync::{Arc, OnceLock};

use datafusion::prelude::SessionContext;
use rayon::ThreadPool;
use rayon::prelude::*;

use crate::observed::{Catalog, ObservedPlan};
use crate::{Analysis, Bounds, Builder, Options, PlanBounds, Result};

/// Several queries to analyze with the same [`Options`], reference plans
/// and row counts, each as [`Builder::build`] analyzes it alone. Made by
/// [`Analysis::sqls`] or [`Analysis::batch`].
///
/// [`Batch::build`], [`Analysis::bounds_all`] and
/// [`Analysis::plan_bounds_all`] run in parallel, one query per thread of
/// a pool of the library's own (one thread per core), and block until all
/// are done: from async code, call them in `spawn_blocking`. Each query
/// gets the results it gets alone: it runs in a Z3 context of its own,
/// and its solver checks are limited by work, not time.
///
/// ```ignore
/// let analyses: Vec<Result<Analysis>> = Analysis::sqls(&ctx, [q1, q2, q3]).await?
///     .options(options)
///     .with_plans(&profiles)
///     .with_cardinalities([("lineitem", 6001215)])
///     .build();
/// let bounds: Vec<Result<Bounds>> = Analysis::bounds_all(analyses.iter().flatten());
/// ```
pub struct Batch<'c> {
    /// In input order; an `Err` for a query that could not be planned.
    queries: Vec<Result<Builder<'c>>>,
}

impl Analysis {
    /// Each of `queries` as [`Analysis::sql`] makes it, sharing one read of
    /// `ctx`'s catalog. Fails only if the catalog cannot be read; a query
    /// that cannot be planned is an `Err` at its index.
    pub async fn sqls(ctx: &SessionContext, queries: impl IntoIterator<Item = impl AsRef<str>>) -> Result<Batch<'static>> {
        let catalog = Arc::new(Catalog::from_context(ctx).await?);
        let mut out = vec![];
        for sql in queries {
            out.push(Builder::sql(ctx, sql.as_ref(), catalog.clone()).await);
        }
        Ok(Batch { queries: out })
    }

    /// A batch of `builders` from any source, e.g. engine plans
    /// ([`Analysis::duckdb`]).
    pub fn batch<'c>(builders: impl IntoIterator<Item = Result<Builder<'c>>>) -> Batch<'c> {
        Batch { queries: builders.into_iter().collect() }
    }

    /// [`Analysis::bounds`] of each of `analyses`, in order, in parallel
    /// ([`Batch`]).
    pub fn bounds_all<'a>(analyses: impl IntoIterator<Item = &'a Analysis>) -> Vec<Result<Bounds>> {
        par_map(analyses.into_iter().collect(), Analysis::bounds)
    }

    /// [`Analysis::plan_bounds`] of each of `analyses`, in order, in
    /// parallel ([`Batch`]).
    pub fn plan_bounds_all<'a>(analyses: impl IntoIterator<Item = &'a Analysis>) -> Vec<Result<PlanBounds>> {
        par_map(analyses.into_iter().collect(), Analysis::plan_bounds)
    }
}

impl<'c> Batch<'c> {
    /// [`Builder::options`] of every query.
    pub fn options(self, options: Options) -> Self {
        self.map(|b| b.options(options.clone()))
    }

    /// [`Builder::with_plans`] of every query.
    pub fn with_plans(self, plans: impl IntoIterator<Item = &'c ObservedPlan>) -> Self {
        let plans: Vec<&ObservedPlan> = plans.into_iter().collect();
        self.map(|b| b.with_plans(plans.iter().copied()))
    }

    /// [`Builder::with_cardinalities`] of every query.
    pub fn with_cardinalities<S: Into<String>>(self, tables: impl IntoIterator<Item = (S, u64)>) -> Self {
        let tables: Vec<(String, u64)> = tables.into_iter().map(|(t, n)| (t.into(), n)).collect();
        self.map(|b| b.with_cardinalities(tables.iter().cloned()))
    }

    /// How many queries the batch holds.
    pub fn len(&self) -> usize {
        self.queries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.queries.is_empty()
    }

    /// Each query's analysis, in input order: [`Builder::build`] of each,
    /// in parallel, or the error that query was made with.
    pub fn build(self) -> Vec<Result<Analysis>> {
        par_map(self.queries, |q| q?.build())
    }

    fn map(self, f: impl Fn(Builder<'c>) -> Builder<'c>) -> Self {
        Batch { queries: self.queries.into_iter().map(|q| q.map(&f)).collect() }
    }
}

/// `f` of each of `items`, in order, on the pool's threads, the caller
/// waiting. A panic in `f` reaches the caller.
fn par_map<T: Send, R: Send>(items: Vec<T>, f: impl Fn(T) -> R + Send + Sync) -> Vec<R> {
    static POOL: OnceLock<ThreadPool> = OnceLock::new();
    let pool = POOL.get_or_init(|| {
        // The plan walk and Z3 recurse deeply: a main thread's stack, not
        // rayon's default 2 MiB.
        rayon::ThreadPoolBuilder::new()
            .stack_size(8 << 20)
            .thread_name(|i| format!("cardinal-{i}"))
            .build()
            .expect("the batch thread pool starts")
    });
    pool.install(|| items.into_par_iter().map(f).collect())
}

/// What runs on the pool's threads.
const _: fn() = || {
    fn send_sync<T: Send + Sync>() {}
    send_sync::<Builder<'_>>();
    send_sync::<Analysis>();
};
