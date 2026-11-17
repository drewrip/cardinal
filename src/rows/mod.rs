//! Rows, named by how they derive from the base tables.
//!
//! A selectivity, a distinct count or a row count is a property of the rows
//! it is measured over. Many plans produce the same rows in different ways:
//! a filter pushed into a scan or applied above a projection, joins in
//! either order. A [`Context`] names those rows canonically, so that the
//! same rows read the same whichever plan computed them, executed or not.
//! [Link](crate::link) relates contexts by how their names relate
//! (`rows::contain`), and facts hold for the contexts they were read over.

mod context;
pub(crate) mod canonical;
pub(crate) mod contain;
pub(crate) mod first;
pub(crate) mod logical;
pub(crate) mod rewrite;

pub use context::{Context, Exists, ExistsKind, Term, terms};
pub(crate) use context::join;

/// The tables `ctx` draws on, by base table, each as often as it does.
pub(crate) fn bases(ctx: &Context) -> Vec<String> {
    let mut out: Vec<String> = ctx.tables().iter().map(|t| crate::observed::base_table(t).unwrap_or(t).to_string()).collect();
    out.sort();
    out
}
