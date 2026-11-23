//! Accuracy evaluations of cardinal: how tightly it bounds a query's
//! cardinality given some set of reference plans, over prebaked
//! benchmarks ([`bench`]). Each run writes raw records ([`record`]).
//! See `EVAL.md` at the repository's root for the plan.

pub mod bench;
pub mod holdout;
pub mod jobs;
pub mod record;
pub mod rng;
