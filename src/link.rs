//! Link: properties between rows the plan's shape does not relate.
//!
//! The [rules](crate::rules) apply [properties](crate::properties) where
//! the plan's shape makes the relationship plain: an operator and its
//! input, one op output. Link is to relate the rest: operators off one
//! root-to-leaf path. It asserts nothing yet.

use crate::analysis::Analyzer;

/// Asserts every property link finds between the rows of `a`'s operators,
/// once its rules have visited every plan. None yet.
pub fn link_all(a: &Analyzer) {
    let _ = a;
}
