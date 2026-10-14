//! Facts saved and read back, with serde.
//!
//! Everything but a [`Term`]'s expression derives its form. An expression
//! goes as DataFusion's protobuf message for it, which serde writes as JSON
//! or any other format, and reads back with the functions a default
//! session knows.

use std::collections::BTreeMap;
use std::sync::{Arc, LazyLock};

use datafusion::execution::TaskContext;
use datafusion::prelude::SessionContext;
use datafusion_proto::logical_plan::DefaultLogicalExtensionCodec;
use datafusion_proto::logical_plan::from_proto::parse_expr;
use datafusion_proto::logical_plan::to_proto::serialize_expr;
use datafusion_proto::protobuf::LogicalExprNode;
use serde::de::Error as _;
use serde::ser::Error as _;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::Term;

static FUNCTIONS: LazyLock<Arc<TaskContext>> = LazyLock::new(|| SessionContext::new().task_ctx());

impl Serialize for Term {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        serialize_expr(&self.expr, &DefaultLogicalExtensionCodec {}).map_err(S::Error::custom)?.serialize(s)
    }
}

impl<'de> Deserialize<'de> for Term {
    /// The term as it was: its expression was canonical when written.
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Term, D::Error> {
        let node = LogicalExprNode::deserialize(d)?;
        let expr = parse_expr(&node, &FUNCTIONS, &DefaultLogicalExtensionCodec {}).map_err(D::Error::custom)?;
        Ok(Term::canonical(expr))
    }
}

/// A map's values, written as a list.
pub(super) fn values<K, V: Serialize, S: Serializer>(m: &BTreeMap<K, V>, s: S) -> Result<S::Ok, S::Error> {
    s.collect_seq(m.values())
}
