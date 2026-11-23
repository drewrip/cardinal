//! Predicates over base columns, encoded in Z3 for [link](crate::link) to
//! decide how two sets of rows relate.
//!
//! The encoding is SQL's three-valued logic. A boolean is a pair
//! `(is_true, is_false)`, both false when NULL; an integer is a pair
//! `(value, null)`. A row is kept when its predicate is TRUE.
//!
//! Supported: integer and boolean columns and literals, NULL, comparisons
//! (`= != < <= > >=` of integers, `= !=` of booleans, TRUE or FALSE only
//! when neither side is NULL, and `IS [NOT] DISTINCT FROM` of integers),
//! and `AND`, `OR`, `NOT` in Kleene logic.
//!
//! Anything else is weakened, never dropped: an integer- or boolean-typed
//! expression becomes a fresh unknown of its type, the same one for equal
//! expressions within one [`Encoder`] (a boolean unknown is never both TRUE
//! and FALSE). A comparison of operands of other types, casts, `IS NULL`,
//! `LIKE`, arithmetic, dates and decimals become unknowns too. A formula
//! valid whatever the unknowns is valid of the expressions they stand for.

use std::collections::HashMap;

use datafusion::arrow::datatypes::DataType;
use datafusion::common::{Column, DFSchema, ScalarValue};
use datafusion::logical_expr::{BinaryExpr, Expr, ExprSchemable, Operator};
use z3::ast::{Bool, Int};

use crate::analysis::symbol;

/// An encoded value.
#[derive(Clone)]
enum Value {
    /// `(is_true, is_false)`.
    Bool(Bool, Bool),
    /// `(value, null)`.
    Int(Int, Bool),
    /// An untyped NULL.
    Null,
}

/// Encodes predicates over base columns in Z3, three-valued. Each encoder
/// has its own variables: one (and a null flag) per column it reads, one
/// per unknown.
pub(crate) struct Encoder<'a> {
    prefix: String,
    /// The base columns' types and nullability.
    schema: &'a DFSchema,
    next: usize,
    /// Each column's and unknown's value, by its index in `values`: the
    /// values drop in the order they were made, so Z3 reuses the ids of
    /// their terms in an order that does not depend on hashing.
    columns: HashMap<Column, usize>,
    unknowns: HashMap<Expr, usize>,
    values: Vec<Option<Value>>,
}

impl<'a> Encoder<'a> {
    /// An encoder whose variables are named `{prefix}_{n}`: `prefix` must be
    /// unique to it. `schema` types the base columns.
    pub(crate) fn new(prefix: &str, schema: &'a DFSchema) -> Self {
        Encoder { prefix: symbol(prefix), schema, next: 0, columns: HashMap::new(), unknowns: HashMap::new(), values: vec![] }
    }

    /// Stores `v`, returning its index.
    fn keep(&mut self, v: Option<Value>) -> usize {
        self.values.push(v);
        self.values.len() - 1
    }

    /// The rows the conjuncts all hold TRUE on, as a Z3 formula.
    pub(crate) fn holds(&mut self, conjuncts: &[Expr]) -> Bool {
        let t: Vec<Bool> = conjuncts.iter().map(|c| self.boolean(c).0).collect();
        Bool::and(&t)
    }

    fn name(&mut self) -> String {
        self.next += 1;
        format!("{}_{}", self.prefix, self.next - 1)
    }

    fn fresh_bool(&mut self) -> Bool {
        Bool::new_const(self.name())
    }

    /// `e` as a boolean `(is_true, is_false)`: a boolean unknown if it is
    /// not one.
    fn boolean(&mut self, e: &Expr) -> (Bool, Bool) {
        match self.value(e) {
            Some(Value::Bool(t, f)) => (t, f),
            Some(Value::Null) => (Bool::from_bool(false), Bool::from_bool(false)),
            _ => self.bool_unknown(e),
        }
    }

    /// `e`'s value, or `None` if it is neither integer nor boolean.
    fn value(&mut self, e: &Expr) -> Option<Value> {
        match e {
            Expr::Alias(a) => self.value(&a.expr),
            Expr::Column(c) => self.column(c),
            Expr::Literal(v, _) => literal(v).or_else(|| self.unknown(e)),
            Expr::Not(x) => {
                let (t, f) = self.boolean(x);
                Some(Value::Bool(f, t))
            }
            Expr::BinaryExpr(BinaryExpr { left, op, right }) => match op {
                Operator::And | Operator::Or => {
                    let (lt, lf) = self.boolean(left);
                    let (rt, rf) = self.boolean(right);
                    Some(match op {
                        Operator::And => Value::Bool(Bool::and(&[lt, rt]), Bool::or(&[lf, rf])),
                        _ => Value::Bool(Bool::or(&[lt, rt]), Bool::and(&[lf, rf])),
                    })
                }
                _ => match (self.value(left), self.value(right)) {
                    (Some(l), Some(r)) => compare(*op, l, r).map(|(t, f)| Value::Bool(t, f)).or_else(|| self.unknown(e)),
                    _ => self.unknown(e),
                },
            },
            _ => self.unknown(e),
        }
    }

    /// The variables of base column `c`, if it is an integer or boolean.
    fn column(&mut self, c: &Column) -> Option<Value> {
        if let Some(&i) = self.columns.get(c) {
            return self.values[i].clone();
        }
        let field = self.schema.field_with_qualified_name(c.relation.as_ref()?, &c.name).ok()?;
        let null = match field.is_nullable() {
            true => self.fresh_bool(),
            false => Bool::from_bool(false),
        };
        let v = match field.data_type() {
            t if t.is_integer() => Value::Int(Int::new_const(self.name()), null),
            DataType::Boolean => {
                let b = self.fresh_bool();
                Value::Bool(Bool::and(&[null.not(), b.clone()]), Bool::and(&[null.not(), b.not()]))
            }
            _ => return None,
        };
        let i = self.keep(Some(v.clone()));
        self.columns.insert(c.clone(), i);
        Some(v)
    }

    /// A fresh unknown of `e`'s type, the same for equal expressions.
    fn unknown(&mut self, e: &Expr) -> Option<Value> {
        if let Some(&i) = self.unknowns.get(e) {
            return self.values[i].clone();
        }
        let v = match e.get_type(self.schema) {
            Ok(t) if t.is_integer() => Some(Value::Int(Int::new_const(self.name()), self.fresh_bool())),
            Ok(DataType::Boolean) => Some(self.new_bool_unknown()),
            _ => None,
        };
        let i = self.keep(v.clone());
        self.unknowns.insert(e.clone(), i);
        v
    }

    /// A boolean unknown standing for `e`, whatever its type.
    fn bool_unknown(&mut self, e: &Expr) -> (Bool, Bool) {
        if let Some(&i) = self.unknowns.get(e)
            && let Some(Value::Bool(t, f)) = &self.values[i]
        {
            return (t.clone(), f.clone());
        }
        let v = self.new_bool_unknown();
        let i = self.keep(Some(v.clone()));
        self.unknowns.insert(e.clone(), i);
        let Value::Bool(t, f) = v else { unreachable!() };
        (t, f)
    }

    fn new_bool_unknown(&mut self) -> Value {
        let (t, f) = (self.fresh_bool(), self.fresh_bool());
        // Never both TRUE and FALSE: the two flags are a three-valued boolean.
        let f = Bool::and(&[f, t.not()]);
        Value::Bool(t, f)
    }
}

/// An integer or boolean literal, or NULL.
fn literal(v: &ScalarValue) -> Option<Value> {
    if v.is_null() {
        return Some(match v.data_type() {
            t if t.is_integer() => Value::Int(Int::from_i64(0), Bool::from_bool(true)),
            DataType::Boolean => {
                Value::Bool(Bool::from_bool(false), Bool::from_bool(false))
            }
            DataType::Null => Value::Null,
            _ => return None,
        });
    }
    let int = |n: i64| Some(Value::Int(Int::from_i64(n), Bool::from_bool(false)));
    match *v {
        ScalarValue::Boolean(Some(b)) => Some(Value::Bool(Bool::from_bool(b), Bool::from_bool(!b))),
        ScalarValue::Int8(Some(n)) => int(n.into()),
        ScalarValue::Int16(Some(n)) => int(n.into()),
        ScalarValue::Int32(Some(n)) => int(n.into()),
        ScalarValue::Int64(Some(n)) => int(n),
        ScalarValue::UInt8(Some(n)) => int(n.into()),
        ScalarValue::UInt16(Some(n)) => int(n.into()),
        ScalarValue::UInt32(Some(n)) => int(n.into()),
        ScalarValue::UInt64(Some(n)) => Some(Value::Int(Int::from_u64(n), Bool::from_bool(false))),
        _ => None,
    }
}

/// `l op r` as `(is_true, is_false)`, if supported.
fn compare(op: Operator, l: Value, r: Value) -> Option<(Bool, Bool)> {
    let f = || Bool::from_bool(false);
    match (l, r) {
        (Value::Null, _) | (_, Value::Null)
            if matches!(op, Operator::Eq | Operator::NotEq | Operator::Lt | Operator::LtEq | Operator::Gt | Operator::GtEq) =>
        {
            Some((f(), f()))
        }
        (Value::Int(a, an), Value::Int(b, bn)) => {
            let cmp = match op {
                Operator::Eq => a.eq(&b),
                Operator::NotEq => a.eq(&b).not(),
                Operator::Lt => a.lt(&b),
                Operator::LtEq => a.le(&b),
                Operator::Gt => a.gt(&b),
                Operator::GtEq => a.ge(&b),
                Operator::IsNotDistinctFrom | Operator::IsDistinctFrom => {
                    let same = Bool::or(&[
                        Bool::and(&[an.clone(), bn.clone()]),
                        Bool::and(&[an.not(), bn.not(), a.eq(&b)]),
                    ]);
                    return Some(match op {
                        Operator::IsNotDistinctFrom => (same.clone(), same.not()),
                        _ => (same.not(), same),
                    });
                }
                _ => return None,
            };
            let known = Bool::and(&[an.not(), bn.not()]);
            Some((Bool::and(&[known.clone(), cmp.clone()]), Bool::and(&[known, cmp.not()])))
        }
        (Value::Bool(at, af), Value::Bool(bt, bf)) => {
            let same = Bool::or(&[Bool::and(&[at.clone(), bt.clone()]), Bool::and(&[af.clone(), bf.clone()])]);
            let differ = Bool::or(&[Bool::and(&[at, bf]), Bool::and(&[af, bt])]);
            match op {
                Operator::Eq => Some((same, differ)),
                Operator::NotEq => Some((differ, same)),
                _ => None,
            }
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use datafusion::arrow::datatypes::{Field, Schema};
    use datafusion::logical_expr::{col, lit};
    use datafusion::prelude::Expr;
    use z3::{SatResult, Solver};

    use super::*;

    fn schema(nullable: bool) -> DFSchema {
        let s = Schema::new(vec![Field::new("a", DataType::Int32, nullable)]);
        DFSchema::try_from_qualified_schema("i0", &s).unwrap()
    }

    fn a() -> Expr {
        col("i0.a")
    }

    /// True if `f` holds for every value of its variables.
    fn valid(f: Bool) -> bool {
        let s = Solver::new();
        s.assert(f.not());
        s.check() == SatResult::Unsat
    }

    #[test]
    fn complementary_ranges_are_disjoint() {
        for nullable in [false, true] {
            let s = schema(nullable);
            let mut e = Encoder::new("t", &s);
            let p1 = e.holds(&[a().lt(lit(18i32))]);
            let p2 = e.holds(&[a().gt_eq(lit(18i32))]);
            assert!(valid(Bool::and(&[p1, p2]).not()), "nullable: {nullable}");
        }
    }

    #[test]
    fn excluded_middle_needs_non_null() {
        for (nullable, expected) in [(false, true), (true, false)] {
            let s = schema(nullable);
            let mut e = Encoder::new("t", &s);
            let p1 = e.holds(&[]);
            let p2 = e.holds(&[a().gt(lit(5i32)).or(a().lt_eq(lit(5i32)))]);
            assert_eq!(valid(p1.implies(p2)), expected, "nullable: {nullable}");
        }
    }

    #[test]
    fn unknowns_are_memoized() {
        let s = schema(true);
        let mut e = Encoder::new("t", &s);
        let f = a().like(lit("x%"));
        let p1 = e.holds(&[f.clone(), a().gt(lit(1i32))]);
        let p2 = e.holds(&[f]);
        assert!(valid(p1.implies(p2)));
    }
}
