//! Expressions over a term's columns: their canonical text (§5), their
//! types, and their meaning in SQL's three-valued logic as SMT, for the
//! quantifier-free decisions of §6.2.
//!
//! A column is named globally (`lineitem.l_quantity`, an alias's
//! `nation.n_name#2`, an expression's `c:<text>`, an aggregate's
//! `a:sum(lineitem.l_quantity)`), so an expression's text denotes it
//! wherever it appears.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use datafusion::arrow::datatypes::DataType;
use datafusion::common::ScalarValue;
use datafusion::logical_expr::expr::{InList, Like};
use datafusion::logical_expr::{Between, BinaryExpr, Cast, Expr, Operator, TryCast};

pub(crate) type Col = String;

/// A value's type, as the decisions see it. Dates and timestamps are
/// integers; decimals and floats reals.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Ty {
    Int,
    Real,
    Str,
    Bool,
    /// A type the decisions don't model: compared only for equality, as an
    /// uninterpreted sort.
    Other,
}

impl Ty {
    pub(crate) fn of(t: &DataType) -> Ty {
        use DataType::*;
        match t {
            Int8 | Int16 | Int32 | Int64 | UInt8 | UInt16 | UInt32 | UInt64 => Ty::Int,
            Date32 | Date64 | Timestamp(..) | Time32(_) | Time64(_) => Ty::Int,
            Decimal32(..) | Decimal64(..) | Decimal128(..) | Decimal256(..) | Float16 | Float32 | Float64 => Ty::Real,
            Utf8 | Utf8View | LargeUtf8 => Ty::Str,
            Boolean => Ty::Bool,
            Dictionary(_, v) => Ty::of(v),
            _ => Ty::Other,
        }
    }

    pub(crate) fn numeric(self) -> bool {
        matches!(self, Ty::Int | Ty::Real)
    }

    fn smt(self) -> &'static str {
        match self {
            Ty::Int => "Int",
            Ty::Real => "Real",
            Ty::Str => "String",
            Ty::Bool => "Bool",
            Ty::Other => "Val",
        }
    }
}

/// A literal. Decimals are exact fractions `num/den`, `den > 0`, in lowest
/// terms; one that is whole is an `Int`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Lit {
    Int(i128),
    Dec(i128, i128),
    Str(String),
    Bool(bool),
    Null,
}

impl Lit {
    pub(crate) fn dec(num: i128, den: i128) -> Lit {
        let (mut n, mut d) = if den < 0 { (-num, -den) } else { (num, den) };
        let g = gcd(n.unsigned_abs(), d.unsigned_abs()) as i128;
        if g > 1 {
            n /= g;
            d /= g;
        }
        if d == 1 { Lit::Int(n) } else { Lit::Dec(n, d) }
    }

    /// The literal's value as a fraction, if it is a number.
    pub(crate) fn ratio(&self) -> Option<(i128, i128)> {
        match self {
            Lit::Int(n) => Some((*n, 1)),
            Lit::Dec(n, d) => Some((*n, *d)),
            _ => None,
        }
    }

    pub(crate) fn text(&self) -> String {
        match self {
            Lit::Int(n) => n.to_string(),
            Lit::Dec(n, d) => decimal_text(*n, *d),
            Lit::Str(s) => format!("'{}'", s.replace('\'', "''")),
            Lit::Bool(b) => b.to_string(),
            Lit::Null => "NULL".into(),
        }
    }

    fn smt(&self) -> String {
        match self {
            Lit::Int(n) => int_smt(*n),
            Lit::Dec(n, d) => format!("(/ {} {}.0)", real_smt(*n), d),
            Lit::Str(s) => format!("\"{}\"", smt_string(s)),
            Lit::Bool(b) => b.to_string(),
            Lit::Null => unreachable!("NULL has no value"),
        }
    }

    pub(crate) fn from_scalar(v: &ScalarValue) -> Option<Lit> {
        use ScalarValue::*;
        if v.is_null() {
            return Some(Lit::Null);
        }
        Some(match v {
            Boolean(Some(b)) => Lit::Bool(*b),
            Int8(Some(n)) => Lit::Int(*n as i128),
            Int16(Some(n)) => Lit::Int(*n as i128),
            Int32(Some(n)) => Lit::Int(*n as i128),
            Int64(Some(n)) => Lit::Int(*n as i128),
            UInt8(Some(n)) => Lit::Int(*n as i128),
            UInt16(Some(n)) => Lit::Int(*n as i128),
            UInt32(Some(n)) => Lit::Int(*n as i128),
            UInt64(Some(n)) => Lit::Int(*n as i128),
            Date32(Some(d)) => Lit::Int(*d as i128),
            Date64(Some(ms)) => Lit::Int((*ms as i128).div_euclid(86_400_000)),
            TimestampSecond(Some(t), _)
            | TimestampMillisecond(Some(t), _)
            | TimestampMicrosecond(Some(t), _)
            | TimestampNanosecond(Some(t), _) => Lit::Int(*t as i128),
            Decimal128(Some(v), _, s) => Lit::dec(*v, 10i128.checked_pow(u32::try_from(*s).ok()?)?),
            Float64(Some(f)) => float(*f)?,
            Float32(Some(f)) => float(*f as f64)?,
            Utf8(Some(s)) | Utf8View(Some(s)) | LargeUtf8(Some(s)) => Lit::Str(s.clone()),
            Dictionary(_, v) => return Lit::from_scalar(v),
            _ => return None,
        })
    }
}

/// A finite float as an exact fraction, if it fits.
fn float(f: f64) -> Option<Lit> {
    if !f.is_finite() {
        return None;
    }
    let mut den: i128 = 1;
    let mut x = f;
    while x.fract() != 0.0 {
        x *= 2.0;
        den = den.checked_mul(2)?;
        if den > 1 << 60 {
            return None;
        }
    }
    if x.abs() > 1e30 {
        return None;
    }
    Some(Lit::dec(x as i128, den))
}

fn decimal_text(n: i128, d: i128) -> String {
    // A power of ten prints as a decimal, anything else as a fraction.
    let mut p = d;
    let mut digits = 0;
    while p % 10 == 0 {
        p /= 10;
        digits += 1;
    }
    let (n2, d2) = match p {
        1 => (n, d),
        2 | 5 => {
            let f = if p == 2 { 5 } else { 2 };
            digits += 1;
            (n * f, d * f)
        }
        _ => return format!("{n}/{d}"),
    };
    let sign = if n2 < 0 { "-" } else { "" };
    let a = n2.unsigned_abs();
    let w = a / d2 as u128;
    let f = a % d2 as u128;
    format!("{sign}{w}.{f:0digits$}")
}

fn int_smt(n: i128) -> String {
    if n < 0 { format!("(- {})", n.unsigned_abs()) } else { n.to_string() }
}

fn real_smt(n: i128) -> String {
    if n < 0 { format!("(- {}.0)", n.unsigned_abs()) } else { format!("{n}.0") }
}

fn smt_string(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        match c {
            '"' => out.push_str("\"\""),
            c if (' '..='~').contains(&c) => out.push(c),
            c => write!(out, "\\u{{{:x}}}", c as u32).unwrap(),
        }
    }
    out
}

fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a.max(1)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Cmp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl Cmp {
    fn text(self) -> &'static str {
        match self {
            Cmp::Eq => "=",
            Cmp::Ne => "!=",
            Cmp::Lt => "<",
            Cmp::Le => "<=",
            Cmp::Gt => ">",
            Cmp::Ge => ">=",
        }
    }

    /// `b op' a` for `a op b`.
    pub(crate) fn flip(self) -> Cmp {
        match self {
            Cmp::Lt => Cmp::Gt,
            Cmp::Le => Cmp::Ge,
            Cmp::Gt => Cmp::Lt,
            Cmp::Ge => Cmp::Le,
            c => c,
        }
    }

    /// `NOT (a op b)` as `a op' b`.
    pub(crate) fn negate(self) -> Cmp {
        match self {
            Cmp::Eq => Cmp::Ne,
            Cmp::Ne => Cmp::Eq,
            Cmp::Lt => Cmp::Ge,
            Cmp::Le => Cmp::Gt,
            Cmp::Gt => Cmp::Le,
            Cmp::Ge => Cmp::Lt,
        }
    }

    pub(crate) fn of_op(op: Operator) -> Option<Cmp> {
        Some(match op {
            Operator::Eq => Cmp::Eq,
            Operator::NotEq => Cmp::Ne,
            Operator::Lt => Cmp::Lt,
            Operator::LtEq => Cmp::Le,
            Operator::Gt => Cmp::Gt,
            Operator::GtEq => Cmp::Ge,
            _ => return None,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Arith {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

impl Arith {
    fn text(self) -> &'static str {
        match self {
            Arith::Add => "+",
            Arith::Sub => "-",
            Arith::Mul => "*",
            Arith::Div => "/",
            Arith::Mod => "%",
        }
    }
}

/// An expression over columns. Booleans are predicates, in SQL's
/// three-valued logic.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum E {
    Col(Col, Ty),
    Lit(Lit, Ty),
    Arith(Arith, Box<E>, Box<E>, Ty),
    Neg(Box<E>),
    Cmp(Cmp, Box<E>, Box<E>),
    And(Vec<E>),
    Or(Vec<E>),
    Not(Box<E>),
    IsNull(Box<E>),
    /// `x LIKE pattern`, with `%` and `_`.
    Like(Box<E>, String),
    /// A deterministic function the decisions don't interpret: `name` over
    /// its arguments, of type `Ty`.
    Func(String, Vec<E>, Ty),
}

impl E {
    pub(crate) fn ty(&self) -> Ty {
        match self {
            E::Col(_, t) | E::Lit(_, t) | E::Arith(.., t) | E::Func(.., t) => *t,
            E::Neg(e) => e.ty(),
            _ => Ty::Bool,
        }
    }

    pub(crate) fn is_bool(&self) -> bool {
        self.ty() == Ty::Bool
    }

    /// The columns it reads.
    pub(crate) fn reads(&self) -> BTreeSet<Col> {
        let mut out = BTreeSet::new();
        self.visit(&mut |e| {
            if let E::Col(c, _) = e {
                out.insert(c.clone());
            }
        });
        out
    }

    pub(crate) fn visit(&self, f: &mut dyn FnMut(&E)) {
        f(self);
        match self {
            E::Col(..) | E::Lit(..) => {}
            E::Arith(_, a, b, _) | E::Cmp(_, a, b) => {
                a.visit(f);
                b.visit(f);
            }
            E::Neg(a) | E::Not(a) | E::IsNull(a) | E::Like(a, _) => a.visit(f),
            E::And(xs) | E::Or(xs) | E::Func(_, xs, _) => xs.iter().for_each(|x| x.visit(f)),
        }
    }

    /// This expression with each column renamed by `f`.
    pub(crate) fn rename(&self, f: &dyn Fn(&str) -> Col) -> E {
        self.map_cols(&|c, t| E::Col(f(c), t))
    }

    /// This expression with each column replaced by `f`'s expression.
    pub(crate) fn map_cols(&self, f: &dyn Fn(&str, Ty) -> E) -> E {
        let m = |e: &E| e.map_cols(f);
        let b = |e: &E| Box::new(e.map_cols(f));
        match self {
            E::Col(c, t) => f(c, *t),
            E::Lit(..) => self.clone(),
            E::Arith(o, x, y, t) => E::Arith(*o, b(x), b(y), *t),
            E::Neg(x) => E::Neg(b(x)),
            E::Cmp(o, x, y) => E::Cmp(*o, b(x), b(y)),
            E::And(xs) => E::And(xs.iter().map(m).collect()),
            E::Or(xs) => E::Or(xs.iter().map(m).collect()),
            E::Not(x) => E::Not(b(x)),
            E::IsNull(x) => E::IsNull(b(x)),
            E::Like(x, p) => E::Like(b(x), p.clone()),
            E::Func(n, xs, t) => E::Func(n.clone(), xs.iter().map(m).collect(), *t),
        }
    }

    /// Canonical text: commutative operands sorted, conjunctions and
    /// disjunctions flattened, sorted and deduplicated.
    pub(crate) fn text(&self) -> String {
        match self {
            E::Col(c, _) => c.clone(),
            E::Lit(l, _) => l.text(),
            E::Arith(o @ (Arith::Add | Arith::Mul), a, b, _) => {
                let mut xs = [paren(a), paren(b)];
                xs.sort();
                format!("{}{}{}", xs[0], o.text(), xs[1])
            }
            E::Arith(o, a, b, _) => format!("{}{}{}", paren(a), o.text(), paren(b)),
            E::Neg(a) => format!("-{}", paren(a)),
            E::Cmp(o @ (Cmp::Eq | Cmp::Ne), a, b) => {
                let mut xs = [a.text(), b.text()];
                // A column first, then by text, so `5=a` reads `a=5`.
                xs.sort_by_key(|x| (!is_name(x), x.clone()));
                format!("{}{}{}", xs[0], o.text(), xs[1])
            }
            E::Cmp(o, a, b) => {
                // A literal on the right.
                if matches!(**a, E::Lit(..)) && !matches!(**b, E::Lit(..)) {
                    format!("{}{}{}", b.text(), o.flip().text(), a.text())
                } else {
                    format!("{}{}{}", a.text(), o.text(), b.text())
                }
            }
            E::And(xs) => joined(xs, " AND ", |x| matches!(x, E::Or(_))),
            E::Or(xs) => joined(xs, " OR ", |x| matches!(x, E::And(_))),
            E::Not(a) => format!("NOT ({})", a.text()),
            E::IsNull(a) => format!("{} IS NULL", paren(a)),
            E::Like(a, p) => format!("{} LIKE '{}'", paren(a), p.replace('\'', "''")),
            E::Func(n, xs, _) => {
                format!("{n}({})", xs.iter().map(E::text).collect::<Vec<_>>().join(","))
            }
        }
    }

    /// The negation normal form of `NOT self` (`negate`) or of `self`, for
    /// a predicate: NOT pushed onto comparisons, which flip.
    pub(crate) fn nnf(&self, negate: bool) -> E {
        match (self, negate) {
            (E::Not(a), n) => a.nnf(!n),
            (E::And(xs), false) => flat_and(xs.iter().map(|x| x.nnf(false)).collect()),
            (E::And(xs), true) => flat_or(xs.iter().map(|x| x.nnf(true)).collect()),
            (E::Or(xs), false) => flat_or(xs.iter().map(|x| x.nnf(false)).collect()),
            (E::Or(xs), true) => flat_and(xs.iter().map(|x| x.nnf(true)).collect()),
            (E::Cmp(o, a, b), true) => E::Cmp(o.negate(), a.clone(), b.clone()),
            (E::Lit(Lit::Bool(v), t), n) => E::Lit(Lit::Bool(*v != n), *t),
            (e, false) => e.clone(),
            (e, true) => E::Not(Box::new(e.clone())),
        }
    }

    /// Sorted and deduplicated conjunctions and disjunctions, everywhere.
    pub(crate) fn sorted(&self) -> E {
        match self {
            E::And(xs) => flat_and(xs.iter().map(E::sorted).collect()),
            E::Or(xs) => flat_or(xs.iter().map(E::sorted).collect()),
            E::Not(a) => E::Not(Box::new(a.sorted())),
            e => e.clone(),
        }
    }
}

fn is_name(x: &str) -> bool {
    x.chars().next().is_some_and(|c| c.is_alphabetic() || c == '_')
}

fn paren(e: &E) -> String {
    match e {
        E::Col(..) | E::Lit(..) | E::Func(..) => e.text(),
        _ => format!("({})", e.text()),
    }
}

fn joined(xs: &[E], sep: &str, wrap: impl Fn(&E) -> bool) -> String {
    let mut parts: Vec<String> = xs.iter().map(|x| if wrap(x) { format!("({})", x.text()) } else { x.text() }).collect();
    parts.sort();
    parts.dedup();
    parts.join(sep)
}

/// A conjunction of `xs`, nested conjunctions flattened, constants folded,
/// sorted by text and deduplicated.
pub(crate) fn flat_and(xs: Vec<E>) -> E {
    let mut out: Vec<E> = vec![];
    for x in xs {
        match x {
            E::And(ys) => out.extend(ys),
            E::Lit(Lit::Bool(true), _) => {}
            E::Lit(Lit::Bool(false), t) => return E::Lit(Lit::Bool(false), t),
            x => out.push(x),
        }
    }
    finish(out, true)
}

/// A disjunction, as [`flat_and`].
pub(crate) fn flat_or(xs: Vec<E>) -> E {
    let mut out: Vec<E> = vec![];
    for x in xs {
        match x {
            E::Or(ys) => out.extend(ys),
            E::Lit(Lit::Bool(false), _) => {}
            E::Lit(Lit::Bool(true), t) => return E::Lit(Lit::Bool(true), t),
            x => out.push(x),
        }
    }
    finish(out, false)
}

fn finish(mut out: Vec<E>, and: bool) -> E {
    out.sort_by_cached_key(E::text);
    out.dedup_by(|a, b| a.text() == b.text());
    match out.len() {
        0 => E::Lit(Lit::Bool(and), Ty::Bool),
        1 => out.pop().unwrap(),
        _ if and => E::And(out),
        _ => E::Or(out),
    }
}

/// Reads DataFusion expressions as [`E`], with each column given by `col`
/// (`None`: it does not resolve).
pub(crate) struct Reader<'a> {
    pub col: &'a dyn Fn(&datafusion::common::Column) -> Option<(Col, Ty)>,
}

impl Reader<'_> {
    /// `e`, or `None` if it reads something that does not resolve, or is
    /// volatile.
    pub(crate) fn read(&self, e: &Expr) -> Option<E> {
        if e.is_volatile() {
            return None;
        }
        self.go(e)
    }

    fn go(&self, e: &Expr) -> Option<E> {
        Some(match e {
            Expr::Column(c) => {
                let (name, t) = (self.col)(c)?;
                E::Col(name, t)
            }
            Expr::Alias(a) => self.go(&a.expr)?,
            Expr::Literal(v, _) => {
                let l = Lit::from_scalar(v)?;
                E::Lit(l, Ty::of(&v.data_type()))
            }
            Expr::BinaryExpr(BinaryExpr { left, op, right }) => {
                let (a, b) = (self.go(left)?, self.go(right)?);
                if let Some(c) = Cmp::of_op(*op) {
                    return Some(E::Cmp(c, Box::new(a), Box::new(b)));
                }
                let arith = |o| {
                    let t = match (a.ty(), b.ty()) {
                        (Ty::Int, Ty::Int) => Ty::Int,
                        (x, y) if x.numeric() && y.numeric() => Ty::Real,
                        _ => Ty::Other,
                    };
                    E::Arith(o, Box::new(a.clone()), Box::new(b.clone()), t)
                };
                match op {
                    Operator::And => flat_and(vec![a, b]),
                    Operator::Or => flat_or(vec![a, b]),
                    Operator::Plus => arith(Arith::Add),
                    Operator::Minus => arith(Arith::Sub),
                    Operator::Multiply => arith(Arith::Mul),
                    Operator::Divide => arith(Arith::Div),
                    Operator::Modulo => arith(Arith::Mod),
                    Operator::IsDistinctFrom | Operator::IsNotDistinctFrom => {
                        let eq = E::Cmp(Cmp::Eq, Box::new(a.clone()), Box::new(b.clone()));
                        let both = E::And(vec![E::IsNull(Box::new(a.clone())), E::IsNull(Box::new(b.clone()))]);
                        let same = flat_or(vec![eq, both]);
                        match op {
                            Operator::IsNotDistinctFrom => same,
                            _ => E::Not(Box::new(same)),
                        }
                    }
                    o => E::Func(format!("{o}"), vec![a, b], Ty::Other),
                }
            }
            Expr::Not(a) => E::Not(Box::new(self.go(a)?)),
            Expr::IsNull(a) => E::IsNull(Box::new(self.go(a)?)),
            Expr::IsNotNull(a) => E::Not(Box::new(E::IsNull(Box::new(self.go(a)?)))),
            Expr::Negative(a) => E::Neg(Box::new(self.go(a)?)),
            Expr::Between(Between { expr, negated, low, high }) => {
                let x = self.go(expr)?;
                let b = flat_and(vec![
                    E::Cmp(Cmp::Ge, Box::new(x.clone()), Box::new(self.go(low)?)),
                    E::Cmp(Cmp::Le, Box::new(x), Box::new(self.go(high)?)),
                ]);
                if *negated { E::Not(Box::new(b)) } else { b }
            }
            Expr::InList(InList { expr, list, negated }) => {
                let x = self.go(expr)?;
                let items: Option<Vec<E>> =
                    list.iter().map(|v| Some(E::Cmp(Cmp::Eq, Box::new(x.clone()), Box::new(self.go(v)?)))).collect();
                let b = flat_or(items?);
                if *negated { E::Not(Box::new(b)) } else { b }
            }
            Expr::Like(Like { negated, expr, pattern, escape_char: None, case_insensitive: false }) => {
                let Expr::Literal(v, _) = pattern.as_ref() else { return self.func("like", &[expr, pattern], Ty::Bool) };
                let Some(Lit::Str(p)) = Lit::from_scalar(v) else { return None };
                let b = E::Like(Box::new(self.go(expr)?), p);
                if *negated { E::Not(Box::new(b)) } else { b }
            }
            Expr::Cast(Cast { expr, field }) | Expr::TryCast(TryCast { expr, field }) => {
                let x = self.go(expr)?;
                let to = Ty::of(field.data_type());
                match (x.ty(), to) {
                    // Widening, or a date as a timestamp: the same value.
                    (Ty::Int, Ty::Int) | (Ty::Int, Ty::Real) | (Ty::Real, Ty::Real) | (Ty::Str, Ty::Str) => {
                        retype(x, to)
                    }
                    _ => E::Func(format!("cast_{}", field.data_type()), vec![x], to),
                }
            }
            Expr::ScalarFunction(f) => {
                let name = f.name();
                let args: Vec<&Expr> = f.args.iter().collect();
                // DuckDB's spellings of LIKE.
                let like = |pre: &str, post: &str| -> Option<E> {
                    let [x, Expr::Literal(v, _)] = args[..] else { return None };
                    let Some(Lit::Str(s)) = Lit::from_scalar(v) else { return None };
                    if s.contains(['%', '_']) {
                        return None;
                    }
                    Some(E::Like(Box::new(self.go(x)?), format!("{pre}{s}{post}")))
                };
                let found = match name {
                    "starts_with" => like("", "%"),
                    "ends_with" => like("%", ""),
                    "contains" => like("%", "%"),
                    _ => None,
                };
                if let Some(e) = found {
                    return Some(e);
                }
                let ty = match name {
                    "date_part" | "extract" | "length" | "character_length" | "strpos" => Ty::Int,
                    "substr" | "substring" | "upper" | "lower" | "trim" | "btrim" | "concat" => Ty::Str,
                    "date_trunc" => Ty::Int,
                    _ => Ty::Other,
                };
                let ty = if ty == Ty::Other { e_type(e) } else { ty };
                self.func(name, &args, ty)?
            }
            Expr::Case(c) => {
                let mut args: Vec<&Expr> = vec![];
                if let Some(x) = &c.expr {
                    args.push(x);
                }
                for (w, t) in &c.when_then_expr {
                    args.push(w);
                    args.push(t);
                }
                if let Some(x) = &c.else_expr {
                    args.push(x);
                }
                let ty = c.when_then_expr.first().map(|(_, t)| self.go(t).map(|t| t.ty())).flatten().unwrap_or(Ty::Other);
                self.func("case", &args, ty)?
            }
            _ => return None,
        })
    }

    fn func(&self, name: &str, args: &[&Expr], ty: Ty) -> Option<E> {
        let args: Option<Vec<E>> = args.iter().map(|a| self.go(a)).collect();
        Some(E::Func(name.to_string(), args?, ty))
    }
}

/// The type of a DataFusion expression whose type is not known without a
/// schema: only literal-typed functions are guessed.
fn e_type(_e: &Expr) -> Ty {
    Ty::Other
}

fn retype(e: E, to: Ty) -> E {
    match e {
        E::Col(c, _) => E::Col(c, to),
        E::Lit(Lit::Int(n), Ty::Int) if to == Ty::Real => E::Lit(Lit::Int(n), to),
        E::Lit(l, _) => E::Lit(l, to),
        E::Arith(o, a, b, _) => E::Arith(o, a, b, to),
        E::Func(n, a, _) => E::Func(n, a, to),
        e => e,
    }
}

/// SMT text for expressions in three-valued logic. Each column `c` is a
/// value `v!c` of its type and a flag `n!c`, true when it is NULL; each
/// uninterpreted function application is a fresh value and flag, named by
/// its text, so that two predicates over one agree on it.
#[derive(Default)]
pub(crate) struct Smt {
    /// Declarations needed, by name.
    pub decls: std::collections::BTreeMap<String, String>,
}

/// A value: its SMT term and when it is NULL.
pub(crate) struct Val {
    pub v: String,
    pub null: String,
}

/// A predicate: when it is TRUE, and when FALSE.
pub(crate) struct Truth {
    pub t: String,
    pub f: String,
}

impl Smt {
    pub(crate) fn var(&mut self, c: &str, ty: Ty) -> Val {
        let v = format!("|v!{c}|");
        let n = format!("|n!{c}|");
        if ty == Ty::Other {
            self.decls.insert("Val".into(), "(declare-sort Val 0)".into());
        }
        self.decls.insert(v.clone(), format!("(declare-const {v} {})", ty.smt()));
        self.decls.insert(n.clone(), format!("(declare-const {n} Bool)"));
        Val { v, null: n }
    }

    pub(crate) fn value(&mut self, e: &E) -> Option<Val> {
        Some(match e {
            E::Col(c, t) => self.var(c, *t),
            E::Lit(Lit::Null, _) => Val { v: "0".into(), null: "true".into() },
            E::Lit(l, t) => {
                let v = match (l, t) {
                    (Lit::Int(n), Ty::Real) => real_smt(*n),
                    (Lit::Int(_) | Lit::Dec(..), Ty::Other) => return None,
                    _ => l.smt(),
                };
                Val { v, null: "false".into() }
            }
            E::Neg(a) => {
                let a = self.value(a)?;
                Val { v: format!("(- {})", a.v), null: a.null }
            }
            E::Arith(o, a, b, t) => {
                let (x, y) = (self.value(a)?, self.value(b)?);
                let null = format!("(or {} {})", x.null, y.null);
                let (xv, yv) = match t {
                    Ty::Real => (to_real(a, x.v), to_real(b, y.v)),
                    Ty::Int => (x.v, y.v),
                    _ => return None,
                };
                let v = match (o, t) {
                    (Arith::Add, _) => format!("(+ {xv} {yv})"),
                    (Arith::Sub, _) => format!("(- {xv} {yv})"),
                    (Arith::Mul, _) => format!("(* {xv} {yv})"),
                    (Arith::Div, Ty::Real) => match constant(b) {
                        Some(k) if k != 0 => format!("(/ {xv} {yv})"),
                        _ => return None,
                    },
                    // SQL's integer division truncates, and `%` keeps the
                    // dividend's sign: by a nonzero constant only.
                    (Arith::Div | Arith::Mod, Ty::Int) => {
                        let k = constant(b).filter(|k| *k != 0)?;
                        let q = format!("(ite (>= {xv} 0) (div {xv} {k}) (- (div (- {xv}) {k})))", k = int_smt(k.abs()));
                        let q = if k < 0 { format!("(- {q})") } else { q };
                        match o {
                            Arith::Div => q,
                            _ => format!("(- {xv} (* {} {q}))", int_smt(k)),
                        }
                    }
                    _ => return None,
                };
                Val { v, null }
            }
            E::Func(..) => {
                let name = e.text();
                let t = e.ty();
                if t == Ty::Bool {
                    return None;
                }
                self.var(&format!("f:{name}"), t)
            }
            _ => return None,
        })
    }

    /// When predicate `e` is TRUE and when FALSE, or `None` for a value.
    pub(crate) fn truth(&mut self, e: &E) -> Option<Truth> {
        Some(match e {
            E::Lit(Lit::Bool(b), _) => Truth { t: b.to_string(), f: (!b).to_string() },
            E::Lit(Lit::Null, _) => Truth { t: "false".into(), f: "false".into() },
            E::Col(..) | E::Func(..) if e.ty() == Ty::Bool => {
                let name = match e {
                    E::Col(c, _) => c.clone(),
                    _ => format!("f:{}", e.text()),
                };
                let x = self.var(&name, Ty::Bool);
                Truth { t: format!("(and (not {}) {})", x.null, x.v), f: format!("(and (not {}) (not {}))", x.null, x.v) }
            }
            E::Cmp(o, a, b) => {
                let (x, y) = (self.value(a)?, self.value(b)?);
                let (xv, yv) = match (a.ty(), b.ty()) {
                    (Ty::Int, Ty::Real) => (format!("(to_real {})", x.v), y.v),
                    (Ty::Real, Ty::Int) => (x.v, format!("(to_real {})", y.v)),
                    (s, t) if s == t => (x.v, y.v),
                    _ => return None,
                };
                let ty = if a.ty() == Ty::Int && b.ty() == Ty::Int { Ty::Int } else { a.ty().max(b.ty()) };
                let rel = match (o, ty) {
                    (Cmp::Eq, _) => format!("(= {xv} {yv})"),
                    (Cmp::Ne, _) => format!("(not (= {xv} {yv}))"),
                    (_, Ty::Int | Ty::Real) => format!("({} {xv} {yv})", o.text()),
                    (Cmp::Lt, Ty::Str) => format!("(str.< {xv} {yv})"),
                    (Cmp::Le, Ty::Str) => format!("(str.<= {xv} {yv})"),
                    (Cmp::Gt, Ty::Str) => format!("(str.< {yv} {xv})"),
                    (Cmp::Ge, Ty::Str) => format!("(str.<= {yv} {xv})"),
                    _ => return None,
                };
                let known = format!("(not (or {} {}))", x.null, y.null);
                Truth { t: format!("(and {known} {rel})"), f: format!("(and {known} (not {rel}))") }
            }
            E::And(xs) => {
                let ts: Option<Vec<Truth>> = xs.iter().map(|x| self.truth(x)).collect();
                let ts = ts?;
                Truth {
                    t: format!("(and {})", ts.iter().map(|t| t.t.as_str()).collect::<Vec<_>>().join(" ")),
                    f: format!("(or {})", ts.iter().map(|t| t.f.as_str()).collect::<Vec<_>>().join(" ")),
                }
            }
            E::Or(xs) => {
                let ts: Option<Vec<Truth>> = xs.iter().map(|x| self.truth(x)).collect();
                let ts = ts?;
                Truth {
                    t: format!("(or {})", ts.iter().map(|t| t.t.as_str()).collect::<Vec<_>>().join(" ")),
                    f: format!("(and {})", ts.iter().map(|t| t.f.as_str()).collect::<Vec<_>>().join(" ")),
                }
            }
            E::Not(a) => {
                let t = self.truth(a)?;
                Truth { t: t.f, f: t.t }
            }
            E::IsNull(a) => {
                let x = match self.value(a) {
                    Some(x) => x.null,
                    None => {
                        let t = self.truth(a)?;
                        format!("(not (or {} {}))", t.t, t.f)
                    }
                };
                Truth { t: x.clone(), f: format!("(not {x})") }
            }
            E::Like(a, p) => {
                let x = self.value(a)?;
                if a.ty() != Ty::Str {
                    return None;
                }
                let rel = format!("(str.in_re {} {})", x.v, like_re(p));
                let known = format!("(not {})", x.null);
                Truth { t: format!("(and {known} {rel})"), f: format!("(and {known} (not {rel}))") }
            }
            _ => return None,
        })
    }

    /// Every declaration, as SMT text.
    pub(crate) fn declarations(&self) -> String {
        let mut out = String::new();
        if let Some(d) = self.decls.get("Val") {
            out.push_str(d);
            out.push('\n');
        }
        for (k, d) in &self.decls {
            if k != "Val" {
                out.push_str(d);
                out.push('\n');
            }
        }
        out
    }
}

fn to_real(e: &E, v: String) -> String {
    if e.ty() == Ty::Int { format!("(to_real {v})") } else { v }
}

/// The value of a constant integer or decimal expression.
fn constant(e: &E) -> Option<i128> {
    match e {
        E::Lit(Lit::Int(n), _) => Some(*n),
        _ => None,
    }
}

/// A LIKE pattern as a regular expression.
fn like_re(p: &str) -> String {
    let mut parts = vec![];
    let mut lit = String::new();
    let flush = |lit: &mut String, parts: &mut Vec<String>| {
        if !lit.is_empty() {
            parts.push(format!("(str.to_re \"{}\")", smt_string(lit)));
            lit.clear();
        }
    };
    for c in p.chars() {
        match c {
            '%' => {
                flush(&mut lit, &mut parts);
                parts.push("(re.* re.allchar)".into());
            }
            '_' => {
                flush(&mut lit, &mut parts);
                parts.push("re.allchar".into());
            }
            c => lit.push(c),
        }
    }
    flush(&mut lit, &mut parts);
    match parts.len() {
        0 => "(str.to_re \"\")".into(),
        1 => parts.pop().unwrap(),
        _ => format!("(re.++ {})", parts.join(" ")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn col(c: &str) -> E {
        E::Col(c.into(), Ty::Int)
    }

    fn int(n: i128) -> E {
        E::Lit(Lit::Int(n), Ty::Int)
    }

    #[test]
    fn canonical_text() {
        let a = E::Cmp(Cmp::Eq, Box::new(col("foo.a")), Box::new(int(1)));
        let b = E::Cmp(Cmp::Eq, Box::new(int(2)), Box::new(col("foo.a")));
        assert_eq!(flat_or(vec![b.clone(), a.clone()]).text(), "foo.a=1 OR foo.a=2");
        assert_eq!(flat_or(vec![a, b]).text(), "foo.a=1 OR foo.a=2");
        assert_eq!(Lit::dec(1000, 100).text(), "10");
        assert_eq!(Lit::dec(5, 100).text(), "0.05");
        assert_eq!(Lit::dec(-1, 2).text(), "-0.5");
        assert_eq!(Lit::dec(1, 3).text(), "1/3");
        let m = E::Arith(Arith::Mod, Box::new(col("foo.a")), Box::new(int(3)), Ty::Int);
        assert_eq!(E::Cmp(Cmp::Gt, Box::new(m), Box::new(int(2))).text(), "foo.a%3>2");
    }
}
