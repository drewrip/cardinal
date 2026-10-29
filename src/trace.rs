//! What Z3 is told, and why a claim follows from it.
//!
//! With [`crate::Options::trace`] set, an analysis keeps a [`Trace`]: every
//! constraint it gave Z3, in order, with the plan node it describes and the
//! line of the analyzer that made it. [`Trace::explain`] proves claims about
//! the output from the constraints and names a minimal set of them each proof
//! needs (an unsat core), so a bound can be traced back to the operators and
//! rules that give it.

use std::collections::{HashMap, HashSet};
use std::panic::Location;

use serde::{Deserialize, Serialize};
use z3::ast::{Bool, Int};
use z3::{Params, SatResult, Solver};

use crate::analyzer::{Analyzer, Node};
use crate::bounds::{self, Bounds};
use crate::facts::Fact;
use crate::{Error, Result};

/// Every constraint of an analysis, with where each comes from.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Trace {
    /// Every plan node, children before parents; a node's id is its index.
    pub nodes: Vec<TraceNode>,
    /// Every constraint, in the order Z3 was given them; a constraint's id is
    /// its index.
    pub constraints: Vec<Constraint>,
    /// The root operator's cardinality variable.
    pub root: String,
    /// Each base-table scan as (scan variable, table name), in visit order.
    pub scans: Vec<(String, String)>,
    /// Each base table as (table name, Z3 symbol), sorted by name.
    pub tables: Vec<(String, String)>,
    /// The SMT-LIB declarations of every variable, one per line.
    pub declarations: String,
}

/// One plan node and its variables.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TraceNode {
    pub id: usize,
    /// The operator, as DataFusion shows it on one line.
    pub label: String,
    /// The cardinality variable.
    pub var: String,
    /// Each output column as (column name, NDV variable).
    pub columns: Vec<(String, String)>,
    /// Node ids of the operator's inputs, in order.
    pub inputs: Vec<usize>,
    /// For a scan with pushed-down filters: the unfiltered scan's variable.
    pub raw_var: Option<String>,
}

/// One constraint given to Z3.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Constraint {
    pub id: usize,
    /// The constraint in SMT-LIB.
    pub smt: String,
    /// The constraint in infix notation, see [`infix`].
    pub infix: String,
    /// The node the constraint describes, or `None` for one over several
    /// relations of a table (partitions of its rows).
    pub node: Option<usize>,
    /// The analyzer's source line that made the constraint, as `file:line`.
    pub source: String,
    /// The function of that line.
    pub function: String,
    /// The text of that line.
    pub code: String,
    /// The variables the constraint mentions.
    pub vars: Vec<String>,
    /// For a constraint a fact gave ([`crate::Informed::trace`]): which, and
    /// what it says. `None` for the analyzer's own.
    #[serde(default)]
    pub fact: Option<FactInfo>,
}

/// What a fact constraint asserts, and the facts it is read from.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactInfo {
    /// What kind of claim it is: `selectivity`, `pinned rows`, `pinned ndv`,
    /// `ndv cap`, `row cap` or `floor`.
    pub source: String,
    /// The facts it is read from.
    pub facts: Vec<FactRef>,
    /// The value it holds its variable to, e.g. `= 6001215` or `<= 50`.
    pub value: String,
}

/// One fact, by its text, and where it was read.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactRef {
    /// The fact without its value, e.g. `|lineitem|`, or how a value was
    /// found without one, e.g. `implied by its input`.
    pub text: String,
    /// Each of the fact's [`crate::facts::Origin`]s, as text.
    pub origins: Vec<String>,
}

impl FactRef {
    pub(crate) fn of(f: &Fact) -> FactRef {
        FactRef { text: f.kind.to_string(), origins: f.origins.iter().map(|o| o.to_string()).collect() }
    }
}

/// A claim a fact gave, as [`crate::informed`] asserts it.
pub(crate) struct FactClaim {
    pub claim: Bool,
    /// The plan node whose variable it holds.
    pub node: Option<usize>,
    pub info: FactInfo,
    /// The line that asserted it.
    pub at: &'static Location<'static>,
}

/// The outcome of proving one claim from the constraints.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Proof {
    /// A short key for the claim, e.g. `sum` or `table:orders`.
    pub name: String,
    /// The claim, e.g. `X <= 1/2·Σ`.
    pub claim: String,
    /// The claim in SMT-LIB.
    pub smt: String,
    pub status: ProofStatus,
    /// If proven, the ids of a minimal set of constraints the proof needs:
    /// dropping any one of them leaves the claim unproven.
    pub core: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProofStatus {
    Proven,
    /// Some assignment satisfies every constraint and breaks the claim.
    Refuted,
    /// Z3 could not decide; holds its reason.
    Unknown(String),
}

/// How long one check of [`Trace::explain`] may take.
const CHECK_MS: u32 = 10_000;
/// How long one check while shrinking a core may take.
const SHRINK_MS: u32 = 2_000;
/// Larger cores are reported as Z3 gives them, without shrinking.
const SHRINK_MAX: usize = 300;

/// The source of the analyzer, to show the lines that made each constraint.
const ANALYZER: &str = include_str!("analyzer.rs");

impl Trace {
    pub(crate) fn build(
        a: &Analyzer,
        constraints: &str,
        root: &str,
        scans: &[(String, String)],
        tables: &[(String, String)],
    ) -> Trace {
        let declarations: String = constraints
            .lines()
            .filter(|l| l.starts_with("(declare-fun") || l.starts_with("(declare-const"))
            .map(|l| format!("{l}\n"))
            .collect();
        let declared = declared(&declarations);
        let nodes = a.nodes.iter().enumerate().map(|(id, n)| node(id, n)).collect();
        let source: Vec<&str> = ANALYZER.lines().collect();
        let constraints = a
            .log
            .borrow()
            .iter()
            .enumerate()
            .map(|(id, l)| {
                let smt = l.expr.to_string();
                let line = l.at.line() as usize;
                let (function, code) = if l.at.file().ends_with("analyzer.rs") {
                    rule(&source, line)
                } else {
                    (String::new(), String::new())
                };
                let vars = vars(&smt, &declared);
                Constraint {
                    id,
                    infix: infix(&smt),
                    smt,
                    node: l.frame.and_then(|f| a.frame_node.get(&f).copied()),
                    source: format!("{}:{line}", l.at.file()),
                    function,
                    code,
                    vars,
                    fact: None,
                }
            })
            .collect();
        Trace {
            nodes,
            constraints,
            root: root.to_string(),
            scans: scans.to_vec(),
            tables: tables.to_vec(),
            declarations,
        }
    }

    /// This trace with a constraint for each of `claims` after its own, in
    /// the order they were asserted.
    pub(crate) fn with_facts(&self, claims: &[FactClaim]) -> Trace {
        let declared = declared(&self.declarations);
        let mut trace = self.clone();
        for c in claims {
            let smt = c.claim.to_string();
            let facts: Vec<&str> = c.info.facts.iter().map(|f| f.text.as_str()).collect();
            trace.constraints.push(Constraint {
                id: trace.constraints.len(),
                infix: infix(&smt),
                vars: vars(&smt, &declared),
                smt,
                node: c.node,
                source: format!("{}:{}", c.at.file(), c.at.line()),
                function: format!("fact: {}", c.info.source),
                code: format!("{} {}", facts.join(", "), c.info.value),
                fact: Some(c.info.clone()),
            });
        }
        trace
    }

    /// This trace, declaring too every variable `smt` declares that it does
    /// not: those of the constraints facts added.
    pub(crate) fn declare(&mut self, smt: &str) {
        let known: HashSet<String> = declared(&self.declarations).into_iter().map(str::to_string).collect();
        for l in smt.lines() {
            if let Some(name) = declared_name(l)
                && !known.contains(name)
            {
                self.declarations.push_str(l);
                self.declarations.push('\n');
            }
        }
    }

    /// This trace with only the analyzer's constraints, none from facts.
    pub fn without_facts(&self) -> Trace {
        let mut trace = self.clone();
        trace.constraints.retain(|c| c.fact.is_none());
        trace
    }

    /// The constraints as an SMT-LIB script Z3 can load, each preceded by a
    /// comment naming its node and source line.
    pub fn to_smt2(&self) -> String {
        let mut out = String::from("; cardinal constraints\n");
        out.push_str(&self.declarations);
        for c in &self.constraints {
            let owner = match c.node {
                Some(n) => format!("node {n} {}", self.nodes[n].label.replace('\n', " ")),
                None => "partition".to_string(),
            };
            out.push_str(&format!("; [c{}] {owner} ({} {})\n", c.id, c.source, c.function));
            out.push_str(&format!("(assert {})\n", c.smt));
        }
        out
    }

    /// The constraints of node `id`.
    pub fn of_node(&self, id: usize) -> impl Iterator<Item = &Constraint> {
        self.constraints.iter().filter(move |c| c.node == Some(id))
    }

    /// Tries to prove each claim, an SMT-LIB formula over the trace's
    /// variables named as (key, display text, formula), from the constraints.
    /// A proven claim comes with a minimal set of constraints that prove it.
    pub fn explain(&self, claims: &[(String, String, String)]) -> Result<Vec<Proof>> {
        let solver = Solver::new();
        let mut params = Params::new();
        params.set_u32("timeout", CHECK_MS);
        solver.set_params(&params);
        let assertions = self.parse(&self.constraints.iter().map(|c| c.smt.as_str()).collect::<Vec<_>>())?;
        let trackers: Vec<Bool> = (0..assertions.len())
            .map(|i| Bool::new_const(format!("cardinal_track_{i}")))
            .collect();
        for (t, a) in trackers.iter().zip(&assertions) {
            solver.assert(t.implies(a));
        }
        let index: HashMap<String, usize> =
            trackers.iter().enumerate().map(|(i, t)| (t.to_string(), i)).collect();
        let mut proofs = vec![];
        for (name, claim, smt) in claims {
            let formula = self.parse(&[smt.as_str()])?.remove(0);
            solver.push();
            solver.assert(formula.not());
            let (status, core) = match solver.check_assumptions(&trackers) {
                SatResult::Unsat => {
                    let core = shrink(&solver, solver.get_unsat_core());
                    let mut ids: Vec<usize> = core.iter().filter_map(|t| index.get(&t.to_string()).copied()).collect();
                    ids.sort();
                    (ProofStatus::Proven, ids)
                }
                SatResult::Sat => (ProofStatus::Refuted, vec![]),
                SatResult::Unknown => (
                    ProofStatus::Unknown(solver.get_reason_unknown().unwrap_or_else(|| "unknown".into())),
                    vec![],
                ),
            };
            solver.pop(1);
            proofs.push(Proof {
                name: name.clone(),
                claim: claim.clone(),
                smt: smt.clone(),
                status,
                core,
            });
        }
        Ok(proofs)
    }

    /// Parses formulas over the trace's variables.
    fn parse(&self, formulas: &[&str]) -> Result<Vec<Bool>> {
        let solver = Solver::new();
        let mut script = self.declarations.clone();
        for f in formulas {
            script.push_str(&format!("(assert {f})\n"));
        }
        solver.from_string(script);
        let parsed = solver.get_assertions();
        if parsed.len() != formulas.len() {
            return Err(Error::Internal(format!(
                "trace parsed back to {} assertions, expected {}",
                parsed.len(),
                formulas.len()
            )));
        }
        Ok(parsed)
    }
}

/// The claims [`crate::Analysis::explain`] proves, as (key, display text,
/// formula): the verdict's `X <= Σ` and each of `bounds`, for root variable
/// `root`, scan variables `scans` and tables as (name, symbol) `tables`.
pub(crate) fn claims(
    root: &str,
    scans: &[String],
    tables: &[(String, String)],
    bounds: Option<&Bounds>,
) -> Vec<(String, String, String)> {
    let x = Int::new_const(root);
    let sum = if scans.is_empty() {
        Int::from_i64(0)
    } else {
        let scans: Vec<Int> = scans.iter().map(|s| Int::new_const(s.as_str())).collect();
        Int::add(&scans)
    };
    let mut claims = vec![("verdict".to_string(), "X <= Σ".to_string(), x.le(&sum).to_string())];
    if let Some(b) = bounds {
        if let Some(n) = b.constant {
            claims.push(("constant".into(), format!("X <= {n}"), x.le(Int::from_u64(n)).to_string()));
        }
        // A bound with no term of its quantity is the constant bound again.
        if let Some(s) = b.sum.as_ref().filter(|s| s.num > 0) {
            let (lhs, rhs) = bounds::sides(&x, &sum, s);
            claims.push(("sum".into(), format!("X <= {}", s.render("Σ")), lhs.le(rhs).to_string()));
        }
        for t in b.tables.iter().filter(|t| t.bound.num > 0) {
            let Some((_, symbol)) = tables.iter().find(|(name, _)| *name == t.table) else {
                continue;
            };
            let (lhs, rhs) = bounds::sides(&x, &Int::new_const(symbol.as_str()), &t.bound);
            let shown = t.bound.render(&format!("|{}|", t.table));
            claims.push((format!("table:{}", t.table), format!("X <= {shown}"), lhs.le(&rhs).to_string()));
            if t.exact {
                claims.push((format!("exact:{}", t.table), format!("X >= {shown}"), lhs.ge(&rhs).to_string()));
            }
        }
    }
    claims
}

/// The names `declarations` declares.
fn declared(declarations: &str) -> HashSet<&str> {
    declarations.lines().filter_map(declared_name).collect()
}

/// The declared variables `smt` mentions, in order, once each.
fn vars(smt: &str, declared: &HashSet<&str>) -> Vec<String> {
    let mut vars: Vec<String> = vec![];
    for t in atoms(smt) {
        if declared.contains(t) && !vars.iter().any(|v| v == t) {
            vars.push(t.to_string());
        }
    }
    vars
}

/// `core` with each tracker dropped that the proof does not need, so that
/// dropping any one left leaves the claim unproven.
pub(crate) fn shrink(solver: &Solver, core: Vec<Bool>) -> Vec<Bool> {
    if core.len() > SHRINK_MAX {
        return core;
    }
    let mut params = Params::new();
    params.set_u32("timeout", SHRINK_MS);
    solver.set_params(&params);
    let mut kept = core;
    let mut i = 0;
    while i < kept.len() {
        let mut without = kept.clone();
        without.remove(i);
        if solver.check_assumptions(&without) == SatResult::Unsat {
            // Z3's core of the smaller set may drop more.
            let smaller = solver.get_unsat_core();
            kept = if smaller.len() < without.len() { smaller } else { without };
            i = 0;
        } else {
            i += 1;
        }
    }
    let mut params = Params::new();
    params.set_u32("timeout", CHECK_MS);
    solver.set_params(&params);
    kept
}

fn node(id: usize, n: &Node) -> TraceNode {
    let schema = n.plan.schema();
    let columns = (0..schema.fields().len())
        .map(|j| {
            let (q, f) = schema.qualified_field(j);
            let name = match q {
                Some(q) => format!("{q}.{}", f.name()),
                None => f.name().clone(),
            };
            (name, n.ndv_vars.get(j).cloned().unwrap_or_default())
        })
        .collect();
    TraceNode {
        id,
        label: n.plan.display().to_string(),
        var: n.var.clone(),
        columns,
        inputs: n.inputs.clone(),
        raw_var: n.raw_scan.as_ref().map(|(v, _, _)| v.clone()),
    }
}

/// The name a `(declare-fun name () Int)` line declares.
fn declared_name(line: &str) -> Option<&str> {
    let rest = line.strip_prefix("(declare-fun ").or_else(|| line.strip_prefix("(declare-const "))?;
    rest.split([' ', ')']).next()
}

/// The function enclosing line `line` (1-based) of `source`, and the line's
/// trimmed text.
fn rule(source: &[&str], line: usize) -> (String, String) {
    let Some(text) = line.checked_sub(1).and_then(|i| source.get(i)) else {
        return (String::new(), String::new());
    };
    let mut arm = None;
    let function = source[..line]
        .iter()
        .rev()
        .find_map(|l| {
            let t = l.trim_start();
            // The plan operator whose match arm the line is in.
            if arm.is_none()
                && let Some(rest) = t.strip_prefix("LogicalPlan::")
            {
                arm = rest.split(|c: char| !c.is_ascii_alphanumeric()).next().map(str::to_string);
            }
            let t = t.strip_prefix("pub(crate) ").or_else(|| t.strip_prefix("pub ")).unwrap_or(t);
            let name = t.strip_prefix("fn ")?;
            Some(name.split(['(', '<']).next().unwrap_or(name).to_string())
        })
        .unwrap_or_default();
    let function = match arm {
        Some(a) if !a.is_empty() => format!("{function}/{a}"),
        _ => function,
    };
    (function, text.trim().to_string())
}

/// The atoms of an SMT-LIB expression: symbols and numerals.
fn atoms(smt: &str) -> impl Iterator<Item = &str> {
    smt.split(|c: char| c.is_whitespace() || c == '(' || c == ')').filter(|t| !t.is_empty())
}

#[derive(Debug, Clone)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

fn parse_sexp(s: &str) -> Option<Sexp> {
    let mut tokens = vec![];
    let mut cur = String::new();
    for c in s.chars() {
        match c {
            '(' | ')' => {
                if !cur.is_empty() {
                    tokens.push(std::mem::take(&mut cur));
                }
                tokens.push(c.to_string());
            }
            c if c.is_whitespace() => {
                if !cur.is_empty() {
                    tokens.push(std::mem::take(&mut cur));
                }
            }
            c => cur.push(c),
        }
    }
    if !cur.is_empty() {
        tokens.push(cur);
    }
    let mut stack: Vec<Vec<Sexp>> = vec![vec![]];
    for t in tokens {
        match t.as_str() {
            "(" => stack.push(vec![]),
            ")" => {
                let list = stack.pop()?;
                stack.last_mut()?.push(Sexp::List(list));
            }
            _ => stack.last_mut()?.push(Sexp::Atom(t)),
        }
    }
    let mut top = stack.pop()?;
    (stack.is_empty() && top.len() == 1).then(|| top.remove(0))
}

/// `e` with each bound name of `env` replaced by its value.
fn substitute(e: &Sexp, env: &HashMap<String, Sexp>) -> Sexp {
    match e {
        Sexp::Atom(a) => env.get(a).cloned().unwrap_or_else(|| e.clone()),
        Sexp::List(items) => Sexp::List(items.iter().map(|x| substitute(x, env)).collect()),
    }
}

/// Binding strength of an infix operator; higher binds tighter.
fn precedence(op: &str) -> Option<u8> {
    Some(match op {
        "=>" => 1,
        "or" => 2,
        "and" => 3,
        "<=" | ">=" | "<" | ">" | "=" => 4,
        "+" | "-" => 5,
        "*" | "/" => 6,
        _ => return None,
    })
}

fn symbol_of(op: &str) -> &str {
    match op {
        "and" => "∧",
        "or" => "∨",
        o => o,
    }
}

/// Renders `e`, parenthesized if its operator binds looser than `outer`.
fn render(e: &Sexp, outer: u8) -> String {
    let Sexp::List(items) = e else {
        let Sexp::Atom(a) = e else { unreachable!() };
        // Z3 prints a real numeral `9` as `9.0`.
        return match a.strip_suffix(".0") {
            Some(n) if !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()) => n.to_string(),
            _ => a.clone(),
        };
    };
    let Some(Sexp::Atom(head)) = items.first() else {
        return items.iter().map(|x| render(x, 0)).collect::<Vec<_>>().join(" ");
    };
    let args = &items[1..];
    match (head.as_str(), args) {
        ("let", [Sexp::List(bindings), body]) => {
            let mut env = HashMap::new();
            for b in bindings {
                if let Sexp::List(pair) = b
                    && let [Sexp::Atom(name), value] = pair.as_slice()
                {
                    env.insert(name.clone(), substitute(value, &env));
                }
            }
            render(&substitute(body, &env), outer)
        }
        ("not", [x]) => format!("¬{}", render(x, 7)),
        // An integer as a real is the same number.
        ("to_real", [x]) => render(x, outer),
        ("-", [x]) => format!("-{}", render(x, 7)),
        ("ite", [c, a, b]) => match c {
            Sexp::List(cmp)
                if cmp.len() == 3
                    && matches!(&cmp[0], Sexp::Atom(o) if o == "<=" || o == ">=")
                    && same(&cmp[1], a)
                    && same(&cmp[2], b) =>
            {
                let f = if matches!(&cmp[0], Sexp::Atom(o) if o == "<=") { "min" } else { "max" };
                format!("{f}({}, {})", render(a, 0), render(b, 0))
            }
            _ => format!("ite({}, {}, {})", render(c, 0), render(a, 0), render(b, 0)),
        },
        (op, _) if args.len() >= 2 && precedence(op).is_some() => {
            let p = precedence(op).unwrap();
            // Operands of a left-associative operator bind one tighter on the
            // right, and comparisons and implications don't chain.
            let parts: Vec<String> = args
                .iter()
                .enumerate()
                .map(|(i, x)| render(x, if i == 0 && p > 4 { p } else { p + 1 }))
                .collect();
            let sep = match op {
                "*" => "·".to_string(),
                "/" => "/".to_string(),
                _ => format!(" {} ", symbol_of(op)),
            };
            let s = parts.join(&sep);
            if p < outer { format!("({s})") } else { s }
        }
        (f, _) => format!("{f}({})", args.iter().map(|x| render(x, 0)).collect::<Vec<_>>().join(", ")),
    }
}

fn same(a: &Sexp, b: &Sexp) -> bool {
    match (a, b) {
        (Sexp::Atom(x), Sexp::Atom(y)) => x == y,
        (Sexp::List(x), Sexp::List(y)) => x.len() == y.len() && x.iter().zip(y).all(|(a, b)| same(a, b)),
        _ => false,
    }
}

/// An SMT-LIB formula in infix notation, e.g. `(<= op3 (* 2 op1))` as
/// `op3 <= 2·op1`; `let` bindings are inlined and `ite` comparisons shown as
/// `min` and `max`. Text that does not parse is returned as is.
pub fn infix(smt: &str) -> String {
    match parse_sexp(smt) {
        Some(e) => render(&e, 0),
        None => smt.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn infix_renders_arithmetic_and_logic() {
        assert_eq!(infix("(<= op3 (* 2 op1))"), "op3 <= 2·op1");
        assert_eq!(infix("(>= x 0)"), "x >= 0");
        assert_eq!(infix("(=> (>= a 1) (>= b 1))"), "a >= 1 => b >= 1");
        assert_eq!(infix("(* (+ a b) c)"), "(a + b)·c");
        assert_eq!(infix("(- a (- b c))"), "a - (b - c)");
        assert_eq!(infix("(- a b c)"), "a - b - c");
        assert_eq!(infix("(not (= a b))"), "¬(a = b)");
        assert_eq!(infix("(= o (ite (<= 5 l) 5 l))"), "o = min(5, l)");
        assert_eq!(infix("(= o (ite (>= a b) a b))"), "o = max(a, b)");
        assert_eq!(infix("(let ((a!1 (+ x y))) (<= a!1 (* 2 a!1)))"), "x + y <= 2·(x + y)");
        assert_eq!(infix("(and (<= a b) (or p q))"), "a <= b ∧ (p ∨ q)");
        assert_eq!(infix("(<= a"), "(<= a");
    }

    #[test]
    fn infix_renders_reals() {
        assert_eq!(infix("(= (to_real op3) (* (/ 9.0 100.0) (to_real op1)))"), "op3 = 9/100·op1");
        assert_eq!(infix("(= (to_real o) (/ 1 2))"), "o = 1/2");
        assert_eq!(infix("(/ (+ a b) c)"), "(a + b)/c");
        assert_eq!(infix("(* a (/ b c))"), "a·(b/c)");
        assert_eq!(infix("(>= x 2.5)"), "x >= 2.5");
    }

    #[test]
    fn rule_finds_the_enclosing_function() {
        let src = ["impl X {", "    pub(crate) fn visit<T>(x: T) {", "        a();", "        LogicalPlan::Filter(f) => {", "            b();"];
        assert_eq!(rule(&src, 3), ("visit".to_string(), "a();".to_string()));
        assert_eq!(rule(&src, 5), ("visit/Filter".to_string(), "b();".to_string()));
    }
}
