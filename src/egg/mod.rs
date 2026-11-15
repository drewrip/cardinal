//! The relations between contexts on egglog, an alternative to
//! `rows::contain`'s pairwise tests ([`crate::Options::egglog`]).
//!
//! Contexts are terms of the schema in `rows.egg`, which mirrors
//! [`Context`]. Sets stay canonical in Rust, and a [`Term`] is an opaque
//! leaf keyed by its text, so equal contexts are one e-class. The rules of
//! `contain.egg` derive which contexts are among, or have fewer rows than,
//! which, asked only of pairs in play: Rust seeds what needs a term's
//! meaning (renamed instances, outer joins' inner joins, which predicates
//! imply which). The relevant contexts are those within reach of the
//! query's over these relations.

use std::cell::RefCell;
use std::collections::HashMap;

use egglog::prelude::*;
use egglog::{EGraph, RawValues, Value};

use crate::rows::{Context, Exists, ExistsKind, Term};

pub(crate) mod contain;

/// How far relevant contexts reach from the query's own, over the
/// relations between them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reach {
    /// Two steps, as the Rust path does.
    TwoSteps,
    /// As far as the relations go.
    Fixpoint,
}

impl Reach {
    /// `EGGLOG=1` is two steps, `EGGLOG=fixpoint` the fixpoint; anything
    /// else, none.
    pub fn from_env() -> Option<Reach> {
        match std::env::var("EGGLOG").as_deref() {
            Ok("1") => Some(Reach::TwoSteps),
            Ok("fixpoint") => Some(Reach::Fixpoint),
            _ => None,
        }
    }
}

const SCHEMA: &str = include_str!("rows.egg");
const CONTAIN: &str = include_str!("contain.egg");

/// An e-graph of contexts.
pub(crate) struct Graph {
    pub(crate) egraph: EGraph,
    /// Each term added, by its key, to read back.
    terms: HashMap<String, Term>,
}

impl Graph {
    /// An empty graph.
    pub(crate) fn new() -> Graph {
        let mut egraph = EGraph::default();
        egraph.parse_and_run_program(None, SCHEMA).expect("the schema is valid");
        egraph.parse_and_run_program(None, CONTAIN).expect("the rules are valid");
        Graph { egraph, terms: HashMap::new() }
    }

    /// Runs `f` on an empty graph, this thread's own emptied. A fresh one,
    /// or a copy, runs its rules the first time a few times as slowly as
    /// an analysis's contexts take.
    pub(crate) fn with<R>(f: impl FnOnce(&mut Graph) -> R) -> R {
        thread_local! {
            static GRAPH: RefCell<Option<Graph>> = const { RefCell::new(None) };
        }
        let mut g = GRAPH.with(|g| g.borrow_mut().take()).unwrap_or_else(Graph::new);
        for name in g.egraph.get_function_names() {
            g.egraph.clear_function(&name).expect("a table of the program");
        }
        g.terms.clear();
        let out = f(&mut g);
        GRAPH.with(|cell| *cell.borrow_mut() = Some(g));
        out
    }

    /// Adds `c`, and gives its e-class.
    #[cfg(test)]
    pub(crate) fn encode(&mut self, c: &Context) -> Value {
        let terms = &mut self.terms;
        self.egraph.update(|mut fs| Ok(rel(&mut fs, terms, c))).expect("contexts fit the schema")
    }

    /// Adds each of `cs`, and gives their e-classes.
    pub(crate) fn encode_all<'c>(&mut self, cs: impl IntoIterator<Item = &'c Context>) -> Vec<Value> {
        let terms = &mut self.terms;
        self.egraph.update(|mut fs| Ok(cs.into_iter().map(|c| rel(&mut fs, terms, c)).collect())).expect("contexts fit the schema")
    }

    /// The context of e-class `v`, an encoded context.
    #[cfg(test)]
    pub(crate) fn extract(&self, v: Value) -> Context {
        Extractor::new(self).rel(v)
    }

    /// A reader of many contexts.
    pub(crate) fn extractor(&self) -> Extractor<'_> {
        Extractor::new(self)
    }
}

type State<'a, 'b> = egglog::FullState<'a, 'b>;

fn add(fs: &mut State, name: &str, children: Vec<Value>) -> Value {
    fs.add(name, RawValues(children)).expect("a constructor of the schema")
}

fn string(fs: &mut State, s: &str) -> Value {
    fs.base_to_value::<egglog::sort::S>(s.to_string().into())
}

/// A list of `items` by `nil` and `cons`, built from the back.
fn list(fs: &mut State, nil: &str, cons: &str, items: Vec<Value>) -> Value {
    let mut out = add(fs, nil, vec![]);
    for v in items.into_iter().rev() {
        out = add(fs, cons, vec![v, out]);
    }
    out
}

fn term(fs: &mut State, terms: &mut HashMap<String, Term>, t: &Term) -> Value {
    if !terms.contains_key(t.key()) {
        terms.insert(t.key().to_string(), t.clone());
    }
    let s = string(fs, t.key());
    add(fs, "T", vec![s])
}

fn term_list<'t>(fs: &mut State, terms: &mut HashMap<String, Term>, ts: impl IntoIterator<Item = &'t Term>) -> Value {
    let items = ts.into_iter().map(|t| term(fs, terms, t)).collect();
    list(fs, "TNil", "TCons", items)
}

fn kind(k: ExistsKind) -> &'static str {
    match k {
        ExistsKind::Semi => "semi",
        ExistsKind::Anti => "anti",
        ExistsKind::NotIn => "not in",
    }
}

fn rel(fs: &mut State, terms: &mut HashMap<String, Term>, c: &Context) -> Value {
    match c {
        Context::Spj { tables, atoms, preds, exists } => {
            let tables: Vec<Value> = tables.iter().map(|t| string(fs, t)).collect();
            let tables = list(fs, "SNil", "SCons", tables);
            let atoms: Vec<Value> = atoms.iter().map(|a| rel(fs, terms, a)).collect();
            let atoms = list(fs, "RNil", "RCons", atoms);
            let preds = term_list(fs, terms, preds);
            let exists: Vec<Value> = exists
                .iter()
                .map(|e| {
                    let k = string(fs, kind(e.kind));
                    let on = term_list(fs, terms, &e.on);
                    let other = rel(fs, terms, &e.other);
                    add(fs, "Exist", vec![k, on, other])
                })
                .collect();
            let exists = list(fs, "ENil", "ECons", exists);
            add(fs, "Spj", vec![tables, atoms, preds, exists])
        }
        Context::Derived { op, args, inputs } => {
            let op = string(fs, op);
            let args = term_list(fs, terms, args);
            let inputs: Vec<Value> = inputs.iter().map(|i| rel(fs, terms, i)).collect();
            let inputs = list(fs, "RNil", "RCons", inputs);
            add(fs, "Derived", vec![op, args, inputs])
        }
    }
}

/// Reads contexts back: each e-class's e-node, read once from the tables.
pub(crate) struct Extractor<'g> {
    graph: &'g Graph,
    nodes: HashMap<Value, (&'static str, Vec<Value>)>,
}

const CONSTRUCTORS: [&str; 12] = ["Spj", "Derived", "RNil", "RCons", "T", "TNil", "TCons", "SNil", "SCons", "Exist", "ENil", "ECons"];

impl<'g> Extractor<'g> {
    fn new(graph: &'g Graph) -> Extractor<'g> {
        let mut nodes = HashMap::new();
        for name in CONSTRUCTORS {
            graph
                .egraph
                .constructor_enodes(name, |n| {
                    nodes.entry(n.eclass).or_insert_with(|| (name, n.children.to_vec()));
                })
                .expect("a constructor of the schema");
        }
        Extractor { graph, nodes }
    }

    fn node(&self, v: Value, name: &str) -> &[Value] {
        match self.nodes.get(&v) {
            Some((n, children)) if *n == name => children,
            other => panic!("e-class {v:?} is {other:?}, not {name}"),
        }
    }

    fn string(&self, v: Value) -> String {
        self.graph.egraph.value_to_base::<egglog::sort::S>(v).0
    }

    /// The items of list `v`.
    fn list(&self, mut v: Value) -> Vec<Value> {
        let mut out = vec![];
        loop {
            match self.nodes.get(&v) {
                Some((name, children)) if name.ends_with("Cons") => {
                    out.push(children[0]);
                    v = children[1];
                }
                Some(_) => return out,
                None => panic!("e-class {v:?} is no list"),
            }
        }
    }

    fn term(&self, v: Value) -> Term {
        let key = self.string(self.node(v, "T")[0]);
        self.graph.terms[&key].clone()
    }

    pub(crate) fn terms<T: FromIterator<Term>>(&self, v: Value) -> T {
        self.list(v).into_iter().map(|t| self.term(t)).collect()
    }

    pub(crate) fn rel(&self, v: Value) -> Context {
        match self.nodes.get(&v) {
            Some(("Spj", c)) => Context::Spj {
                tables: self.list(c[0]).into_iter().map(|s| self.string(s)).collect(),
                atoms: self.list(c[1]).into_iter().map(|a| self.rel(a)).collect(),
                preds: self.terms(c[2]),
                exists: self
                    .list(c[3])
                    .into_iter()
                    .map(|e| {
                        let e = self.node(e, "Exist");
                        let kind = match self.string(e[0]).as_str() {
                            "semi" => ExistsKind::Semi,
                            "anti" => ExistsKind::Anti,
                            _ => ExistsKind::NotIn,
                        };
                        Exists { kind, on: self.terms(e[1]), other: self.rel(e[2]) }
                    })
                    .collect(),
            },
            Some(("Derived", c)) => Context::Derived {
                op: self.string(c[0]),
                args: self.terms(c[1]),
                inputs: self.list(c[2]).into_iter().map(|i| self.rel(i)).collect(),
            },
            other => panic!("e-class {v:?} is {other:?}, no context"),
        }
    }
}

#[cfg(test)]
mod tests {
    use datafusion::common::JoinType;
    use datafusion::prelude::{col, lit};

    use super::*;
    use crate::rows::terms;

    #[test]
    fn contexts_round_trip() {
        let t = Context::table;
        let on = terms([col("a.x").eq(col("b.x"))]);
        let p = terms([col("a.y").lt(lit(3))]);
        let group = Context::Derived { op: "group".into(), args: vec![Term::new(col("c.k"))], inputs: vec![t("c")] };
        let cases = [
            t("a"),
            t("a").filter(&p).cross(&t("b")).unwrap().filter(&on),
            Context::join(JoinType::Left, on.clone(), t("a"), t("b").filter(&terms([col("b.z").gt(lit(1))]))),
            Context::join(JoinType::LeftAnti, on.clone(), t("a"), t("b")),
            t("a").cross(&group).unwrap().exists(ExistsKind::NotIn, on.clone(), t("b")),
        ];
        let mut g = Graph::new();
        let vs = g.encode_all(&cases);
        for (c, v) in cases.iter().zip(&vs) {
            assert_eq!(g.extract(*v), *c);
            // Encoded again, the same e-class.
            assert_eq!(g.encode(c), *v);
        }
    }
}

