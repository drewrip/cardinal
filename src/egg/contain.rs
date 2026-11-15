//! Containment between contexts on egglog: the rules of `contain.egg`,
//! seeded from Rust, give `rows::contain`'s relations between a set of
//! contexts.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::time::{Duration, Instant};

use egglog::prelude::*;
use egglog::{RawValues, Value};

use super::{Graph, Reach};
use crate::axioms::bases;
use crate::rows::contain::{implied, inner_part, renamings};
use crate::rows::{Context, Term};

/// The relations between some contexts, each up to renaming the first's
/// instances, and as named.
pub(crate) struct Relations {
    /// Each context's e-class.
    class: HashMap<Context, Value>,
    /// Each context's e-class, and each of its instances renamed.
    named_class: HashMap<Context, Value>,
    /// `RSub`, `RFewer`, `RGroupsAmong`, between contexts in play.
    subset: HashSet<(Value, Value)>,
    fewer: HashSet<(Value, Value)>,
    groups_among: HashSet<(Value, Value)>,
    /// `Sub`, between any.
    named: HashSet<(Value, Value)>,
    /// The contexts in play the seeds reach.
    reached: Vec<Context>,
    pub(crate) timings: Timings,
}

/// Seconds per stage, and how much the e-graph holds.
#[derive(Debug, Default, Clone)]
pub(crate) struct Timings {
    pub encode: Duration,
    pub saturate: Duration,
    pub extract: Duration,
    /// E-nodes of the contexts, and tuples of every table at the end.
    pub nodes: usize,
    pub tuples: usize,
}

/// Every e-class of constructor `name`, with its children.
fn enodes(g: &Graph, name: &str) -> Vec<(Value, Vec<Value>)> {
    let mut out = vec![];
    g.egraph.constructor_enodes(name, |n| out.push((n.eclass, n.children.to_vec()))).expect("a table of the program");
    out
}

/// Every pair of a relation.
fn pairs(g: &Graph, name: &str) -> HashSet<(Value, Value)> {
    enodes(g, name).into_iter().map(|(_, c)| (c[0], c[1])).collect()
}

fn insert(g: &mut Graph, name: &str, rows: Vec<Vec<Value>>) {
    g.egraph
        .update(|mut fs| {
            for r in rows {
                fs.add(name, RawValues(r))?;
            }
            Ok(())
        })
        .expect("a relation of the program");
}

/// More renamings than this make a graph large.
const LARGE: usize = 1000;

/// Runs `ruleset` until it changes nothing.
fn saturate(g: &mut Graph, ruleset: &str) {
    use egglog::ast::{Command, RunConfig, Schedule};
    let run = Schedule::Run(span!(), RunConfig { ruleset: ruleset.to_string(), until: None });
    g.egraph.run_program(vec![Command::RunSchedule(Schedule::Saturate(span!(), Box::new(run)))]).expect("the rules run");
}

impl Relations {
    /// The relations between `contexts`, and those of them `seeds` reach.
    pub(crate) fn new<'c>(contexts: impl IntoIterator<Item = &'c Context>, seeds: &BTreeSet<Context>, reach: Reach) -> Relations {
        let contexts: Vec<&Context> = contexts.into_iter().collect();
        // Each context with its instances renamed: a context alone over
        // its tables needs none.
        let mut buckets: HashMap<Vec<String>, Vec<usize>> = HashMap::new();
        for (i, c) in contexts.iter().enumerate() {
            buckets.entry(bases(c)).or_default().push(i);
        }
        let mut others = vec![vec![]; contexts.len()];
        for bucket in buckets.values().filter(|b| b.len() > 1) {
            for &i in bucket {
                others[i] = renamings(contexts[i]);
            }
        }
        // The rules run as their first run planned them: a graph that ran
        // small inputs runs large ones far more slowly than a fresh one.
        let large = others.iter().map(Vec::len).sum::<usize>() > LARGE;
        let build = |g: &mut Graph| Relations::build(g, &contexts, &buckets, others, seeds, reach);
        if large { build(&mut Graph::new()) } else { Graph::with(build) }
    }

    fn build(
        g: &mut Graph,
        contexts: &[&Context],
        buckets: &HashMap<Vec<String>, Vec<usize>>,
        others: Vec<Vec<Context>>,
        seeds: &BTreeSet<Context>,
        reach: Reach,
    ) -> Relations {
        let mut timings = Timings::default();
        let start = Instant::now();
        let tops = g.encode_all(contexts.iter().copied());
        let class: HashMap<Context, Value> = contexts.iter().map(|c| (*c).clone()).zip(tops.iter().copied()).collect();
        insert(g, "Top", tops.iter().map(|v| vec![*v]).collect());
        let seeds: Vec<Vec<Value>> = seeds.iter().filter_map(|c| Some(vec![*class.get(c)?])).collect();
        insert(g, "Seed", seeds);
        let limit = match reach {
            Reach::TwoSteps => 2,
            Reach::Fixpoint => i64::MAX,
        };
        g.egraph.update(|mut fs| fs.set("Limit", RawValues(vec![]), limit)).expect("a function of the program");
        // Each context with its instances renamed, and which pairs of
        // contexts over the same tables are asked about.
        let mut renames = vec![];
        let mut named = class.clone();
        let mut renamed: Vec<Vec<Value>> = tops.iter().map(|v| vec![*v]).collect();
        for (i, others) in others.into_iter().enumerate() {
            let classes = g.encode_all(&others);
            for (o, r) in others.into_iter().zip(&classes) {
                renames.push(vec![tops[i], *r]);
                named.entry(o).or_insert(*r);
            }
            renamed[i].extend(classes);
        }
        insert(g, "Renames", renames);
        let group = |c: &Context| matches!(c, Context::Derived { op, .. } if op == "group");
        let (mut fewer, mut groups) = (vec![], vec![]);
        for bucket in buckets.values() {
            for &i in bucket {
                for &j in bucket.iter().filter(|j| **j != i) {
                    let both = group(contexts[i]) && group(contexts[j]);
                    for r in &renamed[i] {
                        fewer.push(vec![*r, tops[j]]);
                        if both {
                            groups.push(vec![*r, tops[j]]);
                        }
                    }
                }
            }
        }
        insert(g, "FewerDemand", fewer);
        insert(g, "GroupDemand", groups);
        // The inner join of each outer join, which may hold outer joins of
        // its own, and any other rows as an SPJ of them alone, as
        // `Spj::of` reads them.
        let mut done = HashSet::new();
        loop {
            let read = g.extractor();
            let derived: Vec<(Value, Context)> =
                enodes(g, "Derived").into_iter().filter(|(v, _)| done.insert(*v)).map(|(v, _)| (v, read.rel(v))).collect();
            if derived.is_empty() {
                break;
            }
            let wraps: Vec<Context> = derived
                .iter()
                .map(|(_, d)| Context::Spj { tables: BTreeSet::new(), atoms: [d.clone()].into(), preds: BTreeSet::new(), exists: BTreeSet::new() })
                .collect();
            let classes = g.encode_all(&wraps);
            insert(g, "Wraps", derived.iter().zip(classes).map(|((d, _), w)| vec![*d, w]).collect());
            let inner: Vec<(Value, Context)> = derived
                .into_iter()
                .filter(|(_, c)| matches!(c, Context::Derived { op, .. } if op == "Left join" || op == "Full join"))
                .filter_map(|(v, c)| Some((v, inner_part(&c)?)))
                .collect();
            let classes = g.encode_all(inner.iter().map(|(_, i)| i));
            insert(g, "Inner", inner.iter().zip(classes).map(|((o, _), i)| vec![*o, i]).collect());
        }
        timings.nodes = g.egraph.num_tuples();
        timings.encode = start.elapsed();

        let start = Instant::now();
        // Which predicate sets cover which, as the rules ask, until they ask
        // nothing new.
        let mut asked = HashSet::new();
        let mut preds: HashMap<Value, BTreeSet<Term>> = HashMap::new();
        loop {
            saturate(g, "contain");
            let demand: Vec<(Value, Value)> = pairs(g, "CoverDemand").into_iter().filter(|p| asked.insert(*p)).collect();
            if demand.is_empty() {
                break;
            }
            let read = g.extractor();
            let mut covers = vec![];
            for (x, y) in demand {
                for p in [x, y] {
                    preds.entry(p).or_insert_with(|| read.terms(p));
                }
                let (px, py) = (&preds[&x], &preds[&y]);
                if py.iter().all(|q| px.contains(q) || implied(px, q)) {
                    covers.push(vec![x, y]);
                }
            }
            insert(g, "PredsCover", covers);
        }
        saturate(g, "reach");
        if std::env::var("EGG_REPORT").is_ok() {
            eprintln!("{}", g.egraph.get_overall_run_report());
        }
        timings.saturate = start.elapsed();
        timings.tuples = g.egraph.num_tuples();

        let start = Instant::now();
        let mut reached = HashSet::new();
        g.egraph.function_entries("Reach", |e| _ = reached.insert(e.inputs[0])).expect("a function of the program");
        let reached = contexts.iter().zip(&tops).filter(|(_, v)| reached.contains(*v)).map(|(c, _)| (*c).clone()).collect();
        let out = Relations {
            reached,
            class,
            named_class: named,
            subset: pairs(g, "RSub"),
            fewer: pairs(g, "RFewer"),
            groups_among: pairs(g, "RGroupsAmong"),
            named: pairs(g, "Sub"),
            timings: Timings::default(),
        };
        timings.extract = start.elapsed();
        Relations { timings, ..out }
    }

    fn holds(&self, rel: &HashSet<(Value, Value)>, a: &Context, b: &Context) -> bool {
        match (self.class.get(a), self.class.get(b)) {
            (Some(x), Some(y)) => rel.contains(&(*x, *y)),
            _ => false,
        }
    }

    /// True if `c` is among the contexts related, or one renamed.
    pub(crate) fn knows(&self, c: &Context) -> bool {
        self.named_class.contains_key(c)
    }

    /// `rows::contain::subset` up to renaming `a`'s instances
    /// (`rows::contain::renamed`).
    pub(crate) fn subset(&self, a: &Context, b: &Context) -> bool {
        self.holds(&self.subset, a, b)
    }

    /// `rows::contain::subset`, as named.
    pub(crate) fn subset_as_named(&self, a: &Context, b: &Context) -> bool {
        match (self.named_class.get(a), self.named_class.get(b)) {
            (Some(x), Some(y)) => self.named.contains(&(*x, *y)),
            _ => false,
        }
    }

    /// `rows::contain::fewer` up to renaming.
    pub(crate) fn fewer(&self, a: &Context, b: &Context) -> bool {
        self.holds(&self.fewer, a, b)
    }

    /// `rows::contain::groups_among` up to renaming.
    pub(crate) fn groups_among(&self, a: &Context, b: &Context) -> bool {
        self.holds(&self.groups_among, a, b)
    }

    /// The contexts in play the seeds reach.
    pub(crate) fn reached(&self) -> &[Context] {
        &self.reached
    }
}

#[cfg(test)]
mod tests {
    //! `rows::contain`'s tests, on egglog.

    use std::collections::BTreeSet;

    use datafusion::common::JoinType;
    use datafusion::prelude::{col, lit};

    use super::*;
    use crate::rows::{ExistsKind, terms};

    fn t(name: &str) -> Context {
        Context::table(name)
    }

    fn eq(a: &str, b: &str) -> BTreeSet<Term> {
        terms([col(a).eq(col(b))])
    }

    fn p(c: &str, v: i64) -> BTreeSet<Term> {
        terms([col(c).eq(lit(v))])
    }

    fn joined() -> Context {
        t("products").cross(&t("sales")).unwrap().filter(&eq("products.id", "sales.product_id"))
    }

    fn rel(cs: &[&Context]) -> Relations {
        Relations::new(cs.iter().copied(), &BTreeSet::new(), Reach::TwoSteps)
    }

    #[test]
    fn filters_narrow() {
        let filtered = joined().filter(&p("products.category", 7));
        let below = t("products").filter(&p("products.category", 7)).cross(&t("sales")).unwrap().filter(&eq("products.id", "sales.product_id"));
        let r = rel(&[&filtered, &joined(), &below, &t("products")]);
        assert!(r.subset(&filtered, &joined()));
        assert!(!r.subset(&joined(), &filtered));
        assert!(r.subset(&below, &joined()));
        assert!(!r.subset(&t("products"), &joined()));
    }

    #[test]
    fn semi_joins_narrow_with_their_other_side() {
        let on = eq("sales.product_id", "products.id");
        let semi = |other: Context| Context::join(JoinType::LeftSemi, on.clone(), t("sales"), other);
        let narrow = semi(t("products").filter(&p("products.category", 7)));
        let wide = semi(t("products"));
        let r = rel(&[&narrow, &wide, &t("sales")]);
        assert!(r.subset(&narrow, &wide));
        assert!(!r.subset(&wide, &narrow));
        // Only contexts over the same tables are related: `sales` alone
        // draws on no `products`.
        assert!(!r.subset(&wide, &t("sales")));
    }

    #[test]
    fn anti_joins_widen_with_their_other_side() {
        let on = eq("sales.product_id", "products.id");
        let anti = |other: Context| Context::join(JoinType::LeftAnti, on.clone(), t("sales"), other);
        let excluded = anti(t("products").filter(&p("products.category", 7)));
        let all = anti(t("products"));
        let store = all.filter(&p("sales.store", 1));
        let r = rel(&[&excluded, &all, &store]);
        assert!(!r.subset(&excluded, &all));
        assert!(r.subset(&all, &excluded));
        assert!(r.subset(&store, &all));
    }

    #[test]
    fn outer_joins_shrink_with_either_input() {
        let on = eq("sales.product_id", "products.id");
        let left = |l: Context, r: Context| Context::join(JoinType::Left, on.clone(), l, r);
        let full = left(t("sales"), t("products"));
        let fewer_sales = left(t("sales").filter(&p("sales.store", 1)), t("products"));
        let fewer_products = left(t("sales"), t("products").filter(&p("products.category", 7)));
        let rejected = full.filter(&p("products.category", 7));
        let unmatched = |c: Context| c.filter(&terms([col("products.id").is_null()]));
        let (un_few, un_full) = (unmatched(fewer_products.clone()), unmatched(full.clone()));
        let both = Context::join(JoinType::Full, on.clone(), t("sales"), t("products"));
        let r = rel(&[&full, &fewer_sales, &fewer_products, &rejected, &un_few, &un_full, &both]);
        assert!(r.fewer(&fewer_sales, &full));
        assert!(r.fewer(&fewer_products, &full));
        assert!(!r.fewer(&full, &fewer_products));
        assert!(r.fewer(&rejected, &full));
        assert!(!r.fewer(&un_few, &un_full));
        assert!(r.fewer(&full, &both));
    }

    #[test]
    fn instances_of_one_table_may_be_numbered_apart() {
        let pair = |a: &str, b: &str| t(a).cross(&t(b)).unwrap().filter(&eq(&format!("{a}.manager"), &format!("{b}.id")));
        let wide = pair("emp@1", "emp@2");
        let narrow = pair("emp@2", "emp@1").filter(&p("emp@1.dept", 3));
        let r = rel(&[&wide, &narrow]);
        assert!(!r.subset_as_named(&narrow, &wide));
        assert!(r.subset(&narrow, &wide));
    }

    #[test]
    fn narrower_ranges_imply_wider_ones() {
        let f = |e: datafusion::logical_expr::Expr| t("lineitem").filter(&terms([e]));
        let q = "lineitem.l_quantity";
        let cases = [
            (f(col(q).lt(lit(5))), f(col(q).lt(lit(10))), true),
            (f(col(q).lt_eq(lit(9))), f(col(q).lt(lit(10))), true),
            (f(col(q).lt_eq(lit(10))), f(col(q).lt(lit(10))), false),
            (f(col(q).lt(lit(10))), f(col(q).lt(lit(5))), false),
            (f(col(q).eq(lit(3))), f(col(q).gt_eq(lit(3))), true),
            (f(col(q).eq(lit(3))), f(col(q).in_list(vec![lit(1), lit(3)], false)), true),
            (f(col("lineitem.l_tax").lt(lit(5))), f(col(q).lt(lit(10))), false),
            (f(col(q).lt(lit(5i32))), f(col(q).lt(lit(10i64))), false),
            (f(col(q).lt(lit("a"))), f(col(q).lt(lit("b"))), false),
            (f(col(q).eq(lit("a"))), f(col(q).in_list(vec![lit("a"), lit("b")], false)), true),
        ];
        for (a, b, holds) in &cases {
            assert_eq!(rel(&[a, b]).subset(a, b), *holds, "{a} ⊆ {b}");
        }
        let both = t("lineitem").filter(&terms([col(q).gt(lit(2)), col(q).lt(lit(4))]));
        let (gt1, narrow) = (f(col(q).gt(lit(1))), f(col(q).gt(lit(2)).and(col(q).lt(lit(3)))));
        let r = rel(&[&both, &gt1, &narrow]);
        assert!(r.subset(&both, &gt1));
        assert!(!r.subset(&both, &narrow));
    }

    #[test]
    fn groups_among_wider_inputs() {
        let g = |c: Context| Context::Derived { op: "group".into(), args: vec![Term::new(col("lineitem.l_partkey"))], inputs: vec![c] };
        let narrow = g(t("lineitem").filter(&p("lineitem.l_tax", 1)));
        let wide = g(t("lineitem"));
        let r = rel(&[&narrow, &wide]);
        assert!(r.groups_among(&narrow, &wide));
        assert!(!r.groups_among(&wide, &narrow));
    }

    #[test]
    fn not_in_widens_with_its_other_side() {
        let on = eq("sales.product_id", "products.id");
        let not_in = |o: Context| t("sales").exists(ExistsKind::NotIn, on.clone(), o);
        let (few, all) = (not_in(t("products").filter(&p("products.category", 7))), not_in(t("products")));
        let r = rel(&[&few, &all]);
        assert!(r.subset(&all, &few));
        assert!(!r.subset(&few, &all));
    }
}

