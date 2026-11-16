//! Facts written the same whichever plan they came from.
//!
//! Plans name table instances by operator (`lineitem#7`), so the same rows
//! read in two plans would differ by name. A fact's instances are renamed:
//! a table's only instance to the table's name, and several instances of one
//! table to `lineitem@1`, `lineitem@2`, ..., in the order that makes the fact
//! least. Any renaming of instances of one table keeps a fact's meaning, so
//! the least is a canonical form.
//!
//! A fact over one context compares its rows first ([`FactKind`]'s field
//! order), so its least form names the context as the context's own least
//! form does, and only the renamings that keep that form compete on the
//! keys. [`Canonicals`] finds those once per context, for all its facts.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use super::rewrite::Classes;
use super::{Context, Exists, ExistsKind, Term, rewrite};
use crate::facts::FactKind;
use crate::observed::base_table;

/// More orders than this are not tried: instances are then numbered as they
/// first appear, which is deterministic but may keep equal facts apart.
pub(crate) const MAX_ORDERS: usize = 5040;

/// Instance names by plan instance, for one order of each table's.
type Names = HashMap<String, String>;

/// Each context seen, canonically renamed: renaming rows is the costly
/// part, and many facts are over the same rows.
#[derive(Default)]
pub(crate) struct Canonicals {
    entries: HashMap<Context, Canonical>,
    /// Lookups that found their context, and those that searched.
    pub(crate) hits: usize,
    pub(crate) misses: usize,
}

/// A context's canonical form.
pub(crate) struct Canonical {
    /// The context, canonically renamed.
    pub(crate) context: Context,
    /// Every renaming of its instances that gives `context`, up to
    /// [`MAX_ORDERS`]: more than one if instances are interchangeable.
    pub(crate) maps: Vec<Names>,
    /// `context`'s classes of equal columns, for keys over it.
    classes: Classes,
}

impl std::fmt::Debug for Canonicals {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Canonicals({} contexts, {} hits, {} misses)", self.entries.len(), self.hits, self.misses)
    }
}

impl Canonicals {
    /// The canonical form of `c`, searched for once.
    pub(crate) fn of(&mut self, c: &Context) -> &Canonical {
        if self.entries.contains_key(c) {
            self.hits += 1;
        } else {
            self.misses += 1;
            let entry = Canonical::search(c);
            self.entries.insert(c.clone(), entry);
        }
        &self.entries[c]
    }
}

impl Canonical {
    /// The least renaming of `c` over every order of its instances, and
    /// each order that gives it.
    fn search(c: &Context) -> Canonical {
        let mut instances = vec![];
        context_instances(c, &mut instances);
        let groups = grouped(&instances);
        let mut all = vec![];
        if orders(&groups).is_none_or(|n| n > MAX_ORDERS) {
            all.push(labels(&groups, &groups.iter().map(|(_, g)| g.clone()).collect::<Vec<_>>()));
        } else {
            each_order(&groups, 0, &mut vec![], &mut |order| all.push(labels(&groups, order)));
        }
        // Renaming a large context is slow: many orders are renamed on
        // several threads, each keeping its least, then the least of those.
        let threads = std::thread::available_parallelism().map_or(1, |n| n.get()).min(all.len() / PER_THREAD).max(1);
        let chunk = all.len().div_ceil(threads);
        let (context, maps) = if threads == 1 {
            least(c, all)
        } else {
            let mut parts = vec![];
            let mut rest = all;
            while !rest.is_empty() {
                let tail = rest.split_off(chunk.min(rest.len()));
                parts.push(std::mem::replace(&mut rest, tail));
            }
            let found: Vec<(Context, Vec<Names>)> = std::thread::scope(|s| {
                let handles: Vec<_> = parts.into_iter().map(|p| s.spawn(move || least(c, p))).collect();
                handles.into_iter().map(|h| h.join().expect("a renaming thread")).collect()
            });
            let best = found.iter().map(|(r, _)| r).min().expect("one order at least").clone();
            let maps = found.into_iter().filter(|(r, _)| *r == best).flat_map(|(_, m)| m).collect();
            (best, maps)
        };
        let classes = rewrite::key_classes(&context);
        Canonical { context, maps, classes }
    }
}

/// Orders one thread renames at least.
const PER_THREAD: usize = 16;

/// The least of `c` renamed by each of `orders`, and the orders that give
/// it, in the order given.
fn least(c: &Context, orders: Vec<Names>) -> (Context, Vec<Names>) {
    let (mut best, mut maps): (Option<Context>, Vec<Names>) = (None, vec![]);
    for names in orders {
        let r = c.rename(&|r| names.get(r).cloned());
        match best.as_ref().map(|b| r.cmp(b)) {
            Some(std::cmp::Ordering::Greater) => {}
            Some(std::cmp::Ordering::Equal) => maps.push(names),
            _ => {
                best = Some(r);
                maps = vec![names];
            }
        }
    }
    (best.expect("one order at least"), maps)
}

impl FactKind {
    /// This fact with its table instances canonically renamed.
    pub fn canonical(&self) -> FactKind {
        self.canonical_in(&mut Canonicals::default())
    }

    /// [`FactKind::canonical`], finding its context's canonical form in
    /// `canonicals`, or adding it.
    pub(crate) fn canonical_in(&self, canonicals: &mut Canonicals) -> FactKind {
        // Lookups no term reads taken out, and decorrelated first: what they
        // take out is no instance to name.
        let ungrouped = self.ungrouped();
        let this = ungrouped.as_ref().unwrap_or(self);
        let unpadded = this.unpadded();
        let this = unpadded.as_ref().unwrap_or(this);
        let decorrelated = this.decorrelated();
        decorrelated.as_ref().unwrap_or(this).named_in(canonicals)
    }

    /// This fact with its instances renamed in the least order, the rest
    /// of [`FactKind::canonical_in`] already done.
    fn named_in(&self, canonicals: &mut Canonicals) -> FactKind {
        let Some(over) = self.over_only() else { return self.search() };
        // Keys over instances the rows do not have are named with them.
        let mut instances = vec![];
        context_instances(over, &mut instances);
        if self.instances().len() != instances.len() {
            return self.search();
        }
        let entry = canonicals.of(over);
        entry
            .maps
            .iter()
            .map(|names| self.around_in(names, entry.context.clone(), &entry.classes))
            .min()
            .expect("one renaming at least")
    }

    /// The least renaming of this fact over every order of its instances,
    /// renaming each whole; past [`MAX_ORDERS`], instances numbered as they
    /// first appear.
    pub(crate) fn search(&self) -> FactKind {
        let instances = self.instances();
        let groups = grouped(&instances);
        if orders(&groups).is_none_or(|n| n > MAX_ORDERS) {
            let names = groups.iter().map(|(_, g)| g.clone()).collect::<Vec<_>>();
            return self.rename(&labels(&groups, &names));
        }
        let mut best: Option<FactKind> = None;
        each_order(&groups, 0, &mut vec![], &mut |order| {
            let candidate = self.rename(&labels(&groups, order));
            if best.as_ref().is_none_or(|b| candidate < *b) {
                best = Some(candidate);
            }
        });
        best.unwrap_or_else(|| self.clone())
    }

    /// This fact as stored, its keys renamed as [`FactKind::canonical`]
    /// names them now: a stored distinct count, uniqueness, least or
    /// greatest value may be spelled as an older canonical form, which
    /// compared keys before rows. Its instances `t@1`, `t@2`, ... are named
    /// again, as a plan's would be; nothing else
    /// [`FactKind::canonical`] does is done again, nor are other kinds
    /// renamed, as derived facts are spelled as the facts they came from.
    pub(crate) fn recanonical_in(&self, canonicals: &mut Canonicals) -> FactKind {
        match self {
            FactKind::Distinct { .. } | FactKind::Unique { .. } | FactKind::Min { .. } | FactKind::Max { .. } => {
                self.respelled().as_ref().unwrap_or(self).named_in(canonicals)
            }
            _ => self.clone(),
        }
    }

    /// This fact with its instances numbered `t@1`, `t@2`, ... spelled as a
    /// plan's, to be named again; `None` if it has none.
    fn respelled(&self) -> Option<FactKind> {
        let mut numbered = vec![];
        self.each_instance(&mut |r| r.contains('@'), &mut numbered);
        let names: Names = numbered.iter().map(|r| (r.clone(), r.replacen('@', "#@", 1))).collect();
        (!names.is_empty()).then(|| self.rename(&names))
    }

    /// A distinct count, min or max of keys over a GROUP BY on them and
    /// more, as over the GROUP BY's input: a group is kept for each
    /// combination of its keys the input has, so the keys take the input's
    /// values. Repeated for GROUP BYs of GROUP BYs. `None` if it is none.
    fn ungrouped(&self) -> Option<FactKind> {
        let input = |keys: &BTreeSet<Term>, over: &Context| match over {
            Context::Derived { op, args, inputs } if op == "group" && keys.iter().all(|k| args.contains(k)) => {
                Some(inputs[0].clone())
            }
            _ => None,
        };
        let mut this = self.clone();
        loop {
            let next = match &this {
                FactKind::Distinct { keys, over } => input(keys, over).map(|o| FactKind::Distinct { keys: keys.clone(), over: o }),
                FactKind::Min { key, over } => input(&[key.clone()].into(), over).map(|o| FactKind::Min { key: key.clone(), over: o }),
                FactKind::Max { key, over } => input(&[key.clone()].into(), over).map(|o| FactKind::Max { key: key.clone(), over: o }),
                _ => None,
            };
            match next {
                Some(n) => this = n,
                None => return (this != *self).then_some(this),
            }
        }
    }

    /// This fact with its left joins that only look up groups nothing
    /// reads, and its inner joins on groups nothing else reads, taken out
    /// (see [`rewrite::unpadded`]), until none is left: taking one out may
    /// leave another that only it read. `None` if there are none, or if any
    /// term reads an aggregate's value, which may be a group's.
    fn unpadded(&self) -> Option<FactKind> {
        let mut this = self.clone();
        loop {
            let next = this.unpadded_once()?;
            if next == this {
                return (this != *self).then_some(this);
            }
            this = next;
        }
    }

    fn unpadded_once(&self) -> Option<FactKind> {
        let (mut read, mut values) = (BTreeMap::new(), false);
        let terms = |ts: &BTreeSet<Term>, read: &mut BTreeMap<String, usize>, values: &mut bool| {
            for t in ts {
                for c in t.expr.column_refs() {
                    match c.relation.as_ref().map(|r| r.table()) {
                        Some("value") | None => *values = true,
                        Some(r) => *read.entry(r.to_string()).or_default() += 1,
                    }
                }
            }
        };
        let contexts: Vec<&Context> = match self {
            FactKind::Cardinality(c) => vec![c],
            FactKind::Selectivity { pred, over } => {
                terms(pred, &mut read, &mut values);
                vec![over]
            }
            FactKind::Match { on, kept, other } => {
                terms(on, &mut read, &mut values);
                vec![kept, other]
            }
            FactKind::Distinct { keys, over } | FactKind::Unique { keys, over } => {
                terms(keys, &mut read, &mut values);
                vec![over]
            }
            FactKind::Min { key, over } | FactKind::Max { key, over } => {
                terms(&[key.clone()].into(), &mut read, &mut values);
                vec![over]
            }
        };
        for c in &contexts {
            rewrite::reads(c, &mut read, &mut values);
        }
        if values {
            return None;
        }
        let f = |c: &Context| rewrite::unpadded(c, &read);
        Some(match self {
            FactKind::Cardinality(c) => FactKind::Cardinality(f(c)),
            FactKind::Selectivity { pred, over } => FactKind::Selectivity { pred: pred.clone(), over: f(over) },
            FactKind::Match { on, kept, other } => FactKind::Match { on: on.clone(), kept: f(kept), other: f(other) },
            FactKind::Distinct { keys, over } => FactKind::Distinct { keys: keys.clone(), over: f(over) },
            FactKind::Unique { keys, over } => FactKind::Unique { keys: keys.clone(), over: f(over) },
            FactKind::Min { key, over } => FactKind::Min { key: key.clone(), over: f(over) },
            FactKind::Max { key, over } => FactKind::Max { key: key.clone(), over: f(over) },
        })
    }

    /// A match share on a copy of its kept side grouped on the correlated
    /// columns, as a semi join of the kept side itself (see
    /// [`rewrite::decorrelate`]). `None` if it is not one.
    fn decorrelated(&self) -> Option<FactKind> {
        let FactKind::Match { on, kept, other: before } = self else { return None };
        let e = Exists { kind: ExistsKind::Semi, on: on.clone(), other: before.clone() };
        let Exists { on, other, .. } = rewrite::decorrelate(kept, e);
        (other != *before).then(|| FactKind::Match { on, kept: kept.clone(), other })
    }

    /// This fact with its instances renamed by `names`, in normal form:
    /// contexts as [`rewrite`] builds them, a selectivity's predicates as its
    /// rows with them write them, and keys and conditions with columns
    /// written as the least column equal to them.
    pub(crate) fn rename(&self, names: &HashMap<String, String>) -> FactKind {
        let f = |r: &str| names.get(r).cloned();
        let terms = |s: &BTreeSet<Term>| s.iter().map(|t| t.rename(&f)).collect::<BTreeSet<_>>();
        if let Some(over) = self.over_only() {
            let over = over.rename(&f);
            let classes = rewrite::key_classes(&over);
            return self.around_in(names, over, &classes);
        }
        match self {
            FactKind::Selectivity { pred, over } => {
                let (pred, over) = (terms(pred), over.rename(&f));
                let delta = rewrite::delta(&over, &pred);
                FactKind::Selectivity { pred: if delta.is_empty() { pred } else { delta }, over }
            }
            FactKind::Match { on, kept, other } => {
                let (kept, other) = (kept.rename(&f), other.rename(&f));
                let on = rewrite::on(&other, &rewrite::on(&kept, &terms(on)));
                FactKind::Match { on, kept, other }
            }
            FactKind::Cardinality(_)
            | FactKind::Distinct { .. }
            | FactKind::Unique { .. }
            | FactKind::Min { .. }
            | FactKind::Max { .. } => unreachable!("over one context"),
        }
    }

    /// The one context a size, distinct count, uniqueness, least or
    /// greatest value is over; `None` for a share.
    fn over_only(&self) -> Option<&Context> {
        match self {
            FactKind::Cardinality(over)
            | FactKind::Distinct { over, .. }
            | FactKind::Unique { over, .. }
            | FactKind::Min { over, .. }
            | FactKind::Max { over, .. } => Some(over),
            FactKind::Selectivity { .. } | FactKind::Match { .. } => None,
        }
    }

    /// This fact, over one context, renamed by `names` given its context
    /// renamed so already, `over`, whose classes of equal columns are
    /// `classes`.
    fn around_in(&self, names: &Names, over: Context, classes: &Classes) -> FactKind {
        let f = |r: &str| names.get(r).cloned();
        let terms = |s: &BTreeSet<Term>| s.iter().map(|t| t.rename(&f)).collect::<BTreeSet<_>>();
        match self {
            FactKind::Distinct { keys, .. } => FactKind::Distinct { keys: classes.keys(&terms(keys)), over },
            FactKind::Unique { keys, .. } => FactKind::Unique { keys: classes.keys(&terms(keys)), over },
            FactKind::Min { key, .. } | FactKind::Max { key, .. } => {
                let key = classes.keys(&[key.rename(&f)].into()).into_iter().next().unwrap_or_else(|| key.rename(&f));
                match self {
                    FactKind::Min { .. } => FactKind::Min { key, over },
                    _ => FactKind::Max { key, over },
                }
            }
            _ => FactKind::Cardinality(over),
        }
    }

    /// Every table instance named, in order of first appearance.
    pub(crate) fn instances(&self) -> Vec<String> {
        let mut out = vec![];
        self.each_instance(&mut |r| base_table(r).is_some(), &mut out);
        out
    }

    /// Every relation named that `is` an instance, in order of first
    /// appearance.
    fn each_instance(&self, is: &mut dyn FnMut(&str) -> bool, out: &mut Vec<String>) {
        let terms = |ts: &mut dyn Iterator<Item = &Term>, is: &mut dyn FnMut(&str) -> bool, out: &mut Vec<String>| {
            for t in ts {
                term_relations(t, is, out);
            }
        };
        match self {
            FactKind::Cardinality(c) => relations(c, is, out),
            FactKind::Selectivity { pred, over } => {
                relations(over, is, out);
                terms(&mut pred.iter(), is, out);
            }
            FactKind::Match { on, kept, other } => {
                relations(kept, is, out);
                relations(other, is, out);
                terms(&mut on.iter(), is, out);
            }
            FactKind::Distinct { keys, over } | FactKind::Unique { keys, over } => {
                relations(over, is, out);
                terms(&mut keys.iter(), is, out);
            }
            FactKind::Min { key, over } | FactKind::Max { key, over } => {
                relations(over, is, out);
                terms(&mut std::iter::once(key), is, out);
            }
        }
    }
}

impl Context {
    /// This context with its table instances canonically renamed.
    pub fn canonical(&self) -> Context {
        match FactKind::Cardinality(self.clone()).canonical() {
            FactKind::Cardinality(c) => c,
            _ => unreachable!(),
        }
    }
}

fn context_instances(c: &Context, out: &mut Vec<String>) {
    relations(c, &mut |r| base_table(r).is_some(), out);
}

/// Every relation `c` names that `is` an instance, in order of first
/// appearance.
fn relations(c: &Context, is: &mut dyn FnMut(&str) -> bool, out: &mut Vec<String>) {
    match c {
        Context::Spj { tables, atoms, preds, exists } => {
            for t in tables {
                push(t, is, out);
            }
            for a in atoms {
                relations(a, is, out);
            }
            for p in preds {
                term_relations(p, is, out);
            }
            for e in exists {
                relations(&e.other, is, out);
                for t in &e.on {
                    term_relations(t, is, out);
                }
            }
        }
        Context::Derived { args, inputs, .. } => {
            for i in inputs {
                relations(i, is, out);
            }
            for a in args {
                term_relations(a, is, out);
            }
        }
    }
}

fn term_relations(t: &Term, is: &mut dyn FnMut(&str) -> bool, out: &mut Vec<String>) {
    for c in t.expr.column_refs() {
        if let Some(r) = c.relation.as_ref() {
            push(r.table(), is, out);
        }
    }
}

fn push(r: &str, is: &mut dyn FnMut(&str) -> bool, out: &mut Vec<String>) {
    if is(r) && !out.iter().any(|o| o == r) {
        out.push(r.to_string());
    }
}

/// `instances` by base table, in the order given.
fn grouped(instances: &[String]) -> Vec<(&str, Vec<&String>)> {
    let mut groups: BTreeMap<&str, Vec<&String>> = BTreeMap::new();
    for i in instances {
        groups.entry(base_table(i).unwrap()).or_default().push(i);
    }
    groups.into_iter().collect()
}

/// How many orders of `groups`' instances there are; `None` past `usize`.
fn orders(groups: &[(&str, Vec<&String>)]) -> Option<usize> {
    groups.iter().try_fold(1usize, |n, (_, g)| (1..=g.len()).try_fold(n, |n, k| n.checked_mul(k)))
}

/// Instance names: the table's for its only instance, else numbered in the
/// order given for each table.
fn labels(groups: &[(&str, Vec<&String>)], order: &[Vec<&String>]) -> Names {
    let mut out = HashMap::new();
    for ((table, _), order) in groups.iter().zip(order) {
        for (k, i) in order.iter().enumerate() {
            let label = if order.len() == 1 { table.to_string() } else { format!("{table}@{}", k + 1) };
            out.insert((*i).clone(), label);
        }
    }
    out
}

/// Calls `f` with every choice of an order for each group's instances.
pub(crate) fn each_order<'a>(
    groups: &[(&str, Vec<&'a String>)],
    at: usize,
    choice: &mut Vec<Vec<&'a String>>,
    f: &mut dyn FnMut(&[Vec<&'a String>]),
) {
    if at == groups.len() {
        f(choice);
        return;
    }
    for p in permutations(&groups[at].1) {
        choice.push(p);
        each_order(groups, at + 1, choice, f);
        choice.pop();
    }
}

fn permutations<'a>(items: &[&'a String]) -> Vec<Vec<&'a String>> {
    if items.len() <= 1 {
        return vec![items.to_vec()];
    }
    let mut out = vec![];
    for i in 0..items.len() {
        let mut rest = items.to_vec();
        let first = rest.remove(i);
        for mut p in permutations(&rest) {
            p.insert(0, first);
            out.push(p);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use datafusion::prelude::col;

    use super::*;
    use crate::rows::terms;

    #[test]
    fn keys_over_a_group_on_more_keys_are_over_its_input() {
        let part = Context::table("part");
        let keys = terms([col("part.p_brand"), col("part.p_size")]);
        let more = Context::Derived { op: "group".into(), args: terms([col("part.p_brand"), col("part.p_size"), col("part.p_type")]).into_iter().collect(), inputs: vec![part.clone()] };
        let grouped = FactKind::Distinct { keys: keys.clone(), over: more.clone() };
        assert_eq!(grouped.canonical(), FactKind::Distinct { keys: keys.clone(), over: part.clone() });
        // Keys the group does not have stay over it.
        let other = FactKind::Distinct { keys: terms([col("part.p_name")]), over: more };
        assert_eq!(other.canonical(), other);
    }

    /// `emp#a ⋈ emp#b ⋈ emp#c` on managers, `a`'s department filtered,
    /// with `dept` alone, and every kind over it, by instance names.
    fn kinds(a: &str, b: &str, c: &str) -> Vec<FactKind> {
        let e = |i: &str, c: &str| col(format!("emp#{i}.{c}"));
        let over = [a, b, c]
            .iter()
            .map(|i| Context::table(&format!("emp#{i}")))
            .chain([Context::table("dept#9")])
            .reduce(|x, y| x.cross(&y).unwrap())
            .unwrap()
            .filter(&terms([
                e(a, "manager").eq(e(b, "id")),
                e(b, "manager").eq(e(c, "id")),
                e(a, "dept").eq(col("dept#9.id")),
                e(a, "salary").gt(datafusion::prelude::lit(10)),
            ]));
        let keys = |cs: &[(&str, &str)]| terms(cs.iter().map(|(i, c)| e(i, c)));
        vec![
            FactKind::Cardinality(over.clone()),
            FactKind::Distinct { over: over.clone(), keys: keys(&[(b, "dept")]) },
            FactKind::Distinct { over: over.clone(), keys: keys(&[(c, "dept"), (a, "salary")]) },
            FactKind::Distinct { over: over.clone(), keys: keys(&[(b, "id")]) },
            FactKind::Unique { over: over.clone(), keys: keys(&[(a, "id"), (c, "id")]) },
            FactKind::Min { over: over.clone(), key: Term::new(e(c, "salary")) },
            FactKind::Max { over, key: Term::new(e(a, "dept")) },
        ]
    }

    /// The least renaming of `k` over every order of its instances, by
    /// brute force.
    fn least(k: &FactKind) -> FactKind {
        let instances = k.instances();
        let groups = grouped(&instances);
        let mut best: Option<FactKind> = None;
        each_order(&groups, 0, &mut vec![], &mut |order| {
            let c = k.rename(&labels(&groups, order));
            if best.as_ref().is_none_or(|b| c < *b) {
                best = Some(c);
            }
        });
        best.unwrap()
    }

    #[test]
    fn every_renaming_has_one_canonical_form() {
        let mut canonicals = Canonicals::default();
        let first = kinds("1", "2", "3");
        let forms: Vec<FactKind> = first.iter().map(|k| k.canonical_in(&mut canonicals)).collect();
        for (a, b, c) in [("1", "3", "2"), ("2", "1", "3"), ("2", "3", "1"), ("3", "1", "2"), ("3", "2", "1"), ("7", "5", "6")] {
            let renamed: Vec<FactKind> = kinds(a, b, c).iter().map(|k| k.canonical_in(&mut canonicals)).collect();
            assert_eq!(renamed, forms, "{a}{b}{c}");
        }
        // One search per context, here one context in seven orders.
        assert_eq!(canonicals.misses, 7);
        // As a search over every order of the whole fact would find.
        for (k, form) in first.iter().zip(&forms) {
            assert_eq!(&least(k), form, "{k}");
            assert_eq!(&k.search(), form, "{k}");
        }
        // Distinct kinds stay apart.
        assert_eq!(forms.iter().collect::<BTreeSet<_>>().len(), forms.len());
    }

    #[test]
    fn interchangeable_instances_take_the_least_keys() {
        // Two unfiltered copies of `emp`: either order names the rows alike.
        let both = Context::table("emp#4").cross(&Context::table("emp#8")).unwrap();
        let mut canonicals = Canonicals::default();
        assert_eq!(canonicals.of(&both).maps.len(), 2);
        for i in ["4", "8"] {
            let k = FactKind::Distinct { over: both.clone(), keys: terms([col(format!("emp#{i}.dept"))]) };
            let c = k.canonical_in(&mut canonicals);
            assert_eq!(c.to_string(), "ndv(\"emp@1\".dept | emp@1 × emp@2)");
            assert_eq!(c, least(&k));
        }
    }

    #[test]
    fn stored_forms_are_read_as_now() {
        // The keys are of the managed copy: spelled as when keys came
        // first, it is `@1`; the rows' least naming has it `@2`.
        let kind = |k: &str, m: &str| {
            let e = |i: &str, c: &str| col(format!("emp{i}.{c}"));
            let over = Context::table(&format!("emp{k}"))
                .cross(&Context::table(&format!("emp{m}")))
                .unwrap()
                .filter(&terms([e(m, "manager").eq(e(k, "id"))]));
            FactKind::Distinct { over, keys: terms([e(m, "dept")]) }
        };
        let old = kind("@2", "@1");
        let now = kind("#1", "#2").canonical();
        assert_ne!(old, now);
        assert_eq!(old.recanonical_in(&mut Canonicals::default()), now);
        assert_eq!(now.recanonical_in(&mut Canonicals::default()), now);
        // A set stored so reads as written now.
        let mut set = crate::facts::FactSet::default();
        let fact = |kind: FactKind| crate::facts::Fact { kind, value: crate::facts::Ratio::int(3), origins: vec![] };
        set.insert(fact(old.clone()));
        set.insert_bound(fact(old.clone()));
        set.insert_floor(fact(old));
        let read: crate::facts::FactSet = serde_json::from_str(&serde_json::to_string(&set).unwrap()).unwrap();
        assert!(read.get(&now).is_some() && read.bound(&now).is_some() && read.floor(&now).is_some());
    }
}
