//! Rewriting contexts into a normal form, so that equivalent plans meet.
//!
//! Engines pick among equivalent plans: joins in any order, filters pushed
//! anywhere below them, semi joins before or after the inner joins around
//! them, and whichever of several equal columns a join condition names. Each
//! of these computes the same rows, so a fact read off one holds for all.
//! Contexts are built through [`Spj::build`], which applies the rewrites
//! below in one direction only, so that every such plan names its rows the
//! same.
//!
//! Each rewrite gives the same rows for any data, and fires only when that
//! can be read off the terms themselves. Otherwise the context is kept as it
//! is: a rewrite that does not fire costs a match, but one that fires wrongly
//! would make a fact about other rows.
//!
//! - **Flatten.** Inner joins and filters over any inputs are one cross
//!   product with a set of predicates: `σp(A × σq(B × C)) = σ(p ∧ q)(A × B ×
//!   C)`. An input that is not itself an SPJ (a GROUP BY, an outer join) is
//!   an atom of the product.
//! - **Existence.** A semi or anti join keeps the rows of its kept side that
//!   pass a test that reads only that row and the other side, so it is a
//!   condition like a predicate: `(K ⋉ O) ⋈ C = (K ⋈ C) ⋉ O`, and two such
//!   conditions commute. This holds for `NOT IN` too.
//! - **Equalities.** `a = b ∧ b = c` and `a = b ∧ a = c` hold of the same
//!   rows: each says all three are non-NULL and equal. The bare column
//!   equalities among an SPJ's predicates are replaced by ones from each
//!   class's least column to every other, and either side's columns in a
//!   semi or anti join's condition are written as their class's least.
//! - **Decorrelation.** An engine may run a correlated `EXISTS` as a semi
//!   join of its outer rows K with `σP(X × group_k'(K'))`, where K' is a copy
//!   of K, on `k IS NOT DISTINCT FROM k'`. Each row of K finds its own key
//!   among K's grouped keys (a NULL too), so it has a partner exactly when
//!   some row of X satisfies P with `k'` read as its `k`: `K ⋉_{P[k'↦k]} X`.
//! - **Left joins.** `A ⟕q B` pairs each row of A with B's rows matching it
//!   under q, or with NULLs: what happens to a row of A depends on that row
//!   alone. So the preserved side is only the inputs q reads, and the rest
//!   of it, its other inputs, predicates and conditions, applies outside:
//!   `σp(Y × X) ⟕q B = σp(X × (Y ⟕q B))` when q reads only Y and B, and in
//!   particular `σp(A) ⟕q B = σp(A ⟕q B)`. A term of q that reads only B
//!   filters B: `A ⟕(q ∧ r) B = A ⟕q σr(B)`.
//! - **Null-rejecting filters.** A row of `A ⟕ B` without a partner has
//!   NULL in every column of B. A predicate that is NULL or false when B's
//!   columns are NULL drops those rows, leaving the inner join. Likewise for
//!   a full join: rejecting one side's NULLs leaves the join preserving it.
//!
//! A predicate on a GROUP BY's keys is not moved below it, though
//! `σp(group_K X) = group_K(σp X)`: a value the GROUP BY computes is named by
//! the rows it ran over (`"value"."sum(x) of group_K(X)"`) where the
//! aggregate ran, and anything reading it above would then name a GROUP BY
//! no longer among the rows. Engines move such predicates below themselves.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use datafusion::logical_expr::{BinaryExpr, Expr, Operator};

use super::context::{Context, Exists, ExistsKind, Term};
use crate::observed::requalify;

/// An SPJ being built. [`Spj::build`] gives it in normal form.
#[derive(Debug, Clone, Default)]
pub(crate) struct Spj {
    pub tables: BTreeSet<String>,
    pub atoms: BTreeSet<Context>,
    pub preds: BTreeSet<Term>,
    pub exists: BTreeSet<Exists>,
}

impl Spj {
    /// The parts of `c`: its own if an SPJ, else `c` as the only atom.
    pub fn of(c: &Context) -> Spj {
        match c {
            Context::Spj { tables, atoms, preds, exists } => Spj {
                tables: tables.clone(),
                atoms: atoms.clone(),
                preds: preds.clone(),
                exists: exists.clone(),
            },
            c => Spj { atoms: [c.clone()].into(), ..Spj::default() },
        }
    }

    /// The cross product of `self` and `other`, with both's conditions.
    pub fn merge(&mut self, other: Spj) {
        self.tables.extend(other.tables);
        self.atoms.extend(other.atoms);
        self.preds.extend(other.preds);
        self.exists.extend(other.exists);
    }

    /// The context, in normal form. One atom and nothing else is that atom.
    pub fn build(mut self) -> Context {
        // An outer join a predicate rejects the NULLs of is narrower.
        for a in &self.atoms {
            if let Some(narrower) = narrow(a, &self.preds) {
                let a = a.clone();
                self.atoms.remove(&a);
                self.merge(Spj::of(&narrower));
                return self.build();
            }
        }
        let Spj { tables, atoms, preds, exists } = self;
        if tables.is_empty() && atoms.len() == 1 && preds.is_empty() && exists.is_empty() {
            return atoms.into_iter().next().unwrap();
        }
        let classes = Classes::of(&preds);
        let preds = classes.preds(preds);
        let exists = exists
            .into_iter()
            .map(|e| Exists { kind: e.kind, on: on(&e.other, &classes.on(&e.on)), other: e.other })
            .collect();
        Context::Spj { tables, atoms, preds, exists }
    }
}

/// `e`, a condition on the rows of `kept`, with a copy of `kept` grouped
/// on the correlated columns taken out of its other side (see the module's
/// Decorrelation). Unchanged unless that copy is `kept` exactly, the
/// condition is exactly each key against its counterpart in `kept`, and
/// nothing else on the other side reads the copy.
pub(crate) fn decorrelate(kept: &Context, e: Exists) -> Exists {
    decorrelated(kept, &e).unwrap_or(e)
}

fn decorrelated(kept: &Context, e: &Exists) -> Option<Exists> {
    if !matches!(e.kind, ExistsKind::Semi | ExistsKind::Anti) {
        return None;
    }
    let Context::Spj { tables, atoms, preds, exists } = &e.other else { return None };
    for g in atoms {
        let Context::Derived { op, args: keys, inputs } = g else { continue };
        if op != "group" || keys.is_empty() {
            continue;
        }
        let copy = &inputs[0];
        let Some(names) = correspondence(copy, kept) else { continue };
        let f = |r: &str| names.get(r).cloned();
        if copy.rename(&f) != *kept {
            continue;
        }
        let mine: BTreeSet<String> = names.keys().cloned().collect();
        let reads = |t: &Term| t.expr.column_refs().iter().any(|c| c.relation.as_ref().is_some_and(|r| mine.contains(r.table())));
        // The condition is each key against its counterpart, and only that.
        let mut on = BTreeSet::new();
        for k in keys {
            if !matches!(k.expr, Expr::Column(_)) || !reads(k) {
                return None;
            }
            let outer = requalify(&k.expr, &f);
            on.insert(Term::new(Expr::BinaryExpr(BinaryExpr::new(Box::new(outer), Operator::IsNotDistinctFrom, Box::new(k.expr.clone())))));
        }
        // Compared with the kept rows' equal columns as their least: the
        // engine may correlate on any of them.
        if self::on(kept, &on) != self::on(kept, &e.on) {
            continue;
        }
        let others = atoms.iter().filter(|a| *a != g);
        if others.clone().any(|a| !a.tables().is_disjoint(&mine))
            || exists.iter().any(|x| x.on.iter().any(reads) || !x.other.tables().is_disjoint(&mine))
        {
            continue;
        }
        if tables.is_empty() && others.clone().next().is_none() {
            continue;
        }
        let (correlated, rest): (BTreeSet<Term>, BTreeSet<Term>) = preds.iter().cloned().partition(|p| reads(p));
        let other = Spj { tables: tables.clone(), atoms: others.cloned().collect(), preds: rest, exists: exists.clone() };
        let on = correlated.iter().map(|p| p.rename(&f)).collect();
        return Some(Exists { kind: e.kind, on, other: other.build() });
    }
    None
}

/// `A ⟕on B` in normal form (see the module's Left joins).
pub(crate) fn left_join(on: BTreeSet<Term>, l: Context, r: Context) -> Context {
    let reads = |t: &Term, instances: &BTreeSet<String>| {
        let refs = t.expr.column_refs();
        !refs.is_empty() && refs.iter().all(|c| c.relation.as_ref().is_some_and(|r| instances.contains(r.table())))
    };
    let rt = r.tables();
    let (only_r, on): (BTreeSet<Term>, BTreeSet<Term>) = on.into_iter().partition(|t| reads(t, &rt));
    let r = r.filter(&only_r);
    let derived = |on: BTreeSet<Term>, l: Context| Context::Derived { op: "Left join".into(), args: on.into_iter().collect(), inputs: vec![l, r.clone()] };
    let Context::Spj { tables, atoms, preds, exists } = &l else { return derived(on, l) };
    // The inputs of `l` that `on` reads.
    let read: BTreeSet<String> = on
        .iter()
        .flat_map(|t| t.expr.column_refs())
        .filter_map(|c| c.relation.as_ref().map(|r| r.table().to_string()))
        .collect();
    // A column of no instance (an aggregate's value) may come from any input.
    let all: BTreeSet<String> = l.tables().into_iter().chain(rt.iter().cloned()).collect();
    if !read.is_subset(&all) || on.iter().any(|t| t.expr.column_refs().iter().any(|c| c.relation.is_none())) {
        return derived(on, l);
    }
    let (kept_tables, rest_tables): (BTreeSet<String>, BTreeSet<String>) = tables.iter().cloned().partition(|t| read.contains(t));
    let (kept_atoms, rest_atoms): (BTreeSet<Context>, BTreeSet<Context>) =
        atoms.iter().cloned().partition(|a| !a.tables().is_disjoint(&read));
    if kept_tables.is_empty() && kept_atoms.is_empty() {
        return derived(on, l);
    }
    let y = Spj { tables: kept_tables, atoms: kept_atoms, ..Spj::default() }.build();
    let mut outer = Spj { tables: rest_tables, atoms: rest_atoms, preds: preds.clone(), exists: exists.clone() };
    outer.atoms.insert(derived(on, y));
    outer.build()
}

/// `a`, an outer join, as the narrower join that leaves the same rows under
/// `preds`; `None` if no predicate rejects either side's NULLs.
fn narrow(a: &Context, preds: &BTreeSet<Term>) -> Option<Context> {
    let Context::Derived { op, args, inputs } = a else { return None };
    let rejects = |side: &Context| {
        let instances = side.tables();
        preds.iter().any(|p| strict(&p.expr, &instances))
    };
    let on: BTreeSet<Term> = args.iter().cloned().collect();
    let inner = |l: &Context, r: &Context| Some(l.cross(r)?.filter(&on));
    match op.as_str() {
        "Left join" if rejects(&inputs[1]) => inner(&inputs[0], &inputs[1]),
        "Full join" => match (rejects(&inputs[0]), rejects(&inputs[1])) {
            (true, true) => inner(&inputs[0], &inputs[1]),
            (true, false) => Some(left_join(on, inputs[0].clone(), inputs[1].clone())),
            (false, true) => Some(left_join(on, inputs[1].clone(), inputs[0].clone())),
            (false, false) => None,
        },
        _ => None,
    }
}

/// Whether `e` is NULL whenever every column of `instances` is: a column of
/// them under operators that give NULL for a NULL operand. Conservative:
/// `IS NULL`, `COALESCE`, `CASE`, functions and the like never are.
fn strict(e: &Expr, instances: &BTreeSet<String>) -> bool {
    let s = |e: &Expr| strict(e, instances);
    match e {
        Expr::Column(c) => c.relation.as_ref().is_some_and(|r| instances.contains(r.table())),
        Expr::BinaryExpr(BinaryExpr { left, op, right }) => match op {
            Operator::Eq
            | Operator::NotEq
            | Operator::Lt
            | Operator::LtEq
            | Operator::Gt
            | Operator::GtEq
            | Operator::Plus
            | Operator::Minus
            | Operator::Multiply
            | Operator::Divide
            | Operator::Modulo
            | Operator::LikeMatch
            | Operator::ILikeMatch
            | Operator::NotLikeMatch
            | Operator::NotILikeMatch => s(left) || s(right),
            // NULL AND x is NULL or false; NULL OR x is x.
            Operator::And => s(left) || s(right),
            Operator::Or => s(left) && s(right),
            _ => false,
        },
        // NOT NULL and -NULL are NULL; NULL IS NOT NULL and NULL IS TRUE false.
        Expr::Not(e) | Expr::Negative(e) | Expr::IsNotNull(e) | Expr::IsTrue(e) => s(e),
        Expr::Cast(c) => s(&c.expr),
        Expr::TryCast(c) => s(&c.expr),
        Expr::Like(l) => s(&l.expr) || s(&l.pattern),
        Expr::Between(b) => s(&b.expr) || s(&b.low) || s(&b.high),
        Expr::InList(l) => s(&l.expr),
        _ => false,
    }
}

/// The renaming taking `from`'s instances to `to`'s, if each table has one
/// instance in each.
fn correspondence(from: &Context, to: &Context) -> Option<HashMap<String, String>> {
    let by_table = |c: &Context| {
        let mut m: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for t in c.tables() {
            m.entry(table_of(&t).to_string()).or_default().push(t);
        }
        m
    };
    let (a, b) = (by_table(from), by_table(to));
    if a.len() != b.len() {
        return None;
    }
    let mut out = HashMap::new();
    for (table, xs) in a {
        let ys = b.get(&table)?;
        let ([x], [y]) = (xs.as_slice(), ys.as_slice()) else { return None };
        out.insert(x.clone(), y.clone());
    }
    Some(out)
}

/// The table an instance reads: `lineitem` of `lineitem#3`, `lineitem#3~r9`,
/// `lineitem@2` or `lineitem`.
fn table_of(instance: &str) -> &str {
    instance.split(['#', '@']).next().unwrap_or(instance)
}

/// The terms of a condition `on` relating the rows of `c` to another
/// context, with `c`'s columns written as their class's least.
pub(crate) fn on(c: &Context, on: &BTreeSet<Term>) -> BTreeSet<Term> {
    match c {
        Context::Spj { preds, .. } => Classes::of(preds).on(on),
        _ => on.clone(),
    }
}

/// Grouping keys over the rows of `c`, with a bare column written as its
/// class's least: equal on every row, they group alike. Only for the keys of
/// a distinct count, which nothing reads: a GROUP BY's rows are read by the
/// columns it was given.
pub(crate) fn keys(c: &Context, keys: &BTreeSet<Term>) -> BTreeSet<Term> {
    let Context::Spj { preds, .. } = c else { return keys.clone() };
    let classes = Classes::of(preds);
    keys.iter().map(|k| classes.column(&k.expr).map_or_else(|| k.clone(), |e| Term::new(e.clone()))).collect()
}

/// `pred` over the rows of `over`, written as `over ∧ pred` writes it: the
/// same rows, whichever of several equal columns `pred` names. Empty if
/// `over` implies `pred`.
pub(crate) fn delta(over: &Context, pred: &BTreeSet<Term>) -> BTreeSet<Term> {
    let full = over.filter(pred);
    let (Context::Spj { preds: all, .. }, base) = (&full, over) else { return pred.clone() };
    match base {
        Context::Spj { preds, .. } => all.difference(preds).cloned().collect(),
        _ => all.clone(),
    }
}

/// The classes of columns that a set of predicates says are equal.
struct Classes {
    /// Each column in a class of more than one, by its text, with itself and
    /// the least column of its class.
    members: BTreeMap<String, (Expr, Expr)>,
}

impl Classes {
    fn of(preds: &BTreeSet<Term>) -> Classes {
        fn find(parent: &mut BTreeMap<String, String>, k: &str) -> String {
            let p = parent.get(k).cloned().unwrap_or_else(|| k.to_string());
            if p == k {
                return p;
            }
            let root = find(parent, &p);
            parent.insert(k.to_string(), root.clone());
            root
        }
        let mut parent: BTreeMap<String, String> = BTreeMap::new();
        let mut columns: BTreeMap<String, Expr> = BTreeMap::new();
        for p in preds {
            let Some((a, b)) = equality(&p.expr) else { continue };
            let (ka, kb) = (a.to_string(), b.to_string());
            columns.insert(ka.clone(), a.clone());
            columns.insert(kb.clone(), b.clone());
            let (ra, rb) = (find(&mut parent, &ka), find(&mut parent, &kb));
            // The root of a class is its least column.
            match ra.cmp(&rb) {
                std::cmp::Ordering::Less => parent.insert(rb, ra),
                std::cmp::Ordering::Greater => parent.insert(ra, rb),
                std::cmp::Ordering::Equal => None,
            };
        }
        let keys: Vec<String> = columns.keys().cloned().collect();
        let members = keys
            .into_iter()
            .map(|k| {
                let root = find(&mut parent, &k);
                let pair = (columns[&k].clone(), columns[&root].clone());
                (k, pair)
            })
            .collect();
        Classes { members }
    }

    /// The least column of `e`'s class, if `e` is a column in one.
    fn column(&self, e: &Expr) -> Option<&Expr> {
        match e {
            Expr::Column(_) => self.members.get(&e.to_string()).map(|(_, least)| least),
            _ => None,
        }
    }

    /// `preds` with their column equalities replaced by a star from each
    /// class's least column.
    fn preds(&self, preds: BTreeSet<Term>) -> BTreeSet<Term> {
        let mut out: BTreeSet<Term> = preds.into_iter().filter(|p| equality(&p.expr).is_none()).collect();
        for (column, least) in self.members.values() {
            if column != least {
                out.insert(Term::new(least.clone().eq(column.clone())));
            }
        }
        out
    }

    /// A condition's terms with each side that is a column of a class
    /// written as its class's least. Only bare `=` and `IS NOT DISTINCT
    /// FROM` comparisons are rewritten: on equal values they agree.
    fn on(&self, on: &BTreeSet<Term>) -> BTreeSet<Term> {
        if self.members.is_empty() {
            return on.clone();
        }
        on.iter()
            .map(|t| match &t.expr {
                Expr::BinaryExpr(BinaryExpr { left, op: op @ (Operator::Eq | Operator::IsNotDistinctFrom), right }) => {
                    let side = |e: &Expr| self.column(e).cloned().unwrap_or_else(|| e.clone());
                    Term::new(Expr::BinaryExpr(BinaryExpr::new(Box::new(side(left)), *op, Box::new(side(right)))))
                }
                _ => t.clone(),
            })
            .collect()
    }
}

/// The two columns of a bare equality of two different columns.
fn equality(e: &Expr) -> Option<(&Expr, &Expr)> {
    match e {
        Expr::BinaryExpr(BinaryExpr { left, op: Operator::Eq, right })
            if matches!(**left, Expr::Column(_)) && matches!(**right, Expr::Column(_)) && left != right =>
        {
            Some((left, right))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use datafusion::common::JoinType;
    use datafusion::prelude::{col, lit};

    use super::*;
    use crate::facts::context::terms;

    fn t(name: &str) -> Context {
        Context::table(name)
    }

    fn eq(a: &str, b: &str) -> BTreeSet<Term> {
        terms([col(a).eq(col(b))])
    }

    fn indf(a: Expr, b: Expr) -> Expr {
        Expr::BinaryExpr(BinaryExpr::new(Box::new(a), Operator::IsNotDistinctFrom, Box::new(b)))
    }

    fn join(l: &Context, r: &Context, on: BTreeSet<Term>) -> Context {
        l.cross(r).unwrap().filter(&on)
    }

    fn group(c: Context, key: &str) -> Context {
        Context::Derived { op: "group".into(), args: vec![Term::new(col(key))], inputs: vec![c] }
    }

    #[test]
    fn joins_over_atoms_flatten() {
        let (a, b) = (t("a"), t("b"));
        let g = group(t("c"), "c.k");
        let left = join(&join(&a, &b, eq("a.x", "b.x")), &g, eq("b.k", "c.k"));
        let right = join(&a, &join(&b, &g, eq("b.k", "c.k")), eq("a.x", "b.x"));
        assert_eq!(left, right);
        // A filter on the atom's rows, below the join or above it.
        let p = terms([col("c.k").gt(lit(1))]);
        assert_eq!(join(&a, &g.filter(&p), eq("a.x", "c.k")), join(&a, &g, eq("a.x", "c.k")).filter(&p));
        // One atom alone is itself.
        assert_eq!(Spj::of(&g).build(), g);
    }

    #[test]
    fn semi_joins_commute_with_inner_joins() {
        let (k, o, c) = (t("k"), t("o"), t("c"));
        let semi = |l: Context| Context::join(JoinType::LeftSemi, eq("k.x", "o.x"), l, o.clone());
        assert_eq!(join(&semi(k.clone()), &c, eq("k.y", "c.y")), semi(join(&k, &c, eq("k.y", "c.y"))));
        // And with each other, and with filters on the kept rows.
        let (o2, p) = (t("o2"), terms([col("k.z").lt(lit(3))]));
        let anti = |l: Context| Context::join(JoinType::LeftAnti, eq("k.x", "o2.x"), l, o2.clone());
        assert_eq!(anti(semi(k.clone())), semi(anti(k.clone())));
        assert_eq!(semi(k.clone()).filter(&p), semi(k.filter(&p)));
    }

    #[test]
    fn existence_kinds_differ() {
        let (k, o) = (t("k"), t("o"));
        let anti = k.exists(ExistsKind::Anti, eq("k.x", "o.x"), o.clone());
        let not_in = k.exists(ExistsKind::NotIn, eq("k.x", "o.x"), o.clone());
        let semi = k.exists(ExistsKind::Semi, eq("k.x", "o.x"), o);
        assert_ne!(anti, not_in);
        assert_ne!(anti, semi);
    }

    #[test]
    fn equal_columns_read_alike() {
        let abc = t("a").cross(&t("b")).unwrap().cross(&t("c")).unwrap();
        let chain = abc.filter(&eq("a.x", "b.x")).filter(&eq("b.x", "c.x"));
        let star = abc.filter(&eq("a.x", "b.x")).filter(&eq("a.x", "c.x"));
        let all = star.filter(&eq("b.x", "c.x"));
        assert_eq!(chain, star);
        assert_eq!(chain, all);
        // Not an equality of columns: kept as written.
        let plus = terms([col("a.x").eq(col("b.x") + lit(0))]);
        assert_ne!(abc.filter(&plus).filter(&eq("b.x", "c.x")), chain);
        let same = terms([indf(col("a.x"), col("b.x"))]).into_iter().chain(eq("b.x", "c.x")).collect();
        assert_ne!(abc.filter(&same), chain);
    }

    #[test]
    fn keys_and_conditions_read_the_least_column() {
        let ab = t("a").cross(&t("b")).unwrap().filter(&eq("a.x", "b.x"));
        assert_eq!(keys(&ab, &terms([col("b.x")])), terms([col("a.x")]));
        assert_eq!(keys(&ab, &terms([col("b.x"), col("a.x")])), terms([col("a.x")]));
        let semi = |c: &str| ab.exists(ExistsKind::Semi, eq(c, "o.x"), t("o"));
        assert_eq!(semi("b.x"), semi("a.x"));
    }

    #[test]
    fn filters_of_other_rows_differ() {
        let (a, b, c) = (t("a"), t("b"), t("c"));
        let p = terms([col("c.y").gt(lit(1))]);
        let ab = join(&a, &b, eq("a.x", "b.x"));
        assert_ne!(join(&ab, &c.filter(&p), eq("b.k", "c.k")), join(&ab, &c, eq("b.k", "c.k")));
    }

    /// `k ⋉ σ(l.k = k'.k)(l × group[k'.k](k'))` on `k.k IS NOT DISTINCT FROM k'.k`.
    fn delim(kept: &Context, copy: &Context, cond: Expr) -> Context {
        let other = join(&t("l"), &group(copy.clone(), "k#2.k"), eq("l.k", "k#2.k"));
        kept.exists(ExistsKind::Semi, terms([cond]), other)
    }

    #[test]
    fn decorrelates_a_copy_of_the_kept_rows() {
        let p = |r: &str| terms([col(format!("{r}.d")).lt(lit(5))]);
        let kept = t("k#1").filter(&p("k#1"));
        let copy = t("k#2").filter(&p("k#2"));
        let indf = indf(col("k#1.k"), col("k#2.k"));
        let plain = kept.exists(ExistsKind::Semi, eq("k#1.k", "l.k"), t("l"));
        assert_eq!(delim(&kept, &copy, indf.clone()), plain);
        // Not if the copy has other rows, or the condition may drop a NULL.
        assert_ne!(delim(&kept, &t("k#2"), indf), plain);
        assert_ne!(delim(&kept, &copy, col("k#1.k").eq(col("k#2.k"))), plain);
    }

    #[test]
    fn renaming_keeps_normal_form() {
        let (a, b) = (t("a#1"), t("b#2"));
        let full = Context::join(JoinType::Full, eq("a#1.x", "b#2.x"), a.clone(), b.clone());
        let swap = |r: &str| Some(if r == "a#1" { "z".to_string() } else { "c".to_string() });
        let renamed = full.rename(&swap);
        let fresh = Context::join(JoinType::Full, eq("z.x", "c.x"), t("z"), t("c"));
        assert_eq!(renamed, fresh);
    }

    fn left(on: BTreeSet<Term>, l: Context, r: Context) -> Context {
        Context::join(JoinType::Left, on, l, r)
    }

    fn pred(e: Expr) -> BTreeSet<Term> {
        terms([e])
    }

    /// A filter on a GROUP BY's keys stays above it, so that a value it
    /// computes, read above, still names a GROUP BY of the rows.
    #[test]
    fn filters_on_keys_stay_above_a_group() {
        let g = group(t("x"), "x.k");
        let p = pred(col("x.k").gt(lit(1)));
        let Context::Spj { atoms, preds, .. } = g.filter(&p) else { panic!() };
        assert_eq!(atoms, [g].into());
        assert_eq!(preds, p);
    }

    #[test]
    fn left_joins_keep_only_what_they_read() {
        let (a, b, c) = (t("a"), t("b"), t("c"));
        let p = pred(col("a.z").gt(lit(1)));
        // A filter on the preserved side, below or above.
        assert_eq!(left(eq("a.x", "b.x"), a.filter(&p), b.clone()), left(eq("a.x", "b.x"), a.clone(), b.clone()).filter(&p));
        // An inner join on the preserved side that the condition does not read.
        let ab = join(&a, &b, eq("a.y", "b.y"));
        assert_eq!(left(eq("b.x", "c.x"), ab, c.clone()), join(&a, &left(eq("b.x", "c.x"), b.clone(), c.clone()), eq("a.y", "b.y")));
        // A term of the condition on the other side alone filters it.
        let q = pred(col("b.w").lt(lit(2)));
        let on: BTreeSet<Term> = eq("a.x", "b.x").into_iter().chain(q.clone()).collect();
        assert_eq!(left(on, a.clone(), b.clone()), left(eq("a.x", "b.x"), a.clone(), b.filter(&q)));
    }

    #[test]
    fn left_joins_keep_preserved_rows_the_condition_reads() {
        let (a, b) = (t("a"), t("b"));
        // A term on the preserved side alone keeps its rows, unmatched.
        let p = pred(col("a.z").gt(lit(1)));
        let on: BTreeSet<Term> = eq("a.x", "b.x").into_iter().chain(p.clone()).collect();
        assert_ne!(left(on, a.clone(), b.clone()), left(eq("a.x", "b.x"), a.filter(&p), b.clone()));
    }

    #[test]
    fn rejecting_nulls_narrows_outer_joins() {
        let (a, b) = (t("a"), t("b"));
        let on = eq("a.x", "b.x");
        let inner = join(&a, &b, on.clone());
        let lj = left(on.clone(), a.clone(), b.clone());
        for p in [col("b.y").gt(lit(1)), col("b.y").is_not_null(), col("b.y").gt(lit(1)).or(col("b.w").eq(lit(2)))] {
            let p = pred(p);
            assert_eq!(lj.filter(&p), inner.filter(&p), "{p:?}");
        }
        for p in [col("b.y").is_null(), col("b.y").gt(lit(1)).or(col("a.z").eq(lit(2))), col("a.z").gt(lit(1))] {
            let p = pred(p);
            assert_ne!(lj.filter(&p), inner.filter(&p), "{p:?}");
        }
        let full = Context::join(JoinType::Full, on.clone(), a.clone(), b.clone());
        let (pa, pb) = (pred(col("a.y").gt(lit(1))), pred(col("b.y").gt(lit(1))));
        assert_eq!(full.filter(&pa), lj.filter(&pa));
        assert_eq!(full.filter(&pb), left(on.clone(), b.clone(), a.clone()).filter(&pb));
        assert_eq!(full.filter(&pa).filter(&pb), inner.filter(&pa).filter(&pb));
        assert!(matches!(full.filter(&pred(col("a.y").is_null())), Context::Spj { ref atoms, .. } if atoms.contains(&full)));
    }

}
