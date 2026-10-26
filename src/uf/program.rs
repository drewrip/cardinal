//! One SMT program: the axiom table instantiated for the terms at hand,
//! the ground facts of §6, and the observations, each tracked so that an
//! unsat core can name it.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write as _;

use super::axioms::{self, Axiom, Fam, ax};
use super::expr::{Arith, Col, E, Lit, Smt, Ty};
use super::preds::{self, Decided, Link};
use super::terms::{ColsId, FamId, JoinKind, Pred, PredId, Rel, RelId, Terms, alias_col, cols_name, sanitize, unalias_col};
use super::translate::{Fact, Tables};

/// Declared keys, foreign keys and value domains of the tables.
#[derive(Debug, Clone, Default)]
pub(crate) struct Schema {
    /// `(table, columns)`: no two rows agree on them.
    pub keys: Vec<(String, Vec<String>)>,
    /// `(T, A, U, B)`: each row of `T` has `A` non-NULL and equal to `B`
    /// of exactly one row of `U`.
    pub fks: Vec<(String, Vec<String>, String, Vec<String>)>,
    /// `(table, column)` never NULL.
    pub nonnull: BTreeSet<(String, String)>,
}

/// A program, and the tracked facts' literals, by name.
pub(crate) struct Program {
    pub text: String,
    pub tracked: Vec<(String, String)>,
    pub root: String,
    pub stats: Stats,
    /// How many assertions the text holds, to check it parses whole.
    pub assertions: usize,
}

#[derive(Debug, Clone, Default)]
pub struct Stats {
    pub relations: usize,
    pub predicates: usize,
    pub families: usize,
    pub colsets: usize,
    pub axioms: usize,
    pub bytes: usize,
}

/// Most column sets in the universe (§6.3).
const MAX_COLSETS: usize = 800;
/// Most columns of a set the universe holds every part of.
const MAX_SMALL: usize = 4;
/// A large integer beyond every value (§3 rule 8), as text.
#[allow(dead_code)]
const BIG: &str = "1000000000000000";

/// Builds the program bounding `root`, with `facts` (named), over
/// `groups`: each plan's relations, whose families may regroup.
pub(crate) fn build(
    terms: &mut Terms,
    tables: &Tables,
    schema: &Schema,
    facts: &[(String, Fact)],
    groups: &[Vec<RelId>],
    root: RelId,
) -> Program {
    let mut roots: Vec<RelId> = facts.iter().flat_map(|(_, f)| fact_rels(f)).collect();
    roots.push(root);
    roots.extend(groups.iter().flatten());

    // Predicates: each literal and its negation, chains, aliases' and
    // expressions' rewrites.
    let mut rels = terms.reachable(roots.iter().copied());
    let mut literals: Vec<PredId> = vec![];
    let mut seen: BTreeSet<PredId> = BTreeSet::new();
    let mut links: Vec<Link> = vec![];
    let mut chained: BTreeSet<PredId> = BTreeSet::new();
    let mut opaque: Vec<PredId> = vec![];
    let mut cmps: Vec<PredId> = vec![];
    let mut todo: Vec<PredId> = rels.iter().flat_map(|r| terms.rel_preds(*r)).collect();
    // A join on several key pairs is a join on fewer, filtered by the rest
    // (`extend_keys`): each family with one pair less, and the equality.
    let mut extensions: Vec<(FamId, FamId, PredId)> = vec![];
    let joined: BTreeSet<FamId> = rels.iter().filter_map(|r| if let Rel::Join(_, f, ..) = terms.get(*r) { Some(*f) } else { None }).collect();
    for f in joined {
        let fam = terms.families[f.0 as usize].clone();
        if fam.residual.is_some() || fam.null_eq || fam.pairs.len() < 2 {
            continue;
        }
        for (k, (a, b)) in fam.pairs.iter().enumerate() {
            let ty = |c: &Col| terms.types.get(c).copied().unwrap_or(Ty::Other);
            let eq = E::Cmp(super::expr::Cmp::Eq, Box::new(E::Col(a.clone(), ty(a))), Box::new(E::Col(b.clone(), ty(b))));
            let p = preds::make(terms, &eq);
            let mut pairs = fam.pairs.clone();
            pairs.remove(k);
            let g = terms.family(super::terms::Family { pairs, null_eq: false, residual: None });
            extensions.push((f, g, p));
            todo.push(p);
        }
    }
    let mut upreds: Vec<(u32, PredId, PredId)> = vec![];
    let mut unfolds: Vec<(Col, PredId, PredId)> = vec![];
    while let Some(p) = todo.pop() {
        let base = match terms.get_pred(p) {
            Pred::Neg(q) => *q,
            _ => p,
        };
        if !seen.insert(base) {
            continue;
        }
        match terms.get_pred(base).clone() {
            Pred::Atom { .. } | Pred::Compound(..) => {
                let n = terms.pred(Pred::Neg(base));
                literals.push(base);
                literals.push(n);
                seen.insert(n);
                let before = links.len();
                preds::chains(terms, base, &mut links, &mut chained);
                for l in &links[before..] {
                    todo.push(l.first);
                    todo.push(l.rest);
                }
                // Its alias-free form (`upred`), and its expression
                // columns unfolded.
                let reads = terms.reads(base).unwrap_or_default();
                let mut aliases: BTreeSet<u32> = BTreeSet::new();
                for c in &reads {
                    if let Some(i) = alias_of(c) {
                        aliases.insert(i);
                    }
                }
                for i in aliases {
                    if let Some(u) = rename_pred(terms, base, &|c| unalias_col(c, i).unwrap_or_else(|| c.to_string())) {
                        upreds.push((i, base, u));
                        todo.push(u);
                    }
                }
                for c in &reads {
                    if let Some(e) = terms.exprs.get(c).cloned()
                        && let Some(u) = substitute_pred(terms, base, c, &e)
                    {
                        unfolds.push((c.clone(), base, u));
                        todo.push(u);
                    }
                }
            }
            Pred::True | Pred::False => {}
            Pred::Cmp { .. } => cmps.push(base),
            Pred::Opaque(..) => opaque.push(base),
            Pred::Neg(_) => unreachable!(),
        }
    }
    literals.sort();
    literals.dedup();
    let t0 = std::time::Instant::now();
    let decided = preds::decide(terms, &literals);
    if std::env::var("CARDINAL_UF_TIME").is_ok() {
        eprintln!("uf: decide {} literals {:.2}s", literals.len(), t0.elapsed().as_secs_f64());
    }

    // Families, with their mirrors and plain forms.
    let mut fams: BTreeSet<FamId> = BTreeSet::new();
    for r in &rels {
        if let Rel::Join(_, f, ..) | Rel::Rt(f, ..) = terms.get(*r) {
            fams.insert(*f);
            fams.insert(terms.mirror(*f));
        }
    }
    let mut plain: BTreeMap<FamId, FamId> = BTreeMap::new();
    for f in fams.clone() {
        let fam = terms.families[f.0 as usize].clone();
        if fam.residual.is_some() {
            let p = terms.family(super::terms::Family { residual: None, ..fam });
            plain.insert(f, p);
            fams.insert(p);
            fams.insert(terms.mirror(p));
        }
    }
    for (_, g, _) in &extensions {
        fams.insert(*g);
        fams.insert(terms.mirror(*g));
    }
    let rt_fams: BTreeSet<FamId> = rels.iter().filter_map(|r| if let Rel::Rt(f, ..) = terms.get(*r) { Some(*f) } else { None }).collect();
    // Families each plan uses, for associativity; and with each runtime
    // filter's and expression column's plan, which they move through.
    let mut pairs: BTreeSet<(FamId, FamId)> = BTreeSet::new();
    let mut rt_pairs: BTreeSet<(FamId, FamId)> = BTreeSet::new();
    let mut expr_pairs: BTreeSet<(Col, FamId)> = BTreeSet::new();
    for g in groups.iter().chain([&vec![root]]) {
        let mut fs = BTreeSet::new();
        let mut rts = BTreeSet::new();
        let mut gs = BTreeSet::new();
        for r in terms.reachable(g.iter().copied()) {
            match terms.get(r) {
                Rel::Join(_, f, ..) => {
                    fs.insert(*f);
                    fs.insert(terms.mirror(*f));
                    if let Some(p) = plain.get(f) {
                        fs.insert(*p);
                        fs.insert(terms.mirror(*p));
                    }
                }
                Rel::Rt(f, ..) => {
                    rts.insert(*f);
                }
                Rel::Extend(c, _) => {
                    gs.insert(c.clone());
                }
                _ => {}
            }
        }
        for f in &fs {
            for g in &fs {
                pairs.insert((*f, *g));
            }
            for t in &rts {
                rt_pairs.insert((*t, *f));
            }
            for c in &gs {
                expr_pairs.insert((c.clone(), *f));
            }
        }
    }

    // Expression columns and aggregates in use.
    let mut exprs: BTreeSet<Col> = BTreeSet::new();
    let mut aggs: BTreeSet<Col> = BTreeSet::new();
    let mut aliases: BTreeSet<u32> = BTreeSet::new();
    for r in &rels {
        match terms.get(*r) {
            Rel::Extend(g, _) => {
                exprs.insert(g.clone());
            }
            Rel::Aggregate(_, g, _) | Rel::Scalar(g, _) => {
                aggs.extend(terms.cols[g.0 as usize].iter().cloned());
            }
            Rel::Alias(i, _) => {
                aliases.insert(*i);
            }
            _ => {}
        }
    }
    for c in terms.types.keys() {
        if let Some(i) = alias_of(c) {
            let _ = i;
        }
    }

    let mut e = Emit { terms, out: String::new(), axioms: 0, colsets: BTreeSet::new(), decls: BTreeSet::new() };
    e.terms.short.set(true);
    e.terms.named.borrow_mut().clear();

    // ---------- axioms ----------
    let mut axs: Vec<Axiom> = axioms::shared();
    let fam_of = |e: &Emit, f: FamId| e.fam(f);
    let mut fam_text: BTreeMap<FamId, Fam> = BTreeMap::new();
    for f in &fams {
        fam_text.insert(*f, fam_of(&e, *f));
    }
    for f in &fams {
        let fam = &fam_text[f];
        axs.extend(axioms::family(fam));
        axs.extend(family_extra(&e, *f, fam));
        for (_, g, p) in extensions.iter().filter(|(x, ..)| x == f) {
            let (fj, gj, ps) = (&fam.j, &fam_text[g].j, e.terms.pred_smt(*p));
            axs.push(ax(
                format!("extend_keys{}{}", fam.tag, fam_text[g].tag),
                "(x Rel) (y Rel)",
                &format!("(= ({fj} x y) (filter {ps} ({gj} x y)))"),
                &[&format!("({fj} x y)"), &format!("(filter {ps} ({gj} x y))")],
            ));
        }
        if let Some(p) = plain.get(f) {
            let r = e.terms.families[f.0 as usize].residual.unwrap();
            axs.extend(axioms::residual(fam, &fam_text[p], &e.terms.pred_smt(r)));
        }
    }
    for (f, g) in &pairs {
        if e.terms.families[g.0 as usize].residual.is_none() {
            axs.push(axioms::assoc(&fam_text[f], &fam_text[g]));
        }
    }
    // A semi or anti join of an alias, on the alias's columns, is the
    // alias of the join of what it aliases.
    for f in &fams {
        let fam = e.terms.families[f.0 as usize].clone();
        let Some(i) = fam.pairs.first().and_then(|(a, _)| alias_of(a)) else { continue };
        if fam.residual.is_some() || fam.pairs.iter().any(|(a, _)| alias_of(a) != Some(i)) {
            continue;
        }
        let mut pairs: Vec<(Col, Col)> = fam.pairs.iter().map(|(a, b)| (unalias_col(a, i).unwrap(), b.clone())).collect();
        pairs.sort();
        let Some(g) = e.terms.find_family(&super::terms::Family { pairs, ..fam }) else { continue };
        if !fams.contains(&g) {
            continue;
        }
        let (ft, gt) = (&fam_text[f], &fam_text[&g]);
        for (kind, fun, gun) in [("semi", &ft.s, &gt.s), ("anti", &ft.a, &gt.a)] {
            axs.push(ax(
                format!("alias_{kind}{}{}", ft.tag, gt.tag),
                "(x Rel) (y Rel)",
                &format!("(= ({fun} (alias {i} x) y) (alias {i} ({gun} x y)))"),
                &[&format!("({fun} (alias {i} x) y)")],
            ));
        }
    }
    for f in &rt_fams {
        let fam = &fam_text[f];
        let t = e.terms.rt_fn(*f);
        axs.extend(axioms::runtime(&t, fam, &fam.kl));
        for g in rt_pairs.iter().filter(|(t, _)| t == f).map(|(_, g)| g) {
            let gf = &fam_text[g];
            for (kind, fun) in [("j", &gf.j), ("s", &gf.s), ("l", &gf.lj)] {
                axs.push(axioms::runtime_push(&t, &fam.tag, fun, &format!("{}{kind}", gf.tag)));
            }
        }
        e.decls.insert(format!("(declare-fun {t} (Occ Rel Rel) Rel)"));
    }
    // Foreign keys, for each family pairing (an alias of) T's columns with
    // (an alias of) U's.
    for (n, (t, a, u, bcols)) in schema.fks.iter().enumerate() {
        for f in &fams {
            let fam = &e.terms.families[f.0 as usize];
            if fam.residual.is_some() || fam.null_eq || fam.pairs.len() != a.len() {
                continue;
            }
            let Some((ti, ui)) = fk_match(fam, t, a, u, bcols) else { continue };
            let tt = aliased_scan(t, ti);
            let ut = aliased_scan(u, ui);
            let r = e.terms.mirror(*f);
            let name = format!("fk{n}{}", fam_text[f].tag);
            axs.extend(axioms::foreign_key(&name, &tt, &ut, &fam_text[f], &fam_text[&r]));
        }
    }
    // Expression columns: their domains, unfolding, and moving above joins.
    for g in &exprs {
        axs.extend(expr_axioms(&mut e, g, tables, &decided));
        for f in expr_pairs.iter().filter(|(c, _)| c == g).map(|(_, f)| f) {
            let fam = &e.terms.families[f.0 as usize];
            if fam.pairs.iter().any(|(l, _)| l == g) {
                continue;
            }
            let gs = e.one(g);
            axs.extend(axioms::extend_join(&gs, &sanitize(g), &fam_text[f]));
        }
    }
    for (g, p, u) in &unfolds {
        let gs = e.one(g);
        let (ps, us) = (e.terms.pred_smt(*p), e.terms.pred_smt(*u));
        let reads = e.terms.reads(*u).unwrap_or_default();
        let rs = e.set(reads);
        axs.push(ax(
            format!("unfold[{}|{}]", sanitize(g), e.terms.pred_text(*p)),
            "(x Rel)",
            &format!("(=> (csub {rs} (cols x)) (= (filter {ps} (extend {gs} x)) (extend {gs} (filter {us} x))))"),
            &[&format!("(filter {ps} (extend {gs} x))")],
        ));
    }
    // Aggregate columns, and HAVING on counts.
    for c in &aggs {
        axs.extend(agg_axioms(&mut e, c));
    }
    axs.extend(having_axioms(&mut e, &decided, &aggs));
    // Each literal's range and NULL-rejection (§7.3).
    for p in &literals {
        if let Some(a) = range_axiom(&mut e, *p, &decided) {
            axs.push(a);
        }
    }
    // A literal never TRUE, but not FALSE everywhere, keeps no rows; it is
    // no constant (`never`), whose negation would keep them all.
    for p in &decided.empty {
        let ps = e.terms.pred_smt(*p);
        axs.push(ax(format!("empty[{}]", e.terms.pred_text(*p)), "(x Rel)", &format!("(= (card (filter {ps} x)) 0)"), &[&format!("(filter {ps} x)")]));
    }

    // ---------- ground facts ----------
    // The columns anything reads: only they get per-column facts.
    let mut used: BTreeSet<Col> = BTreeSet::new();
    for p in literals.iter().chain(&opaque).chain(&cmps) {
        used.extend(e.terms.reads(*p).unwrap_or_default());
    }
    for r in &rels {
        match e.terms.get(*r) {
            Rel::Group(k, _) | Rel::Aggregate(k, ..) => used.extend(e.terms.cols[k.0 as usize].iter().cloned()),
            Rel::Join(_, f, ..) | Rel::Rt(f, ..) => {
                for (a, b) in &e.terms.families[f.0 as usize].pairs {
                    used.insert(a.clone());
                    used.insert(b.clone());
                }
            }
            _ => {}
        }
    }
    for x in e.terms.exprs.values() {
        used.extend(x.reads());
    }
    for a in e.terms.aggs.values() {
        if let Some(x) = &a.arg {
            used.extend(x.reads());
        }
    }
    let used: BTreeSet<Col> = used.iter().map(|c| match alias_of(c) {
        Some(i) => unalias_col(c, i).unwrap(),
        None => c.clone(),
    }).chain(used.iter().cloned()).collect();
    let mut ground: Vec<String> = vec![];
    // Schema facts, for the tables the plans read.
    let mut scanned: BTreeSet<String> = BTreeSet::new();
    for r in &rels {
        if let Rel::Scan(t) = e.terms.get(*r) {
            scanned.insert(t.clone());
        }
    }
    for r in rels.clone() {
        match e.terms.get(r).clone() {
            Rel::Scan(_) | Rel::Opaque(_) => {
                if let Some(c) = e.terms.rel_cols[r.0 as usize] {
                    let s = e.cols(c);
                    ground.push(format!("(= (cols {}) {s})", e.terms.rel_smt(r)));
                }
            }
            _ => {}
        }
    }
    for t in &scanned {
        let scan = format!("(scan |t:{}|)", sanitize(t));
        for (kt, k) in &schema.keys {
            if kt == t {
                let s = e.set(k.iter().map(|c| format!("{t}.{c}")).collect());
                ground.push(format!("(key {scan} {s})"));
            }
        }
        for c in tables.columns(t) {
            let col = format!("{t}.{c}");
            if !used.contains(&col) {
                continue;
            }
            let s = e.one(&col);
            if schema.nonnull.contains(&(t.clone(), c.clone())) {
                ground.push(format!("(nonnull {scan} {s})"));
            }
            let ty = tables.catalog.tables.get(t).and_then(|s| s.field_with_name(&c).ok()).map(|f| f.data_type().clone());
            use datafusion::arrow::datatypes::DataType as D;
            let range = match ty {
                Some(D::Int8) => Some((-128i64, 127i64)),
                Some(D::UInt8) => Some((0, 255)),
                Some(D::Int16) => Some((-32768, 32767)),
                Some(D::UInt16) => Some((0, 65535)),
                Some(D::Boolean) => {
                    ground.push(format!("(<= (ndv {scan} {s}) 3)"));
                    None
                }
                _ => None,
            };
            if let Some((lo, hi)) = range {
                ground.push(format!("(>= (min {scan} {s}) {}) (<= (max {scan} {s}) {})", real(lo as i128), real(hi as i128)));
            }
        }
    }
    for (t, a, u, bcols) in &schema.fks {
        if !(scanned.contains(t) && scanned.contains(u)) {
            continue;
        }
        let sa = e.set(a.iter().map(|c| format!("{t}.{c}")).collect());
        let sb = e.set(bcols.iter().map(|c| format!("{u}.{c}")).collect());
        let (st, su) = (format!("(scan |t:{}|)", sanitize(t)), format!("(scan |t:{}|)", sanitize(u)));
        ground.push(format!("(<= (ndv {st} {sa}) (ndv {su} {sb}))"));
        ground.push(format!("(nonnull {st} {sa})"));
        // The referenced columns are a key.
        ground.push(format!("(key {su} {sb})"));
    }
    // Predicate facts. A constant has no columns of its own: two of them
    // that read different columns are one constant.
    let mut constant: BTreeSet<PredId> = BTreeSet::new();
    for p in decided.never.iter().chain(&decided.always) {
        constant.insert(*p);
        constant.insert(e.terms.pred(Pred::Neg(*p)));
    }
    for p in literals.iter().chain(&opaque) {
        if constant.contains(p) {
            continue;
        }
        let Some(reads) = e.terms.reads(*p) else { continue };
        let s = e.set(reads);
        if let Some(c) = e.terms.pred_const(*p) {
            ground.push(format!("(= (reads {c}) {s})"));
        }
    }
    for p in &cmps {
        let s = e.set(e.terms.reads(*p).unwrap_or_default());
        ground.push(format!("(= (reads {}) {s})", e.terms.pred_smt(*p)));
    }
    for (p, q) in &decided.implies {
        ground.push(format!("(implies {} {})", e.terms.pred_smt(*p), e.terms.pred_smt(*q)));
    }
    for (p, q) in &decided.equal {
        if e.terms.reads(*p) == e.terms.reads(*q) {
            ground.push(format!("(= {} {})", e.terms.pred_smt(*p), e.terms.pred_smt(*q)));
        } else {
            ground.push(format!("(implies {} {})", e.terms.pred_smt(*p), e.terms.pred_smt(*q)));
            ground.push(format!("(implies {} {})", e.terms.pred_smt(*q), e.terms.pred_smt(*p)));
        }
    }
    for p in &decided.never {
        ground.push(format!("(= {} |p:false|)", e.terms.pred_smt(*p)));
    }
    for p in &decided.total {
        ground.push(format!("(total {})", e.terms.pred_smt(*p)));
    }
    ground.push("(total |p:true|)".into());
    ground.push("(total |p:false|)".into());
    for p in &decided.always {
        ground.push(format!("(= {} |p:true|)", e.terms.pred_smt(*p)));
    }
    for (p, f) in &decided.facts {
        if let Some(w) = f.width {
            ground.push(format!("(= (width {}) {w})", e.terms.pred_smt(*p)));
            if w == 1 {
                ground.push(format!("(point {})", e.terms.pred_smt(*p)));
            }
        }
    }
    for l in &links {
        let f = if l.or { "orof" } else { "andof" };
        ground.push(format!("({f} {} {} {})", e.terms.pred_smt(l.p), e.terms.pred_smt(l.first), e.terms.pred_smt(l.rest)));
    }
    for (i, p, u) in &upreds {
        ground.push(format!("(= (upred {i} {}) {})", e.terms.pred_smt(*p), e.terms.pred_smt(*u)));
        let (np, nu) = (e.terms.pred(Pred::Neg(*p)), e.terms.pred(Pred::Neg(*u)));
        ground.push(format!("(= (upred {i} {}) {})", e.terms.pred_smt(np), e.terms.pred_smt(nu)));
    }
    // Expression columns' inputs, and integer columns.
    for g in &exprs {
        let d = e.terms.exprs[g].reads();
        let (gs, ds) = (e.one(g), e.set(d));
        ground.push(format!("(= (def {gs}) {ds})"));
    }
    // Observations and the probe's shape facts, tracked.
    let mut tracked = vec![];
    let mut obs_text = String::new();
    for (name, f) in facts {
        let text = match f {
            Fact::Card(r, n) => format!("(= (card {}) {n})", e.terms.rel_smt(*r)),
            Fact::KeyRange(r, c, lo, hi) => {
                let s = e.one(c);
                let rs = e.terms.rel_smt(*r);
                let mut parts = vec![];
                if let Some(lo) = lo {
                    parts.push(format!("(>= (min {rs} {s}) {})", real(*lo)));
                }
                if let Some(hi) = hi {
                    parts.push(format!("(<= (max {rs} {s}) {})", real(*hi)));
                }
                format!("(and {})", parts.join(" "))
            }
            Fact::KeyCount(r, c, n) => {
                let s = e.one(c);
                let rs = e.terms.rel_smt(*r);
                format!("(and (<= (ndv {rs} {s}) {}) (=> (nonnull {rs} {s}) (<= (ndv {rs} {s}) {n})) (>= (ndv {rs} {s}) {}))", n + 1, (*n).min(2))
            }
        };
        let lit = format!("|a!{}|", sanitize(name));
        writeln!(obs_text, "(declare-const {lit} Bool)\n(assert (=> {lit} {text}))").unwrap();
        tracked.push((name.clone(), lit));
    }

    // ---------- the column-set universe (§6.3) ----------
    // Constants are the small sets (keys, predicates' columns, grouping
    // keys, ...) and the tables' columns. A join's columns stay a `cup`
    // term, which `csub_cup` and `csub_split` decompose on demand.
    let relation_sets: BTreeSet<ColsId> = rels.iter().filter_map(|r| e.terms.rel_cols[r.0 as usize]).collect();
    let mut table_sets: BTreeSet<ColsId> = BTreeSet::new();
    for r in &rels {
        if let Rel::Scan(_) = e.terms.get(*r)
            && let Some(c) = e.terms.rel_cols[r.0 as usize]
        {
            table_sets.insert(c);
            e.colsets.insert(c);
        }
    }
    let mut rhs: BTreeSet<ColsId> = BTreeSet::new();
    for f in &fams {
        let fam = e.terms.families[f.0 as usize].clone();
        let (l, r) = (e.terms.colset(fam.left()), e.terms.colset(fam.right()));
        e.colsets.insert(l);
        e.colsets.insert(r);
        rhs.insert(l);
        rhs.insert(r);
        for (l, r) in &fam.pairs {
            e.one(l);
            e.one(r);
        }
    }
    for p in &cmps {
        if let Pred::Cmp { a, g, .. } = e.terms.get_pred(*p).clone() {
            e.one(&a);
            e.one(&g);
        }
    }
    for r in &rels {
        match e.terms.get(*r).clone() {
            Rel::Extend(g, _) => {
                e.one(&g);
                let id = e.terms.one(&g);
                rhs.insert(id);
            }
            Rel::Group(k, _) => {
                e.colsets.insert(k);
            }
            Rel::Aggregate(k, g, _) => {
                e.colsets.insert(k);
                e.colsets.insert(g);
                let u: BTreeSet<Col> = e.terms.cols[k.0 as usize].union(&e.terms.cols[g.0 as usize]).cloned().collect();
                let id = e.terms.colset(u);
                e.colsets.insert(id);
            }
            Rel::Scalar(g, _) => {
                e.colsets.insert(g);
            }
            _ => {}
        }
    }
    let (universe, tables_u) = universe(&mut e, &relation_sets, &table_sets, &aliases);
    let mut book = String::new();
    let sets: Vec<(ColsId, BTreeSet<Col>)> = universe.iter().map(|c| (*c, e.terms.cols[c.0 as usize].clone())).collect();
    let index: HashMap<BTreeSet<Col>, ColsId> = sets.iter().map(|(c, s)| (s.clone(), *c)).collect();
    let syms: HashMap<ColsId, String> = sets.iter().map(|(c, _)| (*c, e.terms.cols_sym(*c))).collect();
    for (x, xs) in &sets {
        let xn = &syms[x];
        let small = !tables_u.contains(x);
        for (y, ys) in &sets {
            let yn = &syms[y];
            if small && xs.is_subset(ys) {
                writeln!(book, "(assert (csub {xn} {yn}))").unwrap();
            }
            if !small || tables_u.contains(y) || xs.is_empty() || ys.is_empty() {
                continue;
            }
            if x < y {
                let u: BTreeSet<Col> = xs.union(ys).cloned().collect();
                if let Some(z) = index.get(&u) {
                    let zn = &syms[z];
                    writeln!(book, "(assert (= (cup {xn} {yn}) {zn})) (assert (= (cup {yn} {xn}) {zn}))").unwrap();
                }
            } else if x == y {
                writeln!(book, "(assert (= (cup {xn} {xn}) {xn}))").unwrap();
            }
            if rhs.contains(y) {
                let d: BTreeSet<Col> = xs.difference(ys).cloned().collect();
                if !d.is_empty()
                    && d != *xs
                    && let Some(z) = index.get(&d)
                {
                    writeln!(book, "(assert (= (cdiff {xn} {yn}) {}))", syms[z]).unwrap();
                }
            }
        }
        // Integer columns.
        if xs.len() == 1 && xs.iter().all(|c| e.terms.types.get(c) == Some(&Ty::Int)) {
            writeln!(book, "(assert (intcol {xn}))").unwrap();
        }
    }
    // Which small sets each join of the program has: what `csub_cup` and
    // `csub_split` would derive, ground, for the terms there are.
    for r in &rels {
        if !matches!(e.terms.get(*r), Rel::Join(..)) {
            continue;
        }
        let Some(c) = e.terms.rel_cols[r.0 as usize] else { continue };
        let cs = e.terms.cols[c.0 as usize].clone();
        let rs = e.terms.rel_smt(*r);
        let mut within = vec![];
        for (x, xs) in &sets {
            if !tables_u.contains(x) && !xs.is_empty() && xs.is_subset(&cs) {
                within.push(syms[x].clone());
            }
        }
        if !within.is_empty() {
            let parts: Vec<String> = within.iter().map(|w| format!("(csub {w} (cols {rs}))")).collect();
            writeln!(book, "(assert (and {}))", parts.join(" ")).unwrap();
        }
    }
    for i in &aliases {
        for (x, xs) in &sets {
            let a: BTreeSet<Col> = xs.iter().map(|c| alias_col(c, *i)).collect();
            if let Some(z) = index.get(&a) {
                writeln!(book, "(assert (= (acols {i} {}) {}))", e.terms.cols_sym(*x), e.terms.cols_sym(*z)).unwrap();
            }
            let u: BTreeSet<Col> = xs.iter().filter_map(|c| unalias_col(c, *i)).collect();
            if !u.is_empty()
                && let Some(z) = index.get(&u)
            {
                writeln!(book, "(assert (= (ucols {i} {}) {}))", e.terms.cols_sym(*x), e.terms.cols_sym(*z)).unwrap();
            }
        }
    }
    if sets.len() > 1 {
        let names: Vec<String> = sets.iter().map(|(c, _)| e.terms.cols_sym(*c)).collect();
        writeln!(book, "(assert (distinct {}))", names.join(" ")).unwrap();
    }

    // ---------- declarations ----------
    let mut decls = String::from(axioms::DECLS);
    for (c, _) in &sets {
        writeln!(decls, "(declare-const {} Cols)", e.terms.cols_sym(*c)).unwrap();
    }
    for t in &scanned {
        writeln!(decls, "(declare-const |t:{}| Table)", sanitize(t)).unwrap();
    }
    let mut consts: BTreeSet<String> = BTreeSet::new();
    for p in literals.iter().chain(&opaque) {
        if let Some(c) = e.terms.pred_const(*p) {
            consts.insert(c);
        }
    }
    for l in &links {
        for p in [l.p, l.first, l.rest] {
            if let Some(c) = e.terms.pred_const(p) {
                consts.insert(c);
            }
        }
    }
    consts.remove("|p:true|");
    consts.remove("|p:false|");
    for c in consts {
        writeln!(decls, "(declare-const {c} Pred)").unwrap();
    }
    let mut occs: BTreeSet<String> = BTreeSet::new();
    let mut opaques: BTreeSet<String> = BTreeSet::new();
    for r in &rels {
        match e.terms.get(*r) {
            Rel::Part(o, _) | Rel::Opt(o, ..) | Rel::Rt(_, o, ..) => {
                occs.insert(format!("|o:{}|", sanitize(o)));
            }
            Rel::Opaque(n) => {
                opaques.insert(format!("|r:{}|", sanitize(n)));
            }
            _ => {}
        }
    }
    for o in occs {
        writeln!(decls, "(declare-const {o} Occ)").unwrap();
    }
    for o in opaques {
        writeln!(decls, "(declare-const {o} Rel)").unwrap();
    }
    for f in &fams {
        for k in [JoinKind::Inner, JoinKind::Left, JoinKind::Semi, JoinKind::Anti, JoinKind::NotIn, JoinKind::Full] {
            writeln!(decls, "(declare-fun {} (Rel Rel) Rel)", e.terms.fam_fn(*f, k)).unwrap();
        }
    }
    for d in &e.decls {
        writeln!(decls, "{d}").unwrap();
    }

    // ---------- the text ----------
    let mut text = decls;
    let mut names: BTreeSet<String> = BTreeSet::new();
    for a in &axs {
        assert!(names.insert(a.name.clone()), "duplicate axiom {}", a.name);
        a.smt(&mut text);
    }
    text.push_str(&book);
    for g in &ground {
        writeln!(text, "(assert {g})").unwrap();
    }
    text.push_str(&obs_text);
    let root_term = e.terms.rel_smt(root);
    // The probe's subterms enter the e-graph once, here (§6.5).
    writeln!(text, "(assert (>= (card {root_term}) 0))").unwrap();
    // Each relation's definition, before the axioms: macros, which name
    // the terms the text refers to.
    let defs = e.terms.definitions();
    e.terms.short.set(false);
    e.terms.named.borrow_mut().clear();
    let at = text.find("(assert ").unwrap_or(text.len());
    text.insert_str(at, &defs);
    rels.sort();
    let stats = Stats {
        relations: rels.len(),
        predicates: literals.len(),
        families: fams.len(),
        colsets: sets.len(),
        axioms: axs.len(),
        bytes: text.len(),
    };
    let assertions = text.matches("(assert ").count();
    Program { text, tracked, root: root_term, stats, assertions }
}

fn fact_rels(f: &Fact) -> Vec<RelId> {
    match f {
        Fact::Card(r, _) | Fact::KeyRange(r, ..) | Fact::KeyCount(r, ..) => vec![*r],
    }
}

/// A real literal.
fn real(n: i128) -> String {
    if n < 0 { format!("(- {}.0)", n.unsigned_abs()) } else { format!("{n}.0") }
}

fn ratio(n: i128, d: i128) -> String {
    if d == 1 { real(n) } else { format!("(/ {} {}.0)", real(n), d) }
}

/// The alias a column carries (`c#i`), if any.
fn alias_of(c: &str) -> Option<u32> {
    let (_, i) = c.rsplit_once('#')?;
    i.parse().ok()
}

fn aliased_scan(t: &str, i: u32) -> String {
    let s = format!("(scan |t:{}|)", sanitize(t));
    if i == 0 { s } else { format!("(alias {i} {s})") }
}

/// Whether family `f` pairs `T.A` with `U.B` column for column, through
/// aliases: the aliases of `T` and `U`.
fn fk_match(f: &super::terms::Family, t: &str, a: &[String], u: &str, b: &[String]) -> Option<(u32, u32)> {
    let split = |c: &str| -> (String, u32) {
        match alias_of(c) {
            Some(i) => (unalias_col(c, i).unwrap(), i),
            None => (c.to_string(), 0),
        }
    };
    let mut ti = None;
    let mut ui = None;
    let mut want: BTreeSet<(String, String)> = a.iter().zip(b).map(|(x, y)| (format!("{t}.{x}"), format!("{u}.{y}"))).collect();
    for (l, r) in &f.pairs {
        let ((lc, li), (rc, ri)) = (split(l), split(r));
        if *ti.get_or_insert(li) != li || *ui.get_or_insert(ri) != ri {
            return None;
        }
        if !want.remove(&(lc, rc)) {
            return None;
        }
    }
    if !want.is_empty() {
        return None;
    }
    Some((ti?, ui?))
}

/// A predicate with its columns renamed, if it is a literal.
fn rename_pred(terms: &mut Terms, p: PredId, f: &dyn Fn(&str) -> Col) -> Option<PredId> {
    let e = preds::expr_of(terms, p)?;
    let e = e.rename(f).nnf(false).sorted();
    let q = preds::make(terms, &e);
    (q != p).then_some(q)
}

/// A predicate with expression column `g` replaced by its expression.
fn substitute_pred(terms: &mut Terms, p: PredId, g: &str, def: &E) -> Option<PredId> {
    let e = preds::expr_of(terms, p)?;
    let e = e.map_cols(&|c, t| if c == g { def.clone() } else { E::Col(c.to_string(), t) }).nnf(false).sorted();
    let q = preds::make(terms, &e);
    (q != p).then_some(q)
}

struct Emit<'a> {
    terms: &'a mut Terms,
    out: String,
    axioms: usize,
    /// Column sets mentioned.
    colsets: BTreeSet<ColsId>,
    decls: BTreeSet<String>,
}

impl Emit<'_> {
    fn set(&mut self, cs: BTreeSet<Col>) -> String {
        let id = self.terms.colset(cs);
        self.colsets.insert(id);
        self.terms.cols_sym(id)
    }

    fn one(&mut self, c: &str) -> String {
        self.set([c.to_string()].into())
    }

    fn cols(&mut self, id: ColsId) -> String {
        self.colsets.insert(id);
        self.terms.cols_sym(id)
    }

    fn fam(&self, f: FamId) -> Fam {
        let fam = &self.terms.families[f.0 as usize];
        let sym = |cs: BTreeSet<Col>| {
            let id = self.terms.find_colset(&cs).expect("family keys are column sets");
            self.terms.cols_sym(id)
        };
        let m = self.terms.mirror(f);
        Fam {
            tag: self.terms.fam_tag(f),
            j: self.terms.fam_fn(f, JoinKind::Inner),
            lj: self.terms.fam_fn(f, JoinKind::Left),
            s: self.terms.fam_fn(f, JoinKind::Semi),
            a: self.terms.fam_fn(f, JoinKind::Anti),
            m: self.terms.fam_fn(m, JoinKind::Inner),
            kl: sym(fam.left()),
            kr: sym(fam.right()),
            pairs: fam.pairs.iter().map(|(l, r)| (sym([l.clone()].into()), sym([r.clone()].into()))).collect(),
            null_eq: fam.null_eq,
            residual: None,
        }
    }
}

/// What families need beyond the table: NOT IN, full joins, and cross
/// joins.
fn family_extra(e: &Emit, f: FamId, fam: &Fam) -> Vec<Axiom> {
    let ni = e.terms.fam_fn(f, JoinKind::NotIn);
    let fj = e.terms.fam_fn(f, JoinKind::Full);
    let ma = e.terms.fam_fn(e.terms.mirror(f), JoinKind::Anti);
    let (a, j, s, kl, kr, tag) = (&fam.a, &fam.j, &fam.s, &fam.kl, &fam.kr, &fam.tag);
    let mut out = vec![
        ax(
            format!("full_basic{tag}"),
            "(x Rel) (y Rel)",
            &format!(
                "(and (= (cols ({fj} x y)) (jcup (cols x) (cols y)))
                      (= (card ({fj} x y)) (+ (card ({j} x y)) (card ({a} x y)) (card ({ma} y x)))))"
            ),
            &[&format!("({fj} x y)")],
        ),
        ax(
            format!("full_vals{tag}"),
            "(x Rel) (y Rel) (W Cols)",
            &format!(
                "(and (=> (csub W (cols x)) (<= (ndv ({fj} x y) W) (+ (ndv x W) 1)))
                      (=> (csub W (cols y)) (<= (ndv ({fj} x y) W) (+ (ndv y W) 1))))"
            ),
            &[&format!("(ndv ({fj} x y) W)")],
        ),
    ];
    out.push(ax(
        format!("notin_basic{tag}"),
        "(x Rel) (y Rel)",
        &format!(
            "(and (sub ({ni} x y) ({a} x y)) (= (cols ({ni} x y)) (cols x))
                  (=> (and (nonnull x {kl}) (nonnull y {kr})) (= ({ni} x y) ({a} x y))))"
        ),
        &[&format!("({ni} x y)")],
    ));
    let family = &e.terms.families[f.0 as usize];
    if family.pairs.is_empty() && family.residual.is_none() {
        out.push(ax(
            format!("cross{tag}"),
            "(x Rel) (y Rel)",
            &format!(
                "(and (= (card ({j} x y)) (* (card x) (card y)))
                      (= (card ({s} x y)) (ite (>= (card y) 1) (card x) 0)))"
            ),
            &[&format!("({j} x y)"), &format!("({s} x y)")],
        ));
    }
    out
}

/// The axiom stating what literal `p` keeps: its columns' ranges, and
/// which are non-NULL (§7.3).
fn range_axiom(e: &mut Emit, p: PredId, d: &Decided) -> Option<Axiom> {
    let f = d.facts.get(&p)?;
    let ps = e.terms.pred_smt(p);
    let s = format!("(filter {ps} x)");
    let mut parts = vec![];
    for c in &f.nonnull {
        let cs = e.one(c);
        parts.push(format!("(nonnull {s} {cs})"));
    }
    for (c, h) in &f.hull {
        let cs = e.one(c);
        match h.lo {
            Some(((n, dd), strict)) => {
                let op = if strict { ">" } else { ">=" };
                parts.push(format!("({op} (min {s} {cs}) {})", ratio(n, dd)));
            }
            None => parts.push(format!("(>= (min {s} {cs}) (min x {cs}))")),
        }
        match h.hi {
            Some(((n, dd), strict)) => {
                let op = if strict { "<" } else { "<=" };
                parts.push(format!("({op} (max {s} {cs}) {})", ratio(n, dd)));
            }
            None => parts.push(format!("(<= (max {s} {cs}) (max x {cs}))")),
        }
    }
    if parts.is_empty() {
        return None;
    }
    Some(ax(format!("range[{}]", e.terms.pred_text(p)), "(x Rel)", &format!("(and {})", parts.join(" ")), &[&s]))
}

/// `dom[g]` (§7.6): what expression column `g`'s values are, from the
/// expression alone.
fn expr_axioms(e: &mut Emit, g: &str, tables: &Tables, decided: &Decided) -> Vec<Axiom> {
    let def = e.terms.exprs[g].clone();
    let gs = e.one(g);
    let t = format!("(extend {gs} x)");
    let mut parts = vec![];
    if let Some(p) = date_part_axioms(e, &def, &gs, &t, tables, decided) {
        parts.push(p);
    }
    let ty = def.ty();
    let inputs = def.reads();
    if ty.numeric() {
        let mut smt = Smt::default();
        if let Some(v) = smt.value(&def) {
            let decls = smt.declarations();
            let known = format!("(not {})", v.null);
            let lo = optimum_of(&decls, &known, &v.v, false);
            let hi = optimum_of(&decls, &known, &v.v, true);
            if let Some((n, d)) = lo {
                parts.push(format!("(>= (min {t} {gs}) {})", ratio(n, d)));
            }
            if let Some((n, d)) = hi {
                parts.push(format!("(<= (max {t} {gs}) {})", ratio(n, d)));
            }
            // How many values, when few.
            if ty == Ty::Int
                && let (Some((a, 1)), Some((b, 1))) = (lo, hi)
                && b - a < 64
            {
                let k = b - a + 1;
                parts.push(format!("(<= (ndv {t} {gs}) {})", k + 1));
                parts.push(format!("(=> (nonnull {t} {gs}) (<= (ndv {t} {gs}) {k}))"));
            }
            // Total: non-NULL wherever its inputs are.
            let total = !matches!(v.null.as_str(), "true") && !def_has_func(&def);
            if total && !inputs.is_empty() {
                let all: Vec<String> = inputs.iter().map(|c| format!("(nonnull x {})", e.one(c))).collect();
                parts.push(format!("(=> (and {}) (nonnull {t} {gs}))", all.join(" ")));
            }
            // Affine in one column: its range is the column's, mapped.
            if let Some((a, c, d)) = affine(&def) {
                let cs = e.one(&a);
                let (mn, mx) = if c > 0 { ("min", "max") } else { ("max", "min") };
                parts.push(format!(
                    "(=> (and (>= (card x) 1) (nonnull x {cs}))
                         (and (= (min {t} {gs}) (+ (* {} ({mn} x {cs})) {})) (= (max {t} {gs}) (+ (* {} ({mx} x {cs})) {}))))",
                    real(c),
                    real(d),
                    real(c),
                    real(d)
                ));
            }
        }
    }
    if parts.is_empty() {
        return vec![];
    }
    vec![ax(format!("dom[{}]", sanitize(g)), "(x Rel)", &format!("(and {})", parts.join(" ")), &[&t])]
}

fn def_has_func(e: &E) -> bool {
    let mut found = false;
    e.visit(&mut |x| {
        if let E::Func(..) | E::Arith(Arith::Div | Arith::Mod, ..) = x {
            // Division by a nonzero constant is total; the SMT already
            // refused any other.
            if let E::Func(..) = x {
                found = true;
            }
        }
    });
    found
}

/// `e` as `c·a + d` for integers `c ≠ 0`, `d`.
fn affine(e: &E) -> Option<(Col, i128, i128)> {
    fn go(e: &E) -> Option<(Option<Col>, i128, i128)> {
        Some(match e {
            E::Col(c, Ty::Int) => (Some(c.clone()), 1, 0),
            E::Lit(Lit::Int(n), _) => (None, 0, *n),
            E::Neg(a) => {
                let (c, k, d) = go(a)?;
                (c, -k, -d)
            }
            E::Arith(Arith::Add | Arith::Sub, a, b, Ty::Int) => {
                let (ca, ka, da) = go(a)?;
                let (cb, kb, db) = go(b)?;
                let s = if matches!(e, E::Arith(Arith::Sub, ..)) { -1 } else { 1 };
                let c = match (ca, cb) {
                    (Some(x), Some(y)) if x == y => Some(x),
                    (Some(x), None) | (None, Some(x)) => Some(x),
                    (None, None) => None,
                    _ => return None,
                };
                (c, ka + s * kb, da + s * db)
            }
            E::Arith(Arith::Mul, a, b, Ty::Int) => {
                let (ca, ka, da) = go(a)?;
                let (cb, kb, db) = go(b)?;
                match (ca, cb) {
                    (None, c) => (c, da * kb, da * db),
                    (c, None) => (c, ka * db, da * db),
                    _ => return None,
                }
            }
            _ => return None,
        })
    }
    let (c, k, d) = go(e)?;
    (k != 0).then_some((c?, k, d))
}

/// The least (or greatest) value of `v` where `cond` holds.
fn optimum_of(decls: &str, cond: &str, v: &str, max: bool) -> Option<(i128, i128)> {
    let o = z3::Optimize::new();
    let mut p = z3::Params::new();
    p.set_u32("timeout", 2_000);
    o.set_params(&p);
    let goal = if max { "maximize" } else { "minimize" };
    o.from_string(format!("{decls}(assert {cond})\n({goal} {v})"));
    if o.check(&[]) != z3::SatResult::Sat {
        return None;
    }
    let b = if max { o.get_upper(0)? } else { o.get_lower(0)? };
    let text = b.to_string();
    if text.contains("oo") || text.contains("epsilon") {
        return None;
    }
    preds::parse_number(&text)
}

/// `agg[c]` (§7.7): an aggregate column's values, from its input's.
fn agg_axioms(e: &mut Emit, c: &str) -> Vec<Axiom> {
    let Some(a) = e.terms.aggs.get(c).cloned() else { return vec![] };
    let cs = e.one(c);
    let arg = match &a.arg {
        Some(E::Col(x, _)) => Some(e.one(x)),
        _ => None,
    };
    let mut out = vec![];
    for (kind, r, vars) in [
        ("agg", "(aggregate K G x)", "(K Cols) (G Cols) (x Rel)"),
        ("scalar", "(scalar G x)", "(G Cols) (x Rel)"),
    ] {
        let scalar = kind == "scalar";
        let body = match (a.func.as_str(), &arg, a.distinct) {
            ("count", None, _) if scalar => {
                format!("(and (nonnull {r} {cs}) (= (min {r} {cs}) (to_real (card x))) (= (max {r} {cs}) (to_real (card x))))")
            }
            ("count", None, _) => {
                format!("(and (nonnull {r} {cs}) (>= (min {r} {cs}) 1.0) (<= (max {r} {cs}) (to_real (card x))))")
            }
            ("count", Some(_), _) | ("count", None, true) => {
                format!("(and (nonnull {r} {cs}) (>= (min {r} {cs}) 0.0) (<= (max {r} {cs}) (to_real (card x))))")
            }
            ("min", Some(x), _) => format!(
                "(and (= (min {r} {cs}) (min x {x})) (<= (max {r} {cs}) (max x {x})) (<= (ndv {r} {cs}) (+ (ndv x {x}) 1)))"
            ),
            ("max", Some(x), _) => format!(
                "(and (= (max {r} {cs}) (max x {x})) (>= (min {r} {cs}) (min x {x})) (<= (ndv {r} {cs}) (+ (ndv x {x}) 1)))"
            ),
            ("avg", Some(x), _) => format!("(and (>= (min {r} {cs}) (min x {x})) (<= (max {r} {cs}) (max x {x})))"),
            _ => continue,
        };
        out.push(ax(
            format!("{kind}[{}]", sanitize(c)),
            vars,
            &format!("(=> (csub {cs} G) {body})"),
            &[r],
        ));
    }
    out
}

/// `having_count` (§7.7): groups with at least `lo` rows each number at
/// most `card x / lo`.
fn having_axioms(e: &mut Emit, d: &Decided, aggs: &BTreeSet<Col>) -> Vec<Axiom> {
    let mut out = vec![];
    for (p, f) in &d.facts {
        for (c, h) in &f.hull {
            if !aggs.contains(c) {
                continue;
            }
            let Some(a) = e.terms.aggs.get(c) else { continue };
            if a.func != "count" {
                continue;
            }
            let Some(((n, dd), strict)) = h.lo else { continue };
            // The least integer allowed.
            let lo = if dd == 1 { if strict { n + 1 } else { n } } else { n.div_euclid(dd) + 1 };
            if lo < 2 {
                continue;
            }
            let ps = e.terms.pred_smt(*p);
            let cs = e.one(c);
            out.push(ax(
                format!("having_count[{}]", e.terms.pred_text(*p)),
                "(K Cols) (G Cols) (x Rel)",
                &format!("(=> (csub {cs} G) (<= (* {lo} (card (filter {ps} (aggregate K G x)))) (card x)))"),
                &[&format!("(filter {ps} (aggregate K G x))")],
            ));
        }
    }
    out
}

/// The column-set universe: every set mentioned and the tables' columns,
/// their alias images, then (to a cap) unions of small sets that fit in
/// some relation, and differences. Also returns the tables' sets.
fn universe(
    e: &mut Emit,
    relations: &BTreeSet<ColsId>,
    tables: &BTreeSet<ColsId>,
    aliases: &BTreeSet<u32>,
) -> (Vec<ColsId>, BTreeSet<ColsId>) {
    let table_sets: BTreeSet<BTreeSet<Col>> = tables.iter().map(|c| e.terms.cols[c.0 as usize].clone()).collect();
    let mut all: BTreeSet<BTreeSet<Col>> = e.colsets.iter().map(|c| e.terms.cols[c.0 as usize].clone()).collect();
    let exprs: Vec<(Col, E)> = e.terms.exprs.iter().map(|(c, x)| (c.clone(), x.clone())).collect();
    for (_, x) in &exprs {
        all.insert(x.reads());
    }
    let mut tabs = table_sets.clone();
    for i in aliases {
        for s in all.clone() {
            let u: BTreeSet<Col> = s.iter().filter_map(|c| unalias_col(c, *i)).collect();
            if table_sets.contains(&u) {
                tabs.insert(u.clone());
            }
            if !u.is_empty() {
                all.insert(u);
            }
            // Aliases are of scans: a set already aliased has no aliased
            // form (else each alias doubles the sets: `t.c#2#3`, ...).
            if s.iter().any(|c| alias_of(c).is_some()) {
                continue;
            }
            let a: BTreeSet<Col> = s.iter().map(|c| alias_col(c, *i)).collect();
            if table_sets.contains(&s) {
                tabs.insert(a.clone());
            }
            all.insert(a);
        }
    }
    let _ = relations;
    // Splits of each small set, which `ndv_product`, `csub_split` and
    // `nonnull_split` decompose it into: every part of a set of at most
    // `MAX_SMALL` columns, else each column and the rest.
    let small: Vec<BTreeSet<Col>> = all.iter().filter(|s| !tabs.contains(*s) && s.len() >= 2).cloned().collect();
    for w in small {
        if all.len() >= MAX_COLSETS {
            break;
        }
        let cols: Vec<&Col> = w.iter().collect();
        if cols.len() <= MAX_SMALL {
            for mask in 1..(1u32 << cols.len()) - 1 {
                all.insert(cols.iter().enumerate().filter(|(i, _)| mask & (1 << i) != 0).map(|(_, c)| (*c).clone()).collect());
            }
        } else {
            for c in &cols {
                all.insert([(*c).clone()].into());
                all.insert(w.iter().filter(|x| x != c).cloned().collect());
            }
        }
    }
    let mut out: Vec<ColsId> = all.iter().map(|s| e.terms.colset(s.clone())).collect();
    out.sort_by_key(|c| (e.terms.cols[c.0 as usize].len(), *c));
    let tabs: BTreeSet<ColsId> = tabs.into_iter().map(|s| e.terms.colset(s)).collect();
    (out, tabs)
}

/// What `date_part(part, d)` of a date column `d` says (§7.6, `dom[g]`):
/// a fixed range for a part of a year or day, and for the year, which
/// side of each New Year near the predicates' dates the values lie on.
fn date_part_axioms(e: &mut Emit, def: &E, gs: &str, t: &str, tables: &Tables, decided: &Decided) -> Option<String> {
    let E::Func(name, args, _) = def else { return None };
    let [E::Lit(Lit::Str(part), _), E::Col(d, _)] = args.as_slice() else { return None };
    if name != "date_part" {
        return None;
    }
    // A date column (days), not a timestamp.
    let base = match alias_of(d) {
        Some(i) => unalias_col(d, i).unwrap(),
        None => d.clone(),
    };
    let (table, column) = base.split_once('.')?;
    let ty = tables.catalog.tables.get(table)?.field_with_name(column).ok()?.data_type().clone();
    if ty != datafusion::arrow::datatypes::DataType::Date32 {
        return None;
    }
    let ds = e.one(d);
    let total = format!("(=> (nonnull x {ds}) (nonnull {t} {gs}))");
    let fixed = match part.to_lowercase().as_str() {
        "month" => Some((1, 12)),
        "quarter" => Some((1, 4)),
        "day" => Some((1, 31)),
        "dow" => Some((0, 6)),
        "isodow" => Some((1, 7)),
        "doy" => Some((1, 366)),
        "week" => Some((1, 53)),
        _ => None,
    };
    if let Some((lo, hi)) = fixed {
        return Some(format!(
            "(and {total} (>= (min {t} {gs}) {}) (<= (max {t} {gs}) {}))",
            real(lo),
            real(hi)
        ));
    }
    if part.to_lowercase() != "year" {
        return None;
    }
    // New Years around every date a predicate bounds the column by.
    let mut years: BTreeSet<i128> = BTreeSet::new();
    for f in decided.facts.values() {
        for (c, h) in &f.hull {
            if *c != *d && *c != base {
                continue;
            }
            for ((n, den), _) in [h.lo, h.hi].into_iter().flatten() {
                let y = year_of(n.div_euclid(den));
                years.extend([y, y + 1]);
            }
        }
    }
    let mut out = vec![total];
    for y in years {
        let b = days_of(y);
        out.push(format!("(=> (< (max x {ds}) {}) (< (max {t} {gs}) {}))", real(b), real(y)));
        out.push(format!("(=> (>= (min x {ds}) {}) (>= (min {t} {gs}) {}))", real(b), real(y)));
    }
    Some(format!("(and {})", out.join(" ")))
}

/// The year of day `z` since 1970-01-01 (Hinnant's civil-from-days).
fn year_of(z: i128) -> i128 {
    let z = z + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    if m <= 2 { y + 1 } else { y }
}

/// The day since 1970-01-01 of January 1 of year `y`.
fn days_of(y: i128) -> i128 {
    let y = y - 1;
    let era = y.div_euclid(400);
    let yoe = y - era * 400;
    let doy = 306;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146_097 + doe - 719_468
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn calendar() {
        assert_eq!(days_of(1970), 0);
        assert_eq!(days_of(1995), 9131);
        assert_eq!(year_of(9131), 1995);
        assert_eq!(year_of(9130), 1994);
        assert_eq!(year_of(days_of(2000) + 365), 2000);
    }
}
