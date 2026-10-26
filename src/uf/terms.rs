//! Terms (§4, §5): relations, predicates, column sets and join families,
//! hash-consed, so that the same subplan is always the same term.

use std::collections::{BTreeSet, HashMap};
use std::fmt::Write as _;

use super::expr::{Col, E, Lit, Ty};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct RelId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct PredId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct ColsId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct FamId(pub u32);

/// The kinds of join a family has a function for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum JoinKind {
    Inner,
    Left,
    Semi,
    Anti,
    /// `x.L NOT IN (SELECT R FROM y)`: the anti join's rows, but none at all
    /// where `y` has a NULL key, and none with a NULL key of their own.
    NotIn,
    /// The full outer join: the inner join's rows, and each side's rows
    /// without a partner, padded.
    Full,
}

impl JoinKind {
    pub(crate) fn name(self) -> &'static str {
        match self {
            JoinKind::Inner => "join",
            JoinKind::Left => "ljoin",
            JoinKind::Semi => "semi",
            JoinKind::Anti => "anti",
            JoinKind::NotIn => "notin",
            JoinKind::Full => "fjoin",
        }
    }
}

/// A family of joins sharing one key pairing (§4): `pairs` of a left and
/// a right column, sorted. `null_eq` families match NULL keys with each
/// other (`IS NOT DISTINCT FROM`). A family with a `residual` joins only
/// pairs that also satisfy it, a predicate over both sides' columns.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct Family {
    pub pairs: Vec<(Col, Col)>,
    pub null_eq: bool,
    pub residual: Option<PredId>,
}

impl Family {
    pub(crate) fn left(&self) -> BTreeSet<Col> {
        self.pairs.iter().map(|(a, _)| a.clone()).collect()
    }

    pub(crate) fn right(&self) -> BTreeSet<Col> {
        self.pairs.iter().map(|(_, b)| b.clone()).collect()
    }

    pub(crate) fn mirrored(&self) -> Family {
        let mut pairs: Vec<(Col, Col)> = self.pairs.iter().map(|(a, b)| (b.clone(), a.clone())).collect();
        pairs.sort();
        Family { pairs, null_eq: self.null_eq, residual: self.residual }
    }
}

/// A relation term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Rel {
    Scan(String),
    Filter(PredId, RelId),
    Group(ColsId, RelId),
    Limit(u64, RelId),
    Union(RelId, RelId),
    Join(JoinKind, FamId, RelId, RelId),
    /// Some sub-bag of the input, chosen by occurrence `o` (§3 rule 9).
    Part(String, RelId),
    /// The input's rows satisfying the predicate, and maybe others.
    Opt(String, PredId, RelId),
    /// The probe side `x` after a lossless runtime filter from build side
    /// `b`, of the family the join that built it has.
    Rt(FamId, String, RelId, RelId),
    Extend(Col, RelId),
    Aggregate(ColsId, ColsId, RelId),
    Scalar(ColsId, RelId),
    Alias(u32, RelId),
    /// A relation nothing models: `|r:q#n|`.
    Opaque(String),
}

/// A predicate term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Pred {
    /// `col op lit`, with op `>`, `>=` or `=`: always the positive form.
    Atom { col: Col, op: AtomOp, lit: Lit, ty: Ty },
    Neg(PredId),
    /// A predicate that is not an atom, by its canonical text.
    Compound(String, E),
    True,
    False,
    /// `A op (y)` for an uncorrelated scalar subquery `y` with output `G`.
    Cmp { op: CmpOp, a: Col, y: RelId, g: Col },
    /// A predicate nothing models: `|p:q#n|`, with the columns it reads if
    /// known.
    Opaque(String, Option<BTreeSet<Col>>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum AtomOp {
    Gt,
    Ge,
    Eq,
}

impl AtomOp {
    pub(crate) fn text(self) -> &'static str {
        match self {
            AtomOp::Gt => ">",
            AtomOp::Ge => ">=",
            AtomOp::Eq => "=",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum CmpOp {
    Gt,
    Ge,
    Lt,
    Le,
    Eq,
}

impl CmpOp {
    pub(crate) fn name(self) -> &'static str {
        match self {
            CmpOp::Gt => "cmp_gt",
            CmpOp::Ge => "cmp_ge",
            CmpOp::Lt => "cmp_lt",
            CmpOp::Le => "cmp_le",
            CmpOp::Eq => "cmp_eq",
        }
    }
}

/// Every term made so far.
#[derive(Default, Clone)]
pub(crate) struct Terms {
    pub rels: Vec<Rel>,
    rel_ids: HashMap<Rel, RelId>,
    pub preds: Vec<Pred>,
    pred_ids: HashMap<Pred, PredId>,
    compound_ids: HashMap<String, PredId>,
    pub cols: Vec<BTreeSet<Col>>,
    cols_ids: HashMap<BTreeSet<Col>, ColsId>,
    pub families: Vec<Family>,
    fam_ids: HashMap<Family, FamId>,
    /// Each relation's columns, where known.
    pub rel_cols: Vec<Option<ColsId>>,
    /// Each column's type, where known.
    pub types: HashMap<Col, Ty>,
    /// Each expression column's expression.
    pub exprs: std::collections::BTreeMap<Col, E>,
    /// Each aggregate column's definition.
    pub aggs: std::collections::BTreeMap<Col, super::translate::Agg>,
}

impl Terms {
    pub(crate) fn rel(&mut self, r: Rel) -> RelId {
        if let Some(id) = self.rel_ids.get(&r) {
            return *id;
        }
        let id = RelId(self.rels.len() as u32);
        let cols = self.columns_of(&r);
        self.rels.push(r.clone());
        self.rel_cols.push(cols);
        self.rel_ids.insert(r, id);
        id
    }

    pub(crate) fn pred(&mut self, p: Pred) -> PredId {
        // `neg (neg p)` is `p`.
        if let Pred::Neg(q) = &p
            && let Pred::Neg(r) = &self.preds[q.0 as usize]
        {
            return *r;
        }
        if let Some(id) = self.pred_ids.get(&p) {
            return *id;
        }
        // A compound predicate is its text: two readings of one predicate
        // may type its columns differently.
        if let Pred::Compound(t, _) = &p
            && let Some(id) = self.compound_ids.get(t)
        {
            return *id;
        }
        let id = PredId(self.preds.len() as u32);
        if let Pred::Compound(t, _) = &p {
            self.compound_ids.insert(t.clone(), id);
        }
        self.preds.push(p.clone());
        self.pred_ids.insert(p, id);
        id
    }

    pub(crate) fn colset(&mut self, cs: BTreeSet<Col>) -> ColsId {
        if let Some(id) = self.cols_ids.get(&cs) {
            return *id;
        }
        let id = ColsId(self.cols.len() as u32);
        self.cols.push(cs.clone());
        self.cols_ids.insert(cs, id);
        id
    }

    pub(crate) fn find_colset(&self, cs: &BTreeSet<Col>) -> Option<ColsId> {
        self.cols_ids.get(cs).copied()
    }

    pub(crate) fn one(&mut self, c: &str) -> ColsId {
        self.colset([c.to_string()].into())
    }

    pub(crate) fn family(&mut self, f: Family) -> FamId {
        if let Some(id) = self.fam_ids.get(&f) {
            return *id;
        }
        let id = FamId(self.families.len() as u32);
        self.families.push(f.clone());
        self.fam_ids.insert(f.clone(), id);
        // Every family has a mirror (§4).
        let m = f.mirrored();
        if !self.fam_ids.contains_key(&m) {
            let mid = FamId(self.families.len() as u32);
            self.families.push(m.clone());
            self.fam_ids.insert(m, mid);
        }
        for (a, b) in &f.pairs {
            self.colset([a.clone()].into());
            self.colset([b.clone()].into());
        }
        self.colset(f.left());
        self.colset(f.right());
        id
    }

    pub(crate) fn mirror(&self, f: FamId) -> FamId {
        self.fam_ids[&self.families[f.0 as usize].mirrored()]
    }

    pub(crate) fn get(&self, r: RelId) -> &Rel {
        &self.rels[r.0 as usize]
    }

    pub(crate) fn get_pred(&self, p: PredId) -> &Pred {
        &self.preds[p.0 as usize]
    }

    pub(crate) fn cols_of(&self, r: RelId) -> Option<&BTreeSet<Col>> {
        self.rel_cols[r.0 as usize].map(|c| &self.cols[c.0 as usize])
    }

    /// A relation's columns, from its inputs' (§3).
    fn columns_of(&mut self, r: &Rel) -> Option<ColsId> {
        let of = |t: &Terms, x: &RelId| t.rel_cols[x.0 as usize];
        match r {
            Rel::Scan(_) | Rel::Opaque(_) => None,
            Rel::Filter(_, x) | Rel::Limit(_, x) | Rel::Part(_, x) | Rel::Opt(_, _, x) | Rel::Rt(_, _, x, _) => of(self, x),
            Rel::Group(k, _) => Some(*k),
            Rel::Union(x, _) => of(self, x),
            Rel::Join(JoinKind::Semi | JoinKind::Anti | JoinKind::NotIn, _, x, _) => of(self, x),
            Rel::Join(_, _, x, y) => {
                let (a, b) = (of(self, x)?, of(self, y)?);
                let u: BTreeSet<Col> = self.cols[a.0 as usize].union(&self.cols[b.0 as usize]).cloned().collect();
                Some(self.colset(u))
            }
            Rel::Extend(g, x) => {
                let mut u = self.cols[of(self, x)?.0 as usize].clone();
                u.insert(g.clone());
                Some(self.colset(u))
            }
            Rel::Aggregate(k, g, _) => {
                let u: BTreeSet<Col> = self.cols[k.0 as usize].union(&self.cols[g.0 as usize]).cloned().collect();
                Some(self.colset(u))
            }
            Rel::Scalar(g, _) => Some(*g),
            Rel::Alias(i, x) => {
                let cs = self.cols[of(self, x)?.0 as usize].iter().map(|c| alias_col(c, *i)).collect();
                Some(self.colset(cs))
            }
        }
    }

    /// Sets a scan's (or opaque relation's) columns.
    pub(crate) fn set_cols(&mut self, r: RelId, cs: BTreeSet<Col>) {
        let id = self.colset(cs);
        self.rel_cols[r.0 as usize] = Some(id);
    }

    /// The columns predicate `p` reads, if known.
    pub(crate) fn reads(&self, p: PredId) -> Option<BTreeSet<Col>> {
        match self.get_pred(p) {
            Pred::Atom { col, .. } => Some([col.clone()].into()),
            Pred::Neg(q) => self.reads(*q),
            Pred::Compound(_, e) => Some(e.reads()),
            Pred::True | Pred::False => Some(BTreeSet::new()),
            Pred::Cmp { a, .. } => Some([a.clone()].into()),
            Pred::Opaque(_, r) => r.clone(),
        }
    }

    // ---------- SMT text ----------

    pub(crate) fn cols_sym(&self, c: ColsId) -> String {
        cols_name(&self.cols[c.0 as usize], c)
    }

    pub(crate) fn fam_fn(&self, f: FamId, kind: JoinKind) -> String {
        format!("|{}{}|", kind.name(), self.fam_tag(f))
    }

    pub(crate) fn rt_fn(&self, f: FamId) -> String {
        format!("|rt{}|", self.fam_tag(f))
    }

    /// `[l1,l2=r1,r2]`, with `≡` for a NULL-matching family and the
    /// residual's id.
    pub(crate) fn fam_tag(&self, f: FamId) -> String {
        let fam = &self.families[f.0 as usize];
        let l: Vec<&str> = fam.pairs.iter().map(|(a, _)| a.as_str()).collect();
        let r: Vec<&str> = fam.pairs.iter().map(|(_, b)| b.as_str()).collect();
        let eq = if fam.null_eq { "≡" } else { "=" };
        let res = fam.residual.map(|p| format!(";{}", self.pred_text(p))).unwrap_or_default();
        sanitize(&format!("[{}{eq}{}{res}]", l.join(","), r.join(",")))
    }

    pub(crate) fn pred_text(&self, p: PredId) -> String {
        match self.get_pred(p) {
            Pred::Atom { col, op, lit, .. } => format!("{col}{}{}", op.text(), lit.text()),
            Pred::Neg(q) => format!("NOT {}", self.pred_text(*q)),
            Pred::Compound(t, _) => t.clone(),
            Pred::True => "true".into(),
            Pred::False => "false".into(),
            Pred::Cmp { op, a, g, .. } => format!("{}({a},{g})", op.name()),
            Pred::Opaque(n, _) => n.clone(),
        }
    }

    pub(crate) fn pred_smt(&self, p: PredId) -> String {
        match self.get_pred(p) {
            Pred::Neg(q) => format!("(neg {})", self.pred_smt(*q)),
            Pred::Cmp { op, a, y, g } => {
                let (a, g) = (self.find_colset(&[a.clone()].into()).unwrap(), self.find_colset(&[g.clone()].into()).unwrap());
                format!("({} {} {} {})", op.name(), self.cols_sym(a), self.rel_smt(*y), self.cols_sym(g))
            }
            _ => self.pred_const(p).unwrap(),
        }
    }

    /// The constant naming `p`, for a predicate that is one.
    pub(crate) fn pred_const(&self, p: PredId) -> Option<String> {
        Some(match self.get_pred(p) {
            Pred::Atom { .. } | Pred::Compound(..) => format!("|p:{}|", sanitize(&self.pred_text(p))),
            Pred::True => "|p:true|".into(),
            Pred::False => "|p:false|".into(),
            Pred::Opaque(n, _) => format!("|p:{}|", sanitize(n)),
            Pred::Neg(_) | Pred::Cmp { .. } => return None,
        })
    }

    pub(crate) fn rel_smt(&self, r: RelId) -> String {
        let mut out = String::new();
        self.write_rel(r, &mut out);
        out
    }

    fn write_rel(&self, r: RelId, out: &mut String) {
        let rec = |x: &RelId, out: &mut String| self.write_rel(*x, out);
        match self.get(r) {
            Rel::Scan(t) => write!(out, "(scan |t:{}|)", sanitize(t)).unwrap(),
            Rel::Filter(p, x) => {
                write!(out, "(filter {} ", self.pred_smt(*p)).unwrap();
                rec(x, out);
                out.push(')');
            }
            Rel::Group(k, x) => {
                write!(out, "(group {} ", self.cols_sym(*k)).unwrap();
                rec(x, out);
                out.push(')');
            }
            Rel::Limit(n, x) => {
                write!(out, "(limit {n} ").unwrap();
                rec(x, out);
                out.push(')');
            }
            Rel::Union(x, y) => {
                out.push_str("(union ");
                rec(x, out);
                out.push(' ');
                rec(y, out);
                out.push(')');
            }
            Rel::Join(k, f, x, y) => {
                write!(out, "({} ", self.fam_fn(*f, *k)).unwrap();
                rec(x, out);
                out.push(' ');
                rec(y, out);
                out.push(')');
            }
            Rel::Part(o, x) => {
                write!(out, "(part |o:{}| ", sanitize(o)).unwrap();
                rec(x, out);
                out.push(')');
            }
            Rel::Opt(o, p, x) => {
                write!(out, "(opt |o:{}| {} ", sanitize(o), self.pred_smt(*p)).unwrap();
                rec(x, out);
                out.push(')');
            }
            Rel::Rt(f, o, x, b) => {
                write!(out, "({} |o:{}| ", self.rt_fn(*f), sanitize(o)).unwrap();
                rec(x, out);
                out.push(' ');
                rec(b, out);
                out.push(')');
            }
            Rel::Extend(g, x) => {
                let id = self.find_colset(&[g.clone()].into()).unwrap();
                write!(out, "(extend {} ", self.cols_sym(id)).unwrap();
                rec(x, out);
                out.push(')');
            }
            Rel::Aggregate(k, g, x) => {
                write!(out, "(aggregate {} {} ", self.cols_sym(*k), self.cols_sym(*g)).unwrap();
                rec(x, out);
                out.push(')');
            }
            Rel::Scalar(g, x) => {
                write!(out, "(scalar {} ", self.cols_sym(*g)).unwrap();
                rec(x, out);
                out.push(')');
            }
            Rel::Alias(i, x) => {
                write!(out, "(alias {i} ").unwrap();
                rec(x, out);
                out.push(')');
            }
            Rel::Opaque(n) => write!(out, "|r:{}|", sanitize(n)).unwrap(),
        }
    }

    /// Every relation reachable from `roots`, children first.
    pub(crate) fn reachable(&self, roots: impl IntoIterator<Item = RelId>) -> Vec<RelId> {
        let mut seen = vec![false; self.rels.len()];
        let mut out = vec![];
        let mut stack: Vec<(RelId, bool)> = roots.into_iter().map(|r| (r, false)).collect();
        while let Some((r, done)) = stack.pop() {
            if done {
                out.push(r);
                continue;
            }
            if seen[r.0 as usize] {
                continue;
            }
            seen[r.0 as usize] = true;
            stack.push((r, true));
            for c in self.children(r) {
                stack.push((c, false));
            }
            for p in self.rel_preds(r) {
                if let Pred::Cmp { y, .. } = self.get_pred(p) {
                    stack.push((*y, false));
                }
            }
        }
        out
    }

    pub(crate) fn children(&self, r: RelId) -> Vec<RelId> {
        match self.get(r) {
            Rel::Scan(_) | Rel::Opaque(_) => vec![],
            Rel::Filter(_, x)
            | Rel::Group(_, x)
            | Rel::Limit(_, x)
            | Rel::Part(_, x)
            | Rel::Opt(_, _, x)
            | Rel::Extend(_, x)
            | Rel::Aggregate(_, _, x)
            | Rel::Scalar(_, x)
            | Rel::Alias(_, x) => vec![*x],
            Rel::Union(x, y) | Rel::Join(_, _, x, y) | Rel::Rt(_, _, x, y) => vec![*x, *y],
        }
    }

    /// The predicates relation `r` applies itself.
    pub(crate) fn rel_preds(&self, r: RelId) -> Vec<PredId> {
        let mut out = match self.get(r) {
            Rel::Filter(p, _) | Rel::Opt(_, p, _) => vec![*p],
            _ => vec![],
        };
        if let Rel::Join(_, f, ..) | Rel::Rt(f, ..) = self.get(r)
            && let Some(p) = self.families[f.0 as usize].residual
        {
            out.push(p);
        }
        let mut i = 0;
        while i < out.len() {
            if let Pred::Neg(q) = self.get_pred(out[i]) {
                out.push(*q);
            }
            i += 1;
        }
        out
    }
}

/// `c` renamed for alias `i`: `c#i`.
pub(crate) fn alias_col(c: &str, i: u32) -> Col {
    format!("{c}#{i}")
}

/// `c` without alias `i`'s suffix, if it has it.
pub(crate) fn unalias_col(c: &str, i: u32) -> Option<Col> {
    c.strip_suffix(&format!("#{i}")).map(str::to_string)
}

/// A column set's symbol: `|{a,b}|`, or by number when long.
pub(crate) fn cols_name(cs: &BTreeSet<Col>, id: ColsId) -> String {
    let text = cs.iter().map(String::as_str).collect::<Vec<_>>().join(",");
    if text.len() <= 80 { format!("|{{{}}}|", sanitize(&text)) } else { format!("|{{#{}:{}cols}}|", id.0, cs.len()) }
}

/// Text that may stand inside a quoted symbol: no `|` or `\`.
pub(crate) fn sanitize(s: &str) -> String {
    s.replace('|', "¦").replace('\\', "/")
}
