//! The axiom table (§7): each operator's semantics, stated once as a
//! quantified formula with explicit patterns.
//!
//! Every axiom is true of bags of rows in SQL's three-valued logic, with
//! any column possibly NULL (the spec's §3 assumes NOT NULL columns; this
//! table states where NULLs matter instead: `filter_complement` splits a
//! relation exactly only where `nonnull` holds of the predicate's columns,
//! and the per-predicate axioms state which columns a filter leaves
//! non-NULL).

use std::fmt::Write as _;

/// One quantified axiom.
pub(crate) struct Axiom {
    pub name: String,
    pub vars: String,
    pub body: String,
    /// Each a multi-pattern: its terms separated by spaces.
    pub patterns: Vec<String>,
}

impl Axiom {
    pub(crate) fn smt(&self, out: &mut String) {
        let name = format!("|{}|", self.name.replace('|', "¦"));
        if self.vars.is_empty() {
            writeln!(out, "(assert {})", self.body).unwrap();
            return;
        }
        write!(out, "(assert (forall ({}) (! {}", self.vars, self.body).unwrap();
        for p in &self.patterns {
            write!(out, " :pattern ({p})").unwrap();
        }
        writeln!(out, " :weight {} :qid {name})))", weight(&self.name)).unwrap();
    }
}

/// An axiom's weight, which Z3 adds to an instance's generation to rank
/// it: what states one operator's meaning goes first, what relates
/// operators (pushing a filter down, regrouping joins) next, and what
/// combines facts over many terms (containment chains, commuting and
/// complementing filters, FD chains, products) last. A check's budget
/// of instances is spent in that order.
fn weight(name: &str) -> u32 {
    let base = name.split(['[', '|']).next().unwrap_or(name);
    const LAST: &[&str] = &[
        "filter_commute",
        "filter_complement",
        "filter_incl_excl",
        "filter_mono",
        "sub_trans",
        "sub_min",
        "sub_max",
        "sub_ndv",
        "sub_fd",
        "sub_nonnull",
        "sub_key",
        "fd_trans",
        "fd_ndv",
        "ndv_product",
        "ndv_mono",
        "range_point",
        "range_order",
        "range_ndv",
        "one_row",
        "or_incl_excl",
        "and_lower",
        "dom_sub",
    ];
    const NEXT: &[&str] = &["assoc", "inner_mono", "semi_mono", "anti_mono", "left_mono", "group_mono", "extend_join", "rt_push"];
    if LAST.contains(&base) {
        8
    } else if NEXT.iter().any(|p| base.starts_with(p)) || base.ends_with("_push") || base.contains("push") {
        3
    } else {
        0
    }
}

pub(crate) fn ax(name: impl Into<String>, vars: &str, body: &str, patterns: &[&str]) -> Axiom {
    Axiom {
        name: name.into(),
        vars: vars.to_string(),
        body: body.split_whitespace().collect::<Vec<_>>().join(" "),
        patterns: patterns.iter().map(|p| p.to_string()).collect(),
    }
}

pub(crate) const DECLS: &str = "\
(declare-sort Rel 0) (declare-sort Pred 0) (declare-sort Cols 0) (declare-sort Table 0) (declare-sort Occ 0)
(declare-fun scan (Table) Rel)
(declare-fun filter (Pred Rel) Rel)
(declare-fun group (Cols Rel) Rel)
(declare-fun limit (Int Rel) Rel)
(declare-fun union (Rel Rel) Rel)
(declare-fun part (Occ Rel) Rel)
(declare-fun opt (Occ Pred Rel) Rel)
(declare-fun extend (Cols Rel) Rel)
(declare-fun aggregate (Cols Cols Rel) Rel)
(declare-fun scalar (Cols Rel) Rel)
(declare-fun alias (Int Rel) Rel)
(declare-fun cmp_gt (Cols Rel Cols) Pred)
(declare-fun cmp_ge (Cols Rel Cols) Pred)
(declare-fun cmp_lt (Cols Rel Cols) Pred)
(declare-fun cmp_le (Cols Rel Cols) Pred)
(declare-fun cmp_eq (Cols Rel Cols) Pred)
(declare-fun card (Rel) Int)
(declare-fun ndv (Rel Cols) Int)
(declare-fun cols (Rel) Cols)
(declare-fun sub (Rel Rel) Bool)
(declare-fun key (Rel Cols) Bool)
(declare-fun fd (Rel Cols Cols) Bool)
(declare-fun min (Rel Cols) Real)
(declare-fun max (Rel Cols) Real)
(declare-fun nonnull (Rel Cols) Bool)
(declare-fun intcol (Cols) Bool)
(declare-fun reads (Pred) Cols)
(declare-fun neg (Pred) Pred)
(declare-fun implies (Pred Pred) Bool)
(declare-fun point (Pred) Bool)
(declare-fun cup (Cols Cols) Cols)
(declare-fun jcup (Cols Cols) Cols)
(declare-fun cdiff (Cols Cols) Cols)
(declare-fun csub (Cols Cols) Bool)
(declare-fun orof (Pred Pred Pred) Bool)
(declare-fun andof (Pred Pred Pred) Bool)
(declare-fun width (Pred) Int)
(declare-fun dom (Rel Pred) Bool)
(declare-fun def (Cols) Cols)
(declare-fun acols (Int Cols) Cols)
(declare-fun ucols (Int Cols) Cols)
(declare-fun upred (Int Pred) Pred)
(declare-const |p:true| Pred)
(declare-const |p:false| Pred)
";

/// The axioms every program has.
pub(crate) fn shared() -> Vec<Axiom> {
    vec![
        // ---------- core (§7.2) ----------
        ax("card_nonneg", "(x Rel)", "(>= (card x) 0)", &["(card x)"]),
        ax(
            "ndv_range",
            "(x Rel) (W Cols)",
            "(and (>= (ndv x W) 0) (<= (ndv x W) (card x)) (=> (>= (card x) 1) (>= (ndv x W) 1)))",
            &["(ndv x W)"],
        ),
        ax("ndv_mono", "(x Rel) (X Cols) (Y Cols)", "(=> (csub X Y) (<= (ndv x X) (ndv x Y)))", &["(csub X Y) (ndv x X) (ndv x Y)"]),
        ax("ndv_product", "(x Rel) (X Cols) (Y Cols)", "(<= (ndv x (cup X Y)) (* (ndv x X) (ndv x Y)))", &["(ndv x (cup X Y))"]),
        ax("sub_card", "(x Rel) (y Rel)", "(=> (sub x y) (<= (card x) (card y)))", &["(sub x y)"]),
        ax("sub_ndv", "(x Rel) (y Rel) (W Cols)", "(=> (sub x y) (<= (ndv x W) (ndv y W)))", &["(sub x y) (ndv x W)"]),
        ax("sub_trans", "(x Rel) (y Rel) (z Rel)", "(=> (and (sub x y) (sub y z)) (sub x z))", &["(sub x y) (sub y z)"]),
        ax("sub_cols", "(x Rel) (y Rel)", "(=> (sub x y) (= (cols x) (cols y)))", &["(sub x y)"]),
        ax("sub_eq", "(x Rel) (y Rel)", "(=> (and (sub x y) (= (card x) (card y))) (= x y))", &["(sub x y)"]),
        ax("sub_key", "(x Rel) (y Rel) (K Cols)", "(=> (and (key y K) (sub x y)) (key x K))", &["(key y K) (sub x y)"]),
        ax("sub_fd", "(x Rel) (y Rel) (X Cols) (Y Cols)", "(=> (and (fd y X Y) (sub x y)) (fd x X Y))", &["(fd y X Y) (sub x y)"]),
        ax(
            "key_ndv",
            "(x Rel) (K Cols) (W Cols)",
            "(=> (and (key x K) (csub K W)) (= (ndv x W) (card x)))",
            &["(key x K) (ndv x W)"],
        ),
        ax("key_fd", "(x Rel) (K Cols)", "(=> (key x K) (fd x K (cols x)))", &["(key x K)"]),
        ax(
            "fd_trans",
            "(x Rel) (X Cols) (Y Cols) (Y2 Cols) (Z Cols)",
            "(=> (and (fd x X Y) (fd x Y2 Z) (csub Y2 Y)) (fd x X Z))",
            &["(fd x X Y) (fd x Y2 Z)"],
        ),
        ax(
            "fd_ndv",
            "(x Rel) (X Cols) (Y Cols) (W Cols)",
            "(=> (and (fd x X Y) (csub X (cdiff W Y))) (<= (ndv x W) (ndv x (cdiff W Y))))",
            &["(fd x X Y) (ndv x W)"],
        ),
        // A join's columns are a `jcup` of its sides' (an expression
        // column's, of its input's and its own): a set is within it if
        // within either part, or split between them. Small sets' unions
        // are `cup`, which these never match.
        ax("csub_cup", "(W Cols) (A Cols) (B Cols)", "(=> (or (csub W A) (csub W B)) (csub W (jcup A B)))", &["(csub W (jcup A B))"]),
        ax(
            "csub_split",
            "(W1 Cols) (W2 Cols) (A Cols) (B Cols)",
            "(=> (and (csub W1 A) (csub W2 B)) (csub (cup W1 W2) (jcup A B)))",
            &["(csub (cup W1 W2) (jcup A B))"],
        ),
        // A set of columns is non-NULL where each part is.
        ax(
            "nonnull_split",
            "(x Rel) (X Cols) (Y Cols)",
            "(= (nonnull x (cup X Y)) (and (nonnull x X) (nonnull x Y)))",
            &["(nonnull x (cup X Y))"],
        ),
        // ---------- filter ----------
        ax("filter_sub", "(p Pred) (x Rel)", "(and (sub (filter p x) x) (= (cols (filter p x)) (cols x)))", &["(filter p x)"]),
        ax("filter_commute", "(p Pred) (q Pred) (x Rel)", "(= (filter q (filter p x)) (filter p (filter q x)))", &["(filter q (filter p x))"]),
        ax("filter_idem", "(p Pred) (x Rel)", "(= (filter p (filter p x)) (filter p x))", &["(filter p (filter p x))"]),
        ax(
            "filter_mono",
            "(p Pred) (x Rel) (y Rel)",
            "(=> (sub x y) (sub (filter p x) (filter p y)))",
            &["(sub x y) (filter p x) (filter p y)"],
        ),
        ax("neg_neg", "(p Pred)", "(and (= (neg (neg p)) p) (= (reads (neg p)) (reads p)))", &["(neg p)"]),
        // `p` and `NOT p` are never both TRUE; where `p`'s columns are
        // non-NULL, one of them is.
        ax(
            "filter_complement",
            "(p Pred) (x Rel)",
            "(and (<= (+ (card (filter p x)) (card (filter (neg p) x))) (card x))
                  (=> (nonnull x (reads p)) (= (+ (card (filter p x)) (card (filter (neg p) x))) (card x))))",
            &["(filter p x)"],
        ),
        ax(
            "filter_incl_excl",
            "(p Pred) (q Pred) (x Rel)",
            "(>= (card (filter p (filter q x))) (- (+ (card (filter p x)) (card (filter q x))) (card x)))",
            &["(filter p (filter q x))"],
        ),
        ax(
            "filter_implies",
            "(p Pred) (q Pred) (x Rel)",
            "(=> (implies p q) (sub (filter p x) (filter q x)))",
            &["(implies p q) (filter p x) (filter q x)"],
        ),
        ax(
            "filter_redundant",
            "(p Pred) (q Pred) (x Rel)",
            "(=> (implies p q) (= (filter q (filter p x)) (filter p x)))",
            &["(implies p q) (filter q (filter p x))"],
        ),
        ax(
            "filter_disjoint",
            "(p Pred) (q Pred) (x Rel)",
            "(=> (implies p (neg q)) (= (card (filter q (filter p x))) 0))",
            &["(implies p (neg q)) (filter q (filter p x))"],
        ),
        ax("filter_point", "(p Pred) (x Rel)", "(=> (point p) (<= (ndv (filter p x) (reads p)) 1))", &["(point p) (filter p x)"]),
        // ---------- group by ----------
        ax(
            "group_basic",
            "(K Cols) (x Rel)",
            "(and (= (card (group K x)) (ndv x K)) (= (cols (group K x)) K) (key (group K x) K))",
            &["(group K x)"],
        ),
        ax("group_ndv", "(K Cols) (x Rel) (W Cols)", "(=> (csub W K) (= (ndv (group K x) W) (ndv x W)))", &["(ndv (group K x) W)"]),
        ax(
            "group_fd",
            "(K Cols) (x Rel) (X Cols) (Y Cols)",
            "(=> (and (fd x X Y) (csub X K) (csub Y K)) (fd (group K x) X Y))",
            &["(fd x X Y) (group K x)"],
        ),
        ax(
            "group_mono",
            "(K Cols) (x Rel) (y Rel)",
            "(=> (sub x y) (sub (group K x) (group K y)))",
            &["(sub x y) (group K x) (group K y)"],
        ),
        ax(
            "group_pushdown",
            "(p Pred) (K Cols) (x Rel)",
            "(=> (csub (reads p) K) (= (filter p (group K x)) (group K (filter p x))))",
            &["(filter p (group K x))"],
        ),
        // ---------- limit and union ----------
        ax(
            "limit_basic",
            "(n Int) (x Rel)",
            "(and (sub (limit n x) x) (= (card (limit n x)) (ite (<= (card x) n) (card x) n)))",
            &["(limit n x)"],
        ),
        ax(
            "union_basic",
            "(x Rel) (y Rel)",
            "(and (= (card (union x y)) (+ (card x) (card y))) (= (cols (union x y)) (cols x))
                  (=> (= (cols x) (cols y)) (and (sub x (union x y)) (sub y (union x y)))))",
            &["(union x y)"],
        ),
        ax("union_ndv", "(x Rel) (y Rel) (W Cols)", "(<= (ndv (union x y) W) (+ (ndv x W) (ndv y W)))", &["(ndv (union x y) W)"]),
        ax(
            "union_pushdown",
            "(p Pred) (x Rel) (y Rel)",
            "(=> (and (csub (reads p) (cols x)) (= (cols x) (cols y)))
                 (= (filter p (union x y)) (union (filter p x) (filter p y))))",
            &["(filter p (union x y))"],
        ),
        // ---------- value ranges (§7.3) ----------
        ax(
            "range_order",
            "(x Rel) (C Cols)",
            "(=> (and (nonnull x C) (>= (card x) 1)) (<= (min x C) (max x C)))",
            &["(min x C) (max x C)"],
        ),
        ax(
            "range_ndv",
            "(x Rel) (C Cols)",
            "(=> (and (intcol C) (>= (card x) 1))
                 (and (=> (nonnull x C) (<= (to_real (ndv x C)) (+ (- (max x C) (min x C)) 1.0)))
                      (<= (to_real (ndv x C)) (+ (- (max x C) (min x C)) 2.0))))",
            &["(intcol C) (ndv x C)"],
        ),
        ax(
            "range_point",
            "(x Rel) (C Cols)",
            "(=> (= (min x C) (max x C)) (and (=> (nonnull x C) (<= (ndv x C) 1)) (<= (ndv x C) 2)))",
            &["(min x C) (max x C)"],
        ),
        ax("sub_min", "(x Rel) (y Rel) (C Cols)", "(=> (sub x y) (<= (min y C) (min x C)))", &["(sub x y) (min x C)"]),
        ax("sub_max", "(x Rel) (y Rel) (C Cols)", "(=> (sub x y) (<= (max x C) (max y C)))", &["(sub x y) (max x C)"]),
        ax(
            "sub_nonnull",
            "(x Rel) (y Rel) (C Cols)",
            "(=> (and (sub x y) (nonnull y C)) (nonnull x C))",
            &["(sub x y) (nonnull y C) (min x C)", "(sub x y) (nonnull y C) (max x C)"],
        ),
        ax(
            "group_range",
            "(K Cols) (x Rel) (C Cols)",
            "(=> (csub C K) (and (= (min (group K x) C) (min x C)) (= (max (group K x) C) (max x C))
                                 (=> (nonnull x C) (nonnull (group K x) C))))",
            &["(min (group K x) C)", "(max (group K x) C)"],
        ),
        ax(
            "union_range",
            "(x Rel) (y Rel) (C Cols)",
            "(and (or (= (min (union x y) C) (min x C)) (= (min (union x y) C) (min y C)))
                  (<= (min (union x y) C) (min x C)) (<= (min (union x y) C) (min y C))
                  (or (= (max (union x y) C) (max x C)) (= (max (union x y) C) (max y C)))
                  (>= (max (union x y) C) (max x C)) (>= (max (union x y) C) (max y C))
                  (=> (and (nonnull x C) (nonnull y C)) (nonnull (union x y) C)))",
            &["(min (union x y) C)", "(max (union x y) C)"],
        ),
        // ---------- physical operators (§7.4) ----------
        ax("part_sub", "(o Occ) (x Rel)", "(sub (part o x) x)", &["(part o x)"]),
        ax("opt_sub", "(o Occ) (p Pred) (x Rel)", "(and (sub (opt o p x) x) (sub (filter p x) (opt o p x)))", &["(opt o p x)"]),
        ax("opt_check", "(o Occ) (p Pred) (x Rel)", "(= (filter p (opt o p x)) (filter p x))", &["(filter p (opt o p x))"]),
        // ---------- compound predicates (§7.5) ----------
        ax(
            "or_split",
            "(p Pred) (q Pred) (r Pred) (x Rel)",
            "(=> (orof p q r) (<= (card (filter p x)) (+ (card (filter q x)) (card (filter r x)))))",
            &["(orof p q r) (filter p x)"],
        ),
        ax(
            "or_disjoint",
            "(p Pred) (q Pred) (r Pred) (x Rel)",
            "(=> (and (orof p q r) (implies q (neg r))) (= (card (filter p x)) (+ (card (filter q x)) (card (filter r x)))))",
            &["(orof p q r) (implies q (neg r)) (filter p x)"],
        ),
        ax(
            "or_incl_excl",
            "(p Pred) (q Pred) (r Pred) (x Rel)",
            "(=> (orof p q r) (= (card (filter p x)) (- (+ (card (filter q x)) (card (filter r x))) (card (filter q (filter r x))))))",
            &["(orof p q r) (filter p x) (filter q (filter r x))"],
        ),
        ax(
            "or_sub",
            "(p Pred) (q Pred) (r Pred) (x Rel)",
            "(=> (orof p q r) (and (sub (filter q x) (filter p x)) (sub (filter r x) (filter p x))))",
            &["(orof p q r) (filter p x) (filter q x)", "(orof p q r) (filter p x) (filter r x)"],
        ),
        ax(
            "and_lower",
            "(p Pred) (q Pred) (r Pred) (x Rel)",
            "(=> (andof p q r) (>= (card (filter p x)) (- (+ (card (filter q x)) (card (filter r x))) (card x))))",
            &["(andof p q r) (filter p x)"],
        ),
        ax(
            "and_chain",
            "(p Pred) (q Pred) (r Pred) (x Rel)",
            "(=> (andof p q r) (= (filter p x) (filter q (filter r x))))",
            &["(andof p q r) (filter p x) (filter q (filter r x))"],
        ),
        ax("filter_false", "(x Rel)", "(= (card (filter |p:false| x)) 0)", &["(filter |p:false| x)"]),
        ax("filter_true", "(x Rel)", "(= (filter |p:true| x) x)", &["(filter |p:true| x)"]),
        ax("filter_width", "(p Pred) (x Rel)", "(<= (ndv (filter p x) (reads p)) (width p))", &["(filter p x) (width p)"]),
        // ---------- value domains (§7.6) ----------
        ax("dom_filter", "(x Rel) (d Pred)", "(=> (dom x d) (= (filter d x) x))", &["(dom x d)"]),
        ax(
            "dom_sub",
            "(x Rel) (d Pred) (z Rel) (q Pred)",
            "(=> (and (dom x d) (sub z x)) (dom z d))",
            &["(dom x d) (sub z x) (filter q z)"],
        ),
        // ---------- expression columns ----------
        ax(
            "extend_basic",
            "(g Cols) (x Rel)",
            "(and (= (card (extend g x)) (card x)) (= (cols (extend g x)) (jcup (cols x) g)) (fd (extend g x) (def g) g))",
            &["(extend g x)"],
        ),
        ax(
            "extend_ndv",
            "(g Cols) (x Rel) (W Cols)",
            "(=> (csub W (cols x)) (= (ndv (extend g x) W) (ndv x W)))",
            &["(ndv (extend g x) W)"],
        ),
        ax("extend_key", "(g Cols) (x Rel) (K Cols)", "(=> (key x K) (key (extend g x) K))", &["(key x K) (extend g x)"]),
        ax(
            "extend_fd",
            "(g Cols) (x Rel) (X Cols) (Y Cols)",
            "(=> (fd x X Y) (fd (extend g x) X Y))",
            &["(fd x X Y) (extend g x)"],
        ),
        ax(
            "extend_range",
            "(g Cols) (x Rel) (C Cols)",
            "(=> (csub C (cols x)) (and (= (min (extend g x) C) (min x C)) (= (max (extend g x) C) (max x C))
                                        (=> (nonnull x C) (nonnull (extend g x) C))))",
            &["(min (extend g x) C)", "(max (extend g x) C)"],
        ),
        ax(
            "extend_push",
            "(p Pred) (g Cols) (x Rel)",
            "(=> (csub (reads p) (cols x)) (= (filter p (extend g x)) (extend g (filter p x))))",
            &["(filter p (extend g x))"],
        ),
        // ---------- aggregates (§7.7) ----------
        ax(
            "agg_basic",
            "(K Cols) (G Cols) (x Rel)",
            "(and (= (card (aggregate K G x)) (ndv x K)) (= (cols (aggregate K G x)) (cup K G)) (key (aggregate K G x) K)
                  (= (group K (aggregate K G x)) (group K x)))",
            &["(aggregate K G x)"],
        ),
        ax(
            "agg_ndv",
            "(K Cols) (G Cols) (x Rel) (W Cols)",
            "(=> (csub W K) (= (ndv (aggregate K G x) W) (ndv x W)))",
            &["(ndv (aggregate K G x) W)"],
        ),
        ax(
            "agg_range",
            "(K Cols) (G Cols) (x Rel) (C Cols)",
            "(=> (csub C K) (and (= (min (aggregate K G x) C) (min x C)) (= (max (aggregate K G x) C) (max x C))
                                 (=> (nonnull x C) (nonnull (aggregate K G x) C))))",
            &["(min (aggregate K G x) C)", "(max (aggregate K G x) C)"],
        ),
        ax(
            "agg_push",
            "(p Pred) (K Cols) (G Cols) (x Rel)",
            "(=> (csub (reads p) K) (= (filter p (aggregate K G x)) (aggregate K G (filter p x))))",
            &["(filter p (aggregate K G x))"],
        ),
        ax(
            "scalar_basic",
            "(G Cols) (x Rel)",
            "(and (= (card (scalar G x)) 1) (= (cols (scalar G x)) G))",
            &["(scalar G x)"],
        ),
        ax(
            "one_row",
            "(y Rel) (C Cols)",
            "(=> (and (= (card y) 1) (nonnull y C)) (= (min y C) (max y C)))",
            &["(min y C) (max y C)"],
        ),
        // ---------- aliases (§7.8) ----------
        ax(
            "alias_basic",
            "(i Int) (x Rel)",
            "(and (= (card (alias i x)) (card x)) (= (cols (alias i x)) (acols i (cols x))))",
            &["(alias i x)"],
        ),
        ax("alias_ndv", "(i Int) (x Rel) (W Cols)", "(= (ndv (alias i x) W) (ndv x (ucols i W)))", &["(ndv (alias i x) W)"]),
        ax(
            "alias_range",
            "(i Int) (x Rel) (W Cols)",
            "(=> (csub W (cols (alias i x)))
                 (and (= (min (alias i x) W) (min x (ucols i W))) (= (max (alias i x) W) (max x (ucols i W)))
                      (=> (nonnull x (ucols i W)) (nonnull (alias i x) W))))",
            &["(min (alias i x) W)", "(max (alias i x) W)"],
        ),
        ax("alias_key", "(i Int) (x Rel) (K Cols)", "(=> (key x K) (key (alias i x) (acols i K)))", &["(key x K) (alias i x)"]),
        ax(
            "alias_fd",
            "(i Int) (x Rel) (X Cols) (Y Cols)",
            "(=> (fd x X Y) (fd (alias i x) (acols i X) (acols i Y)))",
            &["(fd x X Y) (alias i x)"],
        ),
        ax(
            "alias_push",
            "(i Int) (p Pred) (x Rel)",
            "(=> (csub (reads p) (cols (alias i x))) (= (filter p (alias i x)) (alias i (filter (upred i p) x))))",
            &["(filter p (alias i x))"],
        ),
        ax(
            "alias_group",
            "(i Int) (K Cols) (x Rel)",
            "(=> (csub K (cols (alias i x))) (= (group K (alias i x)) (alias i (group (ucols i K) x))))",
            &["(group K (alias i x))"],
        ),
        // ---------- scalar subqueries (§7.9) ----------
        ax(
            "cmp_gt",
            "(A Cols) (y Rel) (G Cols) (x Rel)",
            "(and (> (min (filter (cmp_gt A y G) x) A) (max y G)) (<= (max (filter (cmp_gt A y G) x) A) (max x A))
                  (nonnull (filter (cmp_gt A y G) x) A)
                  (=> (and (intcol A) (intcol G)) (>= (min (filter (cmp_gt A y G) x) A) (+ (max y G) 1.0))))",
            &["(filter (cmp_gt A y G) x)"],
        ),
        ax(
            "cmp_ge",
            "(A Cols) (y Rel) (G Cols) (x Rel)",
            "(and (>= (min (filter (cmp_ge A y G) x) A) (max y G)) (<= (max (filter (cmp_ge A y G) x) A) (max x A))
                  (nonnull (filter (cmp_ge A y G) x) A))",
            &["(filter (cmp_ge A y G) x)"],
        ),
        ax(
            "cmp_lt",
            "(A Cols) (y Rel) (G Cols) (x Rel)",
            "(and (< (max (filter (cmp_lt A y G) x) A) (min y G)) (>= (min (filter (cmp_lt A y G) x) A) (min x A))
                  (nonnull (filter (cmp_lt A y G) x) A)
                  (=> (and (intcol A) (intcol G)) (<= (max (filter (cmp_lt A y G) x) A) (- (min y G) 1.0))))",
            &["(filter (cmp_lt A y G) x)"],
        ),
        ax(
            "cmp_le",
            "(A Cols) (y Rel) (G Cols) (x Rel)",
            "(and (<= (max (filter (cmp_le A y G) x) A) (min y G)) (>= (min (filter (cmp_le A y G) x) A) (min x A))
                  (nonnull (filter (cmp_le A y G) x) A))",
            &["(filter (cmp_le A y G) x)"],
        ),
        ax(
            "cmp_eq",
            "(A Cols) (y Rel) (G Cols) (x Rel)",
            "(and (>= (min (filter (cmp_eq A y G) x) A) (min y G)) (<= (max (filter (cmp_eq A y G) x) A) (max y G))
                  (<= (ndv (filter (cmp_eq A y G) x) A) 1) (nonnull (filter (cmp_eq A y G) x) A))",
            &["(filter (cmp_eq A y G) x)"],
        ),
    ]
}

/// A join family's functions and key sets, as SMT.
pub(crate) struct Fam {
    pub tag: String,
    pub j: String,
    pub lj: String,
    pub s: String,
    pub a: String,
    /// The mirror's inner join.
    pub m: String,
    pub kl: String,
    pub kr: String,
    /// Single key pairs, as column-set symbols.
    pub pairs: Vec<(String, String)>,
    /// Whether NULL keys match each other.
    pub null_eq: bool,
    /// The residual predicate's symbol and columns, if any.
    pub residual: Option<(String, String)>,
}

/// The axioms of one join family (§7.2, §7.3).
pub(crate) fn family(f: &Fam) -> Vec<Axiom> {
    let Fam { tag, j, lj, s, a, m, kl, kr, .. } = f;
    let n = |what: &str| format!("{what}{tag}");
    let mut out = vec![
        ax(
            n("inner_basic"),
            "(x Rel) (y Rel)",
            &format!(
                "(and (= (cols ({j} x y)) (jcup (cols x) (cols y))) (<= (card ({j} x y)) (* (card x) (card y)))
                      (fd ({j} x y) {kl} {kr}) (fd ({j} x y) {kr} {kl}) (= ({j} x y) ({m} y x)))"
            ),
            &[&format!("({j} x y)")],
        ),
        ax(
            n("inner_keyed"),
            "(x Rel) (y Rel)",
            &format!("(=> (key y {kr}) (= (card ({j} x y)) (card ({s} x y))))"),
            &[&format!("(key y {kr}) ({j} x y)")],
        ),
        ax(n("inner_semi"), "(x Rel) (y Rel)", &format!("(<= (card ({s} x y)) (card ({j} x y)))"), &[&format!("({j} x y) ({s} x y)")]),
        ax(
            n("inner_mono_l"),
            "(x Rel) (x2 Rel) (y Rel)",
            &format!("(=> (sub x x2) (sub ({j} x y) ({j} x2 y)))"),
            &[&format!("(sub x x2) ({j} x y) ({j} x2 y)")],
        ),
        ax(
            n("inner_mono_r"),
            "(x Rel) (y Rel) (y2 Rel)",
            &format!("(=> (sub y y2) (sub ({j} x y) ({j} x y2)))"),
            &[&format!("(sub y y2) ({j} x y) ({j} x y2)")],
        ),
        ax(
            n("inner_vals"),
            "(x Rel) (y Rel) (W Cols)",
            &format!(
                "(and (=> (csub W (cols x)) (<= (ndv ({j} x y) W) (ndv x W)))
                      (=> (csub W (cols y)) (<= (ndv ({j} x y) W) (ndv y W))))"
            ),
            &[&format!("(ndv ({j} x y) W)")],
        ),
        ax(
            n("inner_key"),
            "(x Rel) (y Rel) (K Cols)",
            &format!("(=> (and (key x K) (key y {kr})) (key ({j} x y) K))"),
            &[&format!("(key x K) ({j} x y)")],
        ),
        ax(
            n("inner_fd_l"),
            "(x Rel) (y Rel) (X Cols) (Y Cols)",
            &format!("(=> (fd x X Y) (fd ({j} x y) X Y))"),
            &[&format!("(fd x X Y) ({j} x y)")],
        ),
        ax(
            n("inner_fd_r"),
            "(x Rel) (y Rel) (X Cols) (Y Cols)",
            &format!("(=> (fd y X Y) (fd ({j} x y) X Y))"),
            &[&format!("(fd y X Y) ({j} x y)")],
        ),
        ax(
            n("inner_push"),
            "(p Pred) (x Rel) (y Rel)",
            &format!(
                "(and (=> (csub (reads p) (cols x)) (= (filter p ({j} x y)) ({j} (filter p x) y)))
                      (=> (csub (reads p) (cols y)) (= (filter p ({j} x y)) ({j} x (filter p y)))))"
            ),
            &[
                &format!("(filter p ({j} x y))"),
                &format!("(filter p x) ({j} x y)"),
                &format!("(filter p y) ({j} x y)"),
            ],
        ),
        ax(
            n("inner_range"),
            "(x Rel) (y Rel) (C Cols)",
            &format!(
                "(and (=> (csub C (cols x)) (and (>= (min ({j} x y) C) (min x C)) (<= (max ({j} x y) C) (max x C))
                                                 (=> (nonnull x C) (nonnull ({j} x y) C))))
                      (=> (csub C (cols y)) (and (>= (min ({j} x y) C) (min y C)) (<= (max ({j} x y) C) (max y C))
                                                 (=> (nonnull y C) (nonnull ({j} x y) C)))))"
            ),
            &[&format!("(min ({j} x y) C)"), &format!("(max ({j} x y) C)")],
        ),
        // ---------- left outer ----------
        ax(
            n("left_basic"),
            "(x Rel) (y Rel)",
            &format!(
                "(and (= (cols ({lj} x y)) (jcup (cols x) (cols y))) (= (card ({lj} x y)) (+ (card ({j} x y)) (card ({a} x y)))))"
            ),
            &[&format!("({lj} x y)")],
        ),
        ax(
            n("left_vals"),
            "(x Rel) (y Rel) (W Cols)",
            &format!(
                "(and (=> (csub W (cols x)) (= (ndv ({lj} x y) W) (ndv x W)))
                      (=> (csub W (cols y)) (<= (ndv ({lj} x y) W) (+ (ndv y W) 1))))"
            ),
            &[&format!("(ndv ({lj} x y) W)")],
        ),
        ax(
            n("left_key"),
            "(x Rel) (y Rel) (K Cols)",
            &format!("(=> (and (key x K) (key y {kr})) (key ({lj} x y) K))"),
            &[&format!("(key x K) ({lj} x y)")],
        ),
        ax(
            n("left_fd_l"),
            "(x Rel) (y Rel) (X Cols) (Y Cols)",
            &format!("(=> (fd x X Y) (fd ({lj} x y) X Y))"),
            &[&format!("(fd x X Y) ({lj} x y)")],
        ),
        ax(
            n("left_mono_l"),
            "(x Rel) (x2 Rel) (y Rel)",
            &format!("(=> (sub x x2) (sub ({lj} x y) ({lj} x2 y)))"),
            &[&format!("(sub x x2) ({lj} x y) ({lj} x2 y)")],
        ),
        ax(
            n("left_push"),
            "(p Pred) (x Rel) (y Rel)",
            &format!("(=> (csub (reads p) (cols x)) (= (filter p ({lj} x y)) ({lj} (filter p x) y)))"),
            &[&format!("(filter p ({lj} x y))"), &format!("(filter p x) ({lj} x y)")],
        ),
        ax(
            n("left_range"),
            "(x Rel) (y Rel) (C Cols)",
            &format!(
                "(and (=> (csub C (cols x)) (and (= (min ({lj} x y) C) (min x C)) (= (max ({lj} x y) C) (max x C))
                                                 (=> (nonnull x C) (nonnull ({lj} x y) C))))
                      (=> (csub C (cols y)) (and (>= (min ({lj} x y) C) (min y C)) (<= (max ({lj} x y) C) (max y C)))))"
            ),
            &[&format!("(min ({lj} x y) C)"), &format!("(max ({lj} x y) C)")],
        ),
        // ---------- semi and anti ----------
        ax(
            n("semi_basic"),
            "(x Rel) (y Rel)",
            &format!(
                "(and (sub ({s} x y) x) (= (+ (card ({s} x y)) (card ({a} x y))) (card x)) (<= (ndv ({s} x y) {kl}) (ndv y {kr})))"
            ),
            &[&format!("({s} x y)")],
        ),
        ax(
            n("anti_basic"),
            "(x Rel) (y Rel)",
            &format!("(and (sub ({a} x y) x) (= (+ (card ({s} x y)) (card ({a} x y))) (card x)))"),
            &[&format!("({a} x y)")],
        ),
        ax(
            n("semi_mono_l"),
            "(x Rel) (x2 Rel) (y Rel)",
            &format!("(=> (sub x x2) (sub ({s} x y) ({s} x2 y)))"),
            &[&format!("(sub x x2) ({s} x y) ({s} x2 y)")],
        ),
        ax(
            n("semi_mono_r"),
            "(x Rel) (y Rel) (y2 Rel)",
            &format!("(=> (sub y y2) (sub ({s} x y) ({s} x y2)))"),
            &[&format!("(sub y y2) ({s} x y) ({s} x y2)")],
        ),
        ax(
            n("anti_mono_l"),
            "(x Rel) (x2 Rel) (y Rel)",
            &format!("(=> (sub x x2) (sub ({a} x y) ({a} x2 y)))"),
            &[&format!("(sub x x2) ({a} x y) ({a} x2 y)")],
        ),
        ax(
            n("anti_mono_r"),
            "(x Rel) (y Rel) (y2 Rel)",
            &format!("(=> (sub y y2) (sub ({a} x y2) ({a} x y)))"),
            &[&format!("(sub y y2) ({a} x y) ({a} x y2)")],
        ),
        ax(
            n("semi_push"),
            "(p Pred) (x Rel) (y Rel)",
            &format!("(=> (csub (reads p) (cols x)) (= (filter p ({s} x y)) ({s} (filter p x) y)))"),
            &[&format!("(filter p ({s} x y))")],
        ),
        ax(
            n("anti_push"),
            "(p Pred) (x Rel) (y Rel)",
            &format!("(=> (csub (reads p) (cols x)) (= (filter p ({a} x y)) ({a} (filter p x) y)))"),
            &[&format!("(filter p ({a} x y))")],
        ),
    ];
    // Equal keys have equal ranges in the inner join, and the right keys
    // of the semi join's partners bound its left keys' values.
    if !f.null_eq {
        for (l, r) in &f.pairs {
            out.push(ax(
                format!("inner_keys{tag}{l}{r}"),
                "(x Rel) (y Rel)",
                &format!(
                    "(and (= (min ({j} x y) {l}) (min ({j} x y) {r})) (= (max ({j} x y) {l}) (max ({j} x y) {r}))
                          (nonnull ({j} x y) {l}) (nonnull ({j} x y) {r}))"
                ),
                &[&format!("(min ({j} x y) {l})"), &format!("(max ({j} x y) {l})"), &format!("(min ({j} x y) {r})"), &format!("(max ({j} x y) {r})")],
            ));
            out.push(ax(
                format!("semi_keys{tag}{l}{r}"),
                "(x Rel) (y Rel)",
                &format!(
                    "(and (>= (min ({s} x y) {l}) (min y {r})) (<= (max ({s} x y) {l}) (max y {r})) (nonnull ({s} x y) {l}))"
                ),
                &[&format!("(min ({s} x y) {l})"), &format!("(max ({s} x y) {l})")],
            ));
        }
    }
    if let Some((p, _)) = &f.residual {
        // A residual condition keeps a subset of the plain join's pairs:
        // which plain family is this one's is stated by the caller.
        let _ = p;
    }
    out
}

/// `(x ⋈f y) ⋈g z` regroups around whichever input holds `g`'s left keys.
pub(crate) fn assoc(f: &Fam, g: &Fam) -> Axiom {
    let (j, gj, gkl) = (&f.j, &g.j, &g.kl);
    ax(
        format!("assoc{}{}", f.tag, g.tag),
        "(x Rel) (y Rel) (z Rel)",
        &format!(
            "(and (=> (csub {gkl} (cols y)) (= ({gj} ({j} x y) z) ({j} x ({gj} y z))))
                  (=> (csub {gkl} (cols x)) (= ({gj} ({j} x y) z) ({j} ({gj} x z) y))))"
        ),
        &[&format!("({gj} ({j} x y) z)")],
    )
}

/// A residual family `f` keeps a subset of plain family `p`'s pairs, those
/// satisfying predicate `r`.
pub(crate) fn residual(f: &Fam, p: &Fam, r: &str) -> Vec<Axiom> {
    let (fj, fs, fa, pj, ps, pa) = (&f.j, &f.s, &f.a, &p.j, &p.s, &p.a);
    vec![
        ax(
            format!("residual_inner{}", f.tag),
            "(x Rel) (y Rel)",
            &format!("(= ({fj} x y) (filter {r} ({pj} x y)))"),
            &[&format!("({fj} x y)")],
        ),
        ax(
            format!("residual_semi{}", f.tag),
            "(x Rel) (y Rel)",
            &format!("(and (sub ({fs} x y) ({ps} x y)) (sub ({pa} x y) ({fa} x y)))"),
            &[&format!("({fs} x y)"), &format!("({fa} x y)")],
        ),
    ]
}

/// The axioms of a foreign key `T.A → U.B`, for family `f` pairing `A`
/// with `B` and its mirror `r`; `t` and `u` are the referencing and
/// referenced relations (scans, or aliases of them).
pub(crate) fn foreign_key(name: &str, t: &str, u: &str, f: &Fam, r: &Fam) -> Vec<Axiom> {
    let within = |x: &str| format!("(or (= {x} {t}) (sub {x} {t}))");
    let (j, lj, s, a) = (&f.j, &f.lj, &f.s, &f.a);
    let wx = within("x");
    let wy = within("y");
    vec![
        ax(format!("{name}_inner"), "(x Rel)", &format!("(=> {wx} (= (card ({j} x {u})) (card x)))"), &[&format!("({j} x {u})")]),
        ax(format!("{name}_left"), "(x Rel)", &format!("(=> {wx} (= (card ({lj} x {u})) (card x)))"), &[&format!("({lj} x {u})")]),
        ax(format!("{name}_semi"), "(x Rel)", &format!("(=> {wx} (= ({s} x {u}) x))"), &[&format!("({s} x {u})")]),
        ax(format!("{name}_anti"), "(x Rel)", &format!("(=> {wx} (= (card ({a} x {u})) 0))"), &[&format!("({a} x {u})")]),
        ax(
            format!("{name}_cover"),
            "(y Rel)",
            &format!("(=> {wy} (>= (ndv ({} {u} y) {}) (ndv y {})))", r.s, r.kl, r.kr),
            &[&format!("({} {u} y)", r.s)],
        ),
    ]
}

/// The axioms of a runtime-filter family `T = rt[L=R]` (§7.4), with join
/// family `f` of the same keys.
pub(crate) fn runtime(t: &str, f: &Fam, kl: &str) -> Vec<Axiom> {
    let (j, s) = (&f.j, &f.s);
    vec![
        ax(format!("rt_sub{}", f.tag), "(o Occ) (x Rel) (b Rel)", &format!("(sub ({t} o x b) x)"), &[&format!("({t} o x b)")]),
        ax(
            format!("rt_cover{}", f.tag),
            "(o Occ) (x Rel) (b Rel)",
            &format!("(sub ({s} x b) ({t} o x b))"),
            &[&format!("({t} o x b)")],
        ),
        ax(
            format!("rt_join{}", f.tag),
            "(o Occ) (x Rel) (b Rel)",
            &format!("(= ({j} ({t} o x b) b) ({j} x b))"),
            &[&format!("({j} ({t} o x b) b)")],
        ),
        ax(
            format!("rt_semi{}", f.tag),
            "(o Occ) (x Rel) (b Rel)",
            &format!("(= ({s} ({t} o x b) b) ({s} x b))"),
            &[&format!("({s} ({t} o x b) b)")],
        ),
        ax(
            format!("rt_push_filter{}", f.tag),
            "(o Occ) (p Pred) (x Rel) (b Rel)",
            &format!("(= (filter p ({t} o x b)) ({t} o (filter p x) b))"),
            &[&format!("(filter p ({t} o x b))")],
        ),
        ax(
            format!("rt_push_group{}", f.tag),
            "(o Occ) (K Cols) (x Rel) (b Rel)",
            &format!("(=> (csub {kl} K) (= (group K ({t} o x b)) ({t} o (group K x) b)))"),
            &[&format!("(group K ({t} o x b))")],
        ),
    ]
}

/// A runtime filter of family `T` moves above a join, semi join or left
/// join `g` with it on its left.
pub(crate) fn runtime_push(t: &str, tag: &str, g: &str, gtag: &str) -> Axiom {
    ax(
        format!("rt_push_join{tag}{gtag}"),
        "(o Occ) (x Rel) (b Rel) (y Rel)",
        &format!("(= ({g} ({t} o x b) y) ({t} o ({g} x y) b))"),
        &[&format!("({g} ({t} o x b) y)")],
    )
}

/// An expression moves above a join (`extend_join`), when it is not
/// among the join's left keys.
pub(crate) fn extend_join(g: &str, gname: &str, f: &Fam) -> Vec<Axiom> {
    [&f.j, &f.lj, &f.s, &f.a]
        .iter()
        .map(|fun| {
            ax(
                format!("extend_join{}{}{}", gname, f.tag, fun),
                "(x Rel) (y Rel)",
                &format!("(= ({fun} (extend {g} x) y) (extend {g} ({fun} x y)))"),
                &[&format!("({fun} (extend {g} x) y)")],
            )
        })
        .collect()
}
