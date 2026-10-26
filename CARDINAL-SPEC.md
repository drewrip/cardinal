# Spec: cardinality bounds from abstract relations and axioms

This spec describes how to bound the row counts and distinct-value counts (NDVs) of query plans. Relations are encoded as opaque SMT terms, operator semantics as quantified axioms, and bounds are extracted by Z3's optimizer and confirmed by UNSAT checks. It describes the encoding as implemented and measured in `prototypes/axioms/`; measurements are in `RESULTS.md`. The words MUST, SHOULD and MAY are normative.

## 1. Overview

```
executed plans (with row counts) ─┐
target plan + schema ─────────────┼─▶ terms and ground facts ─┐
counted facts ────────────────────┘                           ├─▶ z3 (pattern matching only) ──▶ [lower, upper] + unsat core
                       axiom table (fixed, written once) ─────┘
```

- Every plan node becomes a **term**: the target plan's nodes and those of every executed plan alike. The same subplan always becomes the same term, which is how facts move between queries.
- An operator's semantics are stated **once**, as ∀-axioms over terms. The encoder never asserts per-node consequences such as `card(o) ≤ card(l)`.
- **Observations** are ground facts on terms. Mostly they are an executed node's row count, `card(t) = n`. Selectivities, match shares and group sizes are not read off plans; they follow from row counts by the axioms. What a physical operator really computed (a scan cut short, an inexact pushed filter, a runtime filter) is a term of its own (§7.4), not a reason to drop the count.
- Only the target plan's root is **probed**. Executed plans contribute facts and are never bounded themselves.
- A **bound** on a term `t` is the tightest `B` such that the axioms and facts entail `t ≤ B` (or `t ≥ B`). It is found by optimize-then-confirm (§9), after the observations have been checked for consistency (§6.6).

## 2. Inputs

| Input | Content |
|---|---|
| Schema | Tables and their columns. Column names are global: each belongs to exactly one table. Keys, functional dependencies (FDs) and foreign keys (FKs). Value domains: types with few values (BOOLEAN, ENUM, small integer types), CHECK constraints, and storage statistics' min and max (§6.1). |
| Plans | Trees of `Scan`, `Filter`, `Project`, `Group` (with aggregates), `Distinct`, `Join` (inner, left, semi, anti; equi-join on column pairs), `Limit`, `Sort` and `Union` (all). A table may be read more than once (self-joins). Projections, group keys and join keys may be expressions, and a filter above a `Group` may read its aggregates (HAVING). |
| Predicates | Quantifier-free conditions over a row's columns: atoms `col op literal`, with op in `> >= = < <= != <>` and a literal that is an integer, a decimal or a string (strings only with `=`); AND, OR and NOT over them; IN lists; comparisons of expressions over columns; and comparisons of a column with an uncorrelated scalar subquery. |
| Executed plans | Plans an engine ran, each node with the rows it output. Physical annotations: a node that may have stopped early, a filter pushed into a scan inexactly, and a runtime filter with the join that built it and any values it printed (a range or an IN list). |
| Counted facts | Facts a query of their own counted: `card(plan) = n`, `ndv(plan, cols) = n`, `unique(plan, cols)`, `min(plan, col) = v`, `max(plan, col) = v` (numeric columns), `domain(plan, cols) = {v₁, …, v_k}`, and shares `card(plan₁) / card(plan₂) = r`. |
| Target | The plan to bound. Its root's `card`, or `ndv(root, cols)`, is the only probe. |

## 3. Semantics

The axioms MUST be true under the following semantics. Any new axiom MUST be checked against them.

1. A relation is a **bag** of rows over a set of named columns.
2. `sub(x, y)` means `x` is a sub-bag of `y`, and `cols(x) = cols(y)`.
3. `ndv(x, W)` is the number of distinct tuples of `W ∩ cols(x)` in `x`, with NULL counted as a value. It equals `|GROUP BY W|`. Taking the intersection keeps the axioms true for terms that triggers create with columns a relation lacks.
4. `key(x, K)` means no two rows of `x` agree on `K`. `fd(x, X, Y)` means `X` determines `Y` in `x`. Both are only stated with `K, X, Y ⊆ cols(x)`.
5. Columns are NOT NULL, except a left join's right-side columns on unmatched rows.
6. `neg(p)` is the complement of `p`. Because of rule 5, `filter(p, x)` and `filter(neg p, x)` partition `x`.
7. `Group(K, x)` models only its key columns: `cols = K`. Aggregates that something above reads are modelled by `aggregate` (rule 11).
8. `min(x, {a})` and `max(x, {a})` are the least and greatest non-NULL value of the numeric column `a` in `x`. When `x` has no non-NULL `a` (it is empty, or `a` is NULL on every row), they are a fixed `+BIG` and `−BIG`, beyond every value and literal, so the range is empty. With this choice the propagation axioms (§7.3) need no emptiness guard. `nonnull(x, {a})` means `a` is NOT NULL on every row of `x`. `intcol({a})` means `a` holds integers.
9. A physical operator's output depends on the run, not only on its inputs. So each one takes an **occurrence** `o`, a constant unique to one node of one executed plan, and two occurrences never denote the same rows:
   - `part(o, x)` is some sub-bag of `x`: a scan that may have stopped early, or rows pruned by a filter nothing models.
   - `opt(o, p, x)` holds every row of `x` satisfying `p`, and maybe others of `x`: a filter pushed into a scan inexactly.
   - `rt[L=R](o, x, b)` is `x` after a runtime filter built from the keys `R` of `b`. It is **lossless**: it drops only rows of `x` whose `L` has no partner in `b`, and whether it keeps a row depends only on the row's `L`. A runtime filter that may drop a row with a partner, or decides by anything else, is a `part`.
10. A **predicate** is a quantifier-free formula over a row's columns, evaluated in SQL's three-valued logic. `filter(p, x)` keeps the rows on which `p` is TRUE.
    - `orof(p, q, r)` means `p` is `q ∨ r`, and `andof(p, q, r)` means `p` is `q ∧ r`.
    - `width(p) = k` means at most `k` distinct tuples of `reads(p)` make `p` TRUE.
    - `dom(x, d)` means `d` is TRUE on every row of `x`: `d` is a **value domain** of `x`.
11. An **expression** is a deterministic function of the columns it reads, `def`. `extend(g, x)` is `x` with one more column `g`, holding `g`'s expression evaluated on each row. A column named by an expression's canonical text (§5) denotes that expression wherever it appears.
12. `aggregate(K, G, x)` has one row per distinct `K`-tuple of `x`, with columns `K ∪ G`. Each column in `G` is an aggregate function over the group's rows, and its name is that function and its argument (`count(*)`, `max(foo.b)`), wherever it appears. `scalar(G, x)` aggregates all of `x` with no GROUP BY: exactly one row, even when `x` is empty.
13. `alias(i, x)` is `x` with every column `c` renamed `c#i`. It changes no row.
14. `cmp_op(A, y, G)`, for `op` among `gt ge lt le eq`, is TRUE on a row when `y` has exactly one row, that row's `G` is not NULL, and the row's `A op` that value holds. Otherwise it is TRUE on no row. That covers an empty subquery and a NULL value, where SQL's comparison is NULL. It also covers more than one row, which is a runtime error, so no plan that ran had one.

## 4. Vocabulary

**Sorts:** `Rel`, `Pred`, `Cols`, `Table`, `Occ`. Column values are `Real`, for Int and Real columns alike; String columns have no `min` or `max`.

**Operators:**

| Function | Signature |
|---|---|
| `scan` | `Table → Rel` |
| `filter` | `Pred × Rel → Rel` |
| `project`, `group` | `Cols × Rel → Rel` |
| `dedup` | `Rel → Rel` (`distinct` is reserved in SMT-LIB) |
| `limit` | `Int × Rel → Rel` |
| `sort` | `Rel → Rel` |
| `union` | `Rel × Rel → Rel` |
| `join[L=R]`, `ljoin[L=R]`, `semi[L=R]`, `anti[L=R]` | `Rel × Rel → Rel`, one family per key pairing |
| `part` | `Occ × Rel → Rel` |
| `opt` | `Occ × Pred × Rel → Rel` |
| `rt[L=R]` | `Occ × Rel × Rel → Rel`, probe side first, one family per key pairing |
| `extend` | `Cols × Rel → Rel`, one expression column |
| `aggregate` | `Cols × Cols × Rel → Rel`, keys, then aggregate columns |
| `scalar` | `Cols × Rel → Rel` |
| `alias` | `Int × Rel → Rel` |
| `cmp_gt`, `cmp_ge`, `cmp_lt`, `cmp_le`, `cmp_eq` | `Cols × Rel × Cols → Pred` |

A join family is identified by its sorted column pairs; for example, `join[o_custkey=c_custkey]`. Every family has a **mirror** with the sides swapped, declared even if no plan uses it. Join keys are never a sort.

**Attributes:**

| Function | Signature |
|---|---|
| `card` | `Rel → Int` |
| `ndv` | `Rel × Cols → Int` |
| `cols` | `Rel → Cols` |
| `sub` | `Rel × Rel → Bool` |
| `key` | `Rel × Cols → Bool` |
| `fd` | `Rel × Cols × Cols → Bool` |
| `min`, `max` | `Rel × Cols → Real`, on single-column sets only |
| `nonnull` | `Rel × Cols → Bool` |
| `intcol` | `Cols → Bool` |
| `reads` | `Pred → Cols` |
| `neg` | `Pred → Pred` |
| `implies` | `Pred × Pred → Bool` |
| `point` | `Pred → Bool` |
| `cup`, `cdiff` | `Cols × Cols → Cols` |
| `csub` | `Cols × Cols → Bool` |
| `orof`, `andof` | `Pred × Pred × Pred → Bool` |
| `width` | `Pred → Int` |
| `dom` | `Rel × Pred → Bool` |
| `def` | `Cols → Cols` |
| `acols`, `ucols` | `Int × Cols → Cols`: rename a set's columns `c` to `c#i`, and back, dropping columns without `#i` |
| `upred` | `Int × Pred → Pred`: rename a predicate's columns back |

**Symbol names** are quoted SMT symbols:

| Symbol | Name |
|---|---|
| table `t` | `\|t:t\|` |
| column set | `\|{a,b}\|`, columns sorted |
| atom predicate | `\|p:a>1\|`, always in its positive form |
| compound predicate | `\|p:<text>\|`, its canonical text (§5), e.g. `\|p:foo.a=1 OR foo.a=2\|` |
| constant predicates | `\|p:true\|`, `\|p:false\|` |
| expression column | `c:<text>`, the expression's canonical text, e.g. `\|{c:foo.a%3}\|` |
| aggregate column | `a:<function>`, e.g. `\|{a:count(*)}\|`, `\|{a:max(foo.b)}\|` |
| aliased column | `c#i`, e.g. `\|{foo.a#2}\|` |
| observation | its name with `\|` and `\` replaced |
| occurrence of node `n` in executed plan `q` | `\|o:q#n\|` |
| opaque relation for node `n` of `q` | `\|r:q#n\|` |
| opaque predicate for node `n` of `q` | `\|p:q#n\|` |

## 5. Translating plans to terms

| Plan node | Term |
|---|---|
| `Scan(t)` | `(scan \|t:t\|)` |
| `Filter(a, x)` | `(filter P x)`, where `P` is the atom's predicate, or `(neg P)` if the atom is negated |
| `Project(C, x)` | `(project \|{C}\| x)` |
| `Group(K, x)` | `(group \|{K}\| x)` |
| `Distinct(x)` | `(dedup x)` |
| `Join(kind, on, l, r)` | `(join[on] l r)`, `(ljoin[on] l r)`, `(semi[on] l r)` or `(anti[on] l r)` |
| `Limit(n, x)` | `(limit n x)` |
| `Sort(x)` | `(sort x)` |
| `Union(l, r)` | `(union l r)` |
| `Filter(p, x)`, `p` with OR, IN, NOT or expressions | `(filter P x)` for each conjunct, where `P` is the conjunct's atom or compound predicate |
| A node that uses an expression `e`: a projected column, group key, join key or aggregate argument | `(extend \|{c:e}\| x)` for each expression, directly above `x`, and the node over that |
| `Group(K, A, x)`, when a node above reads aggregates `A' ⊆ A` | `(aggregate \|{K}\| \|{A'}\| x)`; aggregates nothing reads are dropped, and with none left it is `(group \|{K}\| x)` |
| An aggregate with no GROUP BY | `(scalar \|{A'}\| x)` |
| HAVING `p` | `(filter P <aggregate term>)` |
| `a op (y)`, with `y` an uncorrelated scalar subquery with output column `g` | `(cmp_op \|{a}\| <term of y> \|{g}\|)`, with the op as written |
| `IN`, `EXISTS` and their negations over a subquery | the semi or anti join the engine planned. For a null-aware anti join (`NOT IN`) whose right key may be NULL: `(part o (anti[on] l r))`, with a fresh occurrence |
| A correlated subquery the engine did not decorrelate | a fresh `\|r:q#n\|` |

Normalization rules:
- **Predicates:** a predicate MUST be put in negation normal form, with NOT pushed onto atoms and constants folded. An IN list becomes a disjunction of equalities.
- **Conjunctions:** a top-level conjunction MUST be split into a chain of single filters in a canonical order: atoms sorted by column, operator, literal and negation, then compound predicates sorted by their text. This and the rules below are the only normalization. Filter order across chains, pushdown, join order and join side are left to the axioms.
- **Compound predicates:** a conjunct that is not an atom is a compound predicate. Its canonical text has its disjuncts and nested conjuncts flattened, sorted and deduplicated. So `a IN (2, 1)` and `a = 1 OR a = 2` are one constant.
- **Negated operators:** `<`, `<=`, `!=` and `<>` MUST be stored as the negation of `>=`, `>` and `=` respectively, inside compound predicates too. So `a <= 1` becomes `(neg |p:a>1|)`, and an atom and its negation share one predicate constant.
- **Subquery comparisons:** `neg` MUST NOT be applied to a `cmp_op`, since the subquery's value may be NULL. SQL's NOT is pushed into the operator instead: `NOT a > (y)` is `cmp_le`.
- **Expressions:** an expression's canonical text qualifies its columns, sorts the operands of commutative operators, and folds constants. An expression inside a predicate is inlined rather than extended. `WHERE a % 3 > 2` is the compound predicate `|p:foo.a%3>2|` over `foo.a`, and `unfold` (§7.6) relates it to a filter on an extended column.
- **Aliases:** column names MUST be unique within a relation. Two inputs of a join can share a column: in a self-join, a semi join with a subquery on the same table, or two aggregates with the same aggregate. The encoder then wraps the scan or aggregate that introduces the shared column into the right input in `(alias i …)`, with `i = 2, 3, …` in order of appearance in the plan, and renames the columns above it. Two plans MAY number aliases differently; that costs sharing, not soundness.
- **Nullable columns:** §6.2 decides predicate facts over non-NULL values. A predicate that reads a column that may be NULL at that point MUST be a fresh `|p:q#n|` with only its `reads`. A left join's right-side columns are such columns. Engines usually turn such a left join into an inner join first.

**Executed plans** are translated by the same table and rules, with three additions for what a node actually computed:

| Physical node | Term |
|---|---|
| A node that may have stopped early (below a `LIMIT`, or a probe side whose build side was empty), or was pruned by a filter nothing models | `(part \|o:q#n\| x)` |
| A scan with a filter `p` pushed in inexactly | `(opt \|o:q#n\| P x)`. An exactly applied filter is an ordinary `filter`. |
| A scan pruned by a lossless runtime filter from the join `[L=R]` with build side `b` | `(rt[L=R] \|o:q#n\| x b)`, where `b` is the build side's term |
| A node with no translation (unsupported operator, unresolved column or key) | a fresh `\|r:q#n\|`. Nodes above it build on it as usual. |
| A volatile or unresolved predicate | a fresh `\|p:q#n\|`, with `reads` if its columns are known |

- The encoder MUST attribute a runtime filter to the join that built it. If it cannot tell which join that is, it MUST use `part`.
- Applying a runtime filter to the scan rather than to the scan's filters is a choice, and `rt_push_filter` (§7.4) makes either choice equal.
- These rules replace tainting. A node whose rows are unknown still gets its count asserted. The count constrains a term the axioms connect weakly or not at all, so it can never make a bound unsound.

**Example.** `SELECT a, b FROM foo WHERE a > 1 AND b > 2`:
```
(project |{foo.a,foo.b}| (filter |p:foo.b>2| (filter |p:foo.a>1| (scan |t:foo|))))
```
`WHERE b > 2 AND a > 1` gives the same term. A plan that applies `b > 2` first and `a > 1` above it is a different term, which `filter_commute` makes equal.

**Example.** `SELECT a % 3 AS g, count(*) FROM foo WHERE a IN (1, 2) OR b > 5 GROUP BY g HAVING count(*) > 9`:
```
(filter |p:a:count(*)>9|
  (aggregate |{c:foo.a%3}| |{a:count(*)}|
    (extend |{c:foo.a%3}| (filter |p:foo.a=1 OR foo.a=2 OR foo.b>5| (scan |t:foo|)))))
```
**Example.** `SELECT * FROM emp e JOIN emp m ON e.mgr = m.id`:
```
(join[emp.mgr=emp.id#2] (scan |t:emp|) (alias 2 (scan |t:emp|)))
```

## 6. Ground facts

The encoder MUST assert the following, each as a named assertion.

### 6.1 Schema facts (for tables some plan reads)
```
(= (cols (scan |t:foo|)) |{foo.a,foo.b}|)               ; columns
(key (scan |t:bar|) |{bar.k}|)                           ; each key
(fd (scan |t:foo|) |{foo.a}| |{foo.k}|)                  ; each declared FD
(<= (ndv (scan |t:T|) |{A}|) (ndv (scan |t:U|) |{B}|))   ; each FK T.A -> U.B
(nonnull (scan |t:foo|) |{foo.a}|)                       ; each numeric column
(intcol |{foo.a}|)                                       ; each Int column
(dom (scan |t:t|) |p:t.g=0 OR t.g=1 OR t.g=2|)           ; each CHECK constraint, ENUM or BOOLEAN column
(>= (min (scan |t:foo|) |{foo.a}|) 0)                    ; storage statistics' min, as a bound
(<= (max (scan |t:foo|) |{foo.a}|) 99)                   ; storage statistics' max, as a bound
```
A column's type is that of its literals, as for `implies` below: Int unless a literal is a decimal or a string. A small integer type (`TINYINT`, `UTINYINT`) gives its range as two bounds like storage statistics. Storage statistics MUST bound every row the table holds, such as zone maps that widen on writes and never narrow. Sampled or estimated statistics MUST NOT be asserted.

### 6.2 Predicate facts
```
(= (reads |p:foo.a>1|) |{foo.a}|)
(point |p:foo.b=3|)                                      ; equality atoms only
(implies |p:foo.a>5| |p:foo.a>1|)                        ; decided by z3, see below
```
`implies(p, q)` MUST be asserted exactly when `p ∧ ¬q` is unsatisfiable. The check is quantifier-free, over one variable per column of `reads(p) ∪ reads(q)` of that column's type (Int, Real or String), with SQL's semantics for expressions (`%` keeps the dividend's sign; integer division truncates). It runs for every ordered pair of predicates that read a common column. Those predicates are the atoms, their negations, the compound predicates, and the parts of their `orof` and `andof` chains. Disjointness follows: `a > 5` and `a ≤ 1` are disjoint because `implies(a>5, neg(neg(a>1)))`.

The same checks give these facts, which **compound predicates** (§7.5) use:
```
(= |p:foo.a>=2| |p:foo.a>1|)                             ; implies both ways: one constant
(= |p:foo.a%3>2| |p:false|)                              ; unsatisfiable
(= |p:foo.a=1 OR foo.a!=1| |p:true|)                     ; valid
(orof |p:foo.a=1 OR foo.a=2| |p:foo.a=1| |p:foo.a=2|)    ; one link per disjunct, right-nested
(andof |p:foo.a>1 AND foo.b>2| |p:foo.a>1| |p:foo.b>2|)  ; conjunctions inside a disjunction
(= (width |p:foo.a=1 OR foo.a=2|) 2)
```
- **Equalities** replace the `implies` facts between the predicates they merge. Predicates have no `distinct` assertion, so merging is sound.
- **Chains.** A disjunction `p = d₁ ∨ … ∨ dₙ` is asserted as `orof(p, d₁, p₂)`, `orof(p₂, d₂, p₃)`, …, where each `pᵢ` is the compound predicate of the remaining disjuncts, in canonical order. `andof` works the same way.
- **Width.** `width(p) = k` is asserted when `p` is TRUE only if every column it reads is non-NULL, and Z3, enumerating with blocking clauses, finds at most `k ≤ 64` tuples of `reads(p)` that satisfy it. `point(p)` is asserted when `k = 1`.
- **Hull.** For each numeric column `a` that a predicate reads, the encoder computes `lo` and `hi`, the infimum and supremum of `a` under `p`, with Optimize. Both checks are quantifier-free, so the optimum is exact. Strictness is kept, and Int columns are optimized as integers. A side that is unbounded, or that Optimize cannot settle (nonlinear arithmetic), is omitted. The hull defines the predicate's range axiom (§7.3).
- **Subquery comparisons.** `cmp_op` predicates get `reads`. `implies` facts between two of them are asserted only when they share `A`, `y` and `G`, decided with one variable for the subquery's value. That is sound because neither is TRUE when the value is missing.

**Expression and alias facts.** For every expression column and every alias index a plan uses:
```
(= (def |{c:foo.a%3}|) |{foo.a}|)                        ; the columns an expression reads
(intcol |{c:foo.a%3}|)                                   ; an Int-typed expression or count
(= (acols 2 |{emp.id}|) |{emp.id#2}|)  (= (ucols 2 |{emp.id#2}|) |{emp.id}|)
(= (upred 2 |p:emp.id#2>5|) |p:emp.id>5|)
```

### 6.3 Column-set universe
Column sets are finite constants. The universe `U` MUST contain every set that a term, observation, key, FD, join key or predicate mentions, plus every relation's columns, every expression column's `def`, and the image under `acols` and `ucols` of every set, for each alias index a plan uses. It SHOULD be closed, under a cap (800 in the prototype), under unions of non-relation sets that fit inside some relation, and under differences. Over `U`, the encoder asserts:
```
(csub X Y)          for every X ⊆ Y in U
(= (cup X Y) Z)     whenever X ∪ Y = Z is in U
(= (cdiff X Y) Z)   whenever X − Y = Z is in U and nonempty
(distinct ...all of U...)
```
This is bookkeeping, not cardinality reasoning; it lets axioms state set relations without quantifying over sets.

### 6.4 Observations

**Executed plans.** For each node `n` of each executed plan `q` that output `rows` rows:
```
(! (= (card <term of n>) rows) :named |obs:q#n|)
```
That is all the encoder reads off a node's count. It MUST NOT also assert selectivities, match shares or distinct counts derived from the counts: the axioms give them.
- A filter's share is two cards (`filter_sub`, `filter_complement`).
- A semi or anti join's match share is two cards (`semi_basic`, `anti_basic`).
- A group's `ndv` is the group's card (`group_basic`).

**Values a runtime filter printed.** These are facts about the build side `b` and its keys `R`, named `|rtv:q#n|`. They are bounds, because an engine may derive them from statistics:
```
(<= (max b |{R}|) hi)  (>= (min b |{R}|) lo)    ; a range filter lo <= L <= hi
(<= (ndv b |{R}|) k)                             ; an IN list of k values
```

**Counted facts:**
```
(! (= (card <term>) 300) :named obs_Q)
(! (= (ndv <term> |{foo.a}|) 12) :named distinct_a)
(! (key <term> |{K}|) :named unique_x)
(! (= (max <term> |{foo.a}|) 99) :named max_a)
(! (dom <term> |p:foo.g=0 OR foo.g=1 OR foo.g=2|) :named domain_g)       ; a counted SELECT DISTINCT
(! (= (* 60175 (card <σ term>)) (* 10816 (card <term>))) :named share_s)   ; a share num/den, kept linear
```

### 6.5 Probes
The target's root MUST be asserted in the base scope with a trivially true fact, such as `(>= (card t) 0)`. This puts its subterms in the e-graph once, so pattern matching starts before any check rather than repeating inside each `push`. Executed plans' nodes are already in the e-graph through their observations.

### 6.6 Consistency
Observations from different runs can disagree: the data changed, or a translation is wrong. Contradictory facts prove every bound. So before probing, the encoder MUST check `proves(false)`.
- **If it fails** (the check is `sat` or `unknown`), probing proceeds.
- **If it succeeds**, the unsat core names the conflicting observations.
  - The encoder MUST report them.
  - It MUST drop the older run's, or every observation in the core when there is no order, and repeat the check in a fresh session.

The check is best effort, since a contradiction may need more instantiation than one check's timeout allows. A probe that proves both `t ≤ B` and `t ≥ B + 1` exposes a contradiction the check missed. The encoder MUST treat that as a failed consistency check, not as a bound.

## 7. Axioms

### 7.1 Rules every axiom MUST follow

1. **True under §3.**
2. **Explicit patterns** (`:pattern`), and a `:qid` and `:named` equal to the axiom's name, so profiles and unsat cores can cite it.
3. **A trigger is not a guard.** Every atom (`sub`, `key`, `fd`, `implies`, `point`, `csub`, `orof`, `andof`, `dom`) in a pattern MUST also appear as a hypothesis in the body. Pattern matching fires on every matching *term*, including false ones that other axioms' guards create.
   - Counterexample, which was a real bug: `sub_card` written as `(<= (card x) (card y))` with pattern `(sub x y)`. The FK axioms' guard `(sub x T)` creates `sub` terms that are false, so this proves `|(ord ∪ ord) ⋈ cust| ≤ 1999` when the truth is 2000.
4. **No term stacking.** An axiom MUST NOT create a term deeper than its trigger when the result can trigger it, or a commuting axiom, again.
   - Counterexample, which was a real loop: `implies(p, q) ⟹ filter(q, filter(p, x)) = filter(p, x)` triggered on `(implies p q) (filter p x)`. It made 1.08M instantiations and took the filters case to 7–8 s per probe. Instead, relate only terms that exist: trigger on `(implies p q) (filter p x) (filter q x)`, and separately on `(implies p q) (filter q (filter p x))`.
5. **Triggers should not copy terms downward.** For example, `sub_ndv` triggers on `(sub x y) (ndv x W)`, never on `(sub x y) (ndv y W)`. The second creates `ndv` terms on every sub-bag and made the toy 4× slower without tightening any bound.

### 7.2 Catalogue

The prototype's `axioms/` is the reference text for everything except `sub_eq` and §7.3–§7.9, which it does not implement yet.

| | Prototype | This spec |
|---|---|---|
| Shared | 45 | 88: 45, plus `sub_eq`, 8 range (§7.3), 3 physical (§7.4), 8 predicate (§7.5), 6 expression and domain (§7.6), 4 aggregate (§7.7), 8 alias (§7.8) and 5 subquery-comparison (§7.9) axioms |
| Per join family | 25 | 27: 25, plus `inner_range` and `left_range` |
| Per ordered pair of join families | 1 (`assoc`) | 1 |
| Per foreign key | up to 5 | up to 5, plus up to 5 per alias pairing a join family uses (§7.8) |
| Per predicate (an atom, its negation, or a compound predicate) | none | 1, when its hull bounds a numeric column (§7.3) |
| Per runtime-filter family | none | 6 (§7.4) |
| Per runtime-filter family and join, semi or left-join family | none | 1 (`rt_push_join`) |
| Per expression column | none | 1 (`dom[g]`, §7.6) |
| Per expression column and predicate that reads it | none | 1 (`unfold[g,p]`) |
| Per join family and expression column not among its left keys | none | 1 (`extend_join`) |
| Per aggregate column | none | 1 (`agg[c]`, §7.7) |
| Per predicate and count column it bounds from below | none | 1 (`having_count`) |

**Core** (`axioms/core.py`):
```
card_nonneg   card x ≥ 0                                                  [card x]
ndv_range     0 ≤ ndv x W ≤ card x ∧ (card x ≥ 1 ⟹ ndv x W ≥ 1)          [ndv x W]
ndv_mono      csub X Y ⟹ ndv x X ≤ ndv x Y                                [csub X Y, ndv x X, ndv x Y]
ndv_product   ndv x (cup X Y) ≤ ndv x X · ndv x Y                          [ndv x (cup X Y)]
sub_card      sub x y ⟹ card x ≤ card y                                   [sub x y]
sub_ndv       sub x y ⟹ ndv x W ≤ ndv y W                                 [sub x y, ndv x W]
sub_trans     sub x y ∧ sub y z ⟹ sub x z                                 [sub x y, sub y z]
sub_cols      sub x y ⟹ cols x = cols y                                   [sub x y]
sub_eq        sub x y ∧ card x = card y ⟹ x = y                           [sub x y]   (not yet in the prototype)
sub_key       key y K ∧ sub x y ⟹ key x K                                 [key y K, sub x y]
sub_fd        fd y X Y ∧ sub x y ⟹ fd x X Y                               [fd y X Y, sub x y]
key_ndv       key x K ∧ csub K W ⟹ ndv x W = card x                       [key x K, ndv x W]
key_fd        key x K ⟹ fd x K (cols x)                                   [key x K]
fd_trans      fd x X Y ∧ fd x Y2 Z ∧ csub Y2 Y ⟹ fd x X Z                [fd x X Y, fd x Y2 Z]
fd_ndv        fd x X Y ∧ csub X (cdiff W Y) ⟹ ndv x W ≤ ndv x (cdiff W Y)  [fd x X Y, ndv x W]
```

**Filter:**
- `filter_sub`: a filter is contained in its input and has its columns.
- `filter_commute`, `filter_idem`, `filter_mono`.
- `neg_neg`: `neg(neg p) = p`, and a negation reads the same columns.
- `filter_complement`: `card(σ_p x) + card(σ_¬p x) = card x`.
- `filter_incl_excl`: `card(σ_p σ_q x) ≥ card(σ_p x) + card(σ_q x) − card x`.
- `filter_implies`, `filter_redundant` and `filter_disjoint`, as in rule 4.
- `filter_point`: `point p ⟹ ndv(σ_p x, reads p) ≤ 1`.

**Projection and group by:**
- `project_basic`: same `card`; `cols = C`.
- `project_ndv`: the `ndv` of kept columns is unchanged.
- `project_key`, `project_fd`, `project_mono`, `project_pushdown`.
- `group_basic`: `card(group K x) = ndv x K`, `cols = K`, `key (group K x) K`.
- `group_ndv`, `group_fd`, `group_mono`, `group_pushdown`.
- `dedup_def`: `dedup x = group (cols x) x`.

**Join family `[L=R]`** (`J`, `LJ`, `S`, `A`, mirror `M`):
- `inner_basic`:
  - `cols = cup`
  - `card J ≤ card x · card y`
  - `fd J L R` and `fd J R L`
  - `J x y = M y x`
- `inner_keyed`: `key y R ⟹ card(J x y) = card(S x y)`.
- `inner_semi`: `card S ≤ card J`.
- `inner_mono_l`, `inner_mono_r`.
- `inner_vals`: a column set within one side has `ndv` at most that side's.
- `inner_key`, `inner_fd_l`, `inner_fd_r`.
- `inner_push`: a filter moves into whichever side holds its columns.
- `left_basic`: `card LJ = card J + card A`.
- `left_vals`: left columns keep their `ndv`; right columns have at most the right side's `ndv` + 1.
- `left_key`, `left_fd_l`, `left_fd_r`, `left_mono_l`.
- `left_push`: into the left side only.
- `semi_basic`: `S ⊆ x`, `card S + card A = card x`, and `ndv(S, L) ≤ ndv(y, R)`.
- `anti_basic`, `semi_mono_l`, `semi_mono_r`, `anti_mono_l`, `anti_mono_r` (antitone), `semi_push`, `anti_push`.
- `assoc` (one per pair of families `f`, `g`): `(x ⋈f y) ⋈g z` regroups around whichever input holds `g`'s left keys.

**Foreign key `T.A → U.B`.** These are guarded by `x = scan T ∨ sub x (scan T)`:
- `|J x U| = |LJ x U| = |x|`
- `S x U = x`
- `|A x U| = 0`
- `fk_cover`: `ndv(S_mirror U y, B) ≥ ndv(y, A)`

**Misc:**
- `sort x = x`.
- `limit n x ⊆ x`, with `card = min(card x, n)`.
- `union`: `card` sums, each input is contained in the result, same `cols`, `ndv` is at most the sum, and filters push into both inputs.

### 7.3 Value ranges

These are not yet in the prototype, and §11 does not yet cover them. A predicate bounds the values that pass it: `a < X` gives `max(σ x, {a}) < X`. Those bounds flow up and down plans like `ndv` bounds do, and they bound `ndv` and prove filters empty.

**Per literal.** One axiom per literal (an atom or its negation), named after its predicate. Each triggers on `[filter ℓ x]` and bounds `σ_ℓ x`, written `σ` below. On an Int column, the encoder MUST round a strict bound to the adjacent integer, so `a > 1` gives `min ≥ 2`. Otherwise the integer width bound (`range_ndv`) is lost.

| Literal | Axiom |
|---|---|
| `a > v` | `min(σ, {a}) > v` |
| `a >= v` | `min(σ, {a}) ≥ v` |
| `a = v` | `min(σ, {a}) ≥ v ∧ max(σ, {a}) ≤ v` |
| `a <= v`, i.e. `neg(a > v)` | `max(σ, {a}) ≤ v` |
| `a < v`, i.e. `neg(a >= v)` | `max(σ, {a}) < v` |
| `a != v`, i.e. `neg(a = v)` | none |

A one-sided literal also bounds the other side by its input: `max(σ, {a}) ≤ max(x, {a})` for `>` and `>=`, and `min(σ, {a}) ≥ min(x, {a})` for `<=` and `<`. This creates both of `σ`'s range terms, which `range_order` needs. An atom's axiom also states `nonnull(σ, {a})`; a negation's does not, since `neg p` is the complement and keeps NULL rows (§3, rule 6). Because the values of an empty `σ` are `±BIG`, these axioms hold without a `card` guard; `a = v` is two inequalities rather than equalities for the same reason. `BIG` MUST be an integer, so that rounding stays sound on Int columns.

**Per compound predicate.** A compound predicate (§7.5) gets the same axiom, built from its hull (§6.2). For each numeric column `a` it reads, it states:
- `min(σ, {a}) ≥ lo` and `max(σ, {a}) ≤ hi` for each finite side, strict where the hull is;
- the input bound on any side that is not finite;
- `nonnull(σ, {a})` when the predicate is TRUE only if `a` is non-NULL.

It states nothing for a column whose two sides are both unbounded, such as `a` in `a = 1 OR b = 2`. The per-literal table above is the special case of an atom.

**Shared:**
```
range_order   nonnull x C ∧ card x ≥ 1 ⟹ min x C ≤ max x C                    [min x C, max x C]
range_ndv     nonnull x C ∧ intcol C ∧ card x ≥ 1 ⟹ ndv x C ≤ max x C − min x C + 1
                                                                            [intcol C, ndv x C]
range_point   nonnull x C ∧ min x C = max x C ⟹ ndv x C ≤ 1                  [min x C, max x C]
sub_range     sub x y ⟹ min y C ≤ min x C ∧ max x C ≤ max y C                [sub x y, min x C], [sub x y, max x C]
sub_nonnull   sub x y ∧ nonnull y C ⟹ nonnull x C                            [sub x y, nonnull y C, min x C]
```
- `range_order` is what proves emptiness: if `min > max` is entailed, then `card x = 0`.
- `range_ndv` creates `min` and `max` terms on `x` itself, which is no deeper than its trigger. `sub_range` triggers on the sub-bag's term and creates the superset's, the direction rule 5 allows.
- `nonnull` is never needed on its own, so `sub_nonnull` copies it down only to terms that have a range.

**Per operator.** Each states the equalities or inequalities below and carries `nonnull` the same way:
- `project_range`, `group_range`: a kept column has the same `min` and `max` as in the input.
- `union_range`: `min u C` equals `min l C` or `min r C`, and likewise for `max`. The other direction comes from `sub_range`.
- `inner_range` (per join family): a column of one side has `min` at least, and `max` at most, that side's. For a single key pair `l = r`, `min J {l} = min J {r}` and `max J {l} = max J {r}`.
- `left_range` (per join family): left columns keep their `min` and `max`. Right columns are bounded by the right side's, as in `inner_range`, but are not `nonnull`.

Semi joins, anti joins, filters and limits need no axiom of their own: their outputs are sub-bags, so `sub_range` covers them.

### 7.4 Physical operators

These are not yet in the prototype, and §11 does not yet cover them. They let an executed node's count bound the logical rows it stands for, so that no count needs to be dropped.

**Shared:**
```
part_sub      sub (part o x) x                                            [part o x]
opt_sub       sub (opt o p x) x ∧ sub (filter p x) (opt o p x)            [opt o p x]
opt_check     filter p (opt o p x) = filter p x                           [filter p (opt o p x)]
```

**Per runtime-filter family `[L=R]`** (`T` is `rt[L=R]`):
```
rt_sub        sub (T o x b) x                                             [T o x b]
rt_cover      sub (semi[L=R] x b) (T o x b)                               [T o x b]
rt_join       join[L=R] (T o x b) b = join[L=R] x b                       [join[L=R] (T o x b) b]
rt_semi       semi[L=R] (T o x b) b = semi[L=R] x b                       [semi[L=R] (T o x b) b]
rt_push_filter  filter p (T o x b) = T o (filter p x) b                   [filter p (T o x b)]
rt_push_project csub L C ⟹ project C (T o x b) = T o (project C x) b     [project C (T o x b)]
```

**Per runtime-filter family and join family `g`:** a join, semi join or left join with `T`'s output on its left:
```
rt_push_join  g (T o x b) y = T o (g x y) b                               [g (T o x b) y]
```

Notes:
- **What the axioms rely on.** `rt_join`, `rt_semi`, `rt_cover` and the `rt_push_*` axioms are true because `rt` is lossless and decides by `L` alone (§3, rule 9). A runtime filter that isn't lossless is a `part`, which gets only `part_sub`. DuckDB 1.5.0's bloom filters are one such case.
- **The `rt_push_*` axioms move `rt` above whatever sits between it and the join that built it.** That lets `rt_join` meet the plan's own join term. The created term is no deeper than the trigger and never matches the trigger again (rule 4).
- **`sub_eq` removes a physical operator once the counts show it did nothing.** A `part` scan whose count equals the table's is the table. A required filter that an engine derived from statistics (`c_custkey <= 1499`) is dropped once `filter_complement` and the range axioms show its complement is empty.

**Example.** An executed plan joins `orders` with `σ seg=1 customer`. A runtime filter from that join prunes the `orders` scan to 900 rows, and the join outputs 280:
```
(= (card (rt[o_custkey=c_custkey] |o:q#2| (scan |t:orders|) (filter |p:seg=1| (scan |t:customer|)))) 900)
(= (card (join[o_custkey=c_custkey] (rt[...] |o:q#2| (scan |t:orders|) ...) (filter |p:seg=1| (scan |t:customer|)))) 280)
```
- By `rt_join`, the second fact is `|orders ⋈ σ seg=1 customer| = 280`, the same term as a plan without the filter.
- By `rt_cover`, `|orders ⋉ σ seg=1 customer| ≤ 900`.

### 7.5 Compound predicates: OR, IN, NOT and expressions

These are not yet in the prototype. §11 item 7 covers them. Most of a compound predicate's meaning arrives as ground facts that Z3 decided (§6.2): `implies`, merged constants, `width` and its hull. The existing filter axioms then apply unchanged.
- `filter_implies`, `filter_redundant` and `filter_disjoint` prove that `σ a IN (1,2) σ a>5 x` is empty.
- `filter_mono` puts each disjunct under its disjunction: `max(|σ_q x|, |σ_r x|) ≤ |σ_{q∨r} x|`.
- `filter_point` and the range axioms (§7.3) bound `ndv` and values.

The axioms below add what implication cannot express: how a disjunction's count relates to its disjuncts', and what the constant predicates mean.
```
or_split      orof p q r ⟹ card(σ_p x) ≤ card(σ_q x) + card(σ_r x)                 [orof p q r, filter p x]
or_disjoint   orof p q r ∧ implies q (neg r) ⟹ card(σ_p x) = card(σ_q x) + card(σ_r x)
                                                                     [orof p q r, implies q (neg r), filter p x]
or_incl_excl  orof p q r ⟹ card(σ_p x) = card(σ_q x) + card(σ_r x) − card(σ_q σ_r x)
                                                                     [orof p q r, filter p x, filter q (filter r x)]
and_lower     andof p q r ⟹ card(σ_p x) ≥ card(σ_q x) + card(σ_r x) − card x       [andof p q r, filter p x]
and_chain     andof p q r ⟹ filter p x = filter q (filter r x)                       [andof p q r, filter p x, filter q (filter r x)]
filter_false  card(filter |p:false| x) = 0                                           [filter |p:false| x]
filter_true   filter |p:true| x = x                                                  [filter |p:true| x]
filter_width  ndv(σ_p x, reads p) ≤ width p                                          [filter p x, width p]
```
- **Termination.** `or_split` and `or_disjoint` create `σ_q x` and `σ_r x`, which are no deeper than their trigger. Since `r` is the rest of the chain, they fire again at most once per disjunct, and they create no `Pred` terms. `or_incl_excl` and `and_chain` relate only terms that exist (rule 4).
- **Soundness.** In three-valued logic, `q ∨ r` is TRUE exactly when `q` or `r` is TRUE, so `σ_{q∨r} x` is the union of `σ_q x` and `σ_r x`. `filter_width` relies on `width` being asserted only for predicates that reject NULLs (§6.2).
- **IN lists.** An IN list's disjuncts are pairwise disjoint point atoms. So `or_disjoint` makes `|σ a IN (v₁…vₙ) x|` exactly the sum of the `|σ a=vᵢ x|`, and `filter_width` bounds its `ndv` by `n`.

### 7.6 Expression columns and value domains

These are not yet in the prototype. §11 item 7 covers them.

**Value domains.** A domain fact `dom(x, d)` says that every row of `x` satisfies `d`. Schema facts (§6.1) and counted facts (§6.4) assert them. They reach every axiom that has `d` as a filter:
```
dom_filter    dom x d ⟹ filter d x = x                                               [dom x d]
dom_sub       dom x d ∧ sub z x ⟹ dom z d                                            [dom x d, sub z x, filter q z]
```
Once `filter d x = x`, every `filter q x` is also `filter q (filter d x)`, so the following hold without new terms:
- `d`'s range axiom (§7.3) bounds `min` and `max` of `x`.
- `filter_width` bounds `ndv(x, reads d)`.
- `filter_disjoint` empties `σ_q x` whenever `implies(d, neg q)`. That reaches past ranges: the domain `a % 5 = 0` empties `a = 7`.

`dom_sub` copies a domain only to sub-bags that something filters, which is the direction rule 5 allows. A domain needs no other source: `sub_eq` already makes an observed filter that kept every row equal to its input.

**Expression columns.** For `g` an expression column with `def g = D`:
```
extend_basic  card(extend g x) = card x ∧ cols(extend g x) = cup (cols x) g ∧ fd (extend g x) D g
                                                                                      [extend g x]
extend_ndv    csub W (cols x) ⟹ ndv(extend g x, W) = ndv(x, W)                       [ndv (extend g x) W]
extend_carry  key x K ⟹ key (extend g x) K                                           [key x K, extend g x]
              fd x X Y ⟹ fd (extend g x) X Y                                         [fd x X Y, extend g x]
              csub C (cols x) ⟹ min (extend g x) C = min x C ∧ max (extend g x) C = max x C
                                ∧ (nonnull x C ⟹ nonnull (extend g x) C)            [min (extend g x) C], [max (extend g x) C]
extend_push   csub (reads p) (cols x) ⟹ filter p (extend g x) = extend g (filter p x)   [filter p (extend g x)]
```
`ndv` over sets containing `g` follows from the FD: `fd_ndv` drops `g` from any set that holds `D`, and `ndv_product` bounds the rest.

**Per expression column** (`dom[g]`). The encoder decides the expression `e` over its inputs' types, as for `implies` (§6.2), and states what it found, triggered on `[extend g x]`:

| When | Axiom |
|---|---|
| `e`'s values have a finite infimum `lo` or supremum `hi` | `min(extend g x, g) ≥ lo`, `max(extend g x, g) ≤ hi` |
| `e` takes at most `k ≤ 64` values | `ndv(extend g x, g) ≤ k + 1`, and `≤ k` when `nonnull(extend g x, g)` |
| `e` is total: non-NULL on non-NULL inputs (`+ − *`, and `/` or `%` by a nonzero constant) | `nonnull x {a}` for each `a ∈ D` ⟹ `nonnull(extend g x, g)` |
| `e = c·a + d` with `c > 0` (or `c < 0`, with `min` and `max` swapped) | `card x ≥ 1 ∧ nonnull x {a} ⟹ min(extend g x, g) = c·min(x, {a}) + d ∧ max(…) = c·max(x, {a}) + d` |

So `g = a % 3` gets `−2 ≤ g ≤ 2` and `ndv ≤ 5`, from types alone. The bounds hold unguarded because an empty `x` has `±BIG` ranges (§3, rule 8). The affine rule needs its guard, because `c·BIG + d` is not `BIG`.

**Per expression column and predicate** (`unfold[g,p]`), for each predicate `p` that reads `g`. Let `p'` be `p` with `e` substituted for `g`. `p'` is a compound predicate over `(reads p − g) ∪ D`, with the usual facts.
```
unfold[g,p]   csub (reads p') (cols x) ⟹ filter p (extend g x) = extend g (filter p' x)   [filter p (extend g x)]
```

**Per join family `[L=R]` and expression column `g ∉ L`** (`extend_join`). The expression moves above the join:
```
extend_join   J (extend g x) y = extend g (J x y), and likewise for LJ, S and A              [J (extend g x) y], …
```
The mirror family gives the right side. Each created term is no deeper than its trigger.

### 7.7 Aggregates and HAVING

These are not yet in the prototype. §11 item 7 covers them.
```
agg_basic     project K (aggregate K G x) = group K x ∧ cols(aggregate K G x) = cup K G
              ∧ key (aggregate K G x) K                                               [aggregate K G x]
agg_push      csub (reads p) K ⟹ filter p (aggregate K G x) = aggregate K G (filter p x)   [filter p (aggregate K G x)]
scalar_basic  card(scalar G x) = 1 ∧ cols(scalar G x) = G                             [scalar G x]
one_row       card y = 1 ∧ nonnull y C ⟹ min y C = max y C                            [min y C, max y C]
```
`agg_basic` makes the aggregate's count, keys' `ndv` and keys' ranges those of `group K x`, through `project_basic`, `project_ndv` and `project_range`. A HAVING filter is a sub-bag of it, by `filter_sub`. `agg_push` is true because a predicate on the keys keeps or drops whole groups.

**Per aggregate column** (`agg[c]`), for `r` either `aggregate K G x` or `scalar G x`, with hypothesis `csub c G`, triggered on `[r]`:

| `c` | Axiom |
|---|---|
| `count(*)` | `nonnull(r, c)`. In `aggregate`: `min(r, c) ≥ 1 ∧ max(r, c) ≤ card x`. In `scalar`: `min(r, c) = max(r, c) = card x` |
| `count(a)` | `nonnull(r, c) ∧ min(r, c) ≥ 0 ∧ max(r, c) ≤ card x` |
| `min(a)` | `min(r, c) = min(x, {a}) ∧ max(r, c) ≤ max(x, {a}) ∧ ndv(r, c) ≤ ndv(x, {a})` |
| `max(a)` | `max(r, c) = max(x, {a}) ∧ min(r, c) ≥ min(x, {a}) ∧ ndv(r, c) ≤ ndv(x, {a})` |
| `avg(a)` | `min(r, c) ≥ min(x, {a}) ∧ max(r, c) ≤ max(x, {a})` |
| anything else (`sum`, …) | none: the column exists only for predicates to read |

Each holds on an empty `x` through `±BIG`. A group whose `a` is all NULL has a NULL `min(a)`, which affects neither side's `min`, and adds NULL to both sides' `ndv`.

**Per predicate and count column** (`having_count`). Take a predicate `ℓ` whose hull gives a `count(*)` or `count(a)` column `c` an integer lower bound `lo ≥ 1`:
```
having_count  csub c G ⟹ lo · card(filter ℓ (aggregate K G x)) ≤ card x               [filter ℓ (aggregate K G x)]
```
Groups are disjoint, and their counts sum to at most `card x`, so at most `card x / lo` groups can have a count of `lo` or more. `lo` is a constant, so the axiom is linear. The complementary lower bound on groups with smaller counts follows from `filter_complement`.

### 7.8 Aliases and self-joins

These are not yet in the prototype. §11 item 7 covers them. An alias carries everything about its input across the renaming:
```
alias_basic    card(alias i x) = card x ∧ cols(alias i x) = acols i (cols x)          [alias i x]
alias_ndv      ndv(alias i x, W) = ndv(x, ucols i W)                                  [ndv (alias i x) W]
alias_range    csub W (cols (alias i x)) ⟹ min(alias i x, W) = min(x, ucols i W) ∧ max(alias i x, W) = max(x, ucols i W)
               ∧ (nonnull x (ucols i W) ⟹ nonnull (alias i x) W)                    [min (alias i x) W], [max (alias i x) W]
alias_key      key x K ⟹ key (alias i x) (acols i K)                                 [key x K, alias i x]
alias_fd       fd x X Y ⟹ fd (alias i x) (acols i X) (acols i Y)                     [fd x X Y, alias i x]
alias_push     csub (reads p) (cols (alias i x)) ⟹ filter p (alias i x) = alias i (filter (upred i p) x)
                                                                                      [filter p (alias i x)]
alias_project  csub C (cols (alias i x)) ⟹ project C (alias i x) = alias i (project (ucols i C) x)
                                                                                      [project C (alias i x)]
alias_group    csub K (cols (alias i x)) ⟹ group K (alias i x) = alias i (group (ucols i K) x)
                                                                                      [group K (alias i x)]
```
- `alias_ndv` needs no hypothesis. `ucols` drops the columns that lack `#i`, and those are exactly the columns `ndv` ignores (§3, rule 3).
- The push axioms move `alias` above filters, projections and groups. A filtered self-join side then shares its term with the unaliased plans that observed it.

**Foreign keys.** For an FK `T.A → U.B` and each join family that pairs an alias of `T` with an alias of `U`, the encoder instantiates the FK axioms (§7.2) with the aliased tables and keys. One of the two may be unaliased. The guard becomes `x = alias i (scan T) ∨ sub x (alias i (scan T))`. A self-referencing FK such as `emp.mgr → emp.id` needs this.

### 7.9 Scalar subqueries

These are not yet in the prototype. §11 item 7 covers them. A comparison with a subquery bounds the filtered relation's range by the subquery's own `min` and `max`. With `σ = filter (cmp_op A y G) x`, each axiom triggers on `[filter (cmp_op A y G) x]`:
```
cmp_gt   min(σ, A) > max(y, G) ∧ max(σ, A) ≤ max(x, A) ∧ nonnull(σ, A)
         ∧ (intcol A ∧ intcol G ⟹ min(σ, A) ≥ max(y, G) + 1)
cmp_ge   min(σ, A) ≥ max(y, G) ∧ max(σ, A) ≤ max(x, A) ∧ nonnull(σ, A)
cmp_lt   max(σ, A) < min(y, G) ∧ min(σ, A) ≥ min(x, A) ∧ nonnull(σ, A)
         ∧ (intcol A ∧ intcol G ⟹ max(σ, A) ≤ min(y, G) − 1)
cmp_le   max(σ, A) ≤ min(y, G) ∧ min(σ, A) ≥ min(x, A) ∧ nonnull(σ, A)
cmp_eq   min(σ, A) ≥ min(y, G) ∧ max(σ, A) ≤ max(y, G) ∧ ndv(σ, A) ≤ 1 ∧ nonnull(σ, A)
```
- **Why `min` and `max` of `y`.** When `y` has one non-NULL row, both are its value, by `one_row`. When `y` is empty, has a NULL value, or has several rows, `σ` is empty (§3, rule 14), and `σ`'s range is `+BIG` to `−BIG`. Each inequality then holds whatever `y`'s range is. So the axioms need no guard.
- **What they connect to.** The value is a term like any other: `y`'s observations, and `agg[c]` when `y` is an aggregate, bound it. Comparing with `!=` gets no axiom, as for literals.

## 8. Solver configuration

| Mode | Options | Quantifiers | Use |
|---|---|---|---|
| Pattern (default) | `smt.auto_config=false`, `smt.mbqi=false`, `produce-unsat-cores=true`, `timeout=1000` per check | ∀-axioms, matched by pattern | everything |
| Ground | default auto_config | none: Python instantiates the axiom text over an e-graph (`ground.py`) | cross-checking; exact Optimize |

Pattern mode MUST NOT use model-based quantifier instantiation (MBQI). Under it, false claims return `unknown`, never `sat`.

Ground mode gave identical bounds on all 35 probes compared. Its eager grounding was 3–80× slower: 47k instances, 26 MB of SMT and 75 s of setup for the toy.

## 9. Bound extraction: optimize, then confirm

The bound is defined by entailment: `upper(t) = min { B : axioms ∧ facts ⊨ t ≤ B }`, and `lower` likewise with `≥`. That is a question about all models, so no single satisfiability query answers it. The optimizer proposes a value and UNSAT checks certify it.

```
proves(φ)   := push; assert ¬φ; check-sat = unsat; pop
candidate(t, sense) := push; (maximize|minimize t); check-sat; get-objectives; pop

upper(t):
    v := candidate(t, maximize)
    if v = oo:            return none if not proves(t ≤ 2^30) else binary_search_upper(t)
    if proves(t ≤ v):
        if not proves(t ≤ v − 1): return v            ; 2 checks, exact
        else: binary search on [0, v − 1]             ; v was loose
    else: exponential search upward from v, then binary search
lower(t): symmetric, with minimize and t ≥ v
```

- **Order:** the consistency check (§6.6) runs first, then the target root's `upper` and `lower`. Executed plans' nodes are never probed.
- **Soundness:** `v` is returned only after `proves(t ≤ v)`. The optimizer's own result is `unknown` in pattern mode, and z3 warns that optimization with quantified constraints is unsupported, so its value is never trusted alone.
- **Exactness:** provability is monotone in `B`. So `proves(t ≤ v) ∧ ¬proves(t ≤ v − 1)` means `v` is exactly what binary search returns.
- **Fallback:** if a confirmation check fails, the search resumes from `v`; that is never worse than binary search over `[0, 2^30]`.
- **Ground mode:** there are no quantifiers, so Optimize returns `sat` with the certified optimum. The confirmation checks MAY be skipped, provided the instances are linear. Products such as `card x · card y` make them nonlinear, and z3's optimizer is only reliable on linear arithmetic.
- **Proof:** after the upper bound is found, `(assert (! (not (<= t v)) :named goal))`, then `check-sat` and `get-unsat-core`. The core lists the axioms and observations that proved it.

Measured against binary search, in pattern mode:

| | Agree | Work per probe | Time per probe |
|---|---|---|---|
| 6 cases, 35 probes | 35/35 | 2 Optimize calls + 4 checks, vs 61 checks | 0.01–0.11 s, vs 0.03–0.49 s |
| TPC-H leave-one-out, 38 probes | 38/38 (lineitem: no upper bound in both) | same | ~1.1 s, vs ~3.8 s |

## 10. Worked examples

### 10.1 R ⊆ Q, end to end
This runs as-is in `z3`. It is a subset of the axioms, enough for this query.

```smt2
(set-option :produce-unsat-cores true)
(set-option :smt.auto_config false) (set-option :smt.mbqi false) (set-option :timeout 1000)
(declare-sort Rel 0) (declare-sort Pred 0) (declare-sort Cols 0) (declare-sort Table 0)
(declare-fun scan (Table) Rel) (declare-fun filter (Pred Rel) Rel) (declare-fun project (Cols Rel) Rel)
(declare-fun card (Rel) Int) (declare-fun cols (Rel) Cols) (declare-fun sub (Rel Rel) Bool)

; Axioms: written once, for every query.
(assert (! (forall ((x Rel)) (! (>= (card x) 0) :pattern ((card x)) :qid card_nonneg)) :named card_nonneg))
(assert (! (forall ((x Rel) (y Rel)) (! (=> (sub x y) (<= (card x) (card y)))
                                       :pattern ((sub x y)) :qid sub_card)) :named sub_card))
(assert (! (forall ((x Rel) (y Rel) (z Rel)) (! (=> (and (sub x y) (sub y z)) (sub x z))
                                       :pattern ((sub x y) (sub y z)) :qid sub_trans)) :named sub_trans))
(assert (! (forall ((p Pred) (x Rel)) (! (and (sub (filter p x) x) (= (cols (filter p x)) (cols x)))
                                       :pattern ((filter p x)) :qid filter_sub)) :named filter_sub))
(assert (! (forall ((C Cols) (x Rel)) (! (and (= (card (project C x)) (card x)) (= (cols (project C x)) C))
                                       :pattern ((project C x)) :qid project_basic)) :named project_basic))

(declare-const |t:foo| Table) (declare-const |{foo.a,foo.b}| Cols)
(declare-const |p:foo.a>1| Pred) (declare-const |p:foo.b>2| Pred)

; Observation: Q = SELECT a, b FROM foo WHERE a > 1 returned 300 rows.
(assert (! (= (card (project |{foo.a,foo.b}| (filter |p:foo.a>1| (scan |t:foo|)))) 300) :named obs_Q))

; Probe: R = SELECT a, b FROM foo WHERE a > 1 AND b > 2.
(define-fun R () Int (card (project |{foo.a,foo.b}| (filter |p:foo.b>2| (filter |p:foo.a>1| (scan |t:foo|))))))
(assert (>= R 0))

(push) (maximize R) (check-sat) (get-objectives) (pop)                            ; candidate
(push) (assert (! (not (<= R 300)) :named goal)) (check-sat) (get-unsat-core) (pop)  ; confirm
(push) (assert (not (<= R 299))) (check-sat) (pop)                                  ; tightness
```
Output:
```
WARNING: optimization with quantified constraints is not supported
unknown
(objectives ((card (project ... (filter |p:foo.b>2| (filter |p:foo.a>1| ...)))) 300))
unsat
(sub_card goal filter_sub project_basic obs_Q)
unknown
```
So `|R| ≤ 300`. The proof uses projection's equal row count and `filter_sub`'s `R' ⊆ Q'`; `R ⊆ Q ⟹ |R| ≤ |Q|` is `sub_card`, stated once rather than per plan.

### 10.2 Facts from another query, and an FD chain
- **Schema:** `foo(a, k)` with FD `a → k`; `bar(k, c)` with key `k`.
- **Observations:**
  - `|foo| = 1000`, `|bar| = 50`
  - `|σ a>1 foo| = 300`, `|σ c>0 bar| = 10`
  - `|foo ⋈ σ c>0 bar| = 150`
  - `ndv(σ a>1 foo, a) = 12`
- **Target:** `J = σ a>1 foo ⋈[foo.k=bar.k] σ c>0 bar`.

```
J            = (join[foo.k=bar.k] (filter |p:foo.a>1| (scan |t:foo|)) (filter |p:bar.c>0| (scan |t:bar|)))
GROUP BY a,c = (group |{bar.c,foo.a}| J)
```

| Probe | Bound | Core |
|---|---|---|
| `\|J\|` | ≤ 150 | `inner_basic` (`J` equals its mirror), the mirror's `inner_mono_r` with `filter_sub` (`σ a>1 foo ⊆ foo`, so `J ⊆ foo ⋈ σ c>0 bar`), `sub_card`, the 150 observation |
| `\|GROUP BY a\|` | ≤ 12 | `group_basic`, `inner_vals` (`ndv(J, a) ≤ ndv(σ a>1 foo, a)`), the 12 observation |
| `\|GROUP BY a, c\|` | ≤ 12 | `fd0_foo`, `key_bar`, `key_fd`, `inner_fd_l`, `sub_fd`, `fd_trans` (`a → k`, `k → {k,c}`), `fd_ndv` (`cdiff({a,c}, {k,c}) = {a}`) |
| same, plan with filters above the join | ≤ 150 | `inner_push` makes it the same term as `J` |
| `\|GROUP BY a, c\|` without FD axioms | ≤ 120 | `ndv_product`: 12 · 10 |

### 10.3 A derivation the encoder never spelled out
- **Schema:** `cust(id key, seg)`, `ord(id key, cust)`, without the FK axioms.
- **Observations:** `|cust| = 100`, `|σ seg=1 cust| = 30`, `|ord ⋈ σ seg=1 cust| = 280`, `ndv(ord, cust) = 70`.
- **Probe:** `card(ljoin[cust.id=ord.cust] cust ord)`.

The lower bound is 350, because Z3 combined five axioms:
1. `filter_complement` splits the left join by `seg = 1`.
2. `left_push` turns `σ seg=1 (cust ⟕ ord)` into `σ seg=1 cust ⟕ ord`.
3. `left_basic` makes that `join + anti`. The join is the mirror of the observed 280-row join (`inner_basic`).
4. The `seg ≠ 1` part keeps all its customers, via `inner_semi` (`semi ≤ join`) and `semi + anti = left`. That gives at least 100 − 30 = 70.
5. 280 + 70 = 350.

### 10.4 TPC-H: a foreign key pins an anti join
With fact *customer anti orders* left out, its term is `(anti[c_custkey=o_custkey] (scan |t:customer|) (scan |t:orders|))`. It is bounded to exactly `[500, 500]`, matching the truth, by:
- `fk_cover`: the FK `o_custkey → c_custkey` gives `ndv(customer ⋉ orders, c_custkey) ≥ ndv(orders, o_custkey) = 1000`.
- `semi_basic`: that `ndv` is also at most 1000.
- customer's key makes the semi join's row count equal that `ndv`.
- `anti_basic`: `1500 − 1000`.

### 10.5 Value ranges
- **Schema:** `foo(a Int)`.
- **Observation:** `max(foo, {a}) = 3`.

| Probe | Bound | Derivation |
|---|---|---|
| `\|σ a≥5 foo\|` | = 0 | the literal axiom gives `min(σ, {a}) ≥ 5`, `max(σ, {a}) ≤ max(foo, {a}) = 3` and `nonnull(σ, {a})`, so `range_order` forces `card σ = 0` |
| `ndv(σ a<5 σ a>1 foo, {a})` | ≤ 3, without the observation | `range_ndv` creates the outer filter's range. Its literal gives `max ≤ 4`, and `sub_range` gives `min ≥ 2` from the inner filter: `4 − 2 + 1` |

### 10.6 Negative controls a conforming encoding MUST NOT prove
```
|σ a>1 foo| ≤ 299                when |σ a>1 foo| = 300 is observed
|(ord ∪ ord) ⋈ cust| ≤ 1999       true value 2000; catches unguarded triggers (rule 3)
|σ a IN (1,2) foo| ≤ 64           when |σ a=1 foo| = 40 and |σ a=2 foo| = 25 are observed
|scalar {a:count(*)} (σ a>1 foo)| ≤ 0
                                  when |σ a>1 foo| = 0 is observed; with no GROUP BY there is one row
|GROUP BY a % 3| ≤ 3              with nothing known about a's sign; SQL's % keeps the dividend's sign
|σ b>1 OR b<=1 (foo ⟕ bar)| ≥ |foo ⟕ bar|
                                  b is bar's column; NULL rows fail both disjuncts (§5, nullable columns)
```

### 10.7 Value domains
- **Schema:** `foo(a Int)`; `t(g Int)` with `CHECK (g IN (0, 1, 2))`, or storage statistics `0 ≤ g ≤ 2`.
- **Observations:** none.

| Probe | Bound | Derivation |
|---|---|---|
| `\|σ a%3>2 foo\|` | = 0 | Z3 finds the predicate unsatisfiable, so it is `\|p:false\|` (§6.2), and `filter_false` applies |
| `\|σ g>2 (SELECT a % 3 AS g FROM foo)\|` | = 0 | `unfold[g, g>2]` turns it into the probe above. Without `unfold`, `dom[g]` gives `max ≤ 2`, the literal gives `min ≥ 3`, and `range_order` empties it |
| `\|GROUP BY a % 3\|` | ≤ 5 | `group_basic`, then `dom[g]`: `a % 3` has 5 values, and `nonnull` because `%` by a constant is total |
| `\|σ g>2 t\|` | = 0 | `dom_filter` makes `t` its own filter by the domain, and `filter_disjoint` applies since `implies(d, neg(g>2))`. Storage statistics instead give `max(t, {g}) ≤ 2` and `range_order` |
| `ndv(t, {g})` | ≤ 3 | `filter_width` on `σ_d t = t` |

The last two close the harness's `σ g>2` gap (§12 before this change: truth 0, bound 93) whenever `g`'s domain is declared or in storage statistics.

### 10.8 OR and IN
- **Schema:** `foo(a Int)`.
- **Observations:** `|foo| = 1000`, `|σ a=1 foo| = 40`, `|σ a=2 foo| = 25`.

| Probe | Bound | Derivation |
|---|---|---|
| `\|σ a IN (1,2) foo\|` | = 65 | `or_disjoint`, since `implies(a=1, neg(a=2))` |
| `\|σ a NOT IN (1,2) foo\|` | = 935 | NNF makes it the chain `σ ¬a=1 σ ¬a=2`. Then `filter_complement` (975 rows survive `¬a=2`), and `filter_commute` with `filter_redundant` (40 of those are `a=1`) |
| `ndv(σ a IN (1,2) foo, {a})` | ≤ 2 | `filter_width` |
| `\|σ a IN (1,2) σ a>5 foo\|` | = 0 | `filter_disjoint`, from `implies` decided over the compound predicate |

### 10.9 HAVING
- **Schema:** `foo(k, v)`.
- **Observations:** `|foo| = 1000`.
- **Target:** `SELECT k, count(*) FROM foo GROUP BY k HAVING count(*) > 9`:
```
(filter |p:a:count(*)>9| (aggregate |{foo.k}| |{a:count(*)}| (scan |t:foo|)))
```

| Probe | Bound | Derivation |
|---|---|---|
| card | ≤ 100 | `having_count` with `lo = 10`: `10 · card ≤ 1000` |
| card, with `ndv(foo, {k}) = 40` observed | ≤ 40 | `filter_sub`, `agg_basic`, `group_basic` |
| card with `HAVING count(*) > 1000` | = 0 | `agg[count(*)]` gives `max ≤ card x = 1000`, the literal gives `min ≥ 1001`, and `range_order` empties it |

### 10.10 Self-join
- **Schema:** `emp(id key, mgr)`, FK `emp.mgr → emp.id`.
- **Observations:** `|emp| = 500`.
- **Target:** `(join[emp.mgr=emp.id#2] (scan |t:emp|) (alias 2 (scan |t:emp|)))`.

| Probe | Bound | Derivation |
|---|---|---|
| card | = 500 | the FK axioms instantiated for `alias 2 (scan emp)` (§7.8): `\|J x U\| = \|x\|` |
| card, without the FK | ≤ 500 | `alias_key` gives `key(alias 2 emp, {emp.id#2})`; then `inner_keyed` (`= card` of the semi join) and `semi_basic` (`⊆ emp`) |

### 10.11 Scalar subqueries
- **Schema:** `foo(a Int)`.
- **Observations:** none.
- **Target:** `SELECT * FROM foo WHERE a > (SELECT max(a) FROM foo)`:
```
y = (scalar |{a:max(foo.a)}| (scan |t:foo|))
(filter (cmp_gt |{foo.a}| y |{a:max(foo.a)}|) (scan |t:foo|))
```

| Probe | Bound | Derivation |
|---|---|---|
| card | = 0 | `cmp_gt`: `min(σ, a) > max(y, m)` and `max(σ, a) ≤ max(foo, a)`. `agg[max(a)]`: `max(y, m) = max(foo, a)`. Then `nonnull(σ, a)` and `range_order` |
| `ndv(σ, {a})` with `=` instead of `>` | ≤ 1 | `cmp_eq` |

## 11. Conformance

An implementation conforms when it meets all of the following.

1. **Cases** (`solve.py`, `cases/`): all 35 probes, 2 claims and 4 ablations meet their stated bounds.
2. **TPC-H** (`solve.py realistic/`):
   - With all facts given, all 27 facts are pinned exactly.
   - With each fact left out, its bounds contain the truth. The bounds in `RESULTS.md` §4 are the reference; 11 are exact.
3. **Soundness harness** (`check.py --seed 1 2 3 --queries 30`): no proven bound excludes the true count, and the axioms plus true facts are never contradictory (`proves(false)` fails).
4. **Static check:** every pattern atom appears in its axiom's body (rule 3).
5. **Optimize-then-confirm** returns the same bound as binary search on every probe above.
6. **Executed plans as observations** (once §7.4 is implemented):
   - The harness feeds each held-out query's executed sibling plans, with every node's count, and probes only the held-out root. The siblings include plans with a `LIMIT`, which become `part`.
   - Item 3 holds with these observations.
   - `proves(false)` fails on the true counts, and succeeds when one count is altered. Its core then names the altered observation.
7. **Predicates, expressions, aggregates, aliases and subqueries** (once §7.5–§7.9 are implemented):
  - Examples 10.7–10.11 meet their stated bounds, and none of §10.6's controls is proven.
  - The soundness harness (item 3) also generates queries with these features. They include OR and IN predicates; expressions in predicates, projections, group keys and join keys; HAVING on counts and keys; self-joins; and uncorrelated scalar subqueries, including empty ones. Item 3 holds on them.
  - The predicate facts of §6.2 (`implies`, merged constants, `width`, hulls) and each expression's `dom[g]` agree with brute-force evaluation over a sample of values, including NULLs where §5 allows them.
  - Item 4's static check covers the generated axioms (`dom[g]`, `unfold[g,p]`, `agg[c]`, `having_count`, and the per-predicate range axioms).

### 11.1 Migration from `src/facts`
Executed plans as observations take over most of the reading side:
- **No longer needed:** the fact rules (`rules.rs`), context normalization (`context.rs`, `rewrite.rs`, `canonical.rs`), the `State`, `Pending` and `Taint` bookkeeping, `derive.rs`, and `Conflict`.
- **Still needed:**
  - Translating each engine's profile into plans and physical annotations (`observed/*`).
  - Attributing each runtime filter to the join that built it.
  - `sql.rs`, to count facts no plan ran.

## 12. Out of scope

- **Degree statistics:** rows per join key. Without them, lineitem has no upper bound when its own facts are removed.
- **Value domains no source states:** domains learned from samples, histograms or estimates. Only declared domains, sound storage statistics, counted facts and derived domains (§7.6) are asserted.
- **Expressions Z3 cannot decide:** user-defined, volatile or nondeterministic functions. Such an expression is still an expression column, with `extend_basic`'s FD, but it gets no `dom[g]`. A predicate using one is opaque (§5).
- **Aggregates beyond `count`, `min`, `max` and `avg`:** a `sum` column's values are not bounded, so HAVING on a sum is only a sub-bag of its groups.
- **Subqueries the engine leaves correlated, `ANY` and `ALL` comparisons, window functions and LATERAL:** these become opaque terms (§5). Their counts are asserted, but nothing connects them to other plans.
- **Predicates over a left join's right-side columns:** these are opaque (§5, nullable columns). Facts that hold in three-valued logic over nullable columns would need NULL-aware decisions in §6.2.
- **Symmetric self-joins:** two plans that number the same self-join's aliases differently get different terms. Each still gets every base-table fact through §7.8.
- Selectivities and match shares as inputs. Plans give counts, and the axioms derive shares. A counted share is asserted in linear form (§6.4).
