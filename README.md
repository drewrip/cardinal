# cardinal

Statically proves claims about a SQL query's output cardinality, with no data.

```rust
let a = cardinal::analyze_sql(&ctx, sql).await?;
a.verdict;          // Reduces | MightGrow(counterexample) | Unknown
a.bounds()?;        // e.g. "X <= |nation|; X <= 1/2·Σ"
a.validate(&ctx).await?;  // check the constraints against real data
```

Requires Z3 (`brew install z3`; paths in `.cargo/config.toml`).

## How it works

1. DataFusion parses and optimizes the SQL into a `LogicalPlan`.
2. The plan is walked bottom-up. Each operator gets a Z3 integer for its
   output cardinality (`op{n}_{kind}`), and one per output column bounding
   its number of distinct values, or NDV (`op{n}_{kind}_c{j}`, NULL counts as one value).
   Each base table gets `T{n}_{name}`.
3. Each operator adds constraints relating its variables to its inputs'
   (rules below).
4. Z3 answers two questions about the root's cardinality `X`:
   - **Verdict**: `Reduces` if `X <= Σ` is proven, where `Σ` is the sum of
     rows read by every base-table scan. `MightGrow` if Z3 finds a
     counterexample: either the query really can grow its input, or the
     constraints can't rule it out.
   - **Bounds**: the tightest proven `X <= N` (constant), `X <= c·|T| + d`
     per table (`=` if exact), and `X <= c·Σ + d`. The coefficient `c` is a
     fraction `p/q` with `q <= 12`, and `c < 1` is a proven reduction factor.

Only scans of tables registered in the context count as base tables. Every
spelling of a name maps to one table. Table functions and recursive-CTE work
tables are not counted.

## Rules

Notation: `l` and `r` are the input cardinalities, and `X` is the output cardinality.
Every relation also gets:

- `0 <= ndv <= X`, and `X >= 1 → ndv >= 1`.
- Boolean columns: `ndv <= 3`.
- A column that traces to a declared primary key: `ndv = X`.

| Operator | Cardinality | NDV |
|---|---|---|
| Table scan of `T` | `X = \|T\|`. Composite PK: `X <= Π ndv(pk)` | `<= X` |
| Pushed-down scan filters | `X <= scan` (a scan's `fetch` is a hint: no bound) | `<=` input |
| Projection | `X = l` | Column or injective cast: `=`. Deterministic expression: `<= Π ndv(referenced columns)`. Literal: `<= 1` |
| Filter | `X <= l` | `<=` input. `a = b`: equal, `<=` the other's input. See value domains below |
| Alias, Repartition, Window, Subquery | `X = l` | `=` input (window columns `<= X`) |
| Sort | `X = l`. With fetch `n`: `X = min(n, l)` | `=` / `<=` |
| Limit (skip `k`, fetch `n`) | `X = min(n, max(l − k, 0))` | `<=` |
| Distinct | `X <= l`, `X <= Π ndv`, `l >= 1 → X >= 1`. Unique input: `X = l` | `=` input |
| Distinct On | `X <= l`, `X <= Π ndv(on)`, `l >= 1 → X >= 1` | `<=` |
| Aggregate, no GROUP BY | `X = 1` | |
| GROUP BY | `X <= l`, `X <= Π ndv(keys)`, `l >= 1 → X >= 1`. Keys cover a unique key: `X = l` | Keys: `=` expression's NDV |
| ROLLUP / CUBE / GROUPING SETS | none | |
| Inner join | `X <= l·r`. Right key unique: `X <= l`. Left key unique: `X <= r`. Cross join: `X = l·r`. On a foreign key from the left: `X = l` (mirror) | Columns `<=` input. Equi-keys `<=` the other side's key NDV |
| Left join | Right key unique: `X = l`. Else `l <= X <= inner + l`. Exactly `X = i + l − mₗ` (below) | Left `=`, right `<= ndv + 1` |
| Right join | Mirror of left | Mirror |
| Full join | `X >= l`, `X >= r`, `X <= inner + l + r`. Either key unique: `X <= l + r`. Exactly `X = i + l − mₗ + r − mᵣ` | Both sides `<= ndv + 1` |
| Semi / anti join | `X <=` kept side. On a foreign key from the kept side: semi `X =` kept side, anti `X = 0`. Anti: `X = l − mₗ` | `<=`. Semi: equi-key `<=` other side |
| Mark join | `X =` kept side | `=` |
| Union | `X = Σ inputs` | `<= Σ`, `>=` each input |
| Values | `X = rows` | Domain: the literals |
| Empty relation | `X = 0`, or `1` if it produces a row | |
| Anything else (Unnest, recursive CTE, …) | none | |

`inner` is the bound on an inner join with the same inputs. An outer or anti
join also gets variables for what its selectivities measure (`validate`
counts them): its inner join's rows `i` (`{op}_inner`), and the rows of each
side with a partner `mₗ`, `mᵣ` (`{op}_left`, `{op}_right`). `i <= inner`,
`m <= i` and `m <=` its side, `i >= 1 → m >= 1`; if the other side's key is
unique, `m = i`, and on a foreign key from a side, `m =` the side and `i =` the
side.

**Unique keys.** A set of columns is unique if it covers one of these:

- a declared `PRIMARY KEY`;
- the group keys of a `GROUP BY`;
- all columns of a `DISTINCT`, or the `ON` expressions of a `DISTINCT ON`;
- any column of an ungrouped aggregate, which has at most one row.

A key stays unique:

- through filter, sort, limit, alias, window, `DISTINCT`, and projections of the
  column (or an injective cast of it);
- through semi, anti and mark joins;
- through a `GROUP BY` that groups by it;
- through a join on the other side's unique key (for outer joins, only on the
  preserved side).

`UNIQUE` constraints are not trusted (DataFusion doesn't enforce them), and
ROLLUP / CUBE / GROUPING SETS outputs are not keys, since they repeat key values.

**Foreign keys.** DataFusion has none, so they are declared in
`Options::foreign_keys`: `ForeignKey::new("orders", &["cust"], "customers",
&["id"])` says every order's `cust` is non-NULL and equals the `id` of exactly
one customer. A join on exactly a foreign key's columns (no other condition),
where one side's columns hold one row's referencing values and the other side
holds every row of the referenced table once, matches each row of the first
side exactly once:

- The referencing side may be filtered, joined, grouped by the key, or
  deduplicated: its values are still some row's. Not padded by an outer join,
  whose NULLs match nothing.
- The referenced side must be the whole table: a scan without filters, through
  projections, aliases, sorts without a limit, and windows.

So `orders ⋈ customers` on the key has `X = |orders|`, and its selectivity is
resolved: no fact needed. So is any part of an outer or anti join's formula
the constraints determine: in `customers LEFT JOIN orders` on the key, the
inner join has `|orders|` rows, so `X = |orders| + (1 − m)·|customers|`.

**Value domains.** Rows above a filter or join condition all satisfy it, so
every relation also carries, per expression, a *domain*: an integer range or a
finite set of values, plus whether NULL can occur. An expression whose values
lie in a domain of `k` values has NDV `<= k`, and an empty domain means `X = 0`.

- Facts come from predicates evaluated TRUE: comparisons with literals (`<`,
  `<=`, `=`, `<>`, `>=`, `>`, `BETWEEN`, `IN`), `IS [NOT] NULL`, boolean
  columns, `AND` (intersect) and `OR` (union). Any comparison makes its
  operands non-NULL. Ranges are over integers, dates and decimals of one scale,
  and sets over those, strings and booleans; floats get no domain.
- Comparing with something that has one value for the whole query (a query
  parameter `$1`, or an uncorrelated scalar subquery) leaves at most one value,
  though not which: `id = $1` on a key gives `X <= 1`, `IN ($1, $2)` two.
- `a = b` in a filter or inner/semi equi-join gives both sides the intersection
  of their domains.
- Domains flow through projection (a computed column keeps its expression's
  facts, both ways), filter, sort, limit, alias, window, distinct, joins (NULL
  added on a padded side), union (union of domains), and aggregates (group keys,
  and `MIN` / `MAX` take their argument's domain plus NULL).
- Some expressions have a domain from their shape: literals, `CASE` (union of
  its branches), `date_part` (`year` of a date range, and fixed ranges for
  `month`, `quarter`, `day`, `dow`, ...), and small types (`BOOLEAN`, 8- and
  16-bit integers). Stored tables' non-nullable columns are never NULL.
- Integer arithmetic with a literal maps the domain: `x / k` and `x % k` always
  (so `GROUP BY id % 16` has at most 31 groups plus NULL, 16 if `id >= 0`), and
  `x + k`, `x - k`, `x * k` when both ends of `x`'s range are known and the
  result provably fits its type (Arrow arithmetic wraps on overflow).
- `date_trunc(unit, t)` over a range of dates or time-zone-free timestamps
  takes one value per unit the range meets: 12 months in a year.

So `WHERE id BETWEEN 1 AND 10` on a key gives `X <= 10`, TPC-H Q7 (two
nations each, two ship years) gives `X <= 8`, and `x > 5 AND x < 3` gives `X = 0`.

**Counts.** A GROUP BY's groups split its input, so each `count(..)` column
sums to at most `l` over the output, and a group's `count(*)` is at least 1.
The sum survives operators that keep a subset of rows (filter, sort, limit,
distinct, semi / anti joins, projection of the column). Where the column's
domain says every value is at least `k`, `k·X <= l`: `HAVING count(*) > 1`
gives `X <= 1/2·l`.

**Disjoint subsets.** A filter's selectivity is unknown, but filters that
cannot both pass a row have selectivities summing to at most 1. A relation
built from one scan of `T` by operators that never duplicate a row (filter,
projection, sort, limit, alias, window, distinct, semi / anti / mark join)
keeps an *origin*: `T`, and the domains of `T`'s columns over its rows, which
outlive the columns themselves. Relations with the same origin share a variable
`part` bounding them all, and for every set of origins that are pairwise
disjoint (some column's domains don't meet), `Σ part <= |T|`. So
`... WHERE age < 18 UNION ALL ... WHERE age >= 18` gives `X <= |users|`, not
`2·|users|`.

**Window functions.** `row_number()`, `rank()` and `dense_rank()` are at
least 1. `row_number() OVER (PARTITION BY P)` numbers each partition's rows
1, 2, 3, ..., so `(P, rn)` is unique: `X <= Π ndv(P) · ndv(rn)`, where columns
with a finite domain count as the domain's size. So a top-k-per-group filter
`WHERE rn <= 3` gives `X <= 3·ndv(P)`, and `X <= 3` with no partition.

**Outer-join padding.** On a left join, a right column that no matched row
leaves NULL (an equi-key, or a column never NULL on the right) is NULL exactly
on the padded rows. So rows where it is NULL number at most `l`, and rows where
it is not at most `inner`; both survive operators that keep a subset of rows.
The anti-join idiom `a LEFT JOIN b ON ... WHERE b.key IS NULL` gives
`X <= |a|`. Right joins are symmetric. A full join also keeps each side's own
unmatched rows, whose keys may be NULL, so there only columns never NULL on
their own side qualify.

**Solving.** Every check runs in Z3's incremental mode (after a `push`), which
uses its SMT core. Its one-shot strategy portfolio first tries bit-blasting the
nonlinear products (`l·r`, NDV products) once domains bound many variables,
which is an order of magnitude slower. If the SMT core gives up on the
verdict, the portfolio gets a turn on a fresh solver.

**Caveats.**

- Equality-based NDV rules skip floats: `-0.0 = 0.0` in SQL, but the two differ as bits.
- Products of NDVs are nonlinear and capped at `Options::max_product` factors
  (default 3). Larger products are dropped, which is sound but weaker.
- Declared keys, primary and foreign, are trusted. DataFusion does not enforce them.

## Selectivities

The bounds above are inequalities, because how many rows a filter keeps
depends on the data. With `Options::selectivity` set, the analysis also names
what is unknown: it writes the output cardinality as an exact formula over
table sizes and *selectivities*, each a number `0 <= s <= 1` belonging to one
operator, with the predicate or expressions it depends on.

```rust
let options = Options { selectivity: true, ..Default::default() };
let a = cardinal::analyze_sql_with(&ctx, sql, options).await?;
let s = a.selectivity.unwrap();
s.output;      // X = s1·s2·|orders|·|users|
s.required;    // s1 = s(users.age > 30) over op2_Scan_users, in [0, 1]
               // s2 = join(o.user_id = u.id) over op1_.. × op5_.., in [0, 1]
s.is_exact();  // true if the formula has no unknowns
s.evaluate(&table_sizes, &values)?;  // a count, or a range if values are missing
```

Either the formula has no unknowns, and the cardinality is known statically
from the table sizes, or `required` is the set of selectivities that give the
exact count once they are known.

| Operator | Cardinality | Selectivity |
|---|---|---|
| Table scan of `T` | `\|T\|` | |
| Pushed-down scan filters | `s·\|T\|` | `s(p1 AND p2 ...)` |
| Projection, Alias, Repartition, Window, Subquery, Sort | `l` | 1 |
| Filter on `p` | `s·l` | `s(p)` |
| Sort with fetch `n` | `min(n, l)` | |
| Limit (skip `k`, fetch `n`) | `min(n, max(l − k, 0))`. Not literals: `s·l` | |
| Distinct, Distinct On, GROUP BY | `s·l` | `\|distinct(columns or keys)\| / l` |
| Aggregate, no GROUP BY | `1` | |
| Cross join | `l·r` | |
| Inner join | `s·l·r` | pairs of rows satisfying the condition, of `l·r` |
| Semi join | `m·l` | rows of the kept side with a match, of `l` |
| Anti join | `(1 − m)·l` | the semi join's `m` |
| `NOT IN` (null-aware anti join) | `s·l` | rows kept, of `l` |
| Left join | `s·l·r + (1 − m)·l` | the inner join's `s`, the semi join's `m` |
| Right join | `s·l·r + (1 − m)·r` | mirror |
| Full join | `s·l·r + (1 − mₗ)·l + (1 − mᵣ)·r` | |
| Mark join | kept side | |
| Union | `Σ inputs` | |
| Values, empty relation | its rows | |
| Anything else (ROLLUP, Unnest, table functions, …) | `\|op\|` | |

A selectivity belongs to one operator: the same predicate over another input
is another unknown. The last row's `|op|` is an unknown too, but a row count
rather than a share. A selectivity over no rows has no value, and needs none,
since it multiplies a zero.

**What the constraints resolve.** The solver is asked, for each operator with
a selectivity, whether its cardinality is provably zero or provably one of its
inputs'. If so the formula says that and the selectivity moves to `resolved`:
`GROUP BY` on a key is `l`, a contradictory filter is `0`, and a left join to
a key is `l` with neither of its selectivities. Otherwise, for an operator
that keeps a share of one input, the tightest provable `lo <= s <= hi` (the
same fractions as the bounds) becomes the selectivity's `range`.

**Evaluating.** `evaluate` takes each table's row count and values for some of
the unknowns, by name. Unknowns without a value take their range (`|op|`: any
count), and the result is the range of counts that leaves. With every unknown
given it is one number.

**Caveat.** A range only holds what the constraints say about an operator
relative to its direct input. Facts that span operators (`HAVING count(*) > 1`
keeps at most half of the *grouped* rows; a join on a key outputs at most the
other side's rows) show up in `bounds()` but not in a selectivity's range, so
`evaluate` without values can give a wider range than `bounds()` proves.

## Facts

Selectivities are unknowns; watching queries run fills them in. A *fact* is a
number known exactly from an executed plan: `|lineitem| = 60175`,
`s(l_quantity < 10 | lineitem) = 10816/60175`, `ndv(l_suppkey | lineitem) = 100`.

```rust
let catalog = Catalog::from_context(&ctx).await?;           // schemas only
let plan = observed::from_duckdb(&catalog, "q1", &json)?;   // EXPLAIN (ANALYZE, FORMAT JSON)
let facts = facts::derive_facts(&[plan, ...]);
println!("{facts}");
// or, from PostgreSQL's EXPLAIN (ANALYZE, VERBOSE, FORMAT JSON):
let plan = observed::from_postgres(&catalog, "q1", &json, Some(sql))?;
```

**Observed plans.** `observed::ObservedPlan` is an engine-neutral operator
tree, with each operator's output rows. Its predicates and keys are DataFusion
`Expr`s over base-table columns, whatever projections sit in between: each
output column carries its lineage (exactly an expression, a one-to-one
encoding of one, or unknown). Columns are qualified by *table instance*
(`lineitem#3`, the scan's operator), so two scans of a table stay apart. An
aggregate's output is a column of the aggregate itself (`@7.sum(l_quantity)`),
so HAVING and scalar-subquery comparisons read too.

Every expression is written as DataFusion's optimizer writes it, so that a
predicate reads the same in a profile and in the query it is matched against
(see [Bounds from facts](#bounds-from-facts)): types are coerced as for
execution, so a literal takes its column's type (`l_quantity < 10.00` is
`Decimal128(10.00,15,2)`, an aggregate's value its aggregate's type), and
constants are folded. DuckDB computes `date '1998-12-01' - interval '90' day`
as a timestamp, and DataFusion as a date, so a date compared with a timestamp
at midnight is compared with that date. DuckDB prints `LIKE 'abc%'`,
`'%abc'` and `'%abc%'` as `starts_with`, `ends_with` and `contains`, so they
are written that way.

`from_duckdb` reads DuckDB's profile, resolving names only when one column
has the name, and positions (`#2`) only where the column order is known (not
above a join, which drops and reorders columns unseen). What does not resolve
is kept as text and gives no facts. It also reads the query text the profile
includes, for two things the plan does not print reliably:

- *Aliases.* A projection may print only `nation` or `o_year`; the alias's
  row-level expression in the query (`extract(year from o_orderdate)`) is
  read in its place, unless the alias names two expressions.
- *Tables read twice.* Above a self-join DuckDB prints both instances'
  columns by one name (TPC-H q07's `n_name`s). Each alias of such a table
  (`n1`) is matched to the one instance whose join conditions are all
  equalities its columns take part in with tables read once
  (`s_nationkey = n1.n_nationkey`). A predicate or alias that does not
  resolve by name is then read as the one query expression printed the
  same without qualifiers, its aliases' columns as their instances'.
- *Join conditions.* After decorrelating a subquery, DuckDB may print a
  condition's column under the other side's name. A condition is read only
  if the query compares those base columns: equal under its equalities
  (taken transitively, as DuckDB derives join conditions), or in one
  comparison. Without query text, conditions are taken as printed.

Some operators read another's output again. A materialized CTE's scans, and a
delim join's (DuckDB's plan for a correlated subquery) reads of its input and
of the input's distinct keys, become `Reuse` operators, each an independent
copy of the rows with renamed instances (`lineitem#3~r9`). A delim join is the
join below it, over those copies. A filter on a mark join's mark (`IN`,
`EXISTS`, `NOT IN`) keeps the rows of a semi join, or for `NOT IN` of its own
operator. An `IN` over a constant list, planned as a mark join against a
table of the constants, is read as the `IN` predicate DuckDB also pushes into
the scan.

**PostgreSQL.** `from_postgres` reads PostgreSQL's profile (versions 14 to
18), printed with `VERBOSE`: then every operator lists its output, and every
column is printed with the alias of the relation it is read from, which
PostgreSQL keeps unique in a plan (`n1.n_name`, `lineitem_1.l_partkey`). So a
column reads the same wherever it is printed, with no help from the query,
and an operator's expressions are read on their own; what an input computed,
printed in parentheses (`(sum(l_quantity))`), is that input's column. A plan
without `VERBOSE` is refused. PostgreSQL's spellings are read as the query's:
`'1'::numeric` is `1`, `(c_mktsegment)::text` the column, `x = ANY
('{a,b}'::text[])` is `x IN ('a', 'b')`, and `~~` is `LIKE`. The query text,
which a PostgreSQL profile does not include, is passed for what the plan
still leaves out: the column names of a subquery or CTE the plan reads by
name (`s.rn`) and prints by position, its `LIMIT` counts and offsets, and
whether a `Unique` is a `DISTINCT ON` (whose columns are not printed: no
model).

PostgreSQL's operators do more than one thing each, and run more than once:

- *Filters.* A scan, join or aggregate applies its own `Filter` (a `HAVING`,
  a `WHERE` above an outer join) and reports the rows left, and those
  removed. Each is read as the operator and a filter above it, the rows
  between them being the sum. So a sequential scan gives its table's size,
  and its filter an exact share of it, where DuckDB's pushed filter gives a
  bound. An index scan's condition is a filter too, over a scan whose rows
  were not counted.
- *Rows not counted.* An operator that a merge join, a semi or anti nested
  loop, a window's run condition or a limit stopped reading early reports
  what was read, and one that ran several times (`Actual Loops` other than
  1) reports an average. Neither is a count (`ONode::counted`), but for the
  averages that are one:
  - the inner side of a nested loop that binds nothing in it outputs the
    same rows each time, so their average is their count;
  - the processes of a parallel plan split the rows of a parallel-aware
    scan and of what reads it, and version 18 prints their average to two
    decimals: times the runs, it is their sum, for fewer than 100 runs. The
    rows a filter removed are rounded to a whole number, so a parallel
    scan's filter counts the rows it kept and not its table's
    (`max_parallel_workers_per_gather = 0` counts both). Groups aggregated
    in part (`Partial Mode`) are no rows of the query until the aggregate
    above finishes them.

  An operator whose rows were not counted still has the rows its inputs
  and predicates say. A sort, a hash table's build and a hash aggregate
  read all of their input first, so below them rows are whole again
  (`ONode::blocking`); and one that outputs its input's rows (a sort a
  merge join left early, a `Hash`, which reports the rows it stored,
  without those whose key is NULL) has as many as were counted there. A
  hash join whose table came out empty reads at most one row of its other
  side, unless it outputs that side's unmatched rows.
- *Partial indexes.* A plan prints the index a scan reads, but neither a
  partial index's predicate nor the query's conditions that the predicate
  implies, which PostgreSQL drops: `WHERE priority = 'URGENT' AND day < d`
  over an index `ON orders (day) WHERE priority = 'URGENT'` prints `Index
  Cond: (day < d)` alone. So the catalog must have the partial indexes'
  predicates (`Catalog::with_partial_indexes`, with the rows of `SELECT
  c.relname, pg_get_expr(i.indpred, i.indrelid) FROM pg_index i JOIN
  pg_class c ON c.oid = i.indexrelid WHERE i.indpred IS NOT NULL`: possibly
  none), and a scan of one keeps the rows of its predicate too. Until it
  has them, a scan of any index has a predicate that does not resolve: it
  gives no fact, and bounds only that it keeps some of the table's rows.
- *Index lookups.* A condition printed on the inner side of a nested loop
  that reads the outer side's columns (`Index Cond: (l_orderkey =
  orders.o_orderkey)`) is the join's condition, not the scan's. It goes up
  to the join that binds it, through what keeps a filter's rows (inner
  joins, the kept side of semi, anti and outer joins). Where it cannot (the
  lookup is under an aggregate or a limit: a `LATERAL` subquery), the join
  has no model.
- *Subqueries.* An uncorrelated scalar subquery is an InitPlan, run once:
  its one row (an aggregate without groups) is cross-joined to the rows of
  the filter that reads it (`(InitPlan 1).col1`, or `$0` before version 17),
  as DuckDB plans it. `x [NOT] IN (subquery)` that PostgreSQL did not make a
  join is a hashed SubPlan: a mark join against it, and a filter on the
  mark (since version 17, which prints what is compared; before, the
  predicate does not resolve). A CTE scan is a `Reuse` of its definition; PostgreSQL computes a CTE
  as it is read, so one read short (under a limit) is not counted either. A
  SubPlan that reads the row it runs for (a correlated subquery PostgreSQL
  did not decorrelate, as TPC-H q02, q17 and q20's) has no counts of its
  own, and the predicate that reads it does not resolve.
- *Anti joins.* PostgreSQL plans `a LEFT JOIN b ... WHERE b.key IS NULL` as
  an anti join, and still prints `b`'s columns above it, where all are NULL:
  above a semi or anti join, the other side's columns read as unknown.
- *Windows.* A window's functions are read with its definition, its order's
  directions from the sort below, which the definition leaves out. Before
  version 18 no definition is printed (`row_number() OVER (?)`): it is the
  query's, where the query and the plan each have one window function so
  called. A run condition (`row_number() <= 1`, since version 15) is a
  filter above the window.

**Contexts.** A fact holds for the rows it was measured over: its *context*.
Contexts are built in a normal form (`facts::rewrite`), so that plans that
compute the same rows in a different order name them the same. Filters,
inner joins, and semi and anti joins over any inputs give one `Spj` context:
the cross product of its tables and *atoms* (inputs that are not themselves
SPJs, like a GROUP BY or an outer join), with a set of canonical predicates
and of existence conditions (`exists[on](other)`, `not exists[...]`,
`not in[...]`). Other operators give a `Derived` context, named by the
operator, its keys and its inputs' contexts. Each rewrite into the normal
form holds for any data, and fires only when that can be read off the terms:

- Inner joins and filters flatten, over atoms too: join order does not matter.
- A semi or anti join is a condition on its kept side's rows, so it commutes
  with the inner joins and filters around it, and with other such joins.
- Equal columns (`a = b ∧ b = c`) are written as a star from the least, and
  a semi or anti join's condition reads each side's least.
- DuckDB's decorrelation, a semi join against `σP(X × group_k'(K'))` where
  `K'` is a copy of the kept rows, reads as the semi join of `X` it computes.
- A left join's preserved side is only the inputs its condition reads; the
  rest applies outside it, and a term of the condition on the other side alone
  filters that side. A predicate rejecting the padded side's NULLs makes the
  inner join (a full join, the left join preserving the other side).

A predicate on a GROUP BY's keys stays above it: a value the GROUP BY
computes is named by the rows it ran over, and what reads it above would no
longer name a GROUP BY of the rows. Engines move such predicates below the
GROUP BY themselves.

| Operator | Output context |
|---|---|
| Scan of `T`, filters `p` | `T where p` |
| Project, Sort, Window | the input's |
| Filter `p` | input `where p` |
| Inner join on `c` | `L × R where c` |
| Semi, anti join | `kept where exists[c](other)`, `not exists[c](other)` |
| Left, full join | `Derived`; a right join as the left join with its inputs swapped |
| Filter on a mark | `kept where exists[...]` (`IN`), or `not in[...]` |
| Group by / distinct, aggregate, top-n, union | `Derived` |
| Reuse (CTE scan, delim join input) | the read operator's, over copied instances |
| Limit | tainted, with everything below it |
| Anything else | tainted |

A fact's instances are then named canonically: a table's only instance by
the table's name, several by `lineitem@1`, `lineitem@2`, ..., numbered to make
the fact least, so the same fact from two plans reads the same. A value of an
aggregate reads as `"value"."sum(lineitem.l_quantity) of group[...](...)"`:
the aggregate and the rows it ran over.

Some counts are not exactly a function of the context, and give no fact:

- *Pushed filters.* A filter pushed into a scan, required or optional, may be
  applied loosely (only to skip blocks, say), so the scan's rows are the
  context's and maybe more. Its count, and the count of each operator above
  that keeps all of a superset input's rows (filters, inner and semi joins,
  an anti join's kept side, a left join's preserved side), is only an upper
  bound: `|ctx| <= rows`, and for a GROUP BY over such rows,
  `ndv(k | input) <= rows`. An anti join's other side, an outer join's padded
  side, a mark join, a GROUP BY's values, a top-n and a union cannot take
  extra rows, and taint. A filter above that checks the same predicate makes
  the rows exact again.
- *Runtime filters.* DuckDB pushes a join's build-side keys into the probe
  side's scan as filters, which remove real rows of the context. The rows
  stay pending, with no fact nor bound, until the join on that column (the
  highest one, should several join on it), whose output they cannot change.
- *Early stops.* Below a `LIMIT`, on the probe side of a join that output
  nothing (its build side empty, or with no key that can match), and in a
  scan that reports reading fewer rows than it output, operators may not
  have run to completion.
- *Volatile* (`random()`) and unresolved predicates. Names stay unresolved
  above a self-join where both instances' columns share them and the query
  does not tell them apart (see *Tables read twice*), and aggregates named
  only by an alias (`total_revenue`, `c_count`) stay unknown.

**Rules.** `facts::RULES` read facts off each operator with clean inputs:

| Rule | Fact |
|---|---|
| Cardinality | `\|ctx\| = rows` |
| Filter selectivity | `s(p \| input) = rows / input`, without conjuncts the input already satisfies |
| Join selectivity | inner: `s(c \| L × R) = rows / (l·r)`; semi/anti: the kept side's share with a partner `m` |
| Distinct count | group by / distinct on `k`: `ndv(k \| input) = rows` |
| Upper bound | pending only on pushed filters: `\|ctx\| <= rows`; a GROUP BY over such rows: `ndv(k \| input) <= rows` |

**Closure.** `FactSet::close` combines facts from every plan until nothing new
follows. A filtered size over an unfiltered one is a selectivity (`ratio`); a
selectivity times its input's size is a size (`product`). A join's size over
its inputs' sizes is a join selectivity, even when the inputs were counted in
other plans (`join`). The same goes for a semi join's size over its kept
side's (`match`). A distinct count equal to its context's size makes the keys
unique there (`unique`). A selectivity of 1 says every row of its context
satisfies the predicate, so a context containing that one names the same rows
without it (`redundant`): DuckDB filters a join's side by the other's key
range (`c_custkey <= 1499`), which a query never spells out. The same fact
with two values is a `Conflict`: the data changed, or a context names the
wrong rows. So is a bound below its context's exact value. Bounds keep the
least seen, and do not combine.

**Facts not counted.** An operator whose rows an engine did not count (it
stopped early, or ran several times and reported an average) still has the
rows its context names, and a plan that was not run (`EXPLAIN` alone) has
them all. So the rules name such an operator's facts without a value, and
`FactSet::unobserved` lists those that nothing else gives: each is counted by
the queries `FactKind::count_sql_in` writes, and added with
`FactKind::counted` and `FactSet::insert` (its origin is `Origin::Counted`).

```rust
let mut facts = derive_facts(&plans);
let missing: Vec<FactKind> = facts.unobserved().cloned().collect();
for kind in missing {
    let Some(counts) = kind.count_sql_in(&catalog, &facts, CountDialect::Postgres) else { continue };
    let (value, of) = run(&counts.value, counts.of.as_deref()); // each a single count
    if let Some(fact) = kind.counted(value, of) {
        facts.insert(fact);
    }
}
facts.close();
```

The fixtures under `tests/duckdb` are DuckDB profiles of TPC-H (scale factor
0.01) and some hand-written queries, regenerated by
`scripts/duckdb_fixtures.sh`. It also checks the facts themselves:
`FactKind::count_sql` writes what any fact or bound counts as SQL, from what
its context means rather than how a plan computed it (each instance a
subquery with uniquely named columns, existence conditions as `EXISTS`,
groups as `GROUP BY`, outer joins as outer joins). An aggregate's value is
computed by the GROUP BY among the fact's rows whose context it names, by the
definition the `FactSet` recorded when it read the plan. DuckDB counts
each into `fact_checks.json`, which `facts_match_duckdb` compares against: a
fact must equal its count, a bound be at least it. Rerun the script whenever
the derived facts change.

`tests/fact_truth.rs` does the same live, on many more queries: TPC-H, the
fixtures, the larger queries in `tests/truth/queries.sql`, and generated ones
(joins of every kind, grouped subqueries, nested and correlated semi and anti
joins, `NOT IN` against NULLs), each profiled with one thread and with four.
Every fact and bound is counted, no two plans may disagree, and each query's
bounds with the facts must hold its true count. It needs the `duckdb` CLI.

```sh
scripts/duckdb_fixtures.sh                          # profiles, true counts, fact checks
cargo test --test facts                             # including facts_match_duckdb
cargo test --test facts print_facts -- --nocapture  # every plan's contexts and facts
CARDINAL_TRUTH_N=300 CARDINAL_TRUTH_SEED=11 \
  cargo test --release --test fact_truth -- --nocapture
```

The fixtures under `tests/postgres` are PostgreSQL 18's profiles of the same
queries over the same data, and of some more (`tests/postgres/extra`:
windows, set operations, `LATERAL`, `DISTINCT ON`), regenerated by
`scripts/postgres_fixtures.sh`. Under `indexed` are the same queries with
primary keys and indexes: index scans, nested loops and merge joins. Under
`parallel` they run in three processes, whose averages are read as counts.
PostgreSQL counts every fact itself (`FactKind::count_sql_in` writes the
counts in its dialect), into `fact_checks.json`, which `facts_match_postgres`
compares against; `tests/postgres_bounds.rs` is `fact_bounds` with
PostgreSQL as the engine. `fact_truth` runs live in PostgreSQL too, when a
server has the script's database: each query profiled as PostgreSQL plans
it, with hash joins over sequential scans only, with merge joins, and in
parallel; then the facts no profile counted are counted (`Engine::fill`),
and must agree with the rest. The
script and the live tests connect as `psql` does (`PGHOST`, `PGPORT`,
`PGUSER`, ...), to the database `CARDINAL_PG_DB` (default `cardinal_tpch`),
which the script creates.

```sh
scripts/postgres_fixtures.sh                          # the database, profiles, fact checks
cargo test --test postgres                            # including facts_match_postgres
cargo test --test postgres print_facts -- --nocapture
cargo test --test postgres_bounds
cargo test --release --test fact_truth facts_are_true_in_postgres -- --nocapture
```

## Bounds from facts

Facts fill in selectivities. Each operator of a query gets the context facts
would name its rows by (`facts::logical`), built by the same rules from the
DataFusion plan: scans are instances (`lineitem#4`, by node), predicates are
read through projections and aliases to base columns, and expressions are
normalized as a profile's are. A selectivity's value is then a lookup:

| Selectivity | Fact | Or, from sizes |
|---|---|---|
| Filter `p` over input `I` | `s(p \| I)`, without conjuncts `I` satisfies | `\|I where p\| / \|I\|` |
| Inner join on `c` of `L`, `R` | `s(c \| L × R)` | `\|L × R where c\| / (\|L\|·\|R\|)` |
| Semi / anti join share `m` | `m(c \| kept ⋉ other)` | the semi or anti join's size over the kept side's |
| `NOT IN` | | its size over its input's |
| Distinct, GROUP BY on `k` | `ndv(k \| I) / \|I\|`, or 1 if `unique(k \| I)` | |

```rust
let facts = facts::derive_facts(&plans);
let informed = analysis.with_facts(&facts, FactMode::Ratios)?;
informed.output;   // s1·|lineitem|: the filter is pushed into the scan
informed.matched;  // the selectivities with a value from a fact
informed.bounds()?;  // as Analysis::bounds, with the facts among the constraints
informed.range()?;   // the proven lo <= X <= hi
```

A matched value replaces its selectivity in the formula, and its operator's
relation to its inputs (`X = 10816/60175 · l`, over reals) joins the
constraints, where it combines with what they already know (keys, domains,
disjoint subsets). Two modes:

- `FactMode::Ratios` uses only selectivities. Table sizes stay unknowns, so
  the bounds hold as the tables grow, as long as the shares do (a GROUP BY's
  groups are the least likely to keep their share).
- `FactMode::Pinned` also fixes every row count a fact gives: tables, and any
  operator whose context has a known size (a GROUP BY's from its distinct
  count), and caps every operator whose context has an upper bound
  (`capped`). This holds a join's size even where it was joined in another
  order, and is exact for the data the facts were read from only.

A value outside its selectivity's proven range, or contradicting the
constraints, is `rejected`: a fact matched to the wrong rows, or data that
changed. A relation the solver cannot check in time is left out (`unchecked`).
A conflicting fact is never used.

The fixture queries test this against DuckDB's profiles of themselves: with
every fact, and with only the other queries', no fact is rejected and every
bound holds the true count. With TPC-H's foreign keys declared, 91
selectivities remain to find (23 fewer than without), and with every fact 38
have a value. Most of the rest were never counted: DuckDB joined in another
order, or a runtime filter pruned the scan.

```sh
cargo test --test fact_bounds                                  # bounds hold, match rates
cargo test --test fact_bounds print_matches -- --nocapture     # each query's matches, and why not
cargo test --test fact_bounds print_bounds -- --nocapture      # bounds before and after
```

### Plans from an engine

A fact matches only an operator whose rows it names, and DataFusion may plan
a query in another order than the engine whose profiles gave the facts. So a
query can also be analyzed as the engine planned it:

```rust
let a = cardinal::analyze_duckdb(&catalog, &explain_json, Some(sql), options)?;
// or, from a plan already read:
let plan = observed::from_duckdb_explain(&catalog, "q1", &explain_json, Some(sql))?;
let a = cardinal::analyze_observed(&catalog, &plan, options)?;
// PostgreSQL's, from EXPLAIN (VERBOSE, FORMAT JSON):
let a = cardinal::analyze_postgres(&catalog, &explain_json, Some(sql), options)?;
let plan = observed::from_postgres_explain(&catalog, "q1", &explain_json, Some(sql))?;
```

`from_duckdb_explain` reads `EXPLAIN (FORMAT JSON)` output, or a profile
with its counts ignored. A plain plan has no query text, so `sql` names what
it prints only by alias and vouches for join conditions. Its plan is not
counted (`ObservedPlan::counted`), and gives no facts.

`Catalog::to_logical` writes the plan as an unoptimized DataFusion plan of
the same shape, which the analysis reads as it reads any other. Each
operator outputs its input's instance columns, which is what predicates and
keys read, so projections, sorts and windows are left out:

| Observed | Logical |
|---|---|
| Scan, with filters | `TableScan` with its required filters pushed, aliased as its instance. Optional and runtime filters are dropped: neither changes the rows above |
| Filter, join | Filter, join. Equalities across the sides are keys (all `IS NOT DISTINCT FROM`: keys equal on NULL), the rest a filter. A join on no condition is a cross join |
| Filter on a mark | Semi join, or for `NOT IN` a null-aware anti join |
| Group by | `Aggregate`. Keys that are not columns, and values, are columns of `@node` |
| Reuse (CTE scan, delim join input) | The read operator again, its instances renamed: an independent copy |
| Top-n (`fetch`, `offset`) | `Sort` with fetch `offset + fetch`, then a limit skipping `offset` |
| Limit | A filter on an opaque predicate, then a limit of `at_most` rows if known |
| Union | Each input as one column: nothing traces a union's columns |

Neither DuckDB nor PostgreSQL prints a limit's count, in any `EXPLAIN`
format, so it is read off the query: when the plan has as many limit and
top-n operators as the query has `LIMIT` clauses, each with a constant count,
every limit outputs at most the largest (`Op::Limit { at_most }`). An offset
only drops rows. PostgreSQL plans a top-n as a limit over a sort: the one
limit of a query with one `LIMIT` clause is that clause, and over a sort is
read as the top-n it is, with the clause's count and offset.

DuckDB materializes a limit's rows late: the limit (or top-n) picks rows of
a scan of `T`, and a semi join on `rowid = rowid` reads their columns from a
second, unfiltered scan of `T`. That join outputs exactly the picked rows,
so it reads as the picking side, with the second scan's columns read as the
first's. `tests/plan_truth.rs` checks limits and offsets against a live
DuckDB, and a live PostgreSQL: every bound holds the true count, and limits
bound what they should.

What does not translate is opaque, and bounds nothing: a predicate or key
that did not resolve is a volatile `opaque('<text>')`, and an operator
without a model, or one DataFusion rejects, an extension node over its
inputs.

On the fixtures, with every fact, pinned bounds cap 35 of the 45 queries
DataFusion also plans at their true count, against 30 when DataFusion plans
them. DuckDB's plan does better on join orders (TPC-H q05: `X <= 5`, not 25)
and the filters it pushes, and no worse on any. `explain_plans` checks that each TPC-H query's plain
`EXPLAIN` asks for the same selectivities as its profile.

PostgreSQL's facts are exact where DuckDB's pushed filters give bounds, so
more of them match: on PostgreSQL's fixtures (`tests/postgres_bounds.rs`),
with every fact, 122 selectivities of PostgreSQL's plans find one, and 86 of
DataFusion's, and pinned bounds cap 60 of the 70 queries DataFusion also
plans at their true count as PostgreSQL planned them, 57 as DataFusion does.

## Simple selectivities

A selectivity is a share of its operator's input, and that input is often
other operators' output. A *simple* selectivity is a share of the rows of
stored tables alone, whole:

| Kind | Fact | Over |
|---|---|---|
| Filter | `s(p \| T)` | one table |
| Join | `s(c \| T × U)` | two tables (a table read twice counts twice) |
| Semi join | `m(c \| T ⋉ U)` | a kept table, and the other |
| Distinct | `ndv(k \| T)`, over `\|T\|` | one table |

```rust
for s in analysis.simple_selectivities()? {
    println!("{s}");
    // s1 = s(orders.amount > 10 | orders): filter on orders
    // s2: not simple (over filtered rows: items × orders where orders.amount > 10)
}
```

An operator's input is named as a fact names it (see [Contexts](#facts)), so
views, CTEs, subqueries, projections and aliases read as the stored tables'
scans below them, and predicates and keys as expressions over their columns.
Only scans of tables count: a view is inlined, and its definition read. A
join's share whose condition reads one table only is that table's filter
share, `s(p | T × U) = s(p | T)`.

Where an input is more than whole tables, the constraints may prove it holds
the same rows as one. Each operator that does is seen through, and listed in
`Simple::proof`:

- a filter, or a scan's pushed filters, or a semi or anti join, whose rows the
  constraints prove are all of its input's;
- an inner equi-join where each row of one side has at most one partner (the
  other side's key is unique, or a foreign key goes to it) and the join
  provably has as many rows as that side, so each has exactly one; or a left
  join whose preserved rows each have at most one. Its rows are that side's,
  one for one, and if nothing above reads the other side's columns, the other
  side is dropped.

So `SELECT i.part, count(*) FROM items i JOIN orders o ON i.order_id = o.id
GROUP BY i.part`, with a foreign key from `items` to `orders`, needs
`ndv(items.part | items)`. A filter on `o.amount` above reads the order, and
the join's share stays one of pairs of filtered rows. `tests/simple.rs`
executes every query and checks that each simple selectivity's fact, counted
over its tables alone, gives the value the execution measured. On TPC-H with
its foreign keys, 18 of the 67 selectivities DataFusion's plans need are
simple, and 33 of 101 for DuckDB's.

## Validation

`validate` evaluates the plan bottom-up, running each operator over its
children's materialized output. It never runs DML or DDL. It pins every real
cardinality and NDV onto the constraints and reports the first operator whose
real counts are unsatisfiable. The benchmark and fuzzer use it, and also check
every claimed bound against real row counts.

With selectivities enabled it also measures each one from the execution: the
operator's rows over its input's, and for outer and anti joins the counts of
the inner and semi joins over the same inputs, which it runs for the purpose.
`Validation::selectivity` holds the measured values and the first selectivity
outside its range, or operator whose formula does not give its real row count.

```sh
cargo test                                   # everything
cargo test --test tpch -- --nocapture        # TPC-H verdicts and bounds
CARDINAL_FUZZ_N=1000 cargo test --test fuzz  # larger random-query fuzz
```
