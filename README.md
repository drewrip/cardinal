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
| Inner join | `X <= l·r`. Right key unique: `X <= l`. Left key unique: `X <= r`. Cross join: `X = l·r` | Columns `<=` input. Equi-keys `<=` the other side's key NDV |
| Left join | Right key unique: `X = l`. Else `l <= X <= inner + l` | Left `=`, right `<= ndv + 1` |
| Right join | Mirror of left | Mirror |
| Full join | `X >= l`, `X >= r`, `X <= inner + l + r`. Either key unique: `X <= l + r` | Both sides `<= ndv + 1` |
| Semi / anti join | `X <=` kept side | `<=`. Semi: equi-key `<=` other side |
| Mark join | `X =` kept side | `=` |
| Union | `X = Σ inputs` | `<= Σ`, `>=` each input |
| Values | `X = rows` | Domain: the literals |
| Empty relation | `X = 0`, or `1` if it produces a row | |
| Anything else (Unnest, recursive CTE, …) | none | |

`inner` is the bound on an inner join with the same inputs.

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
`X <= |a|`. Right and full joins are symmetric.

**Caveats.**

- Equality-based NDV rules skip floats: `-0.0 = 0.0` in SQL, but the two differ as bits.
- Products of NDVs are nonlinear and capped at `Options::max_product` factors
  (default 3). Larger products are dropped, which is sound but weaker.
- Declared keys are trusted. DataFusion does not enforce them.

## Validation

`validate` evaluates the plan bottom-up, running each operator over its
children's materialized output. It never runs DML or DDL. It pins every real
cardinality and NDV onto the constraints and reports the first operator whose
real counts are unsatisfiable. The benchmark and fuzzer use it, and also check
every claimed bound against real row counts.

```sh
cargo test                                   # everything
cargo test --test tpch -- --nocapture        # TPC-H verdicts and bounds
CARDINAL_FUZZ_N=1000 cargo test --test fuzz  # larger random-query fuzz
```
