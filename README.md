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
| Filter | `X <= l` | `<=` input. `a = b`: equal, `<=` the other's input. `c = v`, `IS NULL`, `IN (k)`, OR of these: `<= k` |
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
| Values | `X = rows` | `<=` distinct literals |
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
