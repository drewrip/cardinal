# cardinal

Proves bounds on a SQL query's output cardinality, with no data, or with the
executed plans of other queries and tables' row counts.

Downloads and links Z3 5.4.1 when built (needs network, and glibc ≥ 2.39 or macOS ≥ 13.3).

## Usage

```rust
use cardinal::Analysis;

let a = Analysis::sql(&ctx, sql).await?.options(options).build()?;
a.bounds()?;              // e.g. "X <= 25" or "3 <= X <= 25"
a.plan_bounds()?;         // every operator's bounds, and their total
a.validate(&ctx).await?;  // check the constraints against real data

// With executed plans of other queries (EXPLAIN ANALYZE), and row counts:
let a = Analysis::sql(&ctx, sql).await?
    .with_plans(&profiles)
    .with_cardinalities([("lineitem", 6001215), ("orders", 1500000)])
    .build()?;

// Several queries alike, one result per query:
let analyses = Analysis::sqls(&ctx, [q1, q2]).await?.options(options).build();

// As DuckDB or PostgreSQL planned it, from EXPLAIN (FORMAT JSON) output:
let a = Analysis::duckdb(&catalog, &explain_json, Some(sql))?.build()?;
let a = Analysis::postgres(&catalog, &explain_json, Some(sql))?.build()?;
```

The `cardinal-debug` CLI shows the constraints behind a result:

```sh
B="cargo run -p cardinal-debug --"
$B analyze --schema cardinal-debug/tests/fixtures/tpch.sql --sql tests/tpch/q03.sql
$B analyze ... --html q03.html  # plan tree beside its constraints
$B analyze ... --profiles-dir tests/duckdb/tpch --except q03  # with other plans
```

See the API docs with `cargo doc --open`.

## Tests

```sh
cargo test                                   # everything
CARDINAL_FUZZ_N=1000 cargo test --test fuzz  # larger random-query fuzz
```

`scripts/duckdb_fixtures.sh` and `scripts/postgres_fixtures.sh` regenerate the
engine fixtures under `tests/`.
