# cardinal

Proves bounds on a SQL query's output cardinality, with no data, or with facts
read off plans that ran.

Requires Z3 (`brew install z3`; paths in `.cargo/config.toml`).

## Usage

```rust
let a = cardinal::analyze_sql(&ctx, sql, Options::default()).await?;
a.bounds()?;              // e.g. "X <= 25" or "3 <= X <= 25"
a.validate(&ctx).await?;  // check the constraints against real data

// With facts from profiled plans; one `Facts` serves many analyses:
let facts = cardinal::Facts::new(fact_set);
a.with_facts(&facts)?.bounds()?;

// As DuckDB or PostgreSQL planned it, from EXPLAIN (FORMAT JSON) output:
let a = cardinal::analyze_duckdb(&catalog, &explain_json, Some(sql), options)?;
let a = cardinal::analyze_postgres(&catalog, &explain_json, Some(sql), options)?;
```

The `cardinal-debug` CLI shows the constraints behind a result:

```sh
B="cargo run -p cardinal-debug --"
$B analyze --schema cardinal-debug/tests/fixtures/tpch.sql --sql tests/tpch/q03.sql
$B analyze ... --html q03.html  # plan tree beside its constraints
```

See the API docs with `cargo doc --open`.

## Tests

```sh
cargo test                                   # everything
CARDINAL_FUZZ_N=1000 cargo test --test fuzz  # larger random-query fuzz
```

`scripts/duckdb_fixtures.sh` and `scripts/postgres_fixtures.sh` regenerate the
engine fixtures under `tests/`.
