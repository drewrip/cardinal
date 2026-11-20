#!/usr/bin/env bash
# Regenerates the DuckDB EXPLAIN ANALYZE fixtures under tests/duckdb from
# TPC-H at scale factor 0.01, with DuckDB 1.5: the catalog, a profile per
# query, and each TPC-H query's plain EXPLAIN plan.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
out="$root/tests/duckdb"
db="$(mktemp -d)/tpch.duckdb"
trap 'rm -rf "$(dirname "$db")"' EXIT

duckdb "$db" -c "CALL dbgen(sf = 0.01);" > /dev/null

duckdb "$db" -json -c "
  SELECT table_name, column_name, data_type, is_nullable = 'YES' AS nullable
  FROM information_schema.columns
  ORDER BY table_name, ordinal_position;" > "$out/catalog.json"

profile() { # sql file -> json file
  {
    echo "PRAGMA disable_print_progress_bar;"
    echo "SET threads = 1;"
    echo "EXPLAIN (ANALYZE, FORMAT JSON)"
    sed -e 's/;[[:space:]]*$//' "$1"
    echo ";"
  } | duckdb "$db" -list -noheader | sed -n '/^{/,$p' > "$2"
}

explain() { # sql file -> json file
  {
    echo "SET threads = 1;"
    echo "EXPLAIN (FORMAT JSON)"
    sed -e 's/;[[:space:]]*$//' "$1"
    echo ";"
  } | duckdb "$db" -list -noheader | sed -n '/^\[/,$p' > "$2"
}

mkdir -p "$out/explain"
for f in "$root"/tests/tpch/q*.sql; do
  profile "$f" "$out/tpch/$(basename "$f" .sql).json"
  explain "$f" "$out/explain/$(basename "$f" .sql).json"
done
for f in "$out"/extra/*.sql; do
  profile "$f" "${f%.sql}.json"
done
