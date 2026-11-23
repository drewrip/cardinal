#!/usr/bin/env bash
# Prebakes data/tpch: TPC-H at scale factor 1 in DuckDB, its 22 queries'
# EXPLAIN ANALYZE profiles, the schema with its keys (each checked on the
# data), row counts, and Parquet copies; then the truth, by
# `operator-truth`. Usage: prepare/tpch.sh [--sf N] [--jobs N]
set -euo pipefail

sf=1
jobs=8
while [ $# -gt 0 ]; do
  case "$1" in
    --sf) sf="$2"; shift 2 ;;
    --jobs) jobs="$2"; shift 2 ;;
    *) echo "unknown argument $1" >&2; exit 2 ;;
  esac
done

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
duck() { python3 "$here/duck.py" "$@"; }

out="$root/cardinal-eval/data/tpch"
db="$out/tpch.duckdb"
mkdir -p "$out/queries" "$out/profiles/duckdb" "$out/parquet"

if [ ! -f "$db" ]; then
  echo "generating TPC-H sf $sf" >&2
  env -u AI_AGENT duckdb "$db" -c "CALL dbgen(sf = $sf);" > /dev/null
fi

# Primary keys and foreign keys, as TPC-H declares them.
cat > "$out/keys.json" <<'EOF'
{
  "primary": {
    "customer": ["c_custkey"], "lineitem": ["l_orderkey", "l_linenumber"],
    "nation": ["n_nationkey"], "orders": ["o_orderkey"], "part": ["p_partkey"],
    "partsupp": ["ps_partkey", "ps_suppkey"], "region": ["r_regionkey"],
    "supplier": ["s_suppkey"]
  },
  "foreign": [
    {"table": "lineitem", "columns": ["l_orderkey"], "references": "orders", "referenced": ["o_orderkey"]},
    {"table": "lineitem", "columns": ["l_partkey"], "references": "part", "referenced": ["p_partkey"]},
    {"table": "lineitem", "columns": ["l_suppkey"], "references": "supplier", "referenced": ["s_suppkey"]},
    {"table": "lineitem", "columns": ["l_partkey", "l_suppkey"], "references": "partsupp", "referenced": ["ps_partkey", "ps_suppkey"]},
    {"table": "orders", "columns": ["o_custkey"], "references": "customer", "referenced": ["c_custkey"]},
    {"table": "customer", "columns": ["c_nationkey"], "references": "nation", "referenced": ["n_nationkey"]},
    {"table": "supplier", "columns": ["s_nationkey"], "references": "nation", "referenced": ["n_nationkey"]},
    {"table": "partsupp", "columns": ["ps_partkey"], "references": "part", "referenced": ["p_partkey"]},
    {"table": "partsupp", "columns": ["ps_suppkey"], "references": "supplier", "referenced": ["s_suppkey"]},
    {"table": "nation", "columns": ["n_regionkey"], "references": "region", "referenced": ["r_regionkey"]}
  ]
}
EOF

duck keys "$db" "$out"
duck schema "$db" "$out"
duck counts "$db" "$out"
duck parquet "$db" "$out"

for f in "$root"/tests/tpch/q*.sql; do
  cp "$f" "$out/queries/"
done
duck profile "$db" "$out" "$jobs"

jq -n \
  --arg duckdb "$(duck version)" \
  --arg date "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --argjson sf "$sf" \
  --slurpfile dropped "$out/dropped_keys.json" \
  --slurpfile failures "$out/profile_failures.json" \
  '{benchmark: "tpch", engines: {duckdb: $duckdb}, scale_factor: $sf,
    generator: "duckdb tpch extension, CALL dbgen(sf)", seeds: null, date: $date,
    duckdb_threads: 1, dropped_keys: $dropped[0], profile_failures: $failures[0]}' > "$out/manifest.json"
rm "$out/dropped_keys.json" "$out/profile_failures.json" "$out/primary_keys.json"

cargo run --release -q --manifest-path "$root/Cargo.toml" -p cardinal-eval --bin operator-truth -- --bench tpch
