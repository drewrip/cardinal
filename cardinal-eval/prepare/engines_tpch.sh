#!/usr/bin/env bash
# Prebakes data/tpch's PostgreSQL and Snowflake profiles (EVAL.md §5): the
# same 22 queries over a copy of the data DuckDB profiled.
#
# PostgreSQL: a database $CARDINAL_PG_DB (default cardinal_eval_tpch_sf1),
# made from data/tpch/tpch.duckdb, with the primary keys' indexes and
# statistics from every row; each query profiled one at a time with
# EXPLAIN (ANALYZE, VERBOSE, FORMAT JSON), with the default planner settings
# (as tests/live's pg::SETTINGS[0]: no parallel workers, no JIT). Connects
# as psql does.
#
# Snowflake: prepare/snowflake_tpch.py, which keeps a credit ledger and
# stops before the budget (2.0 credits in all) is spent. Run it with
# --dry-run first: it loads nothing, runs only EXPLAIN, and prints the
# projected credits.
#
# Usage: prepare/engines_tpch.sh [--skip-postgres] [--skip-snowflake]
#                                [--dry-run] [--approve-credits N]
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
out="$root/cardinal-eval/data/tpch"
duckdb_file="$out/tpch.duckdb"
pgdb="${CARDINAL_PG_DB:-cardinal_eval_tpch_sf1}"
timeout_ms=$((30 * 60 * 1000))

postgres=1
snowflake=1
sf_args=()
while [ $# -gt 0 ]; do
  case "$1" in
    --skip-postgres) postgres=0; shift ;;
    --skip-snowflake) snowflake=0; shift ;;
    --dry-run) sf_args+=(--dry-run); shift ;;
    --approve-credits) sf_args+=(--approve-credits "$2"); shift 2 ;;
    *) echo "unknown argument $1" >&2; exit 2 ;;
  esac
done

[ -f "$duckdb_file" ] || { echo "no $duckdb_file: run prepare/tpch.sh" >&2; exit 1; }
csv="$out/raw/csv"
tables="customer lineitem nation orders part partsupp region supplier"
if [ ! -f "$csv/supplier.csv" ]; then
  mkdir -p "$csv"
  for t in $tables; do
    echo "COPY $t TO '$csv/$t.csv' (HEADER false, DELIMITER '|');"
  done | env -u AI_AGENT duckdb -readonly "$duckdb_file" > /dev/null
fi

if [ "$postgres" = 1 ]; then
  pg() { psql -X -q -v ON_ERROR_STOP=1 "$@" 2> >(grep -v "collation version\|REFRESH COLLATION\|^DETAIL\|^HINT" >&2); }
  if ! psql -X -At -d "$pgdb" -c "SELECT count(*) FROM supplier" > /dev/null 2>&1; then
    echo "loading PostgreSQL database $pgdb" >&2
    pg -d postgres -c "DROP DATABASE IF EXISTS $pgdb" -c "CREATE DATABASE $pgdb"
    # schema.sql's tables, as PostgreSQL's types, with their primary keys.
    sed -e 's/DECIMAL/numeric/g' -e 's/^--.*//' "$out/schema.sql" | pg -d "$pgdb"
    for t in $tables; do
      pg -d "$pgdb" -c "\\copy $t FROM '$csv/$t.csv' (FORMAT csv, DELIMITER '|')"
    done
    # Statistics from every row, so that the plans are the same each time.
    pg -d "$pgdb" -c "ALTER DATABASE $pgdb SET default_statistics_target = 1000"
    pg -d "$pgdb" -c "ANALYZE"
  fi
  settings="SET max_parallel_workers_per_gather = 0; SET jit = off; SET statement_timeout = $timeout_ms;"
  mkdir -p "$out/profiles/postgres"
  failures="{}"
  # One at a time: the counts of a plan with workers depend on what else runs.
  for f in "$out"/queries/q*.sql; do
    q="$(basename "$f" .sql)"
    echo "postgres $q" >&2
    if res="$({
        echo "$settings"
        echo "EXPLAIN (ANALYZE, TIMING OFF, BUFFERS OFF, SUMMARY OFF, VERBOSE, COSTS OFF, FORMAT JSON)"
        sed -e 's/;[[:space:]]*$//' "$f"
        echo ";"
      } | psql -X -q -At -v ON_ERROR_STOP=1 -d "$pgdb" 2>&1)" && grep -q '^\[' <<< "$res"; then
      printf '%s\n' "$res" | sed -n '/^\[/,$p' > "$out/profiles/postgres/$q.json"
    else
      rm -f "$out/profiles/postgres/$q.json"
      failures="$(jq --arg q "$q" --arg e "$(printf '%s' "$res" | grep -v collation | head -c 500)" '. + {($q): $e}' <<< "$failures")"
    fi
  done
  version="$(psql -X -At -d "$pgdb" -c "SHOW server_version" 2>/dev/null)"
  tmp="$(mktemp)"
  jq --arg v "$version" --arg s "$settings" --argjson f "$failures" --arg db "$pgdb" \
    '.engines.postgres = $v | .postgres = {database: $db, settings: $s, default_statistics_target: 1000,
      indexes: "primary keys", explain: "ANALYZE, TIMING OFF, BUFFERS OFF, SUMMARY OFF, VERBOSE, COSTS OFF, FORMAT JSON",
      failures: $f}' "$out/manifest.json" > "$tmp"
  mv "$tmp" "$out/manifest.json"
fi

if [ "$snowflake" = 1 ]; then
  uv run --quiet --with snowflake-connector-python python "$here/snowflake_tpch.py" --data "$out" --csv "$csv" "${sf_args[@]}"
fi
