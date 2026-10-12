#!/usr/bin/env bash
# Regenerates the PostgreSQL EXPLAIN fixtures under tests/postgres from TPC-H
# at scale factor 0.01, the data DuckDB's dbgen makes for tests/duckdb: a
# profile per query (TPC-H's, tests/duckdb/extra's and tests/postgres/extra's),
# each TPC-H query's plain EXPLAIN plan, the profiles again with indexes on
# the keys, and again in parallel, one over a partial index, and the true
# counts that tests/postgres.rs checks the derived facts against.
#
#
# Connects as psql does (PGHOST, PGPORT, PGUSER, ...), and (re)creates the
# database $CARDINAL_PG_DB (default cardinal_tpch). Needs the duckdb CLI, for
# the data. With CARDINAL_PG_OLD_PORT, the port of a version 14 server on the
# same host, the indexed profiles are also taken there (tests/postgres/v14),
# from a copy of the database: it prints InitPlans, SubPlans and windows
# otherwise.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
out="$root/tests/postgres"
db="${CARDINAL_PG_DB:-cardinal_tpch}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

tables="customer lineitem nation orders part partsupp region supplier"
{
  echo "INSTALL tpch; LOAD tpch; CALL dbgen(sf = 0.01);"
  for t in $tables; do
    echo "COPY $t TO '$tmp/$t.csv' (HEADER false, DELIMITER '|');"
  done
} | duckdb > /dev/null

psql -q -d postgres -c "DROP DATABASE IF EXISTS $db" -c "CREATE DATABASE $db"
# DuckDB's schemas, as PostgreSQL's types.
python3 - "$root/tests/duckdb/catalog.json" <<'PY' | psql -q -d "$db"
import json, sys
tables = {}
for c in json.load(open(sys.argv[1])):
    null = "" if c["nullable"] else " NOT NULL"
    ty = c["data_type"].replace("DECIMAL", "numeric").lower()
    tables.setdefault(c["table_name"], []).append(f'{c["column_name"]} {ty}{null}')
for t, cols in tables.items():
    print(f"CREATE TABLE {t} ({', '.join(cols)});")
PY
for t in $tables; do
  psql -q -d "$db" -c "\\copy $t FROM '$tmp/$t.csv' (FORMAT csv, DELIMITER '|')"
done
# Statistics from every row, so that the plans are the same each time.
psql -q -d "$db" -c "ALTER DATABASE $db SET default_statistics_target = 1000"
psql -q -d "$db" -c "ANALYZE"

# One process, so that the plans are those of one: tests/postgres/parallel
# has those of several.
settings="SET max_parallel_workers_per_gather = 0; SET jit = off;"

explain() { # options, sql file -> json
  {
    echo "$settings"
    echo "EXPLAIN ($1, VERBOSE, COSTS OFF, FORMAT JSON)"
    sed -e 's/;[[:space:]]*$//' "$2"
    echo ";"
  } | psql -q -At -d "$db"
}
profile="ANALYZE, TIMING OFF, BUFFERS OFF, SUMMARY OFF"

mkdir -p "$out/tpch" "$out/explain" "$out/extra" "$out/indexed"
for f in "$root"/tests/tpch/q*.sql; do
  explain "$profile" "$f" > "$out/tpch/$(basename "$f" .sql).json"
  explain "ANALYZE FALSE" "$f" > "$out/explain/$(basename "$f" .sql).json"
done
for f in "$root"/tests/duckdb/extra/*.sql "$out"/extra/*.sql; do
  [ -e "$f" ] || continue
  explain "$profile" "$f" > "$out/extra/$(basename "$f" .sql).json"
done

# The same queries with indexes on the keys: index scans, nested loops and
# merge joins, whose rows are often not counted.
psql -q -d "$db" <<'SQL'
ALTER TABLE region ADD PRIMARY KEY (r_regionkey);
ALTER TABLE nation ADD PRIMARY KEY (n_nationkey);
ALTER TABLE supplier ADD PRIMARY KEY (s_suppkey);
ALTER TABLE customer ADD PRIMARY KEY (c_custkey);
ALTER TABLE part ADD PRIMARY KEY (p_partkey);
ALTER TABLE partsupp ADD PRIMARY KEY (ps_partkey, ps_suppkey);
ALTER TABLE orders ADD PRIMARY KEY (o_orderkey);
ALTER TABLE lineitem ADD PRIMARY KEY (l_orderkey, l_linenumber);
CREATE INDEX ON lineitem (l_partkey, l_suppkey);
CREATE INDEX ON lineitem (l_shipdate);
CREATE INDEX ON orders (o_custkey);
CREATE INDEX ON orders (o_orderdate);
CREATE INDEX ON partsupp (ps_suppkey);
CREATE INDEX ON customer (c_nationkey);
CREATE INDEX ON supplier (s_nationkey);
ANALYZE;
SQL
for f in "$root"/tests/tpch/q*.sql "$root"/tests/duckdb/extra/*.sql "$out"/extra/*.sql; do
  [ -e "$f" ] || continue
  explain "$profile" "$f" > "$out/indexed/$(basename "$f" .sql).json"
done

# And in several processes, which split the rows of what they share: each
# operator reports an average over them.
mkdir -p "$out/parallel"
parallel="SET max_parallel_workers_per_gather = 2; SET parallel_setup_cost = 0; SET parallel_tuple_cost = 0;"
parallel="$parallel SET min_parallel_table_scan_size = 0; SET min_parallel_index_scan_size = 0; SET jit = off;"
for f in "$root"/tests/tpch/q*.sql "$root"/tests/duckdb/extra/*.sql "$out"/extra/*.sql; do
  [ -e "$f" ] || continue
  settings="$parallel" explain "$profile" "$f" > "$out/parallel/$(basename "$f" .sql).json"
done

if [ -n "${CARDINAL_PG_OLD_PORT:-}" ]; then
  mkdir -p "$out/v14"
  PGPORT="$CARDINAL_PG_OLD_PORT" psql -q -d postgres -c "DROP DATABASE IF EXISTS $db" -c "CREATE DATABASE $db"
  # A setting version 14 does not know.
  pg_dump --no-owner -d "$db" | grep -v '^SET transaction_timeout' | PGPORT="$CARDINAL_PG_OLD_PORT" psql -q -d "$db" > /dev/null
  PGPORT="$CARDINAL_PG_OLD_PORT" psql -q -d "$db" -c "ANALYZE"
  for f in "$root"/tests/tpch/q*.sql "$root"/tests/duckdb/extra/*.sql "$out"/extra/*.sql; do
    PGPORT="$CARDINAL_PG_OLD_PORT" explain "$profile" "$f" > "$out/v14/$(basename "$f" .sql).json"
  done
fi

# A partial index, whose predicate the plan of a scan of it does not print.
# (A bitmap scan's recheck would.)
mkdir -p "$out/partial"
psql -q -d "$db" -c "CREATE INDEX orders_urgent ON orders (o_orderdate) WHERE o_orderpriority = '1-URGENT'" -c "ANALYZE orders"
for f in "$out"/partial/*.sql; do
  settings="$settings SET enable_bitmapscan = off;" explain "$profile" "$f" > "${f%.sql}.json"
done
# Its predicate, as Catalog::with_partial_indexes takes it.
psql -q -At -d "$db" > "$out/partial/indexes.txt" <<'SQL'
SELECT c.relname, pg_get_expr(i.indpred, i.indrelid) FROM pg_index i
JOIN pg_class c ON c.oid = i.indexrelid WHERE i.indpred IS NOT NULL;
SQL
psql -q -d "$db" -c "DROP INDEX orders_urgent"

# Every fact the tests derive that counts rows of base tables, counted: of
# the plans with indexes, too.
(cd "$root" && cargo test -q --test postgres dump_fact_queries > /dev/null)
{
  echo "SELECT json_agg(t) FROM ("
  sed -e 's/;[[:space:]]*$//' "$out/fact_checks.sql"
  echo ") t;"
} | psql -q -At -d "$db" > "$out/fact_checks.json"
