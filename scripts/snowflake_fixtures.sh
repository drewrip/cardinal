#!/usr/bin/env bash
# Regenerates the Snowflake fixtures under tests/snowflake from TPC-H at
# scale factor 0.01, the data DuckDB's dbgen makes for tests/duckdb: each
# query's GET_QUERY_OPERATOR_STATS rows (TPC-H's, tests/duckdb/extra's and
# tests/snowflake/extra's), and each TPC-H query's EXPLAIN USING JSON.
#
# Connects with the connection CARDINAL_SF_CONNECTION (default
# my_example_connection) of ~/.config/snowflake, signing in with the key pair
# at CARDINAL_SF_PRIVATE_KEY_PATH, as role CARDINAL_SF_ROLE (default
# CMUADMIN). (Re)creates the tables in schema CARDINAL_SF_SCHEMA (default
# CMU.CARDINAL_TPCH). Needs the duckdb CLI, for the data, and uv.
#
# Rows are written with the query's name for its id, and without times, so
# that a fixture changes only with its plan. Queries Snowflake rejects are
# reported and skipped.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
out="$root/tests/snowflake"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

tables="customer lineitem nation orders part partsupp region supplier"
{
  echo "INSTALL tpch; LOAD tpch; CALL dbgen(sf = 0.01);"
  for t in $tables; do
    echo "COPY $t TO '$tmp/$t.csv' (HEADER false, DELIMITER '|');"
  done
} | duckdb -no-agent > /dev/null

mkdir -p "$out/tpch" "$out/explain" "$out/extra"
uv run --quiet --with snowflake-connector-python python - "$root" "$tmp" "$tables" <<'PY'
import glob, json, os, re, sys, tomllib
import snowflake.connector

root, tmp, tables = sys.argv[1], sys.argv[2], sys.argv[3].split()
out = f"{root}/tests/snowflake"
name = os.environ.get("CARDINAL_SF_CONNECTION", "my_example_connection")
cfg = tomllib.load(open(os.path.expanduser("~/.config/snowflake"), "rb"))["connections"][name]
cfg.pop("password", None)
cfg.update(
    private_key_file=os.path.expanduser(os.environ["CARDINAL_SF_PRIVATE_KEY_PATH"]),
    authenticator="SNOWFLAKE_JWT",
    role=os.environ.get("CARDINAL_SF_ROLE", "CMUADMIN"),
)
database, schema = os.environ.get("CARDINAL_SF_SCHEMA", "CMU.CARDINAL_TPCH").split(".")
cfg.update(database=database, schema=None)

con = snowflake.connector.connect(**cfg, session_parameters={"USE_CACHED_RESULT": False})
cur = con.cursor()
cur.execute(f"CREATE SCHEMA IF NOT EXISTS {database}.{schema}")
cur.execute(f"USE SCHEMA {database}.{schema}")

# DuckDB's schemas.
columns = {}
for c in json.load(open(f"{root}/tests/duckdb/catalog.json")):
    null = "" if c["nullable"] else " NOT NULL"
    columns.setdefault(c["table_name"], []).append(f'{c["column_name"]} {c["data_type"]}{null}')
for t in tables:
    cur.execute(f"CREATE OR REPLACE TABLE {t} ({', '.join(columns[t])})")
    cur.execute(f"PUT file://{tmp}/{t}.csv @%{t} AUTO_COMPRESS=TRUE OVERWRITE=TRUE")
    cur.execute(f"COPY INTO {t} FROM @%{t} FILE_FORMAT=(TYPE=CSV FIELD_DELIMITER='|' FIELD_OPTIONALLY_ENCLOSED_BY='\"') PURGE=TRUE")

def snowflake_sql(path):
    sql = open(path).read().strip().rstrip(";")
    # SUBSTRING(x FROM a FOR b), which Snowflake does not parse.
    return re.sub(r"substring\((\w+) from (\d+) for (\d+)\)", r"substring(\1, \2, \3)", sql, flags=re.I)

def variant(v):
    return json.loads(v) if isinstance(v, str) else v

def profile(path, dest):
    name = os.path.basename(path)[:-4]
    try:
        cur.execute(snowflake_sql(path))
        cur.fetchall()
    except snowflake.connector.errors.ProgrammingError as e:
        print(f"skipped {name}: {str(e).splitlines()[-1]}", file=sys.stderr)
        return False
    cur.execute(f"SELECT * FROM TABLE(GET_QUERY_OPERATOR_STATS('{cur.sfqid}'))")
    cols = [d[0] for d in cur.description]
    rows = []
    for r in cur.fetchall():
        r = dict(zip(cols, r))
        rows.append({
            "QUERY_ID": name,
            "STEP_ID": r["STEP_ID"],
            "OPERATOR_ID": r["OPERATOR_ID"],
            "PARENT_OPERATORS": variant(r["PARENT_OPERATORS"]),
            "OPERATOR_TYPE": r["OPERATOR_TYPE"],
            "OPERATOR_STATISTICS": variant(r["OPERATOR_STATISTICS"]),
            "OPERATOR_ATTRIBUTES": variant(r["OPERATOR_ATTRIBUTES"]),
        })
    rows.sort(key=lambda r: (r["STEP_ID"], r["OPERATOR_ID"]))
    with open(f"{dest}/{name}.json", "w") as f:
        json.dump(rows, f, indent=1)
        f.write("\n")
    return True

for path in sorted(glob.glob(f"{root}/tests/tpch/q*.sql")):
    name = os.path.basename(path)[:-4]
    if profile(path, f"{out}/tpch"):
        cur.execute("EXPLAIN USING JSON " + snowflake_sql(path))
        with open(f"{out}/explain/{name}.json", "w") as f:
            json.dump(json.loads(cur.fetchone()[0]), f, indent=1)
            f.write("\n")
for path in sorted(glob.glob(f"{root}/tests/duckdb/extra/*.sql") + glob.glob(f"{out}/extra/*.sql")):
    profile(path, f"{out}/extra")
con.close()
PY
