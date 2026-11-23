#!/usr/bin/env bash
# Prebakes data/tpcds: TPC-DS at scale factor 1 in DuckDB (its tpcds
# extension), its 99 queries' EXPLAIN ANALYZE profiles, the schema with the
# keys TPC-DS declares that hold on the data, row counts and Parquet copies;
# then the truth, by `operator-truth`.
# Usage: prepare/tpcds.sh [--sf N] [--jobs N]
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

out="$root/cardinal-eval/data/tpcds"
db="$out/tpcds.duckdb"
mkdir -p "$out/queries" "$out/profiles/duckdb"

if [ ! -f "$db" ]; then
  echo "generating TPC-DS sf $sf" >&2
  env -u AI_AGENT duckdb "$db" -c "INSTALL tpcds; LOAD tpcds; CALL dsdgen(sf = $sf);" > /dev/null
fi

# The keys TPC-DS declares: each table's primary key, and its foreign keys
# (each surrogate key references its dimension; returns reference their
# sales). Those that do not hold are dropped by `duck.py keys`.
python3 "$here/tpcds_keys.py" "$out/keys.json"

duck keys "$db" "$out"
duck schema "$db" "$out"
duck counts "$db" "$out"
duck parquet "$db" "$out"

# The queries, as the extension writes them.
python3 - "$db" "$out/queries" <<'EOF'
import json, os, subprocess, sys
env = {k: v for k, v in os.environ.items() if k != "AI_AGENT"}
out = subprocess.run(["duckdb", "-readonly", "-json", sys.argv[1]], capture_output=True, text=True, env=env,
                     input="LOAD tpcds; SELECT query_nr, query FROM tpcds_queries() ORDER BY query_nr;", check=True).stdout
for r in json.loads(out):
    with open(os.path.join(sys.argv[2], f"q{r['query_nr']:02d}.sql"), "w") as f:
        f.write(r["query"].strip() + "\n")
EOF
duck profile "$db" "$out" "$jobs"

jq -n \
  --arg duckdb "$(duck version)" \
  --arg date "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --argjson sf "$sf" \
  --slurpfile dropped "$out/dropped_keys.json" \
  --slurpfile failures "$out/profile_failures.json" \
  '{benchmark: "tpcds", engines: {duckdb: $duckdb}, scale_factor: $sf,
    generator: "duckdb tpcds extension, CALL dsdgen(sf)", seeds: null, date: $date,
    duckdb_threads: 1, dropped_keys: $dropped[0], profile_failures: $failures[0]}' > "$out/manifest.json"
rm "$out/dropped_keys.json" "$out/profile_failures.json" "$out/primary_keys.json"

cargo run --release -q --manifest-path "$root/Cargo.toml" -p cardinal-eval --bin operator-truth -- --bench tpcds
