#!/usr/bin/env bash
# Prebakes data/dsb: microsoft/dsb at a pinned commit, its dsdgen and dsqgen
# built from source; DSB at scale factor 1 (its skewed, correlated
# distributions) loaded into DuckDB; every template of its three query sets
# (SPJ, aggregate, multi-block, PostgreSQL dialect) instantiated three
# times with fixed seeds and each instance profiled; the TPC-DS keys that
# hold, row counts and Parquet copies; then the truth, by `operator-truth`.
# Queries are named <set>/<template>/i<n>.
# Usage: prepare/dsb.sh [--sf N] [--jobs N]
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

commit=ec9a156ceee923db1114cbe388f6183b53d49787
seed=997
out="$root/cardinal-eval/data/dsb"
raw="$out/raw"
db="$out/dsb.duckdb"
mkdir -p "$raw" "$out/queries" "$out/profiles/duckdb"

if [ ! -d "$raw/dsb" ]; then
  git clone -q https://github.com/microsoft/dsb "$raw/dsb"
fi
git -C "$raw/dsb" checkout -q "$commit"
tools="$raw/build"
if [ ! -x "$tools/dsqgen" ]; then
  rm -rf "$tools"
  cp -r "$raw/dsb/code/tools" "$tools"
  make -C "$tools" -f makefile OS=LINUX -j"$jobs" > "$raw/build.log" 2>&1
fi

if [ ! -f "$raw/data/store_sales.dat" ]; then
  echo "generating DSB sf $sf" >&2
  mkdir -p "$raw/data"
  (cd "$tools" && ./dsdgen -scale "$sf" -dir "$raw/data" -terminate n -force -quiet y > "$raw/dsdgen.log" 2>&1)
fi

if [ ! -f "$db" ]; then
  echo "loading DSB" >&2
  python3 - "$raw/dsb/scripts/create_tables.sql" "$raw/data" > "$raw/load.sql" <<'EOF'
import os, re, sys
# The tables without their keys (checked below, and declared to cardinal
# only if they hold), and each loaded from its .dat file.
ddl = re.sub(r"--[^\n]*", "", open(sys.argv[1]).read())
ddl = re.sub(r",\s*primary key\s*\([^)]*\)", "", ddl, flags=re.I)
for stmt in [s.strip() for s in ddl.split(";") if s.strip()]:
    name = re.match(r"create table\s+(\w+)", stmt, re.I).group(1)
    if name == "dbgen_version":
        continue
    print(stmt + ";")
    print(f"COPY {name} FROM '{os.path.join(sys.argv[2], name + '.dat')}' (FORMAT csv, DELIM '|', HEADER false, QUOTE '', ESCAPE '', NULL '');")
EOF
  env -u AI_AGENT duckdb "$db" < "$raw/load.sql" > "$raw/load.log" 2>&1 || { cat "$raw/load.log" >&2; rm -f "$db"; exit 1; }
  if grep -q Error "$raw/load.log"; then cat "$raw/load.log" >&2; rm -f "$db"; exit 1; fi
fi

python3 "$here/tpcds_keys.py" "$out/keys.json"
duck keys "$db" "$out"
duck schema "$db" "$out"
duck counts "$db" "$out"
duck parquet "$db" "$out"

# Three instances of every template, by dsqgen with a fixed seed.
python3 - "$tools" "$raw/dsb/query_templates_pg" "$out" "$sf" "$seed" <<'EOF'
import json, os, shutil, subprocess, sys, tempfile
tools, templates, out, sf, seed = sys.argv[1:]
sets = {"spj_queries": "spj", "agg_queries": "agg", "multi_block_queries": "multi_block"}
meta = {}
for d, name in sets.items():
    for tpl in sorted(os.listdir(os.path.join(templates, d))):
        if not tpl.startswith("query") or not tpl.endswith(".tpl"):
            continue
        template = tpl[:-4]
        tmp = tempfile.mkdtemp()
        subprocess.run(["./dsqgen", "-output_dir", tmp, "-streams", "3", "-directory", os.path.join(templates, d),
                        "-template", tpl, "-dialect", "postgres", "-rngseed", seed, "-scale", sf, "-quiet", "y"],
                       cwd=tools, check=True, capture_output=True)
        for i in range(3):
            q = f"{name}/{template}/i{i + 1}"
            path = os.path.join(out, "queries", q + ".sql")
            os.makedirs(os.path.dirname(path), exist_ok=True)
            sql = open(os.path.join(tmp, f"query_{i}.sql")).read().strip()
            # A template of several statements (query039's two) keeps its
            # first: a profile is of one statement.
            statements = [s.strip() for s in sql.split(";") if s.strip()]
            with open(path, "w") as f:
                f.write(statements[0] + ";\n")
            meta[q] = {"template": f"{name}/{template}", "set": name, "instance": i + 1}
            if len(statements) > 1:
                meta[q]["statements"] = len(statements)
                meta[q]["kept"] = "first statement"
        shutil.rmtree(tmp)
json.dump(meta, open(os.path.join(out, "queries.json"), "w"), indent=1, sort_keys=True)
EOF
duck profile "$db" "$out" "$jobs"

jq -n \
  --arg duckdb "$(duck version)" \
  --arg date "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg commit "$commit" \
  --argjson sf "$sf" \
  --argjson seed "$seed" \
  --slurpfile dropped "$out/dropped_keys.json" \
  --slurpfile failures "$out/profile_failures.json" \
  '{benchmark: "dsb", engines: {duckdb: $duckdb}, scale_factor: $sf,
    generator: ("microsoft/dsb@" + $commit + " dsdgen, built from source"),
    seeds: {dsqgen_rngseed: $seed, instances: 3}, date: $date,
    duckdb_threads: 1, dropped_keys: $dropped[0], profile_failures: $failures[0]}' > "$out/manifest.json"
rm "$out/dropped_keys.json" "$out/profile_failures.json" "$out/primary_keys.json"

cargo run --release -q --manifest-path "$root/Cargo.toml" -p cardinal-eval --bin operator-truth -- --bench dsb
