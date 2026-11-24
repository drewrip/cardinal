#!/usr/bin/env bash
# Prebakes data/job: the IMDB snapshot of the Join Order Benchmark (CWI's
# imdb.tgz) loaded into DuckDB, the 113 queries and schema of
# gregrahn/join-order-benchmark at a pinned commit, their EXPLAIN ANALYZE
# profiles, the keys (each checked on the data), row counts and Parquet
# copies; then the truth, by `operator-truth`.
# Usage: prepare/job.sh [--jobs N]
set -euo pipefail

jobs=8
while [ $# -gt 0 ]; do
  case "$1" in
    --jobs) jobs="$2"; shift 2 ;;
    *) echo "unknown argument $1" >&2; exit 2 ;;
  esac
done

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
duck() { python3 "$here/duck.py" "$@"; }

commit=a39603662e023e449cb2121997a5034df9e02ebf
out="$root/cardinal-eval/data/job"
raw="$out/raw"
db="$out/job.duckdb"
mkdir -p "$raw" "$out/queries" "$out/profiles/duckdb"

if [ ! -d "$raw/jobrepo" ]; then
  git clone -q https://github.com/gregrahn/join-order-benchmark "$raw/jobrepo"
fi
git -C "$raw/jobrepo" checkout -q "$commit"
if [ ! -f "$raw/imdb.tgz.done" ]; then
  curl -sSL -o "$raw/imdb.tgz" https://event.cwi.nl/da/job/imdb.tgz
  touch "$raw/imdb.tgz.done"
fi
if [ ! -f "$raw/csv/title.csv" ]; then
  mkdir -p "$raw/csv"
  tar -xzf "$raw/imdb.tgz" -C "$raw/csv"
fi

if [ ! -f "$raw/rfc/title.csv" ]; then
  echo "rewriting the CSVs as RFC 4180" >&2
  mkdir -p "$raw/rfc"
  ls "$raw"/csv/*.csv | xargs -P "$jobs" -I{} sh -c 'python3 "$0" "$1" "$2/rfc/$(basename "$1")"' "$here/pgcsv.py" {} "$raw"
fi

if [ ! -f "$db" ]; then
  echo "loading IMDB" >&2
  # The schema without its keys (checked below, and declared to cardinal
  # only if they hold), in DuckDB's types.
  sed -e 's/ PRIMARY KEY//' -e 's/character varying([0-9]*)/VARCHAR/' -e 's/\btext\b/VARCHAR/' \
    "$raw/jobrepo/schema.sql" > "$raw/schema_duckdb.sql"
  {
    cat "$raw/schema_duckdb.sql"
    for f in "$raw"/rfc/*.csv; do
      t="$(basename "$f" .csv)"
      echo "COPY $t FROM '$f' (FORMAT csv, HEADER false, DELIM ',', QUOTE '\"', ESCAPE '\"', NULL '', ALLOW_QUOTED_NULLS false);"
    done
  } | env -u AI_AGENT duckdb "$db" > "$raw/load.log" 2>&1 || { cat "$raw/load.log" >&2; rm -f "$db"; exit 1; }
  if grep -q Error "$raw/load.log"; then cat "$raw/load.log" >&2; rm -f "$db"; exit 1; fi
fi

# Every table's key is its id; the foreign keys are those the benchmark
# indexes (fkindexes.sql).
python3 - "$out/keys.json" <<'EOF'
import json, sys
tables = ["aka_name", "aka_title", "cast_info", "char_name", "comp_cast_type", "company_name", "company_type",
          "complete_cast", "info_type", "keyword", "kind_type", "link_type", "movie_companies", "movie_info",
          "movie_info_idx", "movie_keyword", "movie_link", "name", "person_info", "role_type", "title"]
fks = [("aka_name", "person_id", "name"), ("aka_title", "movie_id", "title"), ("aka_title", "kind_id", "kind_type"),
       ("cast_info", "person_id", "name"), ("cast_info", "movie_id", "title"), ("cast_info", "person_role_id", "char_name"),
       ("cast_info", "role_id", "role_type"), ("complete_cast", "movie_id", "title"),
       ("complete_cast", "subject_id", "comp_cast_type"), ("complete_cast", "status_id", "comp_cast_type"),
       ("movie_companies", "movie_id", "title"), ("movie_companies", "company_id", "company_name"),
       ("movie_companies", "company_type_id", "company_type"), ("movie_info", "movie_id", "title"),
       ("movie_info", "info_type_id", "info_type"), ("movie_info_idx", "movie_id", "title"),
       ("movie_info_idx", "info_type_id", "info_type"), ("movie_keyword", "movie_id", "title"),
       ("movie_keyword", "keyword_id", "keyword"), ("movie_link", "movie_id", "title"),
       ("movie_link", "linked_movie_id", "title"), ("movie_link", "link_type_id", "link_type"),
       ("person_info", "person_id", "name"), ("person_info", "info_type_id", "info_type"),
       ("title", "kind_id", "kind_type"), ("title", "episode_of_id", "title")]
json.dump({"primary": {t: ["id"] for t in tables},
           "foreign": [{"table": t, "columns": [c], "references": r, "referenced": ["id"]} for t, c, r in fks]},
          open(sys.argv[1], "w"), indent=1)
EOF

duck keys "$db" "$out"
duck schema "$db" "$out"
duck counts "$db" "$out"
duck parquet "$db" "$out"

# The queries, and each one's template: 1a-1d are template 1.
python3 - "$raw/jobrepo" "$out" <<'EOF'
import json, os, re, sys
src, out = sys.argv[1:]
meta = {}
for f in sorted(os.listdir(src)):
    m = re.fullmatch(r"(\d+)([a-z])\.sql", f)
    if not m:
        continue
    name = f"{int(m.group(1)):02d}{m.group(2)}"
    sql = open(os.path.join(src, f)).read().strip()
    meta[name] = {"template": f"{int(m.group(1)):02d}"}
    # `at` is reserved in DuckDB 2.0: 15a-d's alias of aka_title is renamed,
    # which changes nothing else.
    renamed = re.sub(r"\bat\.", "aka_t.", re.sub(r"\bAS at\b", "AS aka_t", sql))
    if renamed != sql:
        meta[name]["rewritten"] = "alias at renamed aka_t (reserved in DuckDB 2.0)"
    with open(os.path.join(out, "queries", name + ".sql"), "w") as o:
        o.write(renamed + "\n")
json.dump(meta, open(os.path.join(out, "queries.json"), "w"), indent=1, sort_keys=True)
EOF
duck profile "$db" "$out" "$jobs"

jq -n \
  --arg duckdb "$(duck version)" \
  --arg date "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg commit "$commit" \
  --slurpfile dropped "$out/dropped_keys.json" \
  --slurpfile failures "$out/profile_failures.json" \
  '{benchmark: "job", engines: {duckdb: $duckdb}, data: "https://event.cwi.nl/da/job/imdb.tgz",
    queries: ("gregrahn/join-order-benchmark@" + $commit), seeds: null, date: $date,
    duckdb_threads: 1, dropped_keys: $dropped[0], profile_failures: $failures[0]}' > "$out/manifest.json"
rm "$out/dropped_keys.json" "$out/profile_failures.json" "$out/primary_keys.json"

cargo run --release -q --manifest-path "$root/Cargo.toml" -p cardinal-eval --bin operator-truth -- --bench job
