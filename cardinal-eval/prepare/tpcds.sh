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
python3 - "$out/keys.json" <<'EOF'
import json, sys
primary = {
  "call_center": ["cc_call_center_sk"], "catalog_page": ["cp_catalog_page_sk"],
  "catalog_returns": ["cr_item_sk", "cr_order_number"], "catalog_sales": ["cs_item_sk", "cs_order_number"],
  "customer": ["c_customer_sk"], "customer_address": ["ca_address_sk"], "customer_demographics": ["cd_demo_sk"],
  "date_dim": ["d_date_sk"], "household_demographics": ["hd_demo_sk"], "income_band": ["ib_income_band_sk"],
  "inventory": ["inv_date_sk", "inv_item_sk", "inv_warehouse_sk"], "item": ["i_item_sk"], "promotion": ["p_promo_sk"],
  "reason": ["r_reason_sk"], "ship_mode": ["sm_ship_mode_sk"], "store": ["s_store_sk"],
  "store_returns": ["sr_item_sk", "sr_ticket_number"], "store_sales": ["ss_item_sk", "ss_ticket_number"],
  "time_dim": ["t_time_sk"], "warehouse": ["w_warehouse_sk"], "web_page": ["wp_web_page_sk"],
  "web_returns": ["wr_item_sk", "wr_order_number"], "web_sales": ["ws_item_sk", "ws_order_number"],
  "web_site": ["web_site_sk"],
}
dims = {
  "date": "date_dim", "time": "time_dim", "item": "item", "customer": "customer", "cdemo": "customer_demographics",
  "hdemo": "household_demographics", "addr": "customer_address", "store": "store", "promo": "promotion",
  "reason": "reason", "call_center": "call_center", "catalog_page": "catalog_page", "ship_mode": "ship_mode",
  "warehouse": "warehouse", "web_page": "web_page", "web_site": "web_site", "income_band": "income_band",
}
refs = {
  "store_sales": [("ss_sold_date_sk", "date"), ("ss_sold_time_sk", "time"), ("ss_item_sk", "item"),
                  ("ss_customer_sk", "customer"), ("ss_cdemo_sk", "cdemo"), ("ss_hdemo_sk", "hdemo"),
                  ("ss_addr_sk", "addr"), ("ss_store_sk", "store"), ("ss_promo_sk", "promo")],
  "store_returns": [("sr_returned_date_sk", "date"), ("sr_return_time_sk", "time"), ("sr_item_sk", "item"),
                    ("sr_customer_sk", "customer"), ("sr_cdemo_sk", "cdemo"), ("sr_hdemo_sk", "hdemo"),
                    ("sr_addr_sk", "addr"), ("sr_store_sk", "store"), ("sr_reason_sk", "reason")],
  "catalog_sales": [("cs_sold_date_sk", "date"), ("cs_sold_time_sk", "time"), ("cs_ship_date_sk", "date"),
                    ("cs_bill_customer_sk", "customer"), ("cs_bill_cdemo_sk", "cdemo"), ("cs_bill_hdemo_sk", "hdemo"),
                    ("cs_bill_addr_sk", "addr"), ("cs_ship_customer_sk", "customer"), ("cs_ship_cdemo_sk", "cdemo"),
                    ("cs_ship_hdemo_sk", "hdemo"), ("cs_ship_addr_sk", "addr"), ("cs_call_center_sk", "call_center"),
                    ("cs_catalog_page_sk", "catalog_page"), ("cs_ship_mode_sk", "ship_mode"),
                    ("cs_warehouse_sk", "warehouse"), ("cs_item_sk", "item"), ("cs_promo_sk", "promo")],
  "catalog_returns": [("cr_returned_date_sk", "date"), ("cr_returned_time_sk", "time"), ("cr_item_sk", "item"),
                      ("cr_refunded_customer_sk", "customer"), ("cr_refunded_cdemo_sk", "cdemo"),
                      ("cr_refunded_hdemo_sk", "hdemo"), ("cr_refunded_addr_sk", "addr"),
                      ("cr_returning_customer_sk", "customer"), ("cr_returning_cdemo_sk", "cdemo"),
                      ("cr_returning_hdemo_sk", "hdemo"), ("cr_returning_addr_sk", "addr"),
                      ("cr_call_center_sk", "call_center"), ("cr_catalog_page_sk", "catalog_page"),
                      ("cr_ship_mode_sk", "ship_mode"), ("cr_warehouse_sk", "warehouse"), ("cr_reason_sk", "reason")],
  "web_sales": [("ws_sold_date_sk", "date"), ("ws_sold_time_sk", "time"), ("ws_ship_date_sk", "date"),
                ("ws_item_sk", "item"), ("ws_bill_customer_sk", "customer"), ("ws_bill_cdemo_sk", "cdemo"),
                ("ws_bill_hdemo_sk", "hdemo"), ("ws_bill_addr_sk", "addr"), ("ws_ship_customer_sk", "customer"),
                ("ws_ship_cdemo_sk", "cdemo"), ("ws_ship_hdemo_sk", "hdemo"), ("ws_ship_addr_sk", "addr"),
                ("ws_web_page_sk", "web_page"), ("ws_web_site_sk", "web_site"), ("ws_ship_mode_sk", "ship_mode"),
                ("ws_warehouse_sk", "warehouse"), ("ws_promo_sk", "promo")],
  "web_returns": [("wr_returned_date_sk", "date"), ("wr_returned_time_sk", "time"), ("wr_item_sk", "item"),
                  ("wr_refunded_customer_sk", "customer"), ("wr_refunded_cdemo_sk", "cdemo"),
                  ("wr_refunded_hdemo_sk", "hdemo"), ("wr_refunded_addr_sk", "addr"),
                  ("wr_returning_customer_sk", "customer"), ("wr_returning_cdemo_sk", "cdemo"),
                  ("wr_returning_hdemo_sk", "hdemo"), ("wr_returning_addr_sk", "addr"),
                  ("wr_web_page_sk", "web_page"), ("wr_reason_sk", "reason")],
  "inventory": [("inv_date_sk", "date"), ("inv_item_sk", "item"), ("inv_warehouse_sk", "warehouse")],
  "customer": [("c_current_cdemo_sk", "cdemo"), ("c_current_hdemo_sk", "hdemo"), ("c_current_addr_sk", "addr"),
               ("c_first_shipto_date_sk", "date"), ("c_first_sales_date_sk", "date")],
  "household_demographics": [("hd_income_band_sk", "income_band")],
  "store": [("s_closed_date_sk", "date")],
  "call_center": [("cc_closed_date_sk", "date"), ("cc_open_date_sk", "date")],
  "promotion": [("p_start_date_sk", "date"), ("p_end_date_sk", "date"), ("p_item_sk", "item")],
  "web_page": [("wp_creation_date_sk", "date"), ("wp_access_date_sk", "date"), ("wp_customer_sk", "customer")],
  "web_site": [("web_open_date_sk", "date"), ("web_close_date_sk", "date")],
  "catalog_page": [("cp_start_date_sk", "date"), ("cp_end_date_sk", "date")],
}
foreign = [{"table": t, "columns": [c], "references": dims[d], "referenced": primary[dims[d]]}
           for t, cs in refs.items() for c, d in cs]
for ret, sales, (a, b), (x, y) in [
    ("store_returns", "store_sales", ("sr_item_sk", "sr_ticket_number"), ("ss_item_sk", "ss_ticket_number")),
    ("catalog_returns", "catalog_sales", ("cr_item_sk", "cr_order_number"), ("cs_item_sk", "cs_order_number")),
    ("web_returns", "web_sales", ("wr_item_sk", "wr_order_number"), ("ws_item_sk", "ws_order_number"))]:
    foreign.append({"table": ret, "columns": [a, b], "references": sales, "referenced": [x, y]})
json.dump({"primary": primary, "foreign": foreign}, open(sys.argv[1], "w"), indent=1)
EOF

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
