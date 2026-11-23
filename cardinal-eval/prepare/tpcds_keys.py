#!/usr/bin/env python3
"""Writes the keys TPC-DS declares (DSB's are the same) as `keys.json`:
each table's primary key, and its foreign keys (each surrogate key
references its dimension; returns reference their sales). Those that do
not hold on the data are dropped by `duck.py keys`.

    tpcds_keys.py <keys.json>
"""
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
