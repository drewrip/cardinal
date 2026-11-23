"""Snowflake profiles of TPC-H (EVAL.md §5), under a credit budget.

    snowflake_tpch.py --data data/tpch --csv data/tpch/raw/csv
                      [--dry-run] [--approve-credits N]

Loads the SF 1 tables DuckDB made into $CARDINAL_SF_SCHEMA (default
CMU.CARDINAL_EVAL_TPCH_SF1), runs each query once on a dedicated X-Small
warehouse, CARDINAL_EVAL_WH, and writes its GET_QUERY_OPERATOR_STATS rows to
profiles/snowflake/<q>.json. Connects as scripts/snowflake_fixtures.sh does:
connection $CARDINAL_SF_CONNECTION (default my_example_connection) of
~/.config/snowflake, key pair $CARDINAL_SF_PRIVATE_KEY_PATH, role
$CARDINAL_SF_ROLE (default CMUADMIN).

Credits. The budget is 2.0 credits across every run, kept in the ledger
snowflake_credits.json beside the profiles: every statement that needs the
warehouse, its time, its estimated credits and the running total. A
statement's estimate is conservative: its wall time, plus 60 s if the
warehouse was suspended (the minimum billed per resume), plus the time it
sat idle and running since the last statement; each phase adds the 60 s
auto-suspend tail. A statement starts only if the total so far plus a
projection of it (the slowest so far, or 5 minutes for the first) stays
within the limit; otherwise this stops before it, prints the ledger, and
exits with status 3. Raising the limit takes --approve-credits <new total>,
recorded in the ledger. After each phase the warehouse's metered credits
are read and recorded; the total in force is the larger of the two. A
resource monitor with CREDIT_QUOTA = 2 suspends the warehouse if this
script fails to stop, where the role may make one.

--dry-run makes empty tables (no warehouse needed), runs only EXPLAIN, and
prints the projected credits: nothing is spent.
"""

import argparse
import json
import os
import re
import sys
import time
import tomllib
from datetime import datetime, timezone
from pathlib import Path

import snowflake.connector

WAREHOUSE = "CARDINAL_EVAL_WH"
MONITOR = "CARDINAL_EVAL_RM"
BUDGET = 2.0
CREDITS_PER_HOUR = 1.0  # X-Small
RESUME_MIN_S = 60.0
SUSPEND_S = 60.0
FIRST_PROJECTION_S = 300.0
TABLES = ["customer", "lineitem", "nation", "orders", "part", "partsupp", "region", "supplier"]
OVER_BUDGET = 3


def now():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def credits(seconds):
    return seconds / 3600.0 * CREDITS_PER_HOUR


class Ledger:
    """The credit ledger: every statement on the warehouse, and the total."""

    def __init__(self, path):
        self.path = path
        self.d = json.loads(path.read_text()) if path.exists() else {
            "warehouse": WAREHOUSE, "size": "X-Small", "limit": BUDGET, "approvals": [], "statements": [],
            "metered": [], "estimated_total": 0.0, "metered_total": 0.0}
        # When the warehouse last ran a statement (it suspends SUSPEND_S after).
        self.last_end = None

    def save(self):
        self.path.write_text(json.dumps(self.d, indent=1) + "\n")

    @property
    def total(self):
        return max(self.d["estimated_total"], self.d["metered_total"])

    def approve(self, limit):
        if limit < self.d["limit"]:
            sys.exit(f"--approve-credits {limit} is below the limit in force, {self.d['limit']}")
        self.d["approvals"].append({"at": now(), "limit": limit})
        self.d["limit"] = limit
        self.save()

    def projection(self):
        s = [x["estimated_seconds"] for x in self.d["statements"]]
        return credits(max(s) if s else FIRST_PROJECTION_S)

    def guard(self, what):
        """Stops before `what` if it could take the total past the limit."""
        p = self.projection()
        if self.total + p > self.d["limit"]:
            self.print()
            print(f"\nSTOP before {what}: {self.total:.4f} spent + {p:.4f} projected > limit {self.d['limit']}.\n"
                  f"Continuing needs the user's approval: --approve-credits <new total>.", file=sys.stderr)
            sys.exit(OVER_BUDGET)

    def record(self, what, query_id, start, end, resumed):
        idle = 0.0
        if self.last_end is not None and not resumed:
            idle = max(0.0, start - self.last_end)
        seconds = (end - start) + idle + (RESUME_MIN_S if resumed else 0.0)
        self.last_end = end
        self.d["estimated_total"] += credits(seconds)
        self.d["statements"].append({
            "what": what, "query_id": query_id, "start": datetime.fromtimestamp(start, timezone.utc).isoformat(),
            "end": datetime.fromtimestamp(end, timezone.utc).isoformat(), "resumed": resumed,
            "estimated_seconds": round(seconds, 3), "estimated_credits": round(credits(seconds), 6),
            "running_total": round(self.d["estimated_total"], 6)})
        self.save()

    def tail(self, phase):
        """The auto-suspend tail at the end of a phase."""
        if self.last_end is None:
            return
        self.d["estimated_total"] += credits(SUSPEND_S)
        self.d["statements"].append({"what": f"{phase}: auto-suspend tail", "estimated_seconds": SUSPEND_S,
                                     "estimated_credits": round(credits(SUSPEND_S), 6),
                                     "running_total": round(self.d["estimated_total"], 6)})
        self.last_end = None
        self.save()

    def print(self):
        print(f"ledger {self.path}: limit {self.d['limit']}, estimated {self.d['estimated_total']:.4f}, "
              f"metered {self.d['metered_total']:.4f}", file=sys.stderr)
        for s in self.d["statements"][-10:]:
            print(f"  {s['what']}: {s['estimated_credits']:.4f} (total {s['running_total']:.4f})", file=sys.stderr)


def connect(warehouse):
    name = os.environ.get("CARDINAL_SF_CONNECTION", "my_example_connection")
    cfg = tomllib.load(open(os.path.expanduser("~/.config/snowflake"), "rb"))["connections"][name]
    cfg.pop("password", None)
    key = os.environ.get("CARDINAL_SF_PRIVATE_KEY_PATH")
    if not key:
        sys.exit("set CARDINAL_SF_PRIVATE_KEY_PATH to the key pair's private key")
    cfg.update(private_key_file=os.path.expanduser(key), authenticator="SNOWFLAKE_JWT",
               role=os.environ.get("CARDINAL_SF_ROLE", "CMUADMIN"), warehouse=warehouse, database=None, schema=None)
    return snowflake.connector.connect(**cfg, session_parameters={"USE_CACHED_RESULT": False},
                                       client_session_keep_alive=False)


def snowflake_sql(path):
    sql = path.read_text().strip().rstrip(";")
    # SUBSTRING(x FROM a FOR b), which Snowflake does not parse.
    return re.sub(r"substring\((\w+) from (\d+) for (\d+)\)", r"substring(\1, \2, \3)", sql, flags=re.I)


def ddl(schema_sql):
    """schema.sql's CREATE TABLEs, each as one statement."""
    text = "\n".join(l for l in schema_sql.splitlines() if not l.startswith("--"))
    return [s.strip() for s in text.split(";") if s.strip()]


def warehouse_state(cur):
    cur.execute(f"SHOW WAREHOUSES LIKE '{WAREHOUSE}'")
    rows = cur.fetchall()
    return rows[0][1] if rows else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", required=True, type=Path)
    ap.add_argument("--csv", required=True, type=Path)
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--approve-credits", type=float)
    args = ap.parse_args()
    database, schema = os.environ.get("CARDINAL_SF_SCHEMA", "CMU.CARDINAL_EVAL_TPCH_SF1").split(".")
    queries = sorted((args.data / "queries").glob("q*.sql"))
    ledger = Ledger(args.data / "snowflake_credits.json")
    if args.approve_credits is not None:
        ledger.approve(args.approve_credits)

    con = connect(None)
    cur = con.cursor()
    cur.execute(f"CREATE SCHEMA IF NOT EXISTS {database}.{schema}")
    cur.execute(f"USE SCHEMA {database}.{schema}")
    cur.execute("SHOW TABLES")
    cols = [d[0].lower() for d in cur.description]
    present = {r[cols.index("name")].lower(): r[cols.index("rows")] for r in cur.fetchall()}
    counts = json.loads((args.data / "cardinalities.json").read_text())

    if args.dry_run:
        dry_run(cur, args, queries, present, counts, ledger)
        con.close()
        return

    # The warehouse: X-Small, suspended until used, ours alone.
    if warehouse_state(cur) is None:
        cur.execute(f"CREATE WAREHOUSE {WAREHOUSE} WAREHOUSE_SIZE = XSMALL AUTO_SUSPEND = {int(SUSPEND_S)} "
                    f"AUTO_RESUME = TRUE INITIALLY_SUSPENDED = TRUE")
    cur.execute(f"ALTER WAREHOUSE {WAREHOUSE} SET WAREHOUSE_SIZE = XSMALL AUTO_SUSPEND = {int(SUSPEND_S)}")
    try:
        cur.execute(f"CREATE RESOURCE MONITOR IF NOT EXISTS {MONITOR} WITH CREDIT_QUOTA = {BUDGET} "
                    f"TRIGGERS ON 100 PERCENT DO SUSPEND_IMMEDIATE")
        cur.execute(f"ALTER WAREHOUSE {WAREHOUSE} SET RESOURCE_MONITOR = {MONITOR}")
        print(f"resource monitor {MONITOR}: CREDIT_QUOTA = {BUDGET}, suspends at 100 %", file=sys.stderr)
    except snowflake.connector.errors.ProgrammingError as e:
        print(f"no resource monitor ({str(e).splitlines()[-1]}): relying on the ledger alone", file=sys.stderr)
    cur.execute(f"USE WAREHOUSE {WAREHOUSE}")

    def run(what, sql):
        ledger.guard(what)
        resumed = warehouse_state(cur) != "STARTED"
        start = time.time()
        try:
            cur.execute(sql)
            rows = cur.fetchall()
        finally:
            ledger.record(what, cur.sfqid, start, time.time(), resumed)
        return rows

    def reconcile(phase):
        first = ledger.d["statements"][0]["start"] if ledger.d["statements"] else now()
        rows = run(f"{phase}: metering", f"SELECT COALESCE(SUM(CREDITS_USED), 0) FROM TABLE(INFORMATION_SCHEMA."
                   f"WAREHOUSE_METERING_HISTORY(DATE_RANGE_START => '{first}'::TIMESTAMP_LTZ, WAREHOUSE_NAME => '{WAREHOUSE}'))")
        metered = float(rows[0][0])
        ledger.d["metered"].append({"at": now(), "phase": phase, "credits": metered})
        ledger.d["metered_total"] = metered
        ledger.save()
        print(f"{phase}: estimated {ledger.d['estimated_total']:.4f}, metered {metered:.4f} credits", file=sys.stderr)

    # Load: tables made and files staged need no warehouse; COPY does.
    schema_sql = (args.data / "schema.sql").read_text()
    loaded = False
    for stmt in ddl(schema_sql):
        t = re.match(r"CREATE TABLE (\w+)", stmt).group(1)
        if present.get(t) == counts[t]:
            continue
        cur.execute(stmt.replace("CREATE TABLE", "CREATE OR REPLACE TABLE", 1))
        cur.execute(f"PUT file://{args.csv / (t + '.csv')} @%{t} AUTO_COMPRESS=TRUE OVERWRITE=TRUE PARALLEL=8")
        run(f"load {t}", f"COPY INTO {t} FROM @%{t} FILE_FORMAT=(TYPE=CSV FIELD_DELIMITER='|' "
                         f"FIELD_OPTIONALLY_ENCLOSED_BY='\"') PURGE=TRUE")
        loaded = True
    if loaded:
        reconcile("load")
        ledger.tail("load")

    out = args.data / "profiles" / "snowflake"
    out.mkdir(parents=True, exist_ok=True)
    failures = {}
    for path in queries:
        q = path.stem
        if (out / f"{q}.json").exists():
            continue
        try:
            run(f"query {q}", snowflake_sql(path))
        except snowflake.connector.errors.ProgrammingError as e:
            failures[q] = str(e).splitlines()[-1]
            print(f"skipped {q}: {failures[q]}", file=sys.stderr)
            continue
        qid = cur.sfqid
        rows = run(f"stats {q}", f"SELECT * FROM TABLE(GET_QUERY_OPERATOR_STATS('{qid}'))")
        cols = [d[0] for d in cur.description]
        variant = lambda v: json.loads(v) if isinstance(v, str) else v
        stats = []
        for r in rows:
            r = dict(zip(cols, r))
            stats.append({"QUERY_ID": q, "STEP_ID": r["STEP_ID"], "OPERATOR_ID": r["OPERATOR_ID"],
                          "PARENT_OPERATORS": variant(r["PARENT_OPERATORS"]), "OPERATOR_TYPE": r["OPERATOR_TYPE"],
                          "OPERATOR_STATISTICS": variant(r["OPERATOR_STATISTICS"]),
                          "OPERATOR_ATTRIBUTES": variant(r["OPERATOR_ATTRIBUTES"])})
        stats.sort(key=lambda r: (r["STEP_ID"], r["OPERATOR_ID"]))
        (out / f"{q}.json").write_text(json.dumps(stats, indent=1) + "\n")
    reconcile("queries")
    ledger.tail("queries")

    cur.execute(f"ALTER WAREHOUSE {WAREHOUSE} SUSPEND") if warehouse_state(cur) == "STARTED" else None
    cur.execute("SELECT CURRENT_VERSION()")
    version = cur.fetchone()[0]
    con.close()
    manifest_path = args.data / "manifest.json"
    m = json.loads(manifest_path.read_text())
    m.setdefault("engines", {})["snowflake"] = version
    m["snowflake"] = {"schema": f"{database}.{schema}", "warehouse": WAREHOUSE, "size": "X-Small",
                      "use_cached_result": False, "failures": failures,
                      "credits": {"estimated": ledger.d["estimated_total"], "metered": ledger.d["metered_total"],
                                  "limit": ledger.d["limit"]}}
    manifest_path.write_text(json.dumps(m, indent=2) + "\n")
    ledger.print()


def dry_run(cur, args, queries, present, counts, ledger):
    """Empty tables, EXPLAIN of each query, and the projected credits."""
    for stmt in ddl((args.data / "schema.sql").read_text()):
        t = re.match(r"CREATE TABLE (\w+)", stmt).group(1)
        if t not in present:
            cur.execute(stmt)
    # Loading: each COPY at a conservative 10 MB/s of CSV.
    load_s = 0.0
    print("projection (X-Small, 1 credit/hour; conservative):")
    for t in TABLES:
        if present.get(t) == counts[t]:
            continue
        mb = (args.csv / f"{t}.csv").stat().st_size / 1e6 if (args.csv / f"{t}.csv").exists() else 0.0
        s = 5 + mb / 10
        load_s += s
        print(f"  load {t:<9} {mb:8.1f} MB  ~{s:6.0f} s")
    load_s += RESUME_MIN_S + SUSPEND_S + 10  # resume, tail, metering
    # Queries: each at twice DuckDB's one-thread time, at least 5 s, and its
    # operator stats 5 s.
    query_s = RESUME_MIN_S + SUSPEND_S + 10
    failures = {}
    for path in queries:
        q = path.stem
        try:
            cur.execute("EXPLAIN USING JSON " + snowflake_sql(path))
            cur.fetchall()
        except snowflake.connector.errors.ProgrammingError as e:
            failures[q] = str(e).splitlines()[-1]
            continue
        prof = json.loads((args.data / "profiles" / "duckdb" / f"{q}.json").read_text())
        s = max(5.0, 2 * prof["query"]["total_time"]) + 5
        query_s += s
    print(f"  loads: ~{load_s:.0f} s = {credits(load_s):.3f} credits")
    print(f"  {len(queries) - len(failures)} queries: ~{query_s:.0f} s = {credits(query_s):.3f} credits")
    total = credits(load_s + query_s)
    print(f"  projected total {total:.3f} credits; spent so far {ledger.total:.4f}; limit {ledger.d['limit']}")
    for q, e in failures.items():
        print(f"  EXPLAIN failed for {q}: {e}")
    print("  dry run: nothing loaded, no warehouse used")


if __name__ == "__main__":
    main()
