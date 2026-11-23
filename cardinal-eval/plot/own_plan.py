# /// script
# requires-python = ">=3.10"
# dependencies = ["matplotlib>=3.8", "numpy>=1.26"]
# ///
"""Figures and summary of own-plan runs (EVAL.md §4).

    uv run plot/own_plan.py <run>... [--out DIR] [--summary] [--tex]

`own-plan-<bench>.pdf`: (1) the upper bound against the truth, one point
per query, log-log with the diagonal, unbounded queries in the ∞ strip;
(2) the CDF of qU over queries, one line per run (default, --unbounded,
--cardinalities). `--summary` lists every query not exact, with its
bounds: a to-do list.
"""

import argparse
import math
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import style  # noqa: E402
from style import Strip, q  # noqa: E402

import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("runs", nargs="+")
    ap.add_argument("--out", default="figures")
    ap.add_argument("--summary", action="store_true")
    ap.add_argument("--tex", action="store_true")
    args = ap.parse_args()
    style.setup(args.tex)
    by_bench = defaultdict(list)
    for path in args.runs:
        meta, records = style.load_run(path)
        by_bench[meta["bench"]].append((meta, [r for r in records if r["eval"] == "own-plan" and r.get("error") is None]))
    for bench, runs in sorted(by_bench.items()):
        if args.summary:
            for meta, records in runs:
                summary(bench, meta, records)
        else:
            figure(bench, runs, Path(args.out))


def bounds(r):
    lo, up = r.get("lower"), r.get("upper")
    return f"{lo} <= X" if up is None else (f"X = {up}" if lo == up else f"{lo} <= X <= {up}")


def figure(bench, runs, out):
    fig, (a, b) = plt.subplots(1, 2, figsize=(style.TWO_COLUMNS, 2.6), gridspec_kw={"wspace": 0.3})
    meta, records = runs[0]
    truths = [max(r["truth"], 1) for r in records]
    uppers = [math.inf if r["upper"] is None else max(r["upper"], 1) for r in records]
    finite = [u for u in uppers if not math.isinf(u)] + truths
    strip = Strip(a, max(finite))
    lo, hi = 0.7, max(finite) * 1.5
    a.plot([lo, hi], [lo, hi], color="#888888", lw=0.8, linestyle=":", label="exact")
    a.set_xscale("log")
    a.set_xlim(lo, hi)
    st = style.style(0)
    strip.points(truths, uppers, color=st["color"], marker=st["marker"], s=10, label=style.label(meta))
    bad = [r for r in records if r.get("holds") is False]
    strip.unsound([max(r["truth"], 1) for r in bad], [math.inf if r["upper"] is None else max(r["upper"], 1) for r in bad])
    a.set_xlabel("true rows")
    a.set_ylabel("proven upper bound")
    exact = sum(bool(r["exact"]) for r in records)
    a.set_title(f"{bench.upper()}: each query with its own plan ({exact} of {len(records)} exact)", fontsize=8)

    allq = [q(r) for _, rs in runs for r in rs]
    top, brk, inf = style.strip_levels(max([v for v in allq if not math.isinf(v)] or [10]))
    for i, (m, rs) in enumerate(runs):
        vals = sorted(q(r) for r in rs)
        n = len(vals)
        xs = [inf if math.isinf(v) else v for v in vals]
        ys = np.arange(1, n + 1) / n
        st = style.style(i)
        b.step(xs, ys, where="post", color=st["color"], linestyle=st["linestyle"], label=style.label(m))
    b.set_xscale("log")
    b.set_ylim(0, 1.02)
    b.set_yticks([0, 0.25, 0.5, 0.75, 1])
    b.set_yticklabels(["0", "", "0.5", "", "1"])
    b.set_xlim(0.9, inf * 2)
    ticks = [t for t in 10.0 ** np.arange(0, math.log10(top) + 1)]
    b.set_xticks(ticks + [inf])
    b.set_xticklabels([style.tick(t) for t in ticks] + [r"$\infty$"])
    b.axvspan(brk, inf * 2, color="#f4f4f4", zorder=0, lw=0)
    b.set_xlabel(r"upper Q-error $q_U$")
    b.set_ylabel("share of queries")
    b.grid(axis="x", color="#dddddd", lw=0.5)
    b.legend(loc="lower right")
    style.save(fig, out / f"own-plan-{bench}")


def summary(bench, meta, records):
    exact = [r for r in records if r["exact"]]
    print(f"\n{bench.upper()} own plan — {style.label(meta)}: {len(exact)} of {len(records)} exact")
    checks = meta.get("checks", {})
    print(f"  unsound: {len(checks.get('unsound', []))}; records with limited > 0: {checks.get('limited', 'n/a')}")
    print(f"  {'query':<8} {'truth':>10}  bounds")
    for r in sorted((r for r in records if not r["exact"]), key=lambda r: -q(r)):
        print(f"  {r['target']:<8} {r['truth']:>10}  {bounds(r)}  (qU {'∞' if math.isinf(q(r)) else f'{q(r):.3g}'})")


if __name__ == "__main__":
    main()
