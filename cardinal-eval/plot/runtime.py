# /// script
# requires-python = ">=3.10"
# dependencies = ["matplotlib>=3.8", "numpy>=1.26"]
# ///
"""Runtime of any run (EVAL.md §1.6).

    uv run plot/runtime.py <run>... [--out DIR] [--allow-contended] [--tex]

Holdout runs: per benchmark, build and search time against the number of
plans given, median lines with 25-75 % bands, log y; runs with and without
--unbounded overlaid. Own-plan and engines runs: per query, a bar of build
and search time. Only measured records (not reused) count, and only those
timed exclusively unless --allow-contended, which marks the figure so.
"""

import argparse
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import style  # noqa: E402
from style import pct  # noqa: E402

import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("runs", nargs="+")
    ap.add_argument("--out", default="figures")
    ap.add_argument("--allow-contended", action="store_true")
    ap.add_argument("--tex", action="store_true")
    args = ap.parse_args()
    style.setup(args.tex)

    groups = defaultdict(list)
    contended = False
    for path in args.runs:
        meta, records = style.load_run(path)
        timed = [r for r in records if not r.get("reused") and r.get("error") is None and r.get("build")]
        exclusive = [r for r in timed if r.get("timing") == "exclusive"]
        if not exclusive:
            if not args.allow_contended:
                sys.exit(f"{path}: no records timed exclusively (--timing exclusive); --allow-contended plots them anyway")
            exclusive, contended = timed, True
        groups[(meta["eval"], meta["bench"])].append((meta, exclusive))

    out = Path(args.out)
    for (ev, bench), runs in sorted(groups.items()):
        if ev == "holdout":
            by_plans(bench, runs, out, contended)
        else:
            per_query(ev, bench, runs, out, contended)


def mark(fig, contended):
    if contended:
        fig.text(0.99, 0.01, "contended timings", ha="right", va="bottom", fontsize=7, color=style.UNSOUND)


def by_plans(bench, runs, out, contended):
    fig, axes = plt.subplots(1, 2, figsize=(style.TWO_COLUMNS, 2.3), sharey=True, gridspec_kw={"wspace": 0.08})
    for i, (meta, records) in enumerate(runs):
        per = defaultdict(list)
        for r in records:
            per[r["build"]["plans_given"]].append(r)
        x = sorted(per)
        for ax, part in zip(axes, ["build", "search"]):
            vals = [[max(r["time_ms"][part], 1e-3) / 1e3 for r in per[k]] for k in x]
            st = style.style(i)
            ax.fill_between(x, [pct(v, 25) for v in vals], [pct(v, 75) for v in vals], color=st["color"], alpha=0.18, lw=0)
            ax.plot(x, [pct(v, 50) for v in vals], label=style.label(meta), **{**st, "markersize": 3})
    for ax, part in zip(axes, ["build", "search"]):
        ax.set_yscale("log")
        ax.set_xlabel("plans given")
        ax.set_title(f"{bench.upper()}: {part}", fontsize=8)
    axes[0].set_ylabel("time (s)")
    if len(runs) > 1:
        axes[0].legend()
    mark(fig, contended)
    style.save(fig, out / f"runtime-{bench}")


def per_query(ev, bench, runs, out, contended):
    meta, records = runs[0]
    rows = defaultdict(lambda: [0.0, 0.0])
    for r in records:
        name = r["target"] + (f" {r['engine']}/{r['setting']}" if r.get("engine") else "")
        rows[name][0] += r["time_ms"]["build"] / 1e3
        rows[name][1] += r["time_ms"]["search"] / 1e3
    names = sorted(rows)
    fig, ax = plt.subplots(figsize=(style.TWO_COLUMNS, 2.3))
    x = np.arange(len(names))
    b = [rows[n][0] for n in names]
    s = [rows[n][1] for n in names]
    ax.bar(x, b, color=style.PALETTE[0], label="build")
    ax.bar(x, s, bottom=b, color=style.PALETTE[1], label="search", hatch="///", edgecolor="white", lw=0)
    ax.set_xticks(x)
    ax.set_xticklabels(names, rotation=90, fontsize=5)
    ax.set_yscale("log")
    ax.set_ylabel("time (s)")
    ax.legend()
    mark(fig, contended)
    style.save(fig, out / f"runtime-{ev}-{bench}")


if __name__ == "__main__":
    main()
