# /// script
# requires-python = ">=3.10"
# dependencies = ["matplotlib>=3.8", "numpy>=1.26"]
# ///
"""Figures and summary of engines runs (EVAL.md §5).

    uv run plot/engines.py <run> [--out DIR] [--summary] [--tex]

`engines-<bench>.pdf`: for each setting (own plan, the others' plans), a
dot plot of qU by query, one marker per engine, unbounded in the ∞ strip;
and a panel of each engine's median qU with its IQR. `--summary` lists the
queries where the engines disagree, with each one's bounds, and the
operators each engine's plans pinned.
"""

import argparse
import math
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import style  # noqa: E402
from style import Strip, pct, q  # noqa: E402

import matplotlib.pyplot as plt  # noqa: E402

SETTINGS = [("own", "own plan"), ("others", "every other query's plan")]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("run")
    ap.add_argument("--out", default="figures")
    ap.add_argument("--summary", action="store_true")
    ap.add_argument("--tex", action="store_true")
    args = ap.parse_args()
    style.setup(args.tex)
    meta, records = style.load_run(args.run)
    records = [r for r in records if r["eval"] == "engines" and r.get("error") is None]
    if args.summary:
        summary(meta, records)
    else:
        figure(meta, records, Path(args.out))


def bounds(r):
    lo, up = r.get("lower"), r.get("upper")
    return f"{lo} <= X" if up is None else (f"X = {up}" if lo == up else f"{lo} <= X <= {up}")


def figure(meta, records, out):
    engines = sorted({r["engine"] for r in records})
    queries = sorted({r["target"] for r in records})
    fig, axes = plt.subplots(1, 3, figsize=(style.TWO_COLUMNS, 2.5), gridspec_kw={"width_ratios": [3, 3, 1.4], "wspace": 0.3})
    finite = max([q(r) for r in records if not math.isinf(q(r))] or [10])
    for ax, (setting, title) in zip(axes[:2], SETTINGS):
        strip = Strip(ax, finite)
        for i, e in enumerate(engines):
            rs = [r for r in records if r["engine"] == e and r["setting"] == setting]
            x = [queries.index(r["target"]) + (i - (len(engines) - 1) / 2) * 0.22 for r in rs]
            st = style.style(i)
            strip.points(x, [q(r) for r in rs], color=st["color"], marker=st["marker"], s=12, label=e)
            bad = [r for r in rs if r.get("holds") is False]
            strip.unsound([queries.index(r["target"]) for r in bad], [q(r) for r in bad])
        ax.set_xticks(range(len(queries)))
        ax.set_xticklabels([x.lstrip("q") for x in queries], fontsize=6)
        ax.set_xlim(-0.7, len(queries) - 0.3)
        ax.set_title(f"{meta['bench'].upper()}, {title}", fontsize=8)
        ax.set_xlabel("query")
    axes[0].set_ylabel(r"upper Q-error $q_U$")
    axes[0].legend(fontsize=7, loc="upper left", ncol=len(engines))

    ax = axes[2]
    strip = Strip(ax, finite)
    labels = []
    for j, (setting, _) in enumerate(SETTINGS):
        for i, e in enumerate(engines):
            v = [q(r) for r in records if r["engine"] == e and r["setting"] == setting]
            if not v:
                continue
            x = j * (len(engines) + 1) + i
            st = style.style(i)
            lo, med, hi = pct(v, 25), pct(v, 50), pct(v, 75)
            ax.plot([x, x], [strip.y(lo), strip.y(hi)], color=st["color"], lw=1.5)
            ax.plot([x], [strip.y(med)], marker=st["marker"], color=st["color"], linestyle="none")
        labels.append((j * (len(engines) + 1) + (len(engines) - 1) / 2, setting))
    ax.set_xticks([x for x, _ in labels])
    ax.set_xticklabels([s for _, s in labels])
    ax.set_xlim(-0.8, len(SETTINGS) * (len(engines) + 1) - 1.2)
    ax.set_title("median, IQR", fontsize=8)
    style.save(fig, out / f"engines-{meta['bench']}")


def summary(meta, records):
    by = defaultdict(dict)
    for r in records:
        by[(r["target"], r["setting"])][r["engine"]] = r
    print(f"{meta['bench'].upper()} engines — {style.label(meta)}")
    for setting, _ in SETTINGS:
        for e in sorted({r["engine"] for r in records}):
            v = [q(r) for r in records if r["engine"] == e and r["setting"] == setting]
            pinned = sum(r["build"]["pinned"] for r in records if r["engine"] == e and r["setting"] == setting)
            if v:
                f = lambda x: "∞" if math.isinf(x) else f"{x:.3g}"
                exact = sum(bool(r["exact"]) for r in records if r["engine"] == e and r["setting"] == setting)
                print(f"  {setting:<7} {e:<10} median qU {f(pct(v, 50)):>8}  IQR {f(pct(v, 25))} – {f(pct(v, 75))}  "
                      f"exact {exact}/{len(v)}  operators pinned {pinned}")
    print("  disagreements:")
    for (t, setting), es in sorted(by.items()):
        if len({(r["lower"], r["upper"]) for r in es.values()}) > 1:
            print(f"    {t} {setting} (truth {next(iter(es.values()))['truth']}): " +
                  "; ".join(f"{e}: {bounds(r)}" for e, r in sorted(es.items())))
    checks = meta.get("checks", {})
    print(f"  unsound: {len(checks.get('unsound', []))}; root mismatches: {len(checks.get('root_mismatches', []))}")


if __name__ == "__main__":
    main()
