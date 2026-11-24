# /// script
# requires-python = ">=3.10"
# dependencies = ["matplotlib>=3.8", "numpy>=1.26"]
# ///
"""Figures and summaries of holdout runs (EVAL.md §2.4, §3).

    uv run plot/holdout.py <run>... [--out DIR] [--band 25-75] [--summary]
                           [--split-template] [--tex]

Per benchmark, `holdout-<bench>.pdf`: Q-error against k over every target,
and the most and least improved target. Runs of one benchmark with other
switches (row counts, unbounded) overlay their medians in the first panel.
`holdout-all.pdf` overlays every benchmark's median, k as the share of
Q_ref given. Runs with --operators make `holdout-<bench>-operators.pdf`.
"""

import argparse
import math
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import style  # noqa: E402
from style import Strip, capped, pct, q  # noqa: E402

import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.gridspec import GridSpec  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("runs", nargs="+")
    ap.add_argument("--out", default="figures")
    ap.add_argument("--band", default="25-75")
    ap.add_argument("--summary", action="store_true", help="print summaries instead of plotting")
    ap.add_argument("--split-template", action="store_true")
    ap.add_argument("--tex", action="store_true")
    args = ap.parse_args()
    lo, hi = (float(p) for p in args.band.split("-"))
    style.setup(args.tex)

    runs = [style.load_run(r) for r in args.runs]
    by_bench = defaultdict(list)
    for meta, records in runs:
        records = [r for r in records if r["eval"] == "holdout"]
        by_bench[(meta["bench"], records[0]["target_kind"] if records else "root")].append((meta, records))

    if args.summary:
        for (bench, kind), rs in sorted(by_bench.items()):
            for meta, records in rs:
                summary(bench, kind, meta, records)
        return

    out = Path(args.out)
    for (bench, kind), rs in sorted(by_bench.items()):
        if kind == "operator":
            operators_figure(bench, rs[0], out, lo, hi)
        else:
            bench_figure(bench, kind, rs, out, lo, hi, args.split_template)
    all_figure([(b, rs[0]) for (b, k), rs in sorted(by_bench.items()) if k != "operator"], out, lo, hi)


def ok(records):
    return [r for r in records if r.get("error") is None and r.get("truth") is not None]


def n_of(records):
    return max(r["k"] for r in records)


def by_k(records):
    out = defaultdict(list)
    for r in records:
        out[r["k"]].append(r)
    return dict(sorted(out.items()))


def xscale(ax, meta, n):
    if meta["switches"].get("grid") == "log":
        ax.set_xscale("symlog", linthresh=4, linscale=0.6)
        ticks = [k for k in [0, 1, 2, 4, 8, 16, 32, 64] if k < n] + [n]
        ax.set_xticks(ticks)
        ax.set_xticklabels([str(t) for t in ticks])
    ax.set_xlim(0, n)


def median_band(ax, strip, records, lo, hi, i, label, band=True):
    ks = by_k(records)
    x = list(ks)
    vals = [[q(r) for r in rs] for rs in ks.values()]
    st = style.style(i)
    if band:
        strip.band(x, [pct(v, lo) for v in vals], [pct(v, hi) for v in vals], st["color"])
    strip.line(x, [pct(v, 50) for v in vals], label=label, **st)
    bad = [r for r in records if r.get("holds") is False]
    strip.unsound([r["k"] for r in bad], [q(r) for r in bad])
    return x, vals


def finite_max(records):
    f = [q(r) for r in records if not math.isinf(q(r))]
    return max(f) if f else 10.0


def improvement(records):
    """Per target: (improvement, final median qU, k=0 records, k=n records)."""
    out = {}
    per = defaultdict(list)
    for r in records:
        per[r["target"]].append(r)
    for t, rs in per.items():
        n = n_of(rs)
        first = [r for r in rs if r["k"] == 0]
        last = [r for r in rs if r["k"] == n]
        if not first or not last:
            continue
        truth = rs[0]["truth"]
        q0 = capped(pct([q(r) for r in first], 50), truth)
        qn = capped(pct([q(r) for r in last], 50), truth)
        out[t] = (math.log10(q0) - math.log10(qn), qn, first, last)
    return out


def bounds(r):
    lo, up = r.get("lower"), r.get("upper")
    return f"{lo} ≤ X" if up is None else (f"X = {up}" if lo == up else f"{lo} ≤ X ≤ {up}")


def target_panel(ax, records, target, lo, hi):
    rs = [r for r in records if r["target"] == target]
    strip = Strip(ax, finite_max(rs))
    trials = defaultdict(list)
    for r in rs:
        trials[r["trial"]].append(r)
    for tr in trials.values():
        tr.sort(key=lambda r: r["k"])
        strip.line([r["k"] for r in tr], [q(r) for r in tr], markers=False, color=style.PALETTE[0], alpha=0.25, lw=0.6)
    median_band(ax, strip, rs, lo, hi, 0, "median")
    n = n_of(rs)
    first = next(r for r in rs if r["k"] == 0)
    last = next(r for r in rs if r["k"] == n)
    op = f" #{first['operator']}" if first.get("operator") is not None and first["target_kind"] == "core" else ""
    ax.set_title(f"{target}{op}: t = {first['truth']}\nk = 0: {bounds(first)}; k = {n}: {bounds(last)}", fontsize=8)
    return strip


def bench_figure(bench, kind, runs, out, lo, hi, split_template):
    meta, records = runs[0][0], ok(runs[0][1])
    if not records:
        return
    n = n_of(records)
    fig = plt.figure(figsize=(style.TWO_COLUMNS, 2.6))
    gs = GridSpec(2, 3, height_ratios=[4, 1], hspace=0.08, wspace=0.35, figure=fig)
    ax = fig.add_subplot(gs[0, 0])
    share = fig.add_subplot(gs[1, 0], sharex=ax)
    strip = Strip(ax, max(finite_max(ok(rs)) for _, rs in runs))
    for i, (m, rs) in enumerate(runs):
        rs = ok(rs)
        label = style.label(m)
        if split_template:
            for j, (name, sel) in enumerate([("same template", lambda r: newest_same(r)), ("other", lambda r: not newest_same(r))]):
                sub = [r for r in rs if r["k"] == 0 or sel(r)]
                median_band(ax, strip, sub, lo, hi, 2 * i + j, f"{label}, newest of {name}", band=j == 0)
        else:
            median_band(ax, strip, rs, lo, hi, i, label, band=i == 0)
        ks = by_k(rs)
        share.plot(list(ks), [sum(r["upper"] is not None for r in v) / len(v) for v in ks.values()], **{**style.style(i), "marker": None})
    trivial = sum(1 for r in records if r["k"] == 0 and r["trial"] == 1 and (r["exact"] or q(r) <= 2))
    targets = len({r["target"] for r in records})
    ax.set_title(f"{bench.upper()} ({kind}): all {targets} targets, {trivial} trivial at k = 0", fontsize=8)
    ax.set_ylabel(r"upper Q-error $q_U$")
    if len(runs) > 1 or split_template:
        ax.legend(loc="upper right")
    plt.setp(ax.get_xticklabels(), visible=False)
    share.set_ylim(0, 1.05)
    share.set_yticks([0, 1])
    share.set_ylabel("bounded", fontsize=7)
    share.set_xlabel("plans given, k")
    xscale(share, meta, n)

    imp = improvement(records)
    if not imp:
        style.save(fig, out / f"holdout-{bench}{'' if kind == 'root' else '-' + kind}")
        return
    most = sorted(imp, key=lambda t: (-imp[t][0], imp[t][1]))[0]
    least = sorted(imp, key=lambda t: (imp[t][0], -imp[t][1]))[0]
    for col, (t, what) in enumerate([(most, "most"), (least, "least")], start=1):
        a = fig.add_subplot(gs[:, col])
        target_panel(a, records, t, lo, hi)
        a.set_xlabel(f"plans given, k ({what} improved)")
        xscale(a, meta, n)
    style.save(fig, out / f"holdout-{bench}{'' if kind == 'root' else '-' + kind}")


def newest_same(r):
    return bool(r["refs"]) and template_of(r["refs"][-1]) == r["template"]


def template_of(name):
    # JOB: 1a..1d are template 1; DSB: <set>/<template>/i<n>.
    if "/" in name:
        return name.rsplit("/", 1)[0]
    return name.rstrip("abcdefghijklmnopqrstuvwxyz") or name


def all_figure(runs, out, lo, hi):
    if len(runs) < 2:
        return
    fig, ax = plt.subplots(figsize=(style.ONE_COLUMN, 2.2))
    strip = Strip(ax, max(finite_max(ok(rs)) for _, (m, rs) in runs))
    for i, (bench, (meta, rs)) in enumerate(runs):
        rs = ok(rs)
        n = n_of(rs)
        ks = by_k(rs)
        kind = rs[0]["target_kind"] if rs else "root"
        label = f"{bench.upper()} ({kind})"
        strip.line([k / n for k in ks], [pct([q(r) for r in v], 50) for v in ks.values()], label=label, **style.style(i))
    ax.set_xlabel("share of the other queries' plans given")
    ax.set_ylabel(r"median $q_U$")
    ax.set_xlim(0, 1)
    ax.legend()
    style.save(fig, out / "holdout-all")


def operators_figure(bench, run, out, lo, hi):
    meta, records = run[0], ok(run[1])
    if not records:
        return
    n = n_of(records)
    fig, axes = plt.subplots(1, 3, figsize=(style.TWO_COLUMNS, 2.4), gridspec_kw={"wspace": 0.35})
    strip = Strip(axes[0], finite_max(records))
    median_band(axes[0], strip, records, lo, hi, 0, "all operators")
    axes[0].set_title(f"{bench.upper()}: every operator", fontsize=8)
    axes[0].set_ylabel(r"upper Q-error $q_U$")
    axes[0].set_xlabel("plans given, k")
    xscale(axes[0], meta, n)

    group = lambda r: min(r.get("joins") or 0, 5)
    names = ["0", "1", "2", "3", "4", "5+"]
    strip = Strip(axes[1], finite_max(records))
    for j in range(6):
        sub = [r for r in records if group(r) == j]
        if sub:
            median_band(axes[1], strip, sub, lo, hi, j, f"{names[j]} join{'' if names[j] == '1' else 's'}", band=False)
    axes[1].legend(fontsize=6, ncol=2)
    axes[1].set_xlabel("plans given, k")
    axes[1].set_title("median by joins at or below", fontsize=8)
    xscale(axes[1], meta, n)

    strip = Strip(axes[2], finite_max(records))
    for side, (k, dx) in enumerate([(0, -0.18), (n, 0.18)]):
        data = [[min(strip.y(q(r)), strip.inf) for r in records if r["k"] == k and group(r) == j] for j in range(6)]
        pos = [j + dx for j in range(6) if data[j]]
        b = axes[2].boxplot([d for d in data if d], positions=pos, widths=0.3, patch_artist=True, showfliers=False,
                            medianprops={"color": "k"})
        for p in b["boxes"]:
            p.set_facecolor(style.PALETTE[side])
            p.set_alpha(0.6)
        axes[2].plot([], [], color=style.PALETTE[side], lw=4, alpha=0.6, label=f"k = {k}")
    axes[2].set_xticks(range(6))
    axes[2].set_xticklabels(names)
    axes[2].set_xlabel("joins at or below")
    axes[2].legend(fontsize=6)
    style.save(fig, out / f"holdout-{bench}-operators")


def summary(bench, kind, meta, records):
    good = ok(records)
    if not good:
        print(f"{bench}: no records")
        return
    n = n_of(good)
    ks = sorted({0, 1, n // 4, n // 2, n})
    present = sorted({r["k"] for r in good})
    near = lambda k: min(present, key=lambda p: (abs(p - k), p))
    print(f"\n{bench.upper()} {kind} — {style.label(meta)} — {len(good)} records, n = {n}")
    trivial = len({r["target"] for r in good if r["k"] == 0 and (r["exact"] or q(r) <= 2)})
    print(f"  targets trivial at k = 0 (exact or qU <= 2): {trivial} of {len({r['target'] for r in good})}")
    print(f"  {'k':>4} {'median qU':>10} {'IQR':>22} {'bounded':>8} {'exact':>6}")
    for k in sorted({near(k) for k in ks}):
        v = [q(r) for r in good if r["k"] == k]
        f = lambda x: "∞" if math.isinf(x) else f"{x:.3g}"
        print(f"  {k:>4} {f(pct(v, 50)):>10} {f(pct(v, 25)) + ' – ' + f(pct(v, 75)):>22} "
              f"{sum(not math.isinf(x) for x in v) / len(v):>8.0%} {sum(bool(r['exact']) for r in good if r['k'] == k) / len(v):>6.0%}")
    if kind == "operator":
        # Most and least improved query, each scored by the median
        # improvement of its operators.
        per = defaultdict(list)
        for r in good:
            per[(r["target"], r["operator"])].append({**r, "target": f"{r['target']}#{r['operator']}"})
        imp = improvement([r for rs in per.values() for r in rs])
        by_query = defaultdict(list)
        for t, (d, qn, _, _) in imp.items():
            by_query[t.split("#")[0]].append(d)
        score = {t: pct(v, 50) for t, v in by_query.items()}
        if score:
            most = max(score, key=lambda t: score[t])
            least = min(score, key=lambda t: score[t])
            print(f"  most improved query: {most} (median log10 improvement {score[most]:.2f}); "
                  f"least: {least} ({score[least]:.2f})")
    unsound = [r for r in good if r.get("holds") is False]
    checks = meta.get("checks", {})
    print(f"  unsound: {len(unsound)}; non-monotone steps: {len(checks.get('non_monotone', []))}; "
          f"records with limited > 0: {checks.get('limited', 'n/a')}; errors: {sum(r.get('error') is not None for r in records)}")
    for r in unsound:
        print(f"    UNSOUND {r['target']} trial {r['trial']} k {r['k']}: {bounds(r)}, truth {r['truth']}")


if __name__ == "__main__":
    main()
