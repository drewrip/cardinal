"""Shared style of every eval figure (EVAL.md §1.7), and reading runs.

Serif text (STIX Two Text if installed, else matplotlib's STIXGeneral),
one- and two-column widths, the Okabe-Ito palette with distinct line
styles and markers, Q-errors on log axes, unbounded results in a strip
above the plot area, unsound results as red crosses. Saved as PDF with
embedded TrueType fonts and as 300-dpi PNG.
"""

import json
import math
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402
from matplotlib import font_manager  # noqa: E402
from matplotlib.ticker import LogLocator, NullFormatter  # noqa: E402

ONE_COLUMN = 3.4
TWO_COLUMNS = 7.0

# Okabe-Ito, black last.
PALETTE = ["#0072B2", "#E69F00", "#009E73", "#D55E00", "#CC79A7", "#56B4E9", "#F0E442", "#000000"]
LINESTYLES = ["-", "--", "-.", ":", (0, (5, 1)), (0, (3, 1, 1, 1, 1, 1))]
MARKERS = ["o", "s", "D", "v", "P", "X", "*", "<"]
UNSOUND = "#D00000"

# The search treats anything above this as unbounded.
CAP = 2.0**30
INF_LABEL = r"$\infty$ (no upper bound)"


def setup(tex=False):
    """Sets matplotlib's style for every figure."""
    names = {f.name for f in font_manager.fontManager.ttflist}
    serif = "STIX Two Text" if "STIX Two Text" in names else "STIXGeneral"
    rc = {
        "font.family": "serif",
        "font.serif": [serif, "STIXGeneral", "DejaVu Serif"],
        "mathtext.fontset": "stix",
        "font.size": 9,
        "axes.labelsize": 9,
        "axes.titlesize": 9,
        "xtick.labelsize": 8,
        "ytick.labelsize": 8,
        "legend.fontsize": 8,
        "legend.frameon": False,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.grid": True,
        "axes.grid.axis": "y",
        "grid.color": "#dddddd",
        "grid.linewidth": 0.5,
        "lines.linewidth": 1.2,
        "lines.markersize": 4,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.02,
    }
    if tex:
        rc.update({"text.usetex": True, "font.serif": ["Computer Modern Roman"]})
    plt.rcParams.update(rc)


def style(i):
    """The colour, line style and marker of series `i`."""
    return {"color": PALETTE[i % len(PALETTE)], "linestyle": LINESTYLES[i % len(LINESTYLES)], "marker": MARKERS[i % len(MARKERS)]}


def save(fig, path):
    """Saves `fig` as `path`.pdf and `path`.png."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(path.with_suffix(".pdf"))
    fig.savefig(path.with_suffix(".png"), dpi=300)
    plt.close(fig)
    print(path.with_suffix(".pdf"))


# Reading runs.


def key(r):
    o = lambda v, w: "" if v is None else f"{v:0{w}d}" if isinstance(v, int) else str(v)
    return "/".join([r["eval"], r["bench"], r["target"], r["target_kind"], o(r.get("engine"), 0), o(r.get("setting"), 0),
                     o(r.get("trial"), 4), o(r.get("k"), 5), o(r.get("operator"), 5)])


def load_run(path):
    """A run, from its directory or `run.json`: `(meta, records)`. A run
    still going is read from its JSONL, the last record of each key kept."""
    path = Path(path)
    if path.is_file():
        run = json.loads(path.read_text())
        return run["meta"], run["records"]
    if (path / "run.json").exists():
        return load_run(path / "run.json")
    meta = json.loads((path / "meta.json").read_text())
    latest = {}
    for line in (path / "records.jsonl").read_text().splitlines():
        try:
            r = json.loads(line)
        except json.JSONDecodeError:
            continue
        latest[key(r)] = r
    return meta, [latest[k] for k in sorted(latest)]


def label(meta):
    """A short label of a run's switches."""
    sw = meta.get("switches", {})
    parts = []
    if sw.get("cardinalities"):
        parts.append("with row counts")
    if sw.get("unbounded"):
        parts.append("unbounded")
    return ", ".join(parts) or "plans only"


# Q-errors, ∞ as a value.


def q(r):
    """A record's upper Q-error, ∞ for no upper bound."""
    return math.inf if r.get("q_upper") is None else r["q_upper"]


def capped(qu, truth):
    """`qu` with ∞ as the search's cap, `2^30 / t'`."""
    return CAP / max(truth or 0, 1) if math.isinf(qu) else qu


def pct(values, p):
    """The `p`th percentile, ∞ sorted last and never interpolated."""
    if not values:
        return math.nan
    return float(np.percentile(np.array(values, dtype=float), p, method="inverted_cdf"))


# The ∞ strip.


class Strip:
    """A log Q-error axis with a strip above for ∞: values at ∞ are drawn
    at `self.inf`, set off from the finite range by a broken-axis mark."""

    def __init__(self, ax, finite_max, finite_min=1.0):
        self.ax = ax
        top = max(finite_max, 10.0)
        self.top = 10 ** math.ceil(math.log10(top) + 1e-9)
        self.brk = self.top * 10**0.35
        self.inf = self.top * 10**0.75
        ax.set_yscale("log")
        ax.set_ylim(max(finite_min, 1.0) / 1.3, self.top * 10**1.0)
        ax.yaxis.set_major_locator(LogLocator(base=10, numticks=12))
        ax.yaxis.set_minor_formatter(NullFormatter())
        ticks = [t for t in 10.0 ** np.arange(0, math.log10(self.top) + 1) if t <= self.top]
        ax.set_yticks(ticks + [self.inf])
        ax.set_yticklabels([tick(t) for t in ticks] + [r"$\infty$"])
        ax.axhspan(self.brk, ax.get_ylim()[1], color="#f4f4f4", zorder=0, lw=0)
        # Broken-axis mark on the left spine.
        d = dict(transform=ax.get_yaxis_transform(), color="k", clip_on=False, lw=0.8)
        for dy in (0.92, 1.08):
            ax.plot([-0.015, 0.015], [self.brk * dy / 1.04, self.brk * dy * 1.04], **d)

    def y(self, v):
        return self.inf if math.isinf(v) else v

    def line(self, x, ys, markers=True, **kw):
        """A line through `ys`: where it reaches ∞ it steps up into the
        strip, and runs dashed there."""
        xs, ys = list(x), [self.y(v) for v in ys]
        at_inf = [y == self.inf for y in ys]
        label = kw.pop("label", None)
        seg = {**kw, "marker": None}
        for i in range(len(xs) - 1):
            a, b = at_inf[i], at_inf[i + 1]
            if a != b:
                # Level, then a step at the next x.
                self.ax.plot([xs[i], xs[i + 1], xs[i + 1]], [ys[i], ys[i], ys[i + 1]], **seg)
            else:
                self.ax.plot(xs[i:i + 2], ys[i:i + 2], **{**seg, "linestyle": "--" if a else seg.get("linestyle", "-")})
        if markers and kw.get("marker"):
            self.ax.plot(xs, ys, linestyle="none", marker=kw["marker"], color=kw.get("color"), markersize=3)
        self.ax.plot([], [], label=label, **kw)

    def band(self, x, lo, hi, color, alpha=0.18):
        """A band from `lo` to `hi`, its part in the strip hatched."""
        lo = [self.y(v) for v in lo]
        hi = [self.y(v) for v in hi]
        fin_hi = [min(h, self.brk) for h in hi]
        self.ax.fill_between(x, lo, fin_hi, color=color, alpha=alpha, lw=0, step=None)
        over = [h == self.inf for h in hi]
        if any(over):
            self.ax.fill_between(x, [self.brk if o else h for o, h in zip(over, hi)], hi, where=over, facecolor="none",
                                 edgecolor=color, hatch="////", lw=0, alpha=0.6)

    def points(self, x, ys, **kw):
        """Single results: finite as given, ∞ as hollow upward triangles
        in the strip."""
        xs, ys = np.asarray(x, dtype=float), np.asarray(ys, dtype=float)
        fin = np.isfinite(ys)
        self.ax.scatter(xs[fin], ys[fin], **kw)
        if (~fin).any():
            c = kw.get("color", kw.get("c", "k"))
            self.ax.scatter(xs[~fin], np.full((~fin).sum(), self.inf), marker="^", facecolors="none", edgecolors=c,
                            s=kw.get("s", 14), lw=0.7)

    def unsound(self, x, ys):
        """Unsound results: red crosses."""
        if len(x):
            self.ax.scatter(x, [self.y(v) for v in ys], marker="x", color=UNSOUND, s=20, lw=1.0, zorder=5, label="unsound")


def tick(t):
    e = int(round(math.log10(t)))
    return r"$1$" if e == 0 else r"$10$" if e == 1 else rf"$10^{{{e}}}$"
