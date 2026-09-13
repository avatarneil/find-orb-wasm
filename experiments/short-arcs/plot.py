#!/usr/bin/env python3
"""SPDX-License-Identifier: GPL-2.0-or-later. Export scientific SVG/PNG figures."""
import json
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

root = Path(__file__).resolve().parents[2]
data = json.loads((root / "results/short-arcs/analysis.json").read_text())
out = root / "results/short-arcs/figures"
out.mkdir(parents=True, exist_ok=True)
plt.rcParams.update({"font.size": 10, "axes.spines.top": False, "axes.spines.right": False,
                     "svg.hashsalt": "find-orb-short-arcs-v1", "figure.facecolor": "white"})
colors = {"position": "#173f5f", "phase6d": "#16867d", "min-rms": "#cf6535", "predictive1d": "#8857a4"}
labels = {"position": "Existing position", "phase6d": "Position + velocity", "min-rms": "Minimum residual", "predictive1d": "One-day predictive"}
rows = [r for r in data["comparisonRows"] if r["split"] == "held-out" and r["valid"]
        and r["settings"]["scenario"] == "gaussian" and r["settings"]["budget"] == 100]
cases = list(dict.fromkeys(r["caseId"] for r in rows))
fig, axes = plt.subplots(2, 2, figsize=(10, 7), sharex=True, sharey=True, layout="constrained")
for ax, case in zip(axes.flat, cases):
    subset = [r for r in rows if r["caseId"] == case]
    for model, color in colors.items():
        y = np.array([[p["errorArcsec"] for p in r["predictions"]] for r in subset if r["settings"]["selection"] == model])
        x = [0.25, 1, 3, 7]
        ax.plot(x, np.median(y, axis=0), "o-", color=color, label=labels[model], lw=1.6, ms=4)
    ax.set_title(case.replace("observable-", "").replace("-2026-", " · 2026-"), loc="left")
    ax.set_yscale("log"); ax.set_xticks([.25, 1, 3, 7]); ax.grid(axis="y", alpha=.2)
for ax in axes[:, 0]: ax.set_ylabel("Median angular error (arcsec, log scale)")
for ax in axes[-1]: ax.set_xlabel("Days after original last observation")
handles, names = axes[0, 0].get_legend_handles_labels()
fig.legend(handles, names, loc="outside lower center", ncol=2, frameon=False)
fig.suptitle("Held-out predictions from the same one-hour arc", fontsize=15, weight="bold")
for extension in ("svg", "png"):
    fig.savefig(out / f"heldout-predictions.{extension}", dpi=180, metadata={"Date": None} if extension == "svg" else None)
plt.close(fig)

fig, axes = plt.subplots(2, 2, figsize=(10, 7), sharex=True, sharey=True, layout="constrained")
objects = ["Pallas", "Vesta", "Eros", "Achilles"]
for ax, obj in zip(axes.flat, objects):
    for budget, color in [(100, "#173f5f"), (500, "#cf6535")]:
        two = next(f for f in data["followups"] if f["arc"] == "two-tracklets" and f["budget"] == budget)
        three = next(f for f in data["followups"] if f["arc"] == "three-tracklets" and f["budget"] == budget)
        a = [p for p in two["pairs"] if p["object"] == obj]
        b = [p for p in three["pairs"] if p["object"] == obj]
        y = np.array([[p["baseline7dArcsec"] for p in a], [p["error7dArcsec"] for p in a], [p["error7dArcsec"] for p in b]])
        ax.plot([1, 2, 3], np.median(y, axis=1), "o-", color=color, label=f"Initial capacity {budget}", lw=1.8)
        ax.fill_between([1, 2, 3], y.min(axis=1), y.max(axis=1), color=color, alpha=.12)
    ax.set_title(obj, loc="left"); ax.set_yscale("log"); ax.grid(axis="y", alpha=.2); ax.set_xticks([1, 2, 3])
for ax in axes[:, 0]: ax.set_ylabel("Seven-day error (arcsec, log scale)")
for ax in axes[-1]: ax.set_xlabel("One-hour tracklets on successive nights")
handles, names = axes[0, 0].get_legend_handles_labels()
fig.legend(handles, names, loc="outside lower center", ncol=2, frameon=False)
fig.suptitle("Additional nights improve recovery; larger search can change the solver path", fontsize=13, weight="bold")
for extension in ("svg", "png"):
    fig.savefig(out / f"followup-tracklets.{extension}", dpi=180, metadata={"Date": None} if extension == "svg" else None)
plt.close(fig)

# Matplotlib leaves trailing spaces in SVG path data; normalize only whitespace.
for path in out.glob("*.svg"):
    path.write_text("\n".join(line.rstrip() for line in path.read_text().splitlines()) + "\n")
