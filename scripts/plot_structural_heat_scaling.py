#!/usr/bin/env python3
"""Plot the structural-heat scaling sweep as an educational, thesis-ready figure.

This plot is produced from the optional sweep emitted by
`scripts/structural_heat_experiment.py --sweep-records`.

We keep this as a separate plotting script so the harness stays dependency-light
and the thesis figures can be regenerated deterministically.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Iterable, Tuple

import matplotlib.pyplot as plt

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_JSON = REPO_ROOT / "results" / "structural_heat_experiment.json"
DEFAULT_PLOT = REPO_ROOT / "thesis" / "figures" / "structural_heat_scaling.png"


def _apply_plot_style() -> None:
    plt.rcParams.update(
        {
            "figure.dpi": 200,
            "savefig.dpi": 200,
            "font.size": 11,
            "axes.titlesize": 13,
            "axes.labelsize": 11,
            "legend.fontsize": 10,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "axes.grid": True,
            "grid.alpha": 0.35,
            "grid.linestyle": ":",
            "lines.linewidth": 2.2,
            "lines.markersize": 6,
        }
    )


def _iter_sweep_points(payload: dict[str, Any]) -> Iterable[Tuple[int, float, float, float]]:
    for run in payload.get("sweep_runs", []) or []:
        records = int(run["records"])
        mu_total = float(run["mu_total"])
        slack = float(run["mu_minus_lower_bound"])
        log2_ratio = float(run.get("log2_ratio", run.get("structural_bits", 0.0)))
        yield records, mu_total, slack, log2_ratio


def plot_structural_heat_scaling(input_path: Path = DEFAULT_JSON, output_path: Path = DEFAULT_PLOT) -> Path:
    data = json.loads(input_path.read_text(encoding="utf-8"))
    points = list(_iter_sweep_points(data))
    if not points:
        raise ValueError(
            "No sweep points found. Re-run with: scripts/structural_heat_experiment.py --sweep-records"
        )

    _apply_plot_style()

    # Sort by increasing record count.
    points_sorted = sorted(points, key=lambda t: t[0])
    records, mu, slack, log2_ratio = zip(*points_sorted)

    # Educational framing:
    # - x := log2(n!) (information bits in the ordering certificate)
    # - y := μ charged (implemented as ceil(log2(n!)))
    # The ceiling rule implies: 0 <= μ - log2(n!) < 1.
    x = [float(v) for v in log2_ratio]
    y = [float(v) for v in mu]
    s = [float(v) for v in slack]

    fig = plt.figure(figsize=(7.6, 6.2), constrained_layout=True)
    gs = fig.add_gridspec(2, 1, height_ratios=[2.2, 1.0])
    ax1 = fig.add_subplot(gs[0, 0])
    ax2 = fig.add_subplot(gs[1, 0], sharex=ax1)

    ax1.scatter(x, y, color="#d62728", label="Observed μ (artifact)")
    x_min, x_max = min(x), max(x)
    ax1.plot([x_min, x_max], [x_min, x_max], linestyle="--", color="#111111", alpha=0.85, label=r"Lower bound: $\mu=\log_2(n!)$")
    ax1.plot([x_min, x_max], [x_min + 1.0, x_max + 1.0], linestyle=":", color="#111111", alpha=0.6, label=r"Ceiling envelope: $\mu=\log_2(n!)+1$")

    ax1.set_ylabel(r"Charged $\mu$ (bits)")
    ax1.set_title("Structural heat scaling: μ is the ceiling of certificate bits")
    ax1.legend(frameon=False, loc="upper left")

    ax2.plot(x, s, marker="o", color="#2ca02c")
    ax2.axhspan(0.0, 1.0, color="#2ca02c", alpha=0.08, label=r"Expected: $0\le \mu-\log_2(n!)<1$")
    ax2.set_xlabel(r"Certificate bits $\log_2(n!)$")
    ax2.set_ylabel(r"Slack $\mu-\log_2(n!)$")
    ax2.set_ylim(-0.05, 1.05)

    # Small, readable annotation tying back to record counts.
    ax2.text(
        0.0,
        -0.55,
        f"Sweep: n = 2^{int(round((min(records)).bit_length()-1))} .. 2^{int(round((max(records)).bit_length()-1))} records (powers of two)",
        transform=ax2.transAxes,
        fontsize=10,
        color="#444444",
    )

    output_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output_path, bbox_inches="tight")
    plt.close(fig)
    return output_path


def main() -> None:
    parser = argparse.ArgumentParser(description="Plot structural heat scaling sweep")
    parser.add_argument("--in", dest="input_path", type=Path, default=DEFAULT_JSON)
    parser.add_argument("--out", dest="output_path", type=Path, default=DEFAULT_PLOT)
    args = parser.parse_args()

    out = plot_structural_heat_scaling(args.input_path, args.output_path)
    print(f"Saved scaling plot to {out}")


if __name__ == "__main__":
    main()
