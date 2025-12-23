"""Plot the time-dilation artifact as an educational, thesis-ready figure.

This plot is intentionally "from first principles": it visualizes the ledger
allocation rule under a fixed per-tick μ budget and overlays the expected
compute-rate curve in the no-backlog regime.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Iterable

import matplotlib.pyplot as plt


def _apply_plot_style() -> None:
    # Matplotlib-only, deterministic style.
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
            "lines.markersize": 7,
        }
    )

REPO_ROOT = Path(__file__).resolve().parent.parent
RESULTS_DIR = REPO_ROOT / "results"
DEFAULT_JSON = RESULTS_DIR / "time_dilation_experiment.json"
DEFAULT_PLOT = REPO_ROOT / "thesis" / "figures" / "time_dilation_curve.png"


def _load_scenarios(path: Path) -> list[dict[str, Any]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    scenarios = data.get("scenarios", [])
    if not isinstance(scenarios, list):
        raise ValueError("Invalid time dilation artifact: scenarios must be a list")
    return [s for s in scenarios if isinstance(s, dict)]


def plot_time_dilation(input_path: Path = DEFAULT_JSON, output_path: Path = DEFAULT_PLOT) -> Path:
    """Load the time-dilation JSON and emit a thesis-ready PNG."""

    if not input_path.exists():
        raise FileNotFoundError(f"Missing input artifact: {input_path}")

    scenarios = _load_scenarios(input_path)
    if not scenarios:
        raise ValueError("No scenarios found in time-dilation artifact")

    _apply_plot_style()

    # Convert artifact fields into per-tick quantities for clarity.
    points = []
    for s in scenarios:
        ticks = int(s.get("ticks", 0))
        if ticks <= 0:
            continue
        comm_mu_total = float(s["comm_mu"])
        comm_mu_per_tick = comm_mu_total / float(ticks)
        points.append(
            {
                "name": str(s.get("name", "scenario")),
                "budget_per_tick": int(s["budget_per_tick"]),
                "compute_cost": int(s.get("compute_cost", 1)),
                "ticks": ticks,
                "comm_bits_per_tick": int(s.get("comm_bits_per_tick", 0)),
                "comm_mu_per_tick": comm_mu_per_tick,
                "compute_rate": float(s["compute_rate"]),
            }
        )

    if not points:
        raise ValueError("No valid scenarios with ticks>0 in artifact")

    # Assume the run uses a single (budget, cost) across scenarios (true for the harness).
    budget = int(points[0]["budget_per_tick"])
    compute_cost = max(1, int(points[0]["compute_cost"]))

    # Sort by increasing comm μ/tick.
    points.sort(key=lambda p: float(p["comm_mu_per_tick"]))
    x = [float(p["comm_mu_per_tick"]) for p in points]
    y = [float(p["compute_rate"]) for p in points]

    fig, ax = plt.subplots(figsize=(7.3, 4.4))
    ax.plot(x, y, marker="o", color="#1f77b4", label="Observed (artifact)")

    # First-principles overlay in the no-backlog regime: for comm ≤ budget,
    # compute steps/tick = (budget - comm)/compute_cost.
    x_theory = [v for v in x if v <= budget]
    if x_theory:
        y_theory = [(budget - v) / float(compute_cost) for v in x_theory]
        ax.plot(
            x_theory,
            y_theory,
            linestyle="--",
            color="#111111",
            alpha=0.85,
            label=r"Theory (no-backlog): $r=(B-\mu_{comm})/c$",
        )

    # Mark the infeasible region where comm μ/tick exceeds budget.
    ax.axvspan(budget, max(max(x), budget), color="#d62728", alpha=0.08, label="Backlog regime")

    # Annotate points with the configured comm bits/tick (more readable than long names).
    for p in points:
        ax.annotate(
            f"{p['comm_bits_per_tick']}",
            (float(p["comm_mu_per_tick"]), float(p["compute_rate"])),
            textcoords="offset points",
            xytext=(0, 10),
            ha="center",
            va="bottom",
            fontsize=10,
            color="#333333",
        )

    ax.set_xlabel(r"Communication spend per tick $\mu_{comm}$")
    ax.set_ylabel(r"Compute rate $r$ (steps per tick)")
    ax.set_title("Ledger time dilation under a fixed μ budget")
    ax.set_xlim(left=0)
    ax.set_ylim(bottom=0)
    ax.legend(frameon=False, loc="upper right")

    caption = (
        f"Budget per tick B={budget} μ, compute cost c={compute_cost} μ/step. "
        "Numbers above points are configured comm bits/tick."
    )
    ax.text(0.0, -0.22, caption, transform=ax.transAxes, fontsize=10, color="#444444")

    output_path.parent.mkdir(parents=True, exist_ok=True)
    fig.tight_layout()
    fig.savefig(output_path, bbox_inches="tight")
    plt.close(fig)
    return output_path


if __name__ == "__main__":
    path = plot_time_dilation()
    print(f"Saved curve to {path}")
