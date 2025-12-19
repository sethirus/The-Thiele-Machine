"""Plot the time-dilation artifact to make the speed-limit trade-off visible."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Iterable, Tuple

import matplotlib.pyplot as plt

REPO_ROOT = Path(__file__).resolve().parent.parent
RESULTS_DIR = REPO_ROOT / "results"
DEFAULT_JSON = RESULTS_DIR / "time_dilation_experiment.json"
DEFAULT_PLOT = RESULTS_DIR / "time_dilation_curve.svg"


def _load_points(path: Path) -> Iterable[Tuple[float, float, str]]:
    data = json.loads(path.read_text())
    for scenario in data.get("scenarios", []):
        yield float(scenario["comm_mu"]), float(scenario["compute_rate"]), scenario["name"]


def plot_time_dilation(input_path: Path = DEFAULT_JSON, output_path: Path = DEFAULT_PLOT) -> Path:
    """Load the time-dilation JSON and emit a monotonic curve (SVG by default)."""

    if not input_path.exists():
        raise FileNotFoundError(f"Missing input artifact: {input_path}")

    points = list(_load_points(input_path))
    if not points:
        raise ValueError("No scenarios found in time-dilation artifact")

    comm, rate, labels = zip(*points)

    fig, ax = plt.subplots(figsize=(6, 4))
    ax.plot(comm, rate, marker="o", linestyle="-", color="#1f77b4")

    for x, y, label in points:
        ax.annotate(label, (x, y), textcoords="offset points", xytext=(0, 8), ha="center")

    ax.set_xlabel("communication μ per tick")
    ax.set_ylabel("compute steps per tick")
    ax.set_title("Ledger speed limit: compute vs communication μ spend")
    ax.grid(True, linestyle=":", linewidth=0.7)

    output_path.parent.mkdir(parents=True, exist_ok=True)
    fig.tight_layout()
    fig.savefig(output_path)
    plt.close(fig)
    return output_path


if __name__ == "__main__":
    path = plot_time_dilation()
    print(f"Saved curve to {path}")
