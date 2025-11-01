#!/usr/bin/env python3
"""Verify the recorded Tseitin separation metrics."""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path


def _load_scaling_report(root: Path) -> tuple[Path, dict[str, object]]:
    candidates = sorted(root.glob("tseitin_scaling_report_*.json"))
    if not candidates:
        raise FileNotFoundError(f"No tseitin_scaling_report_*.json under {root}")
    path = candidates[-1]
    payload = json.loads(path.read_text())
    if "scaling_analysis" not in payload:
        raise ValueError(f"{path} does not contain 'scaling_analysis'")
    return path, payload["scaling_analysis"]


def _assert(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main(argv: list[str]) -> int:
    root = Path(argv[1]) if len(argv) > 1 else Path(__file__).resolve().parents[2] / "experiments" / "20251101_070033_ci_fix"
    report_path, analysis = _load_scaling_report(root)

    partitions = analysis["partitions"]
    mu_blind = analysis["mu_blind_avg"]
    mu_sighted = analysis["mu_sighted_avg"]
    mu_answer = analysis["mu_answer_avg"]
    ratio = analysis["ratio"]

    _assert(len(partitions) == len(mu_blind) == len(mu_sighted) == len(mu_answer) == len(ratio), "Inconsistent vector lengths")

    # Sighted ledger shows quadratic growth: successive differences are increasing.
    diffs = [b - a for a, b in zip(mu_sighted, mu_sighted[1:])]
    _assert(all(b >= a for a, b in zip(diffs, diffs[1:])), "Sighted μ increments must be non-decreasing (quadratic trend)")

    # Blind ledger grows exponentially: fitted slope confidence interval stays strictly positive.
    slope_ci = analysis["exp_slope_ci"]
    _assert(slope_ci[0] > 0.0, "Exponential fit lower confidence bound must be positive")
    _assert(analysis["exp_r2"] >= 0.95, "Exponential fit must have R^2 ≥ 0.95")

    # Answer-only μ stays linear and tiny compared to the sighted total.
    per_var = analysis["mu_answer_per_var"]
    _assert(all(math.isclose(v, per_var[0], rel_tol=1e-9, abs_tol=1e-9) for v in per_var), "μ_answer per variable should remain constant")
    _assert(all(sa > aa for sa, aa in zip(mu_sighted, mu_answer)), "Sighted μ must dominate answer-only μ")

    # Blind-to-answer ratios grow monotonically.
    ratio_slope = float(analysis.get("ratio_slope", 0.0))
    _assert(ratio_slope > 0.0, "Blind/answer ratio slope must be positive")
    _assert(ratio[-1] > ratio[0] * 3.0, "Blind/answer ratio must grow by at least 3×")

    # Recorded runtime correlation has to match an exponential blind penalty.
    runtime_corr = analysis["runtime_correlation"]
    _assert(runtime_corr["rho"] >= 0.8, "Spearman ρ should witness runtime/μ alignment")
    _assert(runtime_corr["p_value"] <= 1e-6, "Runtime correlation must be statistically significant")

    print("Tseitin scaling report:")
    print(f"  source: {report_path.resolve().relative_to(Path(__file__).resolve().parents[2])}")
    print(f"  partitions examined: {partitions}")
    print(f"  blind μ (avg): {mu_blind}")
    print(f"  sighted μ (avg): {mu_sighted}")
    print(f"  answer μ (avg): {mu_answer}")
    print(f"  ratio (blind/answer): {ratio}")
    print("  exponential fit slope CI:", slope_ci)
    print("  Spearman runtime correlation (ρ, p):", runtime_corr["rho"], runtime_corr["p_value"])
    print("Tseitin separation checks passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
