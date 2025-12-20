#!/usr/bin/env python3
"""Compare a supra-quantum CHSH prediction against published Bell-test results.

Goal: provide an explicit, honest sanity-check: if your predicted CHSH value is
above existing experimental measurements (plus uncertainty), then either:
  (1) the prediction is not the experimentally-measured CHSH quantity,
  (2) the prediction is wrong / applies to a different regime, or
  (3) current experiments are not reaching the predicted bound.

IMPORTANT:
- The default experiment numbers below are placeholders. Replace them with
  the exact reported values (same CHSH convention / normalization) before
  treating the output as anything more than a template.
- This script assumes the standard CHSH normalization with ±1 outcomes.

Convention:
- CHSH S is compared directly. The Tsirelson bound is 2*sqrt(2) ≈ 2.828.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass


@dataclass(frozen=True)
class ExperimentResult:
    name: str
    chsh: float
    error_1sigma: float


DEFAULT_EXPERIMENTS: list[ExperimentResult] = [
    # PLACEHOLDER VALUES.
    ExperimentResult("Delft 2015", chsh=2.42, error_1sigma=0.20),
    ExperimentResult("Vienna 2015", chsh=2.37, error_1sigma=0.18),
    ExperimentResult("NIST 2015", chsh=2.35, error_1sigma=0.22),
]


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Check whether existing Bell-test results constrain a CHSH prediction."
    )
    parser.add_argument(
        "--prediction",
        type=float,
        default=16.0 / 5.0,
        help="Predicted CHSH S value (default: 16/5 = 3.2)",
    )
    parser.add_argument(
        "--sigma",
        type=float,
        default=1.0,
        help="How many σ to use when comparing (default: 1.0)",
    )
    args = parser.parse_args()

    prediction = float(args.prediction)
    sigma = float(args.sigma)

    classical = 2.0
    tsirelson = 2.0 * math.sqrt(2.0)

    print("=" * 72)
    print("CHSH Constraint Check (template)")
    print("=" * 72)
    print(f"Prediction:      S = {prediction:.6f}")
    print(f"Classical bound: |S| ≤ {classical:.6f}")
    print(f"Tsirelson bound: |S| ≤ {tsirelson:.6f}")
    print(f"Comparison:      prediction > measurement + ({sigma:.2f}σ)")
    print()

    any_exceeds = False
    for exp in DEFAULT_EXPERIMENTS:
        threshold = exp.chsh + sigma * exp.error_1sigma
        exceeds = prediction > threshold
        any_exceeds = any_exceeds or exceeds

        verdict = "EXCEEDS" if exceeds else "CONSISTENT"
        print(f"{exp.name:12s}: measured {exp.chsh:.4f} ± {exp.error_1sigma:.4f} (1σ)  -> {verdict}")

        if exceeds:
            delta = prediction - threshold
            print(f"  Δ above {sigma:.2f}σ-upper: {delta:.6f}")

    print()
    print("Conclusion (template):")
    if any_exceeds:
        print("- Your predicted S is above at least one listed measurement + uncertainty.")
        print("- Either the prediction is not the standard loophole-free CHSH S, or it is falsified,")
        print("  or the experimental setup differs from the model assumptions.")
    else:
        print("- Your predicted S is not ruled out by these (placeholder) numbers at the chosen σ.")
        print("- A careful apples-to-apples comparison still requires matching conventions, settings,")
        print("  and the exact statistical treatment used in each experiment.")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
