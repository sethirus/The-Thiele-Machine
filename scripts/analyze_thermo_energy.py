#!/usr/bin/env python3
"""Analyze thermodynamic bridge energy-vs-μ results.

This is a lightweight post-processor for results produced by
scripts/thermo_experiment.py when --measure-energy=rapl is enabled.

It reports:
- per-scenario (energy, μ) points
- slope of a least-squares fit through the origin (E ≈ slope * μ)
- slope normalized by k_B*T*ln2

Note: On cloud hardware the absolute Landauer scale is *far* below measured
energy, so the meaningful output is whether energy scales monotonically with μ
and whether the fit is roughly linear.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description="Analyze thermo_experiment.json energy-vs-μ")
    parser.add_argument(
        "path",
        type=Path,
        nargs="?",
        default=Path("results/thermo_experiment.json"),
        help="Path to thermo_experiment.json (default: results/thermo_experiment.json)",
    )
    args = parser.parse_args()

    payload = json.loads(args.path.read_text(encoding="utf-8"))
    runs = payload.get("runs", [])
    if not runs:
        raise SystemExit("No runs found")

    points = []
    for run in runs:
        energy = run.get("measured_energy_joules")
        mu_total = run.get("energy_mu_total") or run.get("python", {}).get("mu")
        name = run.get("name")
        if energy is None or mu_total in {None, 0}:
            continue
        points.append((str(name), float(mu_total), float(energy)))

    if not points:
        raise SystemExit(
            "No energy points found. Re-run with --measure-energy=rapl (and likely --energy-repetitions >= 1000)."
        )

    # Fit through origin: slope = sum(mu*E)/sum(mu^2)
    num = sum(mu * energy for _, mu, energy in points)
    den = sum(mu * mu for _, mu, _ in points)
    slope = num / den if den else float("nan")

    temperature = float(payload.get("temperature_K", 300.0))
    kB = float(payload.get("boltzmann_constant", 1.380649e-23))
    ln2 = float(payload.get("ln2", math.log(2.0)))
    landauer_per_mu = kB * temperature * ln2
    slope_over_landauer = slope / landauer_per_mu if landauer_per_mu else float("nan")

    print(f"Loaded: {args.path}")
    print(f"energy_observable: {runs[0].get('energy_observable')}")
    print(f"temperature_K: {temperature}")
    print()
    for name, mu, energy in points:
        print(f"{name:>18}  mu={mu:10.1f}  energy_j={energy:.6e}  energy_per_mu={energy/mu:.6e}")

    print()
    print(f"Fit (through origin): energy_j ≈ slope * mu")
    print(f"slope: {slope:.6e} J / μ")
    print(f"k_B*T*ln2: {landauer_per_mu:.6e} J / μ")
    print(f"slope / (k_B*T*ln2): {slope_over_landauer:.6e}")


if __name__ == "__main__":
    main()
