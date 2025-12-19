#!/usr/bin/env python3
"""
Structural heat experiment harness.

This script compares two erasure-style workloads:

- Task A: Erase a pool of high-entropy records (no structural certificate).
- Task B: Erase the same-size pool but with a structural certificate (sorted order)
  whose log2 reduction is priced explicitly as μ-paid "structure bits".

It emits ``results/structural_heat_experiment.json`` with μ totals, Ω→Ω′ bit
reductions, and Landauer lower bounds so the claim is a data artifact, not
prose.
"""
from __future__ import annotations

import argparse
import json
import math
import os
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List

from thielecpu.mdl import info_charge
from thielecpu.state import State

REPO_ROOT = Path(__file__).resolve().parent.parent
RESULTS_PATH = REPO_ROOT / "results" / "structural_heat_experiment.json"

BOLTZMANN_CONSTANT = 1.380649e-23  # J/K
LN2 = math.log(2.0)
DEFAULT_TEMPERATURE_K = float(os.environ.get("THERMO_TEMPERATURE_K", 300.0))


@dataclass
class Workload:
    name: str
    bytes_erased: int
    records: int
    structural_bits: float
    log2_omega_before: float
    log2_omega_after: float
    log2_ratio: float
    mu_total: float
    landauer_min_joules: float
    mu_minus_lower_bound: float
    mu_over_log2_ratio: float | None


def _log2_factorial(n: int) -> float:
    return math.lgamma(n + 1) / LN2


def _run_workload(name: str, bytes_erased: int, records: int, structural_bits: float) -> Workload:
    # Base state: genesis is free; we charge only the information bits we claim.
    state = State()
    # Structural bits reflect the certificate/constraint that the data are sorted.
    info_charge(state, structural_bits)

    erase_bits = float(bytes_erased) * 8.0
    log2_omega_before = erase_bits
    log2_omega_after = erase_bits - float(structural_bits)
    log2_ratio = structural_bits

    mu_total = state.mu_ledger.mu_execution
    landauer_j = BOLTZMANN_CONSTANT * DEFAULT_TEMPERATURE_K * LN2 * mu_total

    return Workload(
        name=name,
        bytes_erased=bytes_erased,
        records=records,
        structural_bits=structural_bits,
        log2_omega_before=log2_omega_before,
        log2_omega_after=log2_omega_after,
        log2_ratio=log2_ratio,
        mu_total=mu_total,
        landauer_min_joules=landauer_j,
        mu_minus_lower_bound=mu_total - log2_ratio,
        mu_over_log2_ratio=mu_total / log2_ratio if log2_ratio else None,
    )


def main() -> None:
    parser = argparse.ArgumentParser(description="Run the structural heat anomaly harness")
    parser.add_argument(
        "--out",
        type=Path,
        default=RESULTS_PATH,
        help="Path to write results JSON (default: results/structural_heat_experiment.json)",
    )
    args = parser.parse_args()

    bytes_erased = 1_073_741_824  # 1 GiB erase task
    records = 1_048_576  # 1M logical records in that buffer

    # Task A: random data, no structural certificate beyond erase itself.
    workload_random = _run_workload(
        name="erase_random_noise",
        bytes_erased=bytes_erased,
        records=records,
        structural_bits=0.0,
    )

    # Task B: structured data (sorted records). log2 reduction ~ log2(records!).
    structural_bits = _log2_factorial(records)
    workload_structured = _run_workload(
        name="erase_structured_sorted",
        bytes_erased=bytes_erased,
        records=records,
        structural_bits=structural_bits,
    )

    runs: List[Dict[str, object]] = [asdict(workload_random), asdict(workload_structured)]

    payload: Dict[str, object] = {
        "temperature_K": DEFAULT_TEMPERATURE_K,
        "boltzmann_constant": BOLTZMANN_CONSTANT,
        "ln2": LN2,
        "runs": runs,
        "mu_slack_bits": {
            "min": min(run["mu_minus_lower_bound"] for run in runs),
            "max": max(run["mu_minus_lower_bound"] for run in runs),
        },
    }

    out_path: Path = args.out
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
