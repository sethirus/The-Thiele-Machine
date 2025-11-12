#!/usr/bin/env python3
"""Utilities for calibrating μ-bit costs against measured energy."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import statistics
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Mapping, MutableMapping

BOLTZMANN_CONSTANT = 1.380_649e-23  # exact by SI definition (J/K)
LN2 = math.log(2.0)
NANOJOULE = 1e-9


@dataclass
class CalibrationSummary:
    """Aggregated statistics describing the μ→energy conversion."""

    source_path: Path
    sha256: str
    sample_count: int
    mean_energy_per_mu_bit_joules: float
    std_energy_per_mu_bit_joules: float
    total_energy_joules: float
    total_mu_bits: float

    def to_payload(self) -> MutableMapping[str, object]:
        return {
            "source_path": str(self.source_path),
            "sha256": self.sha256,
            "sample_count": self.sample_count,
            "mean_energy_per_mu_bit_joules": self.mean_energy_per_mu_bit_joules,
            "std_energy_per_mu_bit_joules": self.std_energy_per_mu_bit_joules,
            "total_energy_joules": self.total_energy_joules,
            "total_mu_bits": self.total_mu_bits,
        }


def _load_dataset(path: Path) -> Mapping[str, object]:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def compute_calibration_summary(path: Path) -> CalibrationSummary:
    """Produce aggregate statistics for a calibration dataset."""

    material = _load_dataset(path)
    entries = list(material.get("instruction_analysis", []))
    if not entries:
        raise ValueError(f"calibration dataset {path} has no instruction_analysis entries")

    energies_per_mu = [float(entry["energy_per_mu_bit"]) * NANOJOULE for entry in entries]
    energy_totals = [float(entry["energy_nanojoules"]) * NANOJOULE for entry in entries]
    mu_totals = [float(entry["mu_cost"]) for entry in entries]

    mean_energy = statistics.fmean(energies_per_mu)
    std_energy = statistics.pstdev(energies_per_mu) if len(energies_per_mu) > 1 else 0.0
    total_energy = sum(energy_totals)
    total_mu = sum(mu_totals)

    sha256 = hashlib.sha256(path.read_bytes()).hexdigest()

    return CalibrationSummary(
        source_path=path,
        sha256=sha256,
        sample_count=len(entries),
        mean_energy_per_mu_bit_joules=mean_energy,
        std_energy_per_mu_bit_joules=std_energy,
        total_energy_joules=total_energy,
        total_mu_bits=total_mu,
    )


def landauer_bound(mu_bits: float, temperature_kelvin: float) -> float:
    """Return the Landauer work bound (joules) for μ-bits at a temperature."""

    effective_bits = max(mu_bits, 0.0)
    return effective_bits * BOLTZMANN_CONSTANT * temperature_kelvin * LN2


def calibrated_work(mu_bits: float, summary: CalibrationSummary) -> float:
    """Predict the empirical work (joules) implied by the calibration data."""

    effective_bits = max(mu_bits, 0.0)
    return effective_bits * summary.mean_energy_per_mu_bit_joules


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("dataset", type=Path, help="path to the calibration dataset JSON file")
    parser.add_argument(
        "--temperature",
        type=float,
        default=300.0,
        help="temperature in Kelvin for reporting the Landauer factor",
    )
    parser.add_argument(
        "--mu-bits",
        type=float,
        default=0.0,
        help="optional μ-bit quantity to convert into energy bounds",
    )
    return parser.parse_args(argv)


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    summary = compute_calibration_summary(args.dataset)
    landauer = landauer_bound(args.mu_bits, args.temperature)
    empirical = calibrated_work(args.mu_bits, summary)
    payload = summary.to_payload()
    payload.update(
        {
            "temperature_kelvin": args.temperature,
            "landauer_factor_j_per_bit": BOLTZMANN_CONSTANT * args.temperature * LN2,
            "landauer_work_bound_joules": landauer,
            "calibrated_work_joules": empirical,
            "mu_bits": args.mu_bits,
        }
    )
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
