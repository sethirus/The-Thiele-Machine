#!/usr/bin/env python3
"""Verify the turbulence head-to-head receipt and recompute the sighted/blind gap."""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
import math
import statistics
from pathlib import Path
from typing import Iterable, List, Mapping

try:
    from tools.make_law_receipt import compute_entry_hash, nusd_payload, verify_chain
except ModuleNotFoundError:  # pragma: no cover - executed inside tools/
    from make_law_receipt import compute_entry_hash, nusd_payload, verify_chain  # type: ignore

try:
    from tools.nusd_domains import ar1_fit, simulate_turbulence_series
except ModuleNotFoundError:  # pragma: no cover - executed inside tools/
    from nusd_domains import ar1_fit, simulate_turbulence_series  # type: ignore

from mu_calibration import CalibrationSummary, compute_calibration_summary

SIGNING_KEY = b"ThieleHeadToHeadKey"


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipt", type=Path, help="path to the head-to-head receipt JSONL")
    parser.add_argument(
        "--calibration-file",
        type=Path,
        default=None,
        help="override the calibration dataset referenced in the receipt",
    )
    parser.add_argument("--skip-calibration", action="store_true", help="skip calibration recomputation")
    return parser.parse_args(argv)


def load_entries(path: Path) -> List[Mapping[str, object]]:
    entries: List[Mapping[str, object]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            material = line.strip()
            if not material:
                continue
            entries.append(json.loads(material))
    if not entries:
        raise ValueError(f"receipt {path} is empty")
    return entries


def ensure(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def calibration_from(summary_dataset: str | None, override: Path | None, skip: bool) -> CalibrationSummary | None:
    if skip:
        return None
    candidate: Path | None = None
    if override is not None:
        candidate = override
    elif summary_dataset:
        candidate = Path(summary_dataset)
    if candidate is None:
        return None
    if not candidate.exists():
        raise FileNotFoundError(f"calibration dataset {candidate} is missing")
    return compute_calibration_summary(candidate)


def dataset_digest(energies: List[float]) -> str:
    payload = json.dumps(energies, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def baseline_bits(energies: List[float]) -> tuple[float, float]:
    if len(energies) < 2:
        raise ValueError("need at least two samples to compute baseline")
    mean_future = statistics.mean(energies[1:])
    baseline_residuals = [actual - mean_future for actual in energies[1:]]
    baseline_energy = sum(value * value for value in baseline_residuals)
    return math.log2(1.0 + baseline_energy), baseline_energy


def sighted_mdl(energies: List[float], baseline: float) -> Mapping[str, float]:
    slope, intercept = ar1_fit(energies)
    predictions = [slope * value + intercept for value in energies[:-1]]
    residuals = [actual - predicted for actual, predicted in zip(energies[1:], predictions)]
    residual_energy = sum(value * value for value in residuals)
    residual_bits = math.log2(1.0 + residual_energy)
    model_bits = math.log2(1.0 + abs(slope)) + math.log2(1.0 + abs(intercept))
    total_bits = model_bits + residual_bits
    return {
        "model_bits": model_bits,
        "residual_bits": residual_bits,
        "baseline_bits": baseline,
        "total_bits": total_bits,
        "delta_vs_baseline": baseline - total_bits,
    }


def blind_mdl(energies: List[float], baseline: float, bits_per_sample: float) -> Mapping[str, float]:
    samples = len(energies)
    model_bits = samples * bits_per_sample + math.log2(1.0 + bits_per_sample)
    residual_bits = baseline
    total_bits = model_bits + residual_bits
    return {
        "model_bits": model_bits,
        "residual_bits": residual_bits,
        "baseline_bits": baseline,
        "total_bits": total_bits,
        "delta_vs_baseline": baseline - total_bits,
    }


def compare_mdl(expected: Mapping[str, float], recorded: Mapping[str, object]) -> None:
    for key, value in expected.items():
        ensure(key in recorded, f"missing mdl field {key}")
        ensure(
            math.isclose(float(recorded.get(key, 0.0)), float(value), rel_tol=1e-6, abs_tol=1e-6),
            f"mdl mismatch for {key}",
        )


def compare_nusd(
    mdl: Mapping[str, float],
    summary: Mapping[str, object],
    temperature: float,
    epsilon_bits: float,
    calibration: CalibrationSummary | None,
) -> Mapping[str, float]:
    recomputed = nusd_payload(mdl, temperature, epsilon_bits, calibration)
    recorded_calibration = summary.get("calibration")
    if calibration is not None and isinstance(recorded_calibration, Mapping):
        recomputed_calibration = recomputed.get("calibration")
        if isinstance(recomputed_calibration, dict):
            recorded_path = recorded_calibration.get("source_path")
            if recorded_path is not None:
                recomputed_calibration["source_path"] = recorded_path
    for key, value in recomputed.items():
        recorded = summary.get(key)
        if isinstance(value, (int, float)):
            ensure(recorded is not None, f"missing nusd field {key}")
            ensure(
                math.isclose(float(recorded), float(value), rel_tol=1e-6, abs_tol=1e-6),
                f"nusd mismatch for {key}",
            )
        else:
            ensure(recorded == value, f"nusd mismatch for {key}")
    return recomputed


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    entries = load_entries(args.receipt)
    summary = entries[-1]
    ensure(summary.get("event") == "turbulence_head_to_head_summary", "final entry is not a head-to-head summary")

    ensure(verify_chain(entries), "hash chain verification failed")
    ensure(compute_entry_hash(summary) == summary.get("crypto_hash"), "summary hash mismatch")
    expected_signature = hmac.new(
        SIGNING_KEY, summary["crypto_hash"].encode("utf-8"), hashlib.sha256
    ).hexdigest()
    ensure(summary.get("signature") == expected_signature, "invalid summary signature")

    generator = summary.get("generator", {})
    ensure(generator.get("script") == "tools/make_turbulence_head_to_head.py", "unexpected generator script")
    generator_sha = generator.get("sha256")
    ensure(generator_sha, "missing generator sha256")
    ensure(
        hashlib.sha256(Path("tools/make_turbulence_head_to_head.py").read_bytes()).hexdigest() == generator_sha,
        "generator sha mismatch",
    )

    parameters = generator.get("parameters", {})
    seed = int(parameters.get("seed", -1))
    samples = int(parameters.get("samples", 0))
    grid = int(parameters.get("grid", 0))
    epsilon_bits = float(parameters.get("epsilon_bits", summary.get("epsilon_bits", 0.0)))
    bits_per_sample = float(parameters.get("blind_bits_per_sample", 0.0))

    dataset_block = summary.get("dataset", {})
    ensure(dataset_block.get("samples") == samples, "dataset sample mismatch")
    ensure(dataset_block.get("grid") == grid, "dataset grid mismatch")
    energies, _ = simulate_turbulence_series(seed, samples)
    ensure(dataset_digest(energies) == dataset_block.get("series_sha256"), "dataset digest mismatch")

    baseline, baseline_energy = baseline_bits(energies)
    ensure(math.isclose(float(dataset_block.get("baseline_bits", 0.0)), baseline, rel_tol=1e-6, abs_tol=1e-6), "baseline bits mismatch")
    ensure(math.isclose(float(dataset_block.get("baseline_energy", 0.0)), baseline_energy, rel_tol=1e-6, abs_tol=1e-6), "baseline energy mismatch")

    sighted_record = summary.get("solvers", {}).get("sighted", {})
    blind_record = summary.get("solvers", {}).get("blind", {})
    ensure(sighted_record, "missing sighted solver record")
    ensure(blind_record, "missing blind solver record")

    sighted_expected = sighted_mdl(energies, baseline)
    blind_expected = blind_mdl(energies, baseline, bits_per_sample)

    compare_mdl(sighted_expected, sighted_record.get("mdl_bits", {}))
    compare_mdl(blind_expected, blind_record.get("mdl_bits", {}))

    temperature = float(summary.get("temperature_kelvin", 0.0))
    calibration_dataset = summary.get("calibration_dataset")
    calibration_summary = calibration_from(calibration_dataset, args.calibration_file, args.skip_calibration)

    sighted_nusd = compare_nusd(sighted_expected, sighted_record.get("nusd_bound", {}), temperature, epsilon_bits, calibration_summary)
    blind_nusd = compare_nusd(blind_expected, blind_record.get("nusd_bound", {}), temperature, epsilon_bits, calibration_summary)

    mu_gap = blind_nusd["mu_total_bits"] - sighted_nusd["mu_total_bits"]
    ensure(
        math.isclose(float(summary.get("mu_gap_bits", 0.0)), mu_gap, rel_tol=1e-6, abs_tol=1e-6),
        "mu gap mismatch",
    )

    chain_validation = summary.get("chain_validation", {})
    ensure(chain_validation.get("self_check") is True, "missing chain self_check flag")
    ensure(chain_validation.get("entries") == len(entries), "chain length mismatch")

    print("Head-to-head receipt verification succeeded")


if __name__ == "__main__":
    main()
