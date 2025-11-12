#!/usr/bin/env python3
"""Replay and verify a turbulence law receipt."""

from __future__ import annotations

import argparse
import hmac
import json
from fractions import Fraction
from pathlib import Path
from typing import Iterable, List, Mapping, MutableMapping, Sequence

from mu_calibration import compute_calibration_summary
from turbulence_law import (
    SeriesBundle,
    ar1_baseline,
    blind_baseline,
    dataset_digest,
    evaluate_law,
    prepare_bundles_from_seeds,
    search_law,
    summarise_evaluations,
)

try:
    from tools.make_law_receipt import compute_entry_hash, verify_chain, nusd_payload
except ModuleNotFoundError:  # pragma: no cover
    from make_law_receipt import compute_entry_hash, verify_chain, nusd_payload  # type: ignore

SIGNING_KEY = b"ThieleTurbulenceLawKey"


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipt", type=Path, help="turbulence law receipt JSONL file")
    parser.add_argument("--root", type=Path, default=Path("."), help="repository root for relative paths")
    return parser.parse_args(argv)


def _load_entries(path: Path) -> List[MutableMapping[str, object]]:
    entries: List[MutableMapping[str, object]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            entries.append(json.loads(line))
    return entries


def _fraction(payload: Mapping[str, object]) -> Fraction:
    return Fraction(int(payload["numerator"]), int(payload["denominator"]))


def _law_from_entry(entry: Mapping[str, object]) -> Mapping[str, object]:
    return entry["law"]


def _bundles_from_summary(summary: Mapping[str, object], samples: int) -> List[SeriesBundle]:
    seeds = summary.get("training_seeds", [])
    return prepare_bundles_from_seeds([int(seed) for seed in seeds], samples)


def _load_eval_bundles(summary: Mapping[str, object], samples: int, root: Path) -> List[SeriesBundle]:
    bundles: List[SeriesBundle] = []
    seeds = summary.get("evaluation_seeds", [])
    if seeds:
        bundles.extend(prepare_bundles_from_seeds([int(seed) for seed in seeds], samples))
    for entry in summary.get("evaluation_datasets", []):
        path = root / Path(entry)
        bundles.append(SeriesBundle.from_dataset(path))
    return bundles


def _aggregate_bundle(bundles: Sequence[SeriesBundle]) -> SeriesBundle:
    energies: List[float] = []
    for bundle in bundles:
        energies.extend(bundle.energies)
    gradients = [energies[index] - energies[index - 1] for index in range(1, len(energies))]
    return SeriesBundle(name="training_aggregate", energies=energies, gradients=gradients)


def _candidate_equal(lhs: Mapping[str, object], rhs: Mapping[str, object]) -> bool:
    if tuple(lhs.get("terms", [])) != tuple(rhs.get("terms", [])):
        return False
    intercept_match = _fraction(lhs["intercept"]) == _fraction(rhs["intercept"])
    coeffs_match = [
        _fraction(value)
        for value in lhs.get("coefficients", [])
    ] == [
        _fraction(value)
        for value in rhs.get("coefficients", [])
    ]
    return intercept_match and coeffs_match


def _expect_close(observed: float, expected: float, label: str, tol: float = 1e-6) -> None:
    if abs(observed - expected) > tol:
        raise ValueError(f"Mismatch for {label}: observed {observed}, expected {expected}")


def _verify_evaluations(
    recorded: Sequence[Mapping[str, object]],
    results,
    bundles: Sequence[SeriesBundle],
    blind_bits: float,
) -> None:
    expected_map = {item["series"]: item for item in recorded}
    for bundle, evaluation in zip(bundles, results):
        ar1 = ar1_baseline(bundle)
        blind = blind_baseline(blind_bits, bundle)
        entry = expected_map.get(bundle.name)
        if entry is None:
            raise ValueError(f"Missing evaluation entry for {bundle.name}")
        _expect_close(evaluation.residual_bits, float(entry["residual_bits"]), f"{bundle.name} residual_bits")
        _expect_close(evaluation.baseline_bits, float(entry["baseline_bits"]), f"{bundle.name} baseline_bits")
        _expect_close(evaluation.delta_vs_baseline, float(entry["delta_vs_baseline"]), f"{bundle.name} delta")
        _expect_close(ar1.total_bits, float(entry["ar1_total_bits"]), f"{bundle.name} ar1_total")
        _expect_close(blind.total_bits, float(entry["blind_total_bits"]), f"{bundle.name} blind_total")


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    entries = _load_entries(args.receipt)
    if not entries:
        raise ValueError("receipt contains no entries")
    if not verify_chain(entries):
        raise RuntimeError("hash chain verification failed")

    summary_entry = entries[-1]
    if summary_entry.get("event") != "turbulence_law_summary":
        raise ValueError("receipt summary event mismatch")
    signature = summary_entry.get("signature")
    if not isinstance(signature, str):
        raise ValueError("summary signature missing")
    expected_hash = compute_entry_hash(summary_entry)
    if summary_entry.get("crypto_hash") != expected_hash:
        raise ValueError("summary crypto hash mismatch")
    expected_signature = hmac.new(SIGNING_KEY, expected_hash.encode("utf-8"), digestmod="sha256").hexdigest()
    if signature != expected_signature:
        raise ValueError("summary signature verification failed")

    nusd_summary: Mapping[str, object] = summary_entry["nusd"]
    samples = int(nusd_summary["samples_per_series"])
    max_terms = int(nusd_summary["max_terms"])
    blind_bits = float(nusd_summary["blind_bits_per_sample"])

    training_bundles = _bundles_from_summary(nusd_summary, samples)
    evaluation_bundles = _load_eval_bundles(nusd_summary, samples, args.root)
    aggregate = _aggregate_bundle(training_bundles)

    candidate = search_law(training_bundles, max_terms=max_terms)

    law_entry = next(entry for entry in entries if entry.get("event") == "turbulence_law")
    recorded_law = _law_from_entry(law_entry)
    if not _candidate_equal(candidate.as_dict(), recorded_law):
        raise ValueError("law coefficients mismatch")

    aggregate_eval = evaluate_law(candidate, aggregate)
    ar1 = ar1_baseline(aggregate)
    blind = blind_baseline(blind_bits, aggregate)

    recomputed_nusd = nusd_payload(candidate.as_dict(), float(nusd_summary["temperature_kelvin"]), float(nusd_summary["epsilon_bits"]), None)
    recomputed_nusd.update(
        {
            "aggregate_residual_bits": aggregate_eval.residual_bits,
            "aggregate_baseline_bits": aggregate_eval.baseline_bits,
            "aggregate_delta_bits": aggregate_eval.delta_vs_baseline,
            "aggregate_ar1_total_bits": ar1.total_bits,
            "aggregate_blind_total_bits": blind.total_bits,
            "mu_gap_vs_blind_bits": blind.total_bits - recomputed_nusd["mu_total_bits"],
            "mu_gap_vs_ar1_bits": ar1.total_bits - recomputed_nusd["mu_total_bits"],
        }
    )

    for key, value in recomputed_nusd.items():
        if key in ("calibration", "calibrated_mu_bits", "calibrated_work_joules"):
            continue
        _expect_close(float(nusd_summary[key]), float(value), key)

    training_results = [evaluate_law(candidate, bundle) for bundle in training_bundles]
    evaluation_results = [evaluate_law(candidate, bundle) for bundle in evaluation_bundles]
    _verify_evaluations(summary_entry.get("training_evaluations", []), training_results, training_bundles, blind_bits)
    _verify_evaluations(summary_entry.get("evaluation_evaluations", []), evaluation_results, evaluation_bundles, blind_bits)

    training_summary = summarise_evaluations(training_results)
    recorded_training_summary = nusd_summary.get("training_summary", {})
    for key, value in training_summary.items():
        if key in recorded_training_summary:
            _expect_close(float(recorded_training_summary[key]), float(value), f"training_summary.{key}")
    evaluation_summary = summarise_evaluations(evaluation_results)
    recorded_evaluation_summary = nusd_summary.get("evaluation_summary", {})
    for key, value in evaluation_summary.items():
        if key in recorded_evaluation_summary:
            _expect_close(float(recorded_evaluation_summary[key]), float(value), f"evaluation_summary.{key}")

    lookup = {bundle.name: bundle for bundle in training_bundles + evaluation_bundles}
    for entry in entries:
        if entry.get("event") != "bundle_observation":
            continue
        summary = entry.get("summary", {})
        series = summary.get("series")
        if series not in lookup:
            raise ValueError(f"unexpected bundle observation for {series}")
        digest = summary.get("digest")
        actual = dataset_digest(lookup[series])
        if digest != actual:
            raise ValueError(f"digest mismatch for {series}")

    recorded_digest = summary_entry["aggregate"]["digest"]
    actual_digest = dataset_digest(aggregate)
    if recorded_digest != actual_digest:
        raise ValueError("aggregate digest mismatch")

    calibration_path = nusd_summary.get("calibration_dataset")
    if calibration_path:
        path = args.root / Path(calibration_path)
        summary = compute_calibration_summary(path)
        payload = summary.to_payload()
        recorded = nusd_summary.get("calibration", {})
        for key, value in payload.items():
            if key not in recorded:
                continue
            if isinstance(value, (int, float)):
                _expect_close(float(recorded[key]), float(value), f"calibration.{key}")
            else:
                if str(recorded[key]) != str(value):
                    raise ValueError(f"calibration field mismatch for {key}")

    print("Turbulence law receipt verified successfully")


if __name__ == "__main__":
    main()
