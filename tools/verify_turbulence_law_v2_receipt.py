#!/usr/bin/env python3
"""Replay and verify a turbulence law v2 receipt."""

from __future__ import annotations

import argparse
import hmac
import json
from fractions import Fraction
from pathlib import Path
from typing import Iterable, List, Mapping, MutableMapping

try:  # pylint: disable=ungrouped-imports
    from tools.make_law_receipt import compute_entry_hash, verify_chain, nusd_payload
    from tools.turbulence_law import SeriesBundle, prepare_bundles_from_seeds
    from tools.turbulence_law_v2 import (
        bundle_metadata,
        compute_baselines,
        discover_symbolic_law,
        evaluate_candidate,
        load_dataset,
    )
except ModuleNotFoundError:  # pragma: no cover
    from make_law_receipt import compute_entry_hash, verify_chain, nusd_payload  # type: ignore
    from turbulence_law import SeriesBundle, prepare_bundles_from_seeds  # type: ignore
    from turbulence_law_v2 import (  # type: ignore
        bundle_metadata,
        compute_baselines,
        discover_symbolic_law,
        evaluate_candidate,
        load_dataset,
    )

SIGNING_KEY = b"ThieleTurbulenceLawV2Key"


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipt", type=Path, help="receipt JSONL file")
    parser.add_argument("--root", type=Path, default=Path("."), help="repository root for relative datasets")
    return parser.parse_args(argv)


def _load_entries(path: Path) -> List[MutableMapping[str, object]]:
    entries: List[MutableMapping[str, object]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            entries.append(json.loads(line))
    if not entries:
        raise ValueError("receipt contains no entries")
    return entries


def _fraction(payload: Mapping[str, object]) -> Fraction:
    return Fraction(int(payload["numerator"]), int(payload["denominator"]))


def _law_equal(lhs: Mapping[str, object], rhs: Mapping[str, object]) -> bool:
    if tuple(lhs.get("terms", [])) != tuple(rhs.get("terms", [])):
        return False
    lhs_intercept = _fraction(lhs["intercept"]) if "intercept" in lhs else Fraction(0, 1)
    rhs_intercept = _fraction(rhs["intercept"]) if "intercept" in rhs else Fraction(0, 1)
    if lhs_intercept != rhs_intercept:
        return False
    lhs_coeffs = [_fraction(item) for item in lhs.get("coefficients", [])]
    rhs_coeffs = [_fraction(item) for item in rhs.get("coefficients", [])]
    return lhs_coeffs == rhs_coeffs


def _expect_close(observed: float, expected: float, label: str, tol: float = 1e-6) -> None:
    if abs(observed - expected) > tol:
        raise ValueError(f"Mismatch for {label}: observed {observed} expected {expected}")


def _aggregate_bundle(name: str, bundles: Iterable[SeriesBundle]) -> SeriesBundle:
    energies: List[float] = []
    for bundle in bundles:
        energies.extend(bundle.energies)
    gradients = [energies[idx] - energies[idx - 1] for idx in range(1, len(energies))]
    return SeriesBundle(name=name, energies=energies, gradients=gradients)


def _bundle_map(entries: Iterable[Mapping[str, object]]) -> Mapping[str, Mapping[str, object]]:
    material: MutableMapping[str, Mapping[str, object]] = {}
    for entry in entries:
        if entry.get("event") != "bundle_observation":
            continue
        summary = entry.get("summary", {})
        name = summary.get("series")
        if not isinstance(name, str):
            continue
        material[name] = entry
    return material


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    entries = _load_entries(args.receipt)
    if not verify_chain(entries):
        raise RuntimeError("hash chain verification failed")

    summary_entry = entries[-1]
    if summary_entry.get("event") != "turbulence_law_v2_summary":
        raise ValueError("receipt summary event mismatch")

    expected_hash = compute_entry_hash(summary_entry)
    if summary_entry.get("crypto_hash") != expected_hash:
        raise ValueError("summary crypto hash mismatch")

    signature = summary_entry.get("signature")
    if not isinstance(signature, str):
        raise ValueError("summary signature missing")
    expected_signature = hmac.new(SIGNING_KEY, expected_hash.encode("utf-8"), digestmod="sha256").hexdigest()
    if signature != expected_signature:
        raise ValueError("summary signature verification failed")

    nusd_summary: Mapping[str, object] = summary_entry["nusd"]
    params = summary_entry.get("generator", {}).get("parameters", {})
    samples = int(nusd_summary.get("samples_per_series", params.get("samples", 0)))
    max_terms = int(nusd_summary.get("max_terms", params.get("max_terms", 0)))
    min_gain_bits = float(nusd_summary.get("min_gain_bits", params.get("min_gain_bits", 0.0)))
    blind_bits = float(nusd_summary.get("blind_bits_per_sample", params.get("blind_bits_per_sample", 0.0)))
    temperature = float(params.get("temperature", nusd_summary.get("temperature_kelvin", 300.0)))
    epsilon_bits = float(params.get("epsilon_bits", nusd_summary.get("epsilon_bits", 0.0)))

    train_seeds = [int(value) for value in nusd_summary.get("training_seeds", [])]
    eval_seeds = [int(value) for value in nusd_summary.get("evaluation_seeds", [])]
    train_datasets = [Path(value) for value in nusd_summary.get("training_datasets", [])]
    eval_datasets = [Path(value) for value in nusd_summary.get("evaluation_datasets", [])]

    root = args.root.resolve()
    training_bundles = prepare_bundles_from_seeds(train_seeds, samples) if train_seeds else []
    for path in train_datasets:
        dataset_path = (root / path).resolve()
        bundle = load_dataset(dataset_path)
        absolute = str(dataset_path)
        if bundle.name.startswith(absolute):
            suffix = bundle.name[len(absolute):]
            bundle.name = f"{path}{suffix}"
        training_bundles.append(bundle)
    evaluation_bundles = prepare_bundles_from_seeds(eval_seeds, samples) if eval_seeds else []
    for path in eval_datasets:
        dataset_path = (root / path).resolve()
        bundle = load_dataset(dataset_path)
        absolute = str(dataset_path)
        if bundle.name.startswith(absolute):
            suffix = bundle.name[len(absolute):]
            bundle.name = f"{path}{suffix}"
        evaluation_bundles.append(bundle)

    discovery = discover_symbolic_law(
        training_bundles,
        evaluation_bundles,
        max_terms=max_terms,
        min_gain_bits=min_gain_bits,
        blind_bits_per_sample=blind_bits,
    )

    law_entry = next(entry for entry in entries if entry.get("event") == "turbulence_law_v2")
    recorded_law = law_entry.get("law", {})
    if not _law_equal(recorded_law, discovery.candidate.as_dict()):
        raise ValueError("law coefficients mismatch")

    aggregate = _aggregate_bundle("training_aggregate", training_bundles)
    aggregate_eval = evaluate_candidate(
        aggregate,
        discovery.candidate,
        bits_per_sample=blind_bits,
    )

    recomputed_nusd = discovery.candidate.as_dict()
    nusd_payload_actual = nusd_payload(recomputed_nusd, temperature, epsilon_bits, None)
    nusd_payload_actual.update(
        {
            "aggregate_residual_bits": aggregate_eval.residual_bits,
            "aggregate_baseline_bits": aggregate_eval.baseline_bits,
            "aggregate_mu_total_bits": discovery.candidate.model_bits + aggregate_eval.mu_answer,
            "training_bundle_count": len(training_bundles),
            "evaluation_bundle_count": len(evaluation_bundles),
            "blind_bits_per_sample": blind_bits,
            "max_terms": max_terms,
            "min_gain_bits": min_gain_bits,
            "samples_per_series": samples,
        }
    )

    for key, value in nusd_payload_actual.items():
        if key not in nusd_summary:
            continue
        _expect_close(float(nusd_summary[key]), float(value), f"nusd.{key}")

    bundle_entries = _bundle_map(entries)
    for bundle in training_bundles + evaluation_bundles:
        entry = bundle_entries.get(bundle.name)
        if entry is None:
            raise ValueError(f"missing receipt entry for {bundle.name}")
        metadata = bundle_metadata(bundle)
        recorded_summary = entry.get("summary", {})
        for field in ("samples", "digest"):
            if field in recorded_summary:
                recorded = float(recorded_summary[field]) if field == "samples" else recorded_summary[field]
                expected = float(metadata[field]) if field == "samples" else metadata[field]
                if recorded != expected:
                    raise ValueError(f"bundle metadata mismatch for {bundle.name} field {field}")
        evaluation = evaluate_candidate(
            bundle,
            discovery.candidate,
            bits_per_sample=blind_bits,
        )
        recorded_eval = entry.get("evaluation", {})
        _expect_close(float(recorded_eval.get("residual_bits", 0.0)), evaluation.residual_bits, f"{bundle.name} residual_bits")
        _expect_close(float(recorded_eval.get("baseline_bits", 0.0)), evaluation.baseline_bits, f"{bundle.name} baseline_bits")
        _expect_close(float(recorded_eval.get("rmse", 0.0)), evaluation.rmse, f"{bundle.name} rmse")
        _expect_close(float(recorded_eval.get("mae", 0.0)), evaluation.mae, f"{bundle.name} mae")
        _expect_close(float(recorded_eval.get("spectrum_error", 0.0)), evaluation.spectrum_error, f"{bundle.name} spectrum")

        baselines = compute_baselines(bundle, bits_per_sample=blind_bits)
        recorded_baselines = entry.get("baselines", [])
        recorded_map = {item["name"]: item for item in recorded_baselines}
        for baseline in baselines:
            material = recorded_map.get(baseline.name)
            if material is None:
                raise ValueError(f"missing baseline {baseline.name} for {bundle.name}")
            _expect_close(float(material.get("mu_question_bits", 0.0)), baseline.mu_question_bits, f"{bundle.name} {baseline.name} mu_question")
            _expect_close(float(material.get("mu_answer_bits", 0.0)), baseline.mu_answer_bits, f"{bundle.name} {baseline.name} mu_answer")
            _expect_close(float(material.get("mu_total_bits", 0.0)), baseline.mu_total_bits, f"{bundle.name} {baseline.name} mu_total")

    print("Receipt verification completed successfully")


if __name__ == "__main__":
    main()
