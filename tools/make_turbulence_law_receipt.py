#!/usr/bin/env python3
"""Generate a turbulence law receipt with hash chaining and NUSD accounting."""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
import math
from pathlib import Path
from typing import Iterable, List, MutableMapping, Sequence

try:
    from tools.mu_calibration import (
        CalibrationSummary,
        compute_calibration_summary,
    )
except ModuleNotFoundError:  # pragma: no cover
    from mu_calibration import (  # type: ignore
        CalibrationSummary,
        compute_calibration_summary,
    )
from turbulence_law import (
    SeriesBundle,
    ar1_baseline,
    blind_baseline,
    bundle_summary,
    evaluate_law,
    law_expression,
    prepare_bundles_from_seeds,
    search_law,
    summarise_evaluations,
    dataset_digest,
)

try:
    from tools.make_law_receipt import append_entry, compute_entry_hash, nusd_payload, verify_chain
except ModuleNotFoundError:  # pragma: no cover
    from make_law_receipt import append_entry, compute_entry_hash, nusd_payload, verify_chain  # type: ignore

DEFAULT_OUTPUT = Path("artifacts/turbulence_law_receipt.jsonl")
DEFAULT_TRAIN_SEEDS = [314159, 271828, 161803]
DEFAULT_EVAL_SEEDS = [57721, 173205]
DEFAULT_SAMPLES = 256
DEFAULT_MAX_TERMS = 3
DEFAULT_EPSILON_FACTOR = 0.01
DEFAULT_TEMPERATURE = 300.0
DEFAULT_BLIND_BITS_PER_SAMPLE = 16.0
DEFAULT_CALIBRATION = Path("mu_bit_correlation_data.json")
SIGNING_KEY = b"ThieleTurbulenceLawKey"


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="receipt output path")
    parser.add_argument(
        "--train-seed",
        dest="train_seeds",
        action="append",
        type=int,
        help="synthetic seeds used for fitting (default: 314159,271828,161803)",
    )
    parser.add_argument(
        "--eval-seed",
        dest="eval_seeds",
        action="append",
        type=int,
        help="synthetic seeds evaluated without refitting (default: 57721,173205)",
    )
    parser.add_argument("--samples", type=int, default=DEFAULT_SAMPLES, help="samples per synthetic series")
    parser.add_argument("--max-terms", type=int, default=DEFAULT_MAX_TERMS, help="maximum symbolic terms in the law")
    parser.add_argument(
        "--blind-bits-per-sample",
        type=float,
        default=DEFAULT_BLIND_BITS_PER_SAMPLE,
        help="bits-per-sample encoding cost for the blind baseline",
    )
    parser.add_argument(
        "--temperature",
        type=float,
        default=DEFAULT_TEMPERATURE,
        help="temperature (Kelvin) for Landauer reporting",
    )
    parser.add_argument(
        "--epsilon-bits",
        type=float,
        help="override epsilon slack bits (default scales with sample count)",
    )
    parser.add_argument(
        "--calibration-file",
        type=Path,
        default=DEFAULT_CALIBRATION,
        help="μ-bit calibration dataset",
    )
    parser.add_argument("--no-calibration", action="store_true", help="omit calibration metadata")
    parser.add_argument(
        "--eval-dataset",
        dest="eval_datasets",
        action="append",
        type=Path,
        help="external datasets (JSON) evaluated without refitting",
    )
    return parser.parse_args(argv)


def _ensure_inputs(args: argparse.Namespace) -> None:
    if args.samples < 8:
        raise ValueError("need at least eight samples to synthesise turbulence series")
    if args.max_terms <= 0:
        raise ValueError("max-terms must be positive")
    if args.blind_bits_per_sample <= 0.0:
        raise ValueError("blind bits per sample must be positive")
    if args.temperature <= 0.0:
        raise ValueError("temperature must be positive")


def _bundles_from_seeds(seeds: Sequence[int] | None, samples: int) -> List[SeriesBundle]:
    selected = list(seeds) if seeds else DEFAULT_TRAIN_SEEDS
    return prepare_bundles_from_seeds(selected, samples)


def _load_eval_bundles(args: argparse.Namespace) -> List[SeriesBundle]:
    bundles: List[SeriesBundle] = []
    seeds = args.eval_seeds if args.eval_seeds else DEFAULT_EVAL_SEEDS
    if seeds:
        bundles.extend(prepare_bundles_from_seeds(seeds, args.samples))
    if args.eval_datasets:
        for path in args.eval_datasets:
            bundles.append(SeriesBundle.from_dataset(path))
    return bundles


def _aggregate_bundle(name: str, bundles: Sequence[SeriesBundle]) -> SeriesBundle:
    energies: List[float] = []
    for bundle in bundles:
        energies.extend(bundle.energies)
    if len(energies) < 4:
        raise ValueError("aggregated energies must contain at least four samples")
    gradients = [energies[index] - energies[index - 1] for index in range(1, len(energies))]
    return SeriesBundle(name=name, energies=energies, gradients=gradients)


def _append_bundle_entries(
    entries: List[MutableMapping[str, object]],
    role: str,
    bundles: Sequence[SeriesBundle],
    results: Sequence[MutableMapping[str, object]] | None = None,
) -> None:
    previous_hash = "0" * 64 if not entries else entries[-1]["crypto_hash"]
    results_map = {result["series"]: result for result in results or []}
    for bundle in bundles:
        summary = dict(bundle_summary(bundle))
        entry: MutableMapping[str, object] = {
            "event": "bundle_observation",
            "role": role,
            "summary": summary,
        }
        if bundle.name in results_map:
            entry["evaluation"] = results_map[bundle.name]
        previous_hash = append_entry(entries, entry, previous_hash)


def _load_calibration(path: Path, skip: bool) -> tuple[CalibrationSummary | None, Path | None]:
    if skip:
        return None, None
    if not path.exists():
        raise FileNotFoundError(f"calibration dataset {path} is missing")
    return compute_calibration_summary(path), path


def _evaluation_payload(candidate, bundles: Sequence[SeriesBundle], blind_bits: float) -> List[MutableMapping[str, object]]:
    payload: List[MutableMapping[str, object]] = []
    for bundle in bundles:
        evaluation = evaluate_law(candidate, bundle)
        ar1 = ar1_baseline(bundle)
        blind = blind_baseline(blind_bits, bundle)
        payload.append(
            {
                "series": bundle.name,
                "residual_bits": evaluation.residual_bits,
                "baseline_bits": evaluation.baseline_bits,
                "delta_vs_baseline": evaluation.delta_vs_baseline,
                "ar1_total_bits": ar1.total_bits,
                "blind_total_bits": blind.total_bits,
            }
        )
    return payload


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    _ensure_inputs(args)

    training_bundles = _bundles_from_seeds(args.train_seeds, args.samples)
    evaluation_bundles = _load_eval_bundles(args)
    aggregate = _aggregate_bundle("training_aggregate", training_bundles)

    candidate = search_law(training_bundles, max_terms=args.max_terms)
    aggregate_eval = evaluate_law(candidate, aggregate)
    ar1_aggregate = ar1_baseline(aggregate)
    blind_aggregate = blind_baseline(args.blind_bits_per_sample, aggregate)

    training_evaluations = _evaluation_payload(candidate, training_bundles, args.blind_bits_per_sample)
    evaluation_evaluations = _evaluation_payload(candidate, evaluation_bundles, args.blind_bits_per_sample)

    epsilon_bits = (
        args.epsilon_bits
        if args.epsilon_bits is not None
        else math.log2(len(aggregate.energies)) * DEFAULT_EPSILON_FACTOR
    )

    calibration_summary, calibration_path = _load_calibration(args.calibration_file, args.no_calibration)

    entries: List[MutableMapping[str, object]] = []
    _append_bundle_entries(entries, "training", training_bundles, training_evaluations)
    if evaluation_bundles:
        _append_bundle_entries(entries, "evaluation", evaluation_bundles, evaluation_evaluations)

    previous_hash = entries[-1]["crypto_hash"] if entries else "0" * 64
    law_entry: MutableMapping[str, object] = {
        "event": "turbulence_law",
        "law": candidate.as_dict(),
        "expression": law_expression(candidate),
        "aggregate_digest": dataset_digest(aggregate),
    }
    previous_hash = append_entry(entries, law_entry, previous_hash)

    summary_payload = nusd_payload(candidate.as_dict(), args.temperature, epsilon_bits, calibration_summary)
    summary_payload.update(
        {
            "aggregate_residual_bits": aggregate_eval.residual_bits,
            "aggregate_baseline_bits": aggregate_eval.baseline_bits,
            "aggregate_delta_bits": aggregate_eval.delta_vs_baseline,
            "aggregate_ar1_total_bits": ar1_aggregate.total_bits,
            "aggregate_blind_total_bits": blind_aggregate.total_bits,
            "mu_gap_vs_blind_bits": blind_aggregate.total_bits - summary_payload["mu_total_bits"],
            "mu_gap_vs_ar1_bits": ar1_aggregate.total_bits - summary_payload["mu_total_bits"],
            "training_summary": summarise_evaluations(
                [evaluate_law(candidate, bundle) for bundle in training_bundles]
            ),
            "evaluation_summary": summarise_evaluations(
                [evaluate_law(candidate, bundle) for bundle in evaluation_bundles]
            ),
            "blind_bits_per_sample": args.blind_bits_per_sample,
            "max_terms": args.max_terms,
            "samples_per_series": args.samples,
            "training_seeds": list(args.train_seeds) if args.train_seeds else DEFAULT_TRAIN_SEEDS,
            "evaluation_seeds": list(args.eval_seeds) if args.eval_seeds else DEFAULT_EVAL_SEEDS,
            "evaluation_datasets": [str(path) for path in args.eval_datasets or []],
            "calibration_dataset": str(calibration_path) if calibration_path else None,
        }
    )

    generator_sha = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

    summary: MutableMapping[str, object] = {
        "event": "turbulence_law_summary",
        "generator": {
            "script": "tools/make_turbulence_law_receipt.py",
            "sha256": generator_sha,
            "parameters": {
                "samples": args.samples,
                "max_terms": args.max_terms,
                "temperature": args.temperature,
                "epsilon_bits": epsilon_bits,
                "blind_bits_per_sample": args.blind_bits_per_sample,
            },
        },
        "nusd": summary_payload,
        "training_evaluations": training_evaluations,
        "evaluation_evaluations": evaluation_evaluations,
        "aggregate": {
            "series": aggregate.name,
            "samples": len(aggregate.energies),
            "digest": dataset_digest(aggregate),
        },
        "chain_validation": {"entries": len(entries) + 1, "self_check": True},
    }

    append_entry(entries, summary, previous_hash)

    summary_entry = entries[-1]
    summary_entry["signature_algorithm"] = "HMAC-SHA256"
    summary_entry["crypto_hash"] = compute_entry_hash(summary_entry)
    summary_entry["signature"] = hmac.new(
        SIGNING_KEY, summary_entry["crypto_hash"].encode("utf-8"), hashlib.sha256
    ).hexdigest()

    if not verify_chain(entries):
        raise RuntimeError("hash chain verification failed before writing receipt")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as handle:
        for entry in entries:
            handle.write(json.dumps(entry, sort_keys=True))
            handle.write("\n")

    print(f"Turbulence law receipt written to {args.output}")


if __name__ == "__main__":
    main()
