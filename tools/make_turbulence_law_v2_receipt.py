#!/usr/bin/env python3
"""Generate a hash-chained receipt for the NUSD turbulence law v2 discovery."""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
import math
from pathlib import Path
from typing import Iterable, List, Mapping, MutableMapping, Sequence

from mu_calibration import CalibrationSummary, compute_calibration_summary

try:  # pylint: disable=ungrouped-imports
    from tools.make_law_receipt import append_entry, compute_entry_hash, nusd_payload, verify_chain
    from tools.turbulence_law import SeriesBundle, prepare_bundles_from_seeds
    from tools.turbulence_law_v2 import (
        DiscoverySummary,
        bundle_metadata,
        discover_symbolic_law,
        evaluate_candidate,
        load_dataset,
    )
except ModuleNotFoundError:  # pragma: no cover - execution within tools/
    from make_law_receipt import append_entry, compute_entry_hash, nusd_payload, verify_chain  # type: ignore
    from turbulence_law import SeriesBundle, prepare_bundles_from_seeds  # type: ignore
    from turbulence_law_v2 import (  # type: ignore
        DiscoverySummary,
        bundle_metadata,
        discover_symbolic_law,
        evaluate_candidate,
        load_dataset,
    )

DEFAULT_OUTPUT = Path("artifacts/turbulence_law_v2_receipt.jsonl")
DEFAULT_SUMMARY = Path("artifacts/turbulence_law_v2_summary.json")
DEFAULT_TRAIN_SEEDS = [314159, 271828, 161803]
DEFAULT_EVAL_SEEDS = [57721, 173205]
DEFAULT_TRAIN_DATASETS = [
    Path("public_data/jhtdb/isotropic1024_coarse.json"),
    Path("public_data/jhtdb/channel_flow_centerline.json"),
]
DEFAULT_EVAL_DATASETS = [Path("public_data/jhtdb/sample/jhtdb_samples.json")]
DEFAULT_SAMPLES = 384
DEFAULT_MAX_TERMS = 4
DEFAULT_MIN_GAIN_BITS = 0.05
DEFAULT_BLIND_BITS_PER_SAMPLE = 16.0
DEFAULT_TEMPERATURE = 300.0
DEFAULT_EPSILON_FACTOR = 0.01
DEFAULT_CALIBRATION = Path("mu_bit_correlation_data.json")
SIGNING_KEY = b"ThieleTurbulenceLawV2Key"


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="receipt output path")
    parser.add_argument("--summary", type=Path, default=DEFAULT_SUMMARY, help="optional summary JSON output")
    parser.add_argument("--train-seed", dest="train_seeds", action="append", type=int, help="synthetic training seeds")
    parser.add_argument("--eval-seed", dest="eval_seeds", action="append", type=int, help="synthetic evaluation seeds")
    parser.add_argument(
        "--train-dataset",
        dest="train_datasets",
        action="append",
        type=Path,
        help="external dataset used for training",
    )
    parser.add_argument(
        "--eval-dataset",
        dest="eval_datasets",
        action="append",
        type=Path,
        help="external dataset used for evaluation",
    )
    parser.add_argument("--samples", type=int, default=DEFAULT_SAMPLES, help="synthetic samples per series")
    parser.add_argument("--max-terms", type=int, default=DEFAULT_MAX_TERMS, help="maximum symbolic terms")
    parser.add_argument(
        "--min-gain-bits",
        type=float,
        default=DEFAULT_MIN_GAIN_BITS,
        help="minimum MDL improvement to accept a feature",
    )
    parser.add_argument(
        "--blind-bits-per-sample",
        type=float,
        default=DEFAULT_BLIND_BITS_PER_SAMPLE,
        help="encoding cost for blind baseline (bits/sample)",
    )
    parser.add_argument("--temperature", type=float, default=DEFAULT_TEMPERATURE, help="Landauer temperature (Kelvin)")
    parser.add_argument("--epsilon-bits", type=float, help="override epsilon slack bits")
    parser.add_argument("--calibration-file", type=Path, default=DEFAULT_CALIBRATION, help="μ-bit calibration dataset")
    parser.add_argument("--no-calibration", action="store_true", help="omit calibration metadata")
    return parser.parse_args(argv)


def _resolve(values: Sequence[int] | None, fallback: Sequence[int]) -> List[int]:
    return list(dict.fromkeys(values if values else fallback))


def _resolve_paths(values: Sequence[Path] | None, fallback: Sequence[Path]) -> List[Path]:
    return list(dict.fromkeys(values if values else fallback))


def _load_training_bundles(seeds: Sequence[int], datasets: Sequence[Path], samples: int) -> List[SeriesBundle]:
    bundles = prepare_bundles_from_seeds(seeds, samples) if seeds else []
    for path in datasets:
        if not path.exists():
            raise FileNotFoundError(f"training dataset {path} not found")
        bundles.append(load_dataset(path))
    if not bundles:
        raise ValueError("no training bundles provided")
    return bundles


def _load_evaluation_bundles(seeds: Sequence[int], datasets: Sequence[Path], samples: int) -> List[SeriesBundle]:
    bundles = prepare_bundles_from_seeds(seeds, samples) if seeds else []
    for path in datasets:
        if not path.exists():
            raise FileNotFoundError(f"evaluation dataset {path} not found")
        bundles.append(load_dataset(path))
    return bundles


def _aggregate_bundle(name: str, bundles: Sequence[SeriesBundle]) -> SeriesBundle:
    energies: List[float] = []
    for bundle in bundles:
        energies.extend(bundle.energies)
    gradients = [energies[idx] - energies[idx - 1] for idx in range(1, len(energies))]
    return SeriesBundle(name=name, energies=energies, gradients=gradients)


def _calibration(summary: argparse.Namespace) -> tuple[CalibrationSummary | None, Path | None]:
    if summary.no_calibration:
        return None, None
    if not summary.calibration_file.exists():
        raise FileNotFoundError(f"calibration file {summary.calibration_file} is missing")
    return compute_calibration_summary(summary.calibration_file), summary.calibration_file


def _append_bundle_entries(
    entries: List[MutableMapping[str, object]],
    *,
    role: str,
    bundles: Sequence[SeriesBundle],
    discovery: DiscoverySummary,
) -> None:
    previous_hash = entries[-1]["crypto_hash"] if entries else "0" * 64
    for bundle in bundles:
        metadata = dict(bundle_metadata(bundle))
        evaluation = next(metric for metric in discovery.evaluations if metric.bundle.name == bundle.name)
        baselines = [baseline.as_dict() for baseline in discovery.baselines.get(bundle.name, [])]
        entry: MutableMapping[str, object] = {
            "event": "bundle_observation",
            "role": role,
            "summary": metadata,
            "evaluation": evaluation.as_dict(),
            "baselines": baselines,
        }
        previous_hash = append_entry(entries, entry, previous_hash)


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    if args.samples < 32:
        raise ValueError("synthetic samples must be at least 32")
    if args.max_terms <= 0:
        raise ValueError("max-terms must be positive")
    if args.blind_bits_per_sample <= 0.0:
        raise ValueError("blind bits per sample must be positive")
    if args.temperature <= 0.0:
        raise ValueError("temperature must be positive")

    train_seeds = _resolve(args.train_seeds, DEFAULT_TRAIN_SEEDS)
    eval_seeds = _resolve(args.eval_seeds, DEFAULT_EVAL_SEEDS)
    train_paths = _resolve_paths(args.train_datasets, DEFAULT_TRAIN_DATASETS)
    eval_paths = _resolve_paths(args.eval_datasets, DEFAULT_EVAL_DATASETS)

    training_bundles = _load_training_bundles(train_seeds, train_paths, args.samples)
    evaluation_bundles = _load_evaluation_bundles(eval_seeds, eval_paths, args.samples)

    discovery = discover_symbolic_law(
        training_bundles,
        evaluation_bundles,
        max_terms=args.max_terms,
        min_gain_bits=args.min_gain_bits,
        blind_bits_per_sample=args.blind_bits_per_sample,
    )

    calibration, calibration_path = _calibration(args)

    entries: List[MutableMapping[str, object]] = []
    _append_bundle_entries(entries, role="training", bundles=training_bundles, discovery=discovery)
    if evaluation_bundles:
        _append_bundle_entries(entries, role="evaluation", bundles=evaluation_bundles, discovery=discovery)

    previous_hash = entries[-1]["crypto_hash"] if entries else "0" * 64

    aggregate = _aggregate_bundle("training_aggregate", training_bundles)
    aggregate_eval = evaluate_candidate(
        aggregate,
        discovery.candidate,
        bits_per_sample=args.blind_bits_per_sample,
    )

    law_entry: MutableMapping[str, object] = {
        "event": "turbulence_law_v2",
        "law": discovery.candidate.as_dict(),
        "expression": discovery.candidate.expression,
        "aggregate_digest": bundle_metadata(aggregate)["digest"],
    }
    previous_hash = append_entry(entries, law_entry, previous_hash)

    epsilon_bits = (
        args.epsilon_bits
        if args.epsilon_bits is not None
        else math.log2(discovery.candidate.sample_count + 1) * DEFAULT_EPSILON_FACTOR
    )

    nusd_summary = discovery.candidate.as_dict()
    summary_payload = nusd_payload(nusd_summary, args.temperature, epsilon_bits, calibration)
    summary_payload.update(
        {
            "aggregate_residual_bits": aggregate_eval.residual_bits,
            "aggregate_baseline_bits": aggregate_eval.baseline_bits,
            "aggregate_mu_total_bits": discovery.candidate.model_bits + aggregate_eval.mu_answer,
            "training_bundle_count": len(training_bundles),
            "evaluation_bundle_count": len(evaluation_bundles),
            "blind_bits_per_sample": args.blind_bits_per_sample,
            "max_terms": args.max_terms,
            "min_gain_bits": args.min_gain_bits,
            "samples_per_series": args.samples,
            "training_seeds": train_seeds,
            "evaluation_seeds": eval_seeds,
            "training_datasets": [str(path) for path in train_paths],
            "evaluation_datasets": [str(path) for path in eval_paths],
            "calibration_dataset": str(calibration_path) if calibration_path else None,
        }
    )

    mu_gap_vs_blind = []
    for bundle in training_bundles + evaluation_bundles:
        evaluation = next(metric for metric in discovery.evaluations if metric.bundle.name == bundle.name)
        blind_entry = next((baseline for baseline in discovery.baselines[bundle.name] if baseline.name == "Blind"), None)
        if blind_entry is not None:
            mu_gap_vs_blind.append(blind_entry.mu_total_bits - (discovery.candidate.model_bits + evaluation.mu_answer))
    if mu_gap_vs_blind:
        summary_payload["mu_gap_vs_blind_min"] = float(min(mu_gap_vs_blind))
        summary_payload["mu_gap_vs_blind_mean"] = float(sum(mu_gap_vs_blind) / len(mu_gap_vs_blind))

    generator_sha = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

    summary_entry: MutableMapping[str, object] = {
        "event": "turbulence_law_v2_summary",
        "generator": {
            "script": "tools/make_turbulence_law_v2_receipt.py",
            "sha256": generator_sha,
            "parameters": {
                "samples": args.samples,
                "max_terms": args.max_terms,
                "min_gain_bits": args.min_gain_bits,
                "temperature": args.temperature,
                "epsilon_bits": epsilon_bits,
                "blind_bits_per_sample": args.blind_bits_per_sample,
            },
        },
        "nusd": summary_payload,
        "training_evaluations": [
            metric.as_dict()
            for metric in discovery.evaluations
            if metric.bundle in training_bundles and metric.sample_count > 0
        ],
        "evaluation_evaluations": [
            metric.as_dict()
            for metric in discovery.evaluations
            if metric.bundle not in training_bundles and metric.sample_count > 0
        ],
        "baselines": {
            name: [baseline.as_dict() for baseline in items]
            for name, items in discovery.baselines.items()
        },
        "aggregate": {
            "series": aggregate.name,
            "samples": len(aggregate.energies),
            "digest": bundle_metadata(aggregate)["digest"],
        },
        "chain_validation": {"entries": len(entries) + 1, "self_check": True},
    }

    append_entry(entries, summary_entry, previous_hash)

    summary_entry = entries[-1]
    summary_entry["signature_algorithm"] = "HMAC-SHA256"
    summary_entry["crypto_hash"] = compute_entry_hash(summary_entry)
    summary_entry["signature"] = hmac.new(
        SIGNING_KEY,
        summary_entry["crypto_hash"].encode("utf-8"),
        hashlib.sha256,
    ).hexdigest()

    if not verify_chain(entries):
        raise RuntimeError("hash chain verification failed before writing receipt")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as handle:
        for entry in entries:
            handle.write(json.dumps(entry, sort_keys=True))
            handle.write("\n")

    if args.summary:
        args.summary.parent.mkdir(parents=True, exist_ok=True)
        summary_document = {
            "candidate": discovery.candidate.as_dict(),
            "summary_entry": summary_entry,
        }
        args.summary.write_text(
            json.dumps(summary_document, indent=2, sort_keys=True),
            encoding="utf-8",
        )

    print(f"Turbulence law v2 receipt written to {args.output}")


if __name__ == "__main__":
    main()
