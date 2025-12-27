"""Emit a hash-chained, signed receipt for the NUSD turbulence closure law."""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
import math
from pathlib import Path
from typing import Iterable, List, Mapping, MutableMapping, Sequence

try:
    from tools.mu_calibration import CalibrationSummary, compute_calibration_summary
except ModuleNotFoundError:  # pragma: no cover
    from mu_calibration import (  # type: ignore
        CalibrationSummary,
        compute_calibration_summary,
    )

try:  # pragma: no cover - executed from within tools/
    from tools.make_law_receipt import append_entry, compute_entry_hash, nusd_payload, verify_chain
    from tools.turbulence_closure_v1 import (
        bundle_metadata,
        discover_closure,
        load_dataset,
        prepare_bundles_from_seeds,
    )
except ModuleNotFoundError:  # pragma: no cover - execution from repo root
    from make_law_receipt import append_entry, compute_entry_hash, nusd_payload, verify_chain  # type: ignore
    from turbulence_closure_v1 import (  # type: ignore
        bundle_metadata,
        discover_closure,
        load_dataset,
        prepare_bundles_from_seeds,
    )


DEFAULT_OUTPUT = Path("artifacts/turbulence_closure_v1_receipt.jsonl")
DEFAULT_SUMMARY = Path("artifacts/turbulence_closure_v1_summary.json")
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
DEFAULT_CALIBRATION = Path("mu_bit_correlation_data.json")
SIGNING_KEY = b"ThieleTurbulenceClosureKey"


def _parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="receipt output path")
    parser.add_argument("--summary", type=Path, default=DEFAULT_SUMMARY, help="optional summary JSON")
    parser.add_argument("--train-seed", dest="train_seeds", action="append", type=int, help="synthetic training seed")
    parser.add_argument("--eval-seed", dest="eval_seeds", action="append", type=int, help="synthetic evaluation seed")
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
    parser.add_argument("--min-gain-bits", type=float, default=DEFAULT_MIN_GAIN_BITS, help="minimum MDL gain")
    parser.add_argument(
        "--blind-bits-per-sample",
        type=float,
        default=DEFAULT_BLIND_BITS_PER_SAMPLE,
        help="encoding cost for blind baseline (bits/sample)",
    )
    parser.add_argument("--temperature", type=float, default=DEFAULT_TEMPERATURE, help="Landauer temperature (K)")
    parser.add_argument("--epsilon-bits", type=float, help="override epsilon slack bits")
    parser.add_argument("--calibration-file", type=Path, default=DEFAULT_CALIBRATION, help="μ calibration dataset")
    parser.add_argument("--no-calibration", action="store_true", help="skip calibration metadata")
    return parser.parse_args(argv)


def _unique(values: Sequence[int] | Sequence[Path] | None, fallback: Sequence[int] | Sequence[Path]) -> List[int] | List[Path]:
    selected = fallback if values is None else values
    seen: List[int] | List[Path] = []  # type: ignore
    for entry in selected:
        if entry not in seen:
            seen.append(entry)
    return list(seen)


def _load_training(seeds: Sequence[int], datasets: Sequence[Path], samples: int):
    bundles = list(prepare_bundles_from_seeds(seeds, samples) if seeds else [])
    for path in datasets:
        if not path.exists():
            raise FileNotFoundError(f"training dataset {path} missing")
        bundles.append(load_dataset(path))
    if not bundles:
        raise ValueError("no training bundles provided")
    return bundles


def _load_evaluation(seeds: Sequence[int], datasets: Sequence[Path], samples: int):
    bundles = list(prepare_bundles_from_seeds(seeds, samples) if seeds else [])
    for path in datasets:
        if not path.exists():
            raise FileNotFoundError(f"evaluation dataset {path} missing")
        bundles.append(load_dataset(path))
    return bundles


def _calibration(args: argparse.Namespace) -> tuple[CalibrationSummary | None, Path | None]:
    if args.no_calibration:
        return None, None
    if not args.calibration_file.exists():
        raise FileNotFoundError(f"calibration file {args.calibration_file} not found")
    return compute_calibration_summary(args.calibration_file), args.calibration_file


def _epsilon(bits: float | None, samples: int) -> float:
    if bits is not None:
        return float(bits)
    if samples <= 0:
        return 0.0
    return 0.01 * math.log2(samples)


def _bundle_entry(
    bundle,
    role: str,
    metrics: Mapping[str, float],
    baselines,
    previous_hash: str,
    entries: List[MutableMapping[str, object]],
) -> str:
    entry: MutableMapping[str, object] = {
        "event": "closure_bundle",
        "role": role,
        "summary": bundle_metadata(bundle),
        "metrics": metrics,
        "baselines": [baseline.as_dict() for baseline in baselines],
    }
    return append_entry(entries, entry, previous_hash)


def main(argv: Iterable[str] | None = None) -> None:
    args = _parse_args(argv)
    if args.samples < 64:
        raise ValueError("synthetic samples must be at least 64")
    if args.max_terms <= 0:
        raise ValueError("max-terms must be positive")
    if args.blind_bits_per_sample <= 0.0:
        raise ValueError("blind bits per sample must be positive")
    if args.temperature <= 0.0:
        raise ValueError("temperature must be positive")

    train_seeds = _unique(args.train_seeds, DEFAULT_TRAIN_SEEDS)  # type: ignore[arg-type]
    eval_seeds = _unique(args.eval_seeds, DEFAULT_EVAL_SEEDS)  # type: ignore[arg-type]
    train_paths = _unique(args.train_datasets, DEFAULT_TRAIN_DATASETS)  # type: ignore[arg-type]
    eval_paths = _unique(args.eval_datasets, DEFAULT_EVAL_DATASETS)  # type: ignore[arg-type]

    training_bundles = _load_training(train_seeds, train_paths, args.samples)
    evaluation_bundles = _load_evaluation(eval_seeds, eval_paths, args.samples)

    candidate, baselines, train_metrics, eval_metrics = discover_closure(
        training_bundles,
        evaluation_bundles,
        max_terms=args.max_terms,
        min_gain_bits=args.min_gain_bits,
        blind_bits_per_sample=args.blind_bits_per_sample,
    )

    calibration, calibration_path = _calibration(args)
    epsilon_bits = _epsilon(args.epsilon_bits, sum(int(metric.get("sample_count", 0)) for metric in train_metrics.values()))

    entries: List[MutableMapping[str, object]] = []
    previous = "0" * 64
    for bundle in training_bundles:
        metrics = train_metrics.get(bundle.name, {"mu_answer_bits": 0.0, "rmse": 0.0, "sample_count": 0.0})
        previous = _bundle_entry(bundle, "training", metrics, baselines.get(bundle.name, []), previous, entries)
    for bundle in evaluation_bundles:
        metrics = eval_metrics.get(bundle.name, {"mu_answer_bits": 0.0, "rmse": 0.0, "sample_count": 0.0})
        previous = _bundle_entry(bundle, "evaluation", metrics, baselines.get(bundle.name, []), previous, entries)

    summary_payload = {
        "model_bits": candidate.model_bits,
        "residual_bits": candidate.residual_bits,
        "total_bits": candidate.total_bits,
        "features": [feature.name for feature in candidate.features],
        "coefficients": [
            {"numerator": coeff.numerator, "denominator": coeff.denominator}
            for coeff in candidate.coefficients
        ],
        "intercept": {
            "numerator": candidate.intercept.numerator,
            "denominator": candidate.intercept.denominator,
        },
        "expression": candidate.expression(),
    }

    nusd = nusd_payload(
        {
            "model_bits": candidate.model_bits,
            "baseline_bits": args.blind_bits_per_sample,
            "residual_bits": candidate.residual_bits,
        },
        args.temperature,
        epsilon_bits,
        calibration,
    )

    summary_entry: MutableMapping[str, object] = {
        "event": "turbulence_closure_v1_summary",
        "generator": {
            "script": "tools/make_turbulence_closure_v1_receipt.py",
            "sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "parameters": {
                "samples": args.samples,
                "max_terms": args.max_terms,
                "min_gain_bits": args.min_gain_bits,
                "blind_bits_per_sample": args.blind_bits_per_sample,
                "temperature": args.temperature,
                "epsilon_bits": epsilon_bits,
                "training_seeds": list(train_seeds),
                "evaluation_seeds": list(eval_seeds),
                "training_datasets": [str(path) for path in train_paths],
                "evaluation_datasets": [str(path) for path in eval_paths],
            },
        },
        "law": summary_payload,
        "nusd": nusd,
        "calibration_path": str(calibration_path) if calibration_path else None,
        "training_metrics": train_metrics,
        "evaluation_metrics": eval_metrics,
        "baselines": {name: [baseline.as_dict() for baseline in items] for name, items in baselines.items()},
        "training_bundles": [bundle_metadata(bundle) for bundle in training_bundles],
        "evaluation_bundles": [bundle_metadata(bundle) for bundle in evaluation_bundles],
        "chain_validation": {"entries": len(entries) + 1},
    }

    append_entry(entries, summary_entry, previous)

    summary_entry = entries[-1]
    summary_entry["signature_algorithm"] = "HMAC-SHA256"
    summary_entry["crypto_hash"] = compute_entry_hash(summary_entry)
    summary_entry["signature"] = hmac.new(
        SIGNING_KEY,
        summary_entry["crypto_hash"].encode("utf-8"),
        hashlib.sha256,
    ).hexdigest()

    if not verify_chain(entries):
        raise RuntimeError("hash-chain verification failed")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as handle:
        for entry in entries:
            handle.write(json.dumps(entry, sort_keys=True))
            handle.write("\n")

    if args.summary:
        args.summary.parent.mkdir(parents=True, exist_ok=True)
        args.summary.write_text(
            json.dumps({"candidate": summary_payload, "nusd": nusd}, indent=2, sort_keys=True),
            encoding="utf-8",
        )


if __name__ == "__main__":  # pragma: no cover
    main()
