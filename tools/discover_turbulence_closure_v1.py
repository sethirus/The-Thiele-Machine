"""Discover a NUSD turbulence closure law across multiple datasets."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Iterable, List, Mapping, MutableMapping, Sequence

try:
    from tools.mu_calibration import landauer_bound
except ModuleNotFoundError:  # pragma: no cover
    from mu_calibration import landauer_bound  # type: ignore

try:  # pragma: no cover - executed as a script under tools/
    from tools.turbulence_closure_v1 import (
        ClosureCandidate,
        bundle_metadata,
        discover_closure,
        load_dataset,
        prepare_bundles_from_seeds,
    )
except ModuleNotFoundError:  # pragma: no cover - repository root execution
    from turbulence_closure_v1 import (  # type: ignore
        ClosureCandidate,
        bundle_metadata,
        discover_closure,
        load_dataset,
        prepare_bundles_from_seeds,
    )


DEFAULT_OUTPUT = Path("artifacts/turbulence_closure_v1_summary.json")
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


def _parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_OUTPUT, help="summary JSON output path")
    parser.add_argument("--train-seed", dest="train_seeds", action="append", type=int, help="synthetic training seed")
    parser.add_argument("--eval-seed", dest="eval_seeds", action="append", type=int, help="synthetic evaluation seed")
    parser.add_argument(
        "--train-dataset",
        dest="train_datasets",
        action="append",
        type=Path,
        help="external dataset (JSON) for training",
    )
    parser.add_argument(
        "--eval-dataset",
        dest="eval_datasets",
        action="append",
        type=Path,
        help="external dataset (JSON) for evaluation",
    )
    parser.add_argument("--samples", type=int, default=DEFAULT_SAMPLES, help="synthetic samples per series")
    parser.add_argument("--max-terms", type=int, default=DEFAULT_MAX_TERMS, help="maximum symbolic terms")
    parser.add_argument("--min-gain-bits", type=float, default=DEFAULT_MIN_GAIN_BITS, help="minimum MDL improvement")
    parser.add_argument(
        "--blind-bits-per-sample",
        type=float,
        default=DEFAULT_BLIND_BITS_PER_SAMPLE,
        help="bits per sample allocated to blind baseline",
    )
    return parser.parse_args(argv)


def _unique(values: Sequence[int] | Sequence[Path] | None, fallback: Sequence[int] | Sequence[Path]) -> List[int] | List[Path]:
    selected = fallback if values is None else values
    seen = []
    for entry in selected:
        if entry not in seen:
            seen.append(entry)
    return list(seen)


def _load_bundles_from_seeds(seeds: Sequence[int], samples: int):
    return prepare_bundles_from_seeds(seeds, samples) if seeds else []


def _load_datasets(paths: Sequence[Path]):
    bundles = []
    for path in paths:
        if not path.exists():
            raise FileNotFoundError(f"dataset {path} is missing")
        bundles.append(load_dataset(path))
    return bundles


def _landauer_payload(mu_bits: float, temperature: float = 300.0) -> Mapping[str, float]:
    return {"mu_bits": mu_bits, "landauer_work_joules": landauer_bound(mu_bits, temperature)}


def _mu_gap_vs_blind(
    baselines: Mapping[str, Sequence[Mapping[str, float | str]]],
    metrics: Mapping[str, Mapping[str, float]],
    model_bits: float,
) -> float:
    gaps: List[float] = []
    for name, entries in baselines.items():
        blind = next((entry for entry in entries if entry.get("name") == "blind"), None)
        metric = metrics.get(name)
        if blind is None or metric is None:
            continue
        blind_total = float(blind["mu_total_bits"])  # type: ignore[index]
        law_total = model_bits + float(metric.get("mu_answer_bits", 0.0))
        gaps.append(blind_total - law_total)
    return float(min(gaps)) if gaps else 0.0


def _serialise_candidate(candidate: ClosureCandidate) -> Mapping[str, object]:
    return {
        "features": [feature.name for feature in candidate.features],
        "intercept": {
            "numerator": candidate.intercept.numerator,
            "denominator": candidate.intercept.denominator,
        },
        "coefficients": [
            {"numerator": coeff.numerator, "denominator": coeff.denominator}
            for coeff in candidate.coefficients
        ],
        "model_bits": candidate.model_bits,
        "residual_bits": candidate.residual_bits,
        "total_bits": candidate.total_bits,
        "expression": candidate.expression(),
    }


def main(argv: Iterable[str] | None = None) -> None:
    args = _parse_args(argv)
    if args.samples < 64:
        raise ValueError("synthetic sample count must be at least 64 for closure discovery")
    if args.max_terms <= 0:
        raise ValueError("max-terms must be positive")
    if args.blind_bits_per_sample <= 0:
        raise ValueError("blind bits per sample must be positive")

    train_seeds = _unique(args.train_seeds, DEFAULT_TRAIN_SEEDS)  # type: ignore[arg-type]
    eval_seeds = _unique(args.eval_seeds, DEFAULT_EVAL_SEEDS)  # type: ignore[arg-type]
    train_datasets = _unique(args.train_datasets, DEFAULT_TRAIN_DATASETS)  # type: ignore[arg-type]
    eval_datasets = _unique(args.eval_datasets, DEFAULT_EVAL_DATASETS)  # type: ignore[arg-type]

    training_bundles = list(_load_bundles_from_seeds(train_seeds, args.samples))
    training_bundles.extend(_load_datasets(train_datasets))
    if not training_bundles:
        raise ValueError("no training bundles provided")
    evaluation_bundles = list(_load_bundles_from_seeds(eval_seeds, args.samples))
    evaluation_bundles.extend(_load_datasets(eval_datasets))

    candidate, baselines, train_metrics, eval_metrics = discover_closure(
        training_bundles,
        evaluation_bundles,
        max_terms=args.max_terms,
        min_gain_bits=args.min_gain_bits,
        blind_bits_per_sample=args.blind_bits_per_sample,
    )

    baseline_payload = {name: [entry.as_dict() for entry in entries] for name, entries in baselines.items()}
    mu_gap = _mu_gap_vs_blind(baseline_payload, {**train_metrics, **eval_metrics}, candidate.model_bits)

    payload: MutableMapping[str, object] = {
        "law": _serialise_candidate(candidate),
        "training_bundles": [bundle_metadata(bundle) for bundle in training_bundles],
        "evaluation_bundles": [bundle_metadata(bundle) for bundle in evaluation_bundles],
        "training_metrics": train_metrics,
        "evaluation_metrics": eval_metrics,
        "baselines": baseline_payload,
        "aggregate": {
            "training_mu_mean": float(
                sum(candidate.model_bits + entry["mu_answer_bits"] for entry in train_metrics.values())
                / len(train_metrics)
            ),
            "evaluation_mu_mean": float(
                sum(candidate.model_bits + entry["mu_answer_bits"] for entry in eval_metrics.values())
                / max(len(eval_metrics), 1)
            ),
            "mu_gap_vs_blind_min": mu_gap,
            "blind_bits_per_sample": args.blind_bits_per_sample,
        },
        "mu_question_bits": candidate.model_bits,
        "mu_answer_bits": candidate.residual_bits,
        "mu_total_bits": candidate.total_bits,
        "landauer_reference": _landauer_payload(candidate.total_bits),
        "parameters": {
            "samples": args.samples,
            "max_terms": args.max_terms,
            "min_gain_bits": args.min_gain_bits,
            "blind_bits_per_sample": args.blind_bits_per_sample,
            "training_seeds": train_seeds,
            "evaluation_seeds": eval_seeds,
            "training_datasets": [str(path) for path in train_datasets],
            "evaluation_datasets": [str(path) for path in eval_datasets],
        },
    }

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


if __name__ == "__main__":  # pragma: no cover
    main()
