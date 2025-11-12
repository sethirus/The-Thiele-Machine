#!/usr/bin/env python3
"""Discover a symbolic turbulence law across multiple datasets and report MDL metrics."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Iterable, List, Mapping, MutableMapping, Sequence

from mu_calibration import landauer_bound

try:  # pylint: disable=ungrouped-imports
    from tools.turbulence_law import prepare_bundles_from_seeds
    from tools.turbulence_law_v2 import (
        DiscoverySummary,
        bundle_metadata,
        discover_symbolic_law,
        load_dataset,
    )
except ModuleNotFoundError:  # pragma: no cover - execution within tools/
    from turbulence_law import prepare_bundles_from_seeds  # type: ignore
    from turbulence_law_v2 import (  # type: ignore
        DiscoverySummary,
        bundle_metadata,
        discover_symbolic_law,
        load_dataset,
    )

DEFAULT_OUTPUT = Path("artifacts/turbulence_law_v2_summary.json")
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


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_OUTPUT, help="summary JSON output path")
    parser.add_argument("--train-seed", dest="train_seeds", action="append", type=int, help="synthetic training seeds")
    parser.add_argument("--eval-seed", dest="eval_seeds", action="append", type=int, help="synthetic evaluation seeds")
    parser.add_argument(
        "--train-dataset",
        dest="train_datasets",
        action="append",
        type=Path,
        help="external dataset used for training (JSON with velocity frames)",
    )
    parser.add_argument(
        "--eval-dataset",
        dest="eval_datasets",
        action="append",
        type=Path,
        help="external dataset used for evaluation only",
    )
    parser.add_argument("--samples", type=int, default=DEFAULT_SAMPLES, help="synthetic samples per series")
    parser.add_argument("--max-terms", type=int, default=DEFAULT_MAX_TERMS, help="maximum symbolic terms")
    parser.add_argument(
        "--min-gain-bits",
        type=float,
        default=DEFAULT_MIN_GAIN_BITS,
        help="minimum MDL improvement (bits) to accept a new feature",
    )
    parser.add_argument(
        "--blind-bits-per-sample",
        type=float,
        default=DEFAULT_BLIND_BITS_PER_SAMPLE,
        help="encoding cost for blind baselines (bits/sample)",
    )
    return parser.parse_args(argv)


def _resolve_seeds(explicit: Sequence[int] | None, fallback: Sequence[int]) -> List[int]:
    values = list(dict.fromkeys(explicit if explicit else fallback))
    return values


def _resolve_datasets(explicit: Sequence[Path] | None, fallback: Sequence[Path]) -> List[Path]:
    selected = list(dict.fromkeys(explicit if explicit else fallback))
    return selected


def _load_training_bundles(seeds: Sequence[int], datasets: Sequence[Path], samples: int):
    bundles = prepare_bundles_from_seeds(seeds, samples) if seeds else []
    for path in datasets:
        if not path.exists():
            raise FileNotFoundError(f"training dataset {path} is missing")
        bundles.append(load_dataset(path))
    if not bundles:
        raise ValueError("no training bundles were provided")
    return bundles


def _load_evaluation_bundles(seeds: Sequence[int], datasets: Sequence[Path], samples: int):
    bundles = prepare_bundles_from_seeds(seeds, samples) if seeds else []
    for path in datasets:
        if not path.exists():
            raise FileNotFoundError(f"evaluation dataset {path} is missing")
        bundles.append(load_dataset(path))
    return bundles


def _aggregate_statistics(summary: DiscoverySummary, training_names: Sequence[str], blind_bits: float) -> Mapping[str, object]:
    training_mu: List[float] = []
    evaluation_mu: List[float] = []
    blind_mu: List[float] = []
    gaps: List[float] = []
    for metric in summary.evaluations:
        if metric.sample_count <= 0:
            continue
        law_total = summary.candidate.model_bits + metric.residual_bits
        blind_total = metric.baseline_bits
        gap = blind_total - law_total
        if metric.bundle.name in training_names:
            training_mu.append(law_total)
        else:
            evaluation_mu.append(law_total)
        blind_mu.append(blind_total)
        gaps.append(gap)
    gap = float(min(gaps)) if gaps else 0.0
    return {
        "training_mu_mean": float(sum(training_mu) / len(training_mu)) if training_mu else 0.0,
        "evaluation_mu_mean": float(sum(evaluation_mu) / len(evaluation_mu)) if evaluation_mu else 0.0,
        "blind_mu_mean": float(sum(blind_mu) / len(blind_mu)) if blind_mu else 0.0,
        "mu_gap_vs_blind_min": gap,
        "blind_bits_per_sample": blind_bits,
    }


def _landauer_bits(candidate_bits: float, temperature: float = 300.0) -> Mapping[str, float]:
    return {
        "mu_bits": candidate_bits,
        "landauer_work_joules": landauer_bound(candidate_bits, temperature),
    }


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    if args.samples < 32:
        raise ValueError("synthetic sample count must be at least 32")
    if args.max_terms <= 0:
        raise ValueError("max-terms must be positive")
    if args.blind_bits_per_sample <= 0:
        raise ValueError("blind bits per sample must be positive")

    train_seeds = _resolve_seeds(args.train_seeds, DEFAULT_TRAIN_SEEDS)
    eval_seeds = _resolve_seeds(args.eval_seeds, DEFAULT_EVAL_SEEDS)
    train_datasets = _resolve_datasets(args.train_datasets, DEFAULT_TRAIN_DATASETS)
    eval_datasets = _resolve_datasets(args.eval_datasets, DEFAULT_EVAL_DATASETS)

    training_bundles = _load_training_bundles(train_seeds, train_datasets, args.samples)
    evaluation_bundles = _load_evaluation_bundles(eval_seeds, eval_datasets, args.samples)

    summary = discover_symbolic_law(
        training_bundles,
        evaluation_bundles,
        max_terms=args.max_terms,
        min_gain_bits=args.min_gain_bits,
        blind_bits_per_sample=args.blind_bits_per_sample,
    )

    training_names = {bundle.name for bundle in training_bundles}
    training_metrics = [metric.as_dict() for metric in summary.evaluations if metric.bundle.name in training_names]
    evaluation_metrics = [metric.as_dict() for metric in summary.evaluations if metric.bundle.name not in training_names]

    baselines: MutableMapping[str, List[Mapping[str, object]]] = {}
    for bundle_name, entries in summary.baselines.items():
        baselines[bundle_name] = [baseline.as_dict() for baseline in entries]

    aggregate = _aggregate_statistics(summary, list(training_names), args.blind_bits_per_sample)

    payload: MutableMapping[str, object] = {
        "law": summary.candidate.as_dict(),
        "training_bundles": [bundle_metadata(bundle) for bundle in training_bundles],
        "evaluation_bundles": [bundle_metadata(bundle) for bundle in evaluation_bundles],
        "training_metrics": training_metrics,
        "evaluation_metrics": evaluation_metrics,
        "baselines": baselines,
        "aggregate": aggregate,
        "mu_question_bits": summary.candidate.model_bits,
        "mu_answer_bits": summary.candidate.residual_bits,
        "mu_total_bits": summary.candidate.total_bits,
        "landauer_reference": _landauer_bits(summary.candidate.total_bits),
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
    print(f"Summary written to {args.json_out}")


if __name__ == "__main__":
    main()
