#!/usr/bin/env python3
"""Search for a compact turbulence law and report its performance."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Iterable, List, Sequence

from turbulence_law import (
    bundle_summary,
    evaluate_law,
    law_expression,
    prepare_bundles_from_seeds,
    search_law,
    summarise_evaluations,
    load_external_bundle,
    ar1_baseline,
    blind_baseline,
    SeriesBundle,
)

DEFAULT_TRAIN_SEEDS = [314159, 271828, 161803]
DEFAULT_EVAL_SEEDS = [57721, 173205]
DEFAULT_SAMPLES = 256
DEFAULT_MAX_TERMS = 3
DEFAULT_BLIND_BITS_PER_SAMPLE = 16.0


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--train-seed",
        dest="train_seeds",
        action="append",
        type=int,
        help="synthetic seeds used for training (default: 314159,271828,161803)",
    )
    parser.add_argument(
        "--eval-seed",
        dest="eval_seeds",
        action="append",
        type=int,
        help="synthetic seeds evaluated after fitting (default: 57721,173205)",
    )
    parser.add_argument(
        "--samples",
        type=int,
        default=DEFAULT_SAMPLES,
        help="number of samples per synthetic series",
    )
    parser.add_argument(
        "--max-terms",
        type=int,
        default=DEFAULT_MAX_TERMS,
        help="maximum number of symbolic terms to consider",
    )
    parser.add_argument(
        "--blind-bits-per-sample",
        type=float,
        default=DEFAULT_BLIND_BITS_PER_SAMPLE,
        help="bits-per-sample budget for the blind baseline",
    )
    parser.add_argument(
        "--eval-dataset",
        dest="eval_datasets",
        action="append",
        type=Path,
        help="external datasets (JSON) evaluated without re-fitting",
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        help="optional path for a JSON summary",
    )
    return parser.parse_args(argv)


def _ensure_samples(count: int) -> None:
    if count < 8:
        raise ValueError("need at least eight samples to fit the turbulence law")


def _ensure_terms(max_terms: int) -> None:
    if max_terms <= 0:
        raise ValueError("max-terms must be positive")


def _load_training_bundles(seeds: Sequence[int] | None, samples: int) -> List[SeriesBundle]:
    selected = list(seeds) if seeds else DEFAULT_TRAIN_SEEDS
    _ensure_samples(samples)
    return prepare_bundles_from_seeds(selected, samples)


def _load_eval_bundles(args: argparse.Namespace) -> List[SeriesBundle]:
    bundles: List[SeriesBundle] = []
    seeds = args.eval_seeds if args.eval_seeds else DEFAULT_EVAL_SEEDS
    if seeds:
        bundles.extend(prepare_bundles_from_seeds(seeds, args.samples))
    if args.eval_datasets:
        for path in args.eval_datasets:
            bundles.append(load_external_bundle(path))
    return bundles


def _summarise_bundle_set(bundles: Sequence[SeriesBundle]) -> List[dict]:
    return [dict(bundle_summary(bundle)) for bundle in bundles]


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    _ensure_terms(args.max_terms)
    training_bundles = _load_training_bundles(args.train_seeds, args.samples)
    evaluation_bundles = _load_eval_bundles(args)

    candidate = search_law(training_bundles, max_terms=args.max_terms)
    print("Discovered law:")
    print("  "+law_expression(candidate))
    print(f"  model_bits={candidate.model_bits:.4f} residual_bits={candidate.residual_bits:.4f} total_bits={candidate.total_bits:.4f}")

    results_training = [evaluate_law(candidate, bundle) for bundle in training_bundles]
    print("\nTraining bundles:")
    for result in results_training:
        ar1 = ar1_baseline(result.bundle)
        blind = blind_baseline(args.blind_bits_per_sample, result.bundle)
        print(
            f"  {result.bundle.name}: residual_bits={result.residual_bits:.4f} baseline_bits={result.baseline_bits:.4f} "
            f"Δ={result.delta_vs_baseline:.4f} | ar1_total={ar1.total_bits:.4f} blind_total={blind.total_bits:.4f}"
        )

    if evaluation_bundles:
        results_eval = [evaluate_law(candidate, bundle) for bundle in evaluation_bundles]
        print("\nEvaluation bundles:")
        for result in results_eval:
            ar1 = ar1_baseline(result.bundle)
            blind = blind_baseline(args.blind_bits_per_sample, result.bundle)
            print(
                f"  {result.bundle.name}: residual_bits={result.residual_bits:.4f} baseline_bits={result.baseline_bits:.4f} "
                f"Δ={result.delta_vs_baseline:.4f} | ar1_total={ar1.total_bits:.4f} blind_total={blind.total_bits:.4f}"
            )
    else:
        results_eval = []

    summary = {
        "law": candidate.as_dict(),
        "training_bundles": _summarise_bundle_set(training_bundles),
        "evaluation_bundles": _summarise_bundle_set(evaluation_bundles),
        "training_summary": dict(summarise_evaluations(results_training)),
        "evaluation_summary": dict(summarise_evaluations(results_eval)),
        "blind_bits_per_sample": args.blind_bits_per_sample,
        "max_terms": args.max_terms,
        "samples": args.samples,
    }

    if args.json_out:
        args.json_out.write_text(json.dumps(summary, indent=2, sort_keys=True))
        print(f"\nSummary written to {args.json_out}")


if __name__ == "__main__":
    main()
