"""Verify the turbulence closure receipt by recomputing the discovery."""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
from pathlib import Path
from typing import Iterable, Mapping, Sequence

try:  # pragma: no cover - executed inside tools/
    from tools.make_law_receipt import verify_chain
    from tools.turbulence_closure_v1 import discover_closure, load_dataset, prepare_bundles_from_seeds
except ModuleNotFoundError:  # pragma: no cover - repository root execution
    from make_law_receipt import verify_chain  # type: ignore
    from turbulence_closure_v1 import discover_closure, load_dataset, prepare_bundles_from_seeds  # type: ignore


SIGNING_KEY = b"ThieleTurbulenceClosureKey"


def _parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipt", type=Path, nargs="?", default=Path("artifacts/turbulence_closure_v1_receipt.jsonl"))
    return parser.parse_args(argv)


def _load_entries(path: Path) -> Sequence[Mapping[str, object]]:
    if not path.exists():
        raise FileNotFoundError(f"receipt {path} not found")
    entries = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            entries.append(json.loads(line))
    if not entries:
        raise ValueError("receipt contained no entries")
    return entries


def _summary_entry(entries: Sequence[Mapping[str, object]]) -> Mapping[str, object]:
    for entry in reversed(entries):
        if entry.get("event") == "turbulence_closure_v1_summary":
            return entry
    raise ValueError("receipt missing summary entry")


def _recompute(parameters: Mapping[str, object]):
    samples = int(parameters.get("samples", 0))
    max_terms = int(parameters.get("max_terms", 0))
    min_gain_bits = float(parameters.get("min_gain_bits", 0.05))
    blind_bits = float(parameters.get("blind_bits_per_sample", 16.0))
    train_seeds = [int(value) for value in parameters.get("training_seeds", [])]
    eval_seeds = [int(value) for value in parameters.get("evaluation_seeds", [])]
    train_datasets = [Path(value) for value in parameters.get("training_datasets", [])]
    eval_datasets = [Path(value) for value in parameters.get("evaluation_datasets", [])]

    training = list(prepare_bundles_from_seeds(train_seeds, samples) if train_seeds else [])
    for path in train_datasets:
        training.append(load_dataset(path))
    evaluation = list(prepare_bundles_from_seeds(eval_seeds, samples) if eval_seeds else [])
    for path in eval_datasets:
        evaluation.append(load_dataset(path))

    candidate, baselines, train_metrics, eval_metrics = discover_closure(
        training,
        evaluation,
        max_terms=max_terms,
        min_gain_bits=min_gain_bits,
        blind_bits_per_sample=blind_bits,
    )
    return candidate, baselines, train_metrics, eval_metrics


def _compare_summary(summary: Mapping[str, object], candidate) -> None:
    law = summary.get("law", {})
    if not law:
        raise ValueError("summary entry missing law payload")
    if abs(float(law.get("model_bits", 0.0)) - candidate.model_bits) > 1e-6:
        raise ValueError("model bits mismatch")
    if abs(float(law.get("residual_bits", 0.0)) - candidate.residual_bits) > 1e-6:
        raise ValueError("residual bits mismatch")
    if law.get("features") != [feature.name for feature in candidate.features]:
        raise ValueError("feature set mismatch")


def _verify_signature(entry: Mapping[str, object]) -> None:
    expected = hmac.new(
        SIGNING_KEY,
        str(entry.get("crypto_hash", "")).encode("utf-8"),
        hashlib.sha256,
    ).hexdigest()
    if entry.get("signature") != expected:
        raise ValueError("summary signature mismatch")


def main(argv: Iterable[str] | None = None) -> None:
    args = _parse_args(argv)
    entries = _load_entries(args.receipt)
    if not verify_chain(entries):
        raise RuntimeError("hash-chain verification failed")

    summary = _summary_entry(entries)
    _verify_signature(summary)

    parameters = summary.get("generator", {}).get("parameters", {})
    candidate, _, _, _ = _recompute(parameters)
    _compare_summary(summary, candidate)

    print("turbulence_closure_v1_receipt: verification passed")


if __name__ == "__main__":  # pragma: no cover
    main()
