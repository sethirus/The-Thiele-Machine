#!/usr/bin/env python3
"""Verify the NUSD self-model receipt end to end."""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
from pathlib import Path
from typing import Iterable, Mapping, Sequence

import os
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from make_law_receipt import verify_chain
from self_model_v1 import (
    BLIND_BITS_PER_STEP,
    DEFAULT_EPSILON_BITS,
    DEFAULT_TRACE_INDEX,
    discover_self_model,
)

SIGNING_KEY = b"ThieleSelfModelKey"


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipt", type=Path, help="receipt JSONL to verify")
    parser.add_argument(
        "--trace-index",
        type=Path,
        default=DEFAULT_TRACE_INDEX,
        help="optional override for the self-trace index JSON",
    )
    parser.add_argument(
        "--blind-bits-per-step",
        type=float,
        default=BLIND_BITS_PER_STEP,
        help="blind baseline cost per step (bits)",
    )
    parser.add_argument(
        "--epsilon-bits",
        type=float,
        default=DEFAULT_EPSILON_BITS,
        help="slack ε bits for μ accounting",
    )
    return parser.parse_args(argv)


def _load_entries(path: Path) -> Sequence[Mapping[str, object]]:
    entries = []
    with path.open(encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            entries.append(json.loads(line))
    if not entries:
        raise ValueError("receipt file is empty")
    return entries


def _compare_float(recorded: float, recomputed: float, *, name: str, tol: float = 1e-6) -> None:
    if abs(recorded - recomputed) > tol:
        raise ValueError(f"mismatch for {name}: recorded={recorded:.8f} recomputed={recomputed:.8f}")


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    entries = _load_entries(args.receipt)
    if not verify_chain(entries):
        raise RuntimeError("receipt hash chain verification failed")

    summary_entry = entries[-1]
    recorded_signature = summary_entry.get("signature")
    expected_signature = hmac.new(
        SIGNING_KEY, summary_entry.get("crypto_hash", "").encode("utf-8"), hashlib.sha256
    ).hexdigest()
    if recorded_signature != expected_signature:
        raise RuntimeError("summary HMAC signature mismatch")

    trace_index_path = args.trace_index
    if not trace_index_path.exists():
        trace_info = summary_entry.get("trace_index") or {}
        candidate = Path(trace_info.get("path", ""))
        if candidate.exists():
            trace_index_path = candidate
        else:
            raise FileNotFoundError("trace index unavailable; provide --trace-index")

    recomputed = discover_self_model(
        trace_index_path,
        blind_bits_per_step=args.blind_bits_per_step,
        epsilon_bits=args.epsilon_bits,
    )

    _compare_float(float(summary_entry["mu_question_bits"]), float(recomputed["mu_question_bits"]), name="μ_question")
    _compare_float(float(summary_entry["mu_answer_bits"]), float(recomputed["mu_answer_bits"]), name="μ_answer")
    _compare_float(float(summary_entry["mu_total_bits"]), float(recomputed["mu_total_bits"]), name="μ_total")
    _compare_float(float(summary_entry["mu_gap_bits"]), float(recomputed["mu_gap_bits"]), name="μ_gap")

    recorded_workloads = summary_entry.get("workloads", {})
    recomputed_workloads = recomputed.get("workloads", {})
    for workload, metrics in recomputed_workloads.items():
        recorded = recorded_workloads.get(workload)
        if recorded is None:
            raise ValueError(f"missing workload {workload} in receipt summary")
        _compare_float(float(recorded["mu_question_bits"]), float(metrics["mu_question_bits"]), name=f"{workload} μ_question")
        _compare_float(float(recorded["mu_answer_bits"]), float(metrics["mu_answer_bits"]), name=f"{workload} μ_answer")
        _compare_float(float(recorded["mu_total_bits"]), float(metrics["mu_total_bits"]), name=f"{workload} μ_total")
        _compare_float(float(recorded["mu_gap_bits"]), float(metrics["mu_gap_bits"]), name=f"{workload} μ_gap")

    print(f"Receipt {args.receipt} verified successfully")
    print(f"  trace index: {trace_index_path}")
    print(f"  workloads: {len(recomputed_workloads)}")
    print(f"  μ_gap vs blind: {recomputed['mu_gap_bits']:.6f} bits")


if __name__ == "__main__":
    main()
