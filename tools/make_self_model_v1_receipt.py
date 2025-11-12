#!/usr/bin/env python3
"""Generate a hash-chained receipt for the NUSD self-model witness."""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
from pathlib import Path
from typing import Iterable, List, Mapping, MutableMapping

import os
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from make_self_traces import DEFAULT_INDEX as DEFAULT_TRACE_INDEX
from make_self_traces import generate_traces
from make_law_receipt import append_entry, verify_chain
from self_model_v1 import (
    BLIND_BITS_PER_STEP,
    DEFAULT_EPSILON_BITS,
    discover_self_model,
)

DEFAULT_RECEIPT = Path("artifacts/self_model_v1_receipt.jsonl")
DEFAULT_SUMMARY = Path("artifacts/self_model_v1_summary.json")
SIGNING_KEY = b"ThieleSelfModelKey"


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--trace-index",
        type=Path,
        default=DEFAULT_TRACE_INDEX,
        help="self-trace index JSON",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_RECEIPT,
        help="receipt output path",
    )
    parser.add_argument(
        "--summary",
        type=Path,
        default=DEFAULT_SUMMARY,
        help="optional path to persist the discovery summary JSON",
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
    parser.add_argument(
        "--refresh-traces",
        action="store_true",
        help="regenerate traces even if the index already exists",
    )
    return parser.parse_args(argv)


def _load_index(index_path: Path) -> Mapping[str, object]:
    if not index_path.exists():
        raise FileNotFoundError(f"trace index {index_path} is missing")
    return json.loads(index_path.read_text(encoding="utf-8"))


def _compute_script_sha(script_path: Path) -> str:
    return hashlib.sha256(script_path.read_bytes()).hexdigest()


def _hmac_signature(digest: str) -> str:
    return hmac.new(SIGNING_KEY, digest.encode("utf-8"), hashlib.sha256).hexdigest()


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    if args.refresh_traces or not args.trace_index.exists():
        generate_traces(args.trace_index)
    index_payload = _load_index(args.trace_index)
    summary = discover_self_model(
        args.trace_index,
        blind_bits_per_step=args.blind_bits_per_step,
        epsilon_bits=args.epsilon_bits,
    )
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.summary.write_text(json.dumps(summary, indent=2), encoding="utf-8")

    entries: List[MutableMapping[str, object]] = []
    previous_hash = "0" * 64
    workload_metrics = summary.get("workloads", {})
    for trace_entry in index_payload.get("traces", []):
        entry = {
            "event": "self_model_workload",
            "workload": trace_entry.get("workload"),
            "seed": trace_entry.get("seed"),
            "trace_path": trace_entry.get("path"),
            "trace_sha256": trace_entry.get("sha256"),
            "steps": trace_entry.get("steps"),
        }
        metrics = workload_metrics.get(entry["workload"], {})
        entry.update(
            {
                "mu_question_bits": metrics.get("mu_question_bits"),
                "mu_answer_bits": metrics.get("mu_answer_bits"),
                "mu_total_bits": metrics.get("mu_total_bits"),
                "mu_gap_bits": metrics.get("mu_gap_bits"),
                "blind_total_bits": metrics.get("blind_total_bits"),
                "rmse": metrics.get("rmse"),
            }
        )
        previous_hash = append_entry(entries, entry, previous_hash)

    summary_entry: MutableMapping[str, object] = {
        "event": "self_model_summary",
        "mu_question_bits": summary["mu_question_bits"],
        "mu_answer_bits": summary["mu_answer_bits"],
        "mu_total_bits": summary["mu_total_bits"],
        "mu_gap_bits": summary["mu_gap_bits"],
        "blind_bits_per_step": summary["blind_bits_per_step"],
        "blind_total_bits": summary["blind_total_bits"],
        "epsilon_bits": summary["epsilon_bits"],
        "expression": summary["expression"],
        "trace_index": summary["trace_index"],
        "workloads": summary["workloads"],
        "generator": {
            "script": "tools/make_self_model_v1_receipt.py",
            "sha256": _compute_script_sha(Path(__file__)),
        },
        "signature_algorithm": "HMAC-SHA256",
    }
    previous_hash = append_entry(entries, summary_entry, previous_hash)
    summary_entry["signature"] = _hmac_signature(summary_entry["crypto_hash"])

    if not verify_chain(entries):
        raise RuntimeError("receipt chain verification failed")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as handle:
        for entry in entries:
            handle.write(json.dumps(entry, sort_keys=True) + "\n")

    print(f"Receipt written to {args.output}")
    print(f"  entries: {len(entries)}")
    print(f"  μ_gap vs blind: {summary['mu_gap_bits']:.6f} bits")


if __name__ == "__main__":
    main()
