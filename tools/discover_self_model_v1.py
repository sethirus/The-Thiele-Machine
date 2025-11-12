#!/usr/bin/env python3
"""CLI wrapper that discovers self-laws from Thiele runtime traces."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Iterable

import os
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from self_model_v1 import (
    BLIND_BITS_PER_STEP,
    DEFAULT_EPSILON_BITS,
    DEFAULT_TRACE_INDEX,
    discover_self_model,
)

DEFAULT_OUTPUT = Path("artifacts/self_model_v1_summary.json")


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--trace-index",
        type=Path,
        default=DEFAULT_TRACE_INDEX,
        help="self-trace index JSON (defaults to artifacts/self_traces/self_trace_index.json)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="summary JSON output path",
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


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    summary = discover_self_model(
        args.trace_index,
        blind_bits_per_step=args.blind_bits_per_step,
        epsilon_bits=args.epsilon_bits,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(f"Self-model summary written to {args.output}")
    print(f"  μ_question bits: {summary['mu_question_bits']:.6f}")
    print(f"  μ_answer bits:   {summary['mu_answer_bits']:.6f}")
    print(f"  μ_total bits:    {summary['mu_total_bits']:.6f}")
    print(f"  μ_gap vs blind:  {summary['mu_gap_bits']:.6f}")
    print(f"  expression:      {summary['expression']}")


if __name__ == "__main__":
    main()
