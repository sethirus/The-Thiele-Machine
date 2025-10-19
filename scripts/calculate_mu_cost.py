#!/usr/bin/env python3
"""Reference calculator for μ-spec v2.0.

The tool accepts a claim/question written as an S-expression together with the
size of the possibility space before and after answering the question.  The
output reports the description-length cost, the information gain, and the total
μ-cost.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from typing import Dict

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from thielecpu.mu import (
    calculate_mu_cost,
    canonical_s_expression,
    information_gain_bits,
    question_cost_bits,
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="μ-spec v2.0 calculator")
    parser.add_argument("claim", help="Question or claim expressed as an S-expression")
    parser.add_argument("before", type=int, help="Number of possibilities before the step")
    parser.add_argument("after", type=int, help="Number of possibilities after the step")
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit the breakdown as JSON instead of a human-readable string",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    breakdown: Dict[str, float] = {
        "canonical": canonical_s_expression(args.claim),
        "question_bits": float(question_cost_bits(args.claim)),
        "information_gain": information_gain_bits(args.before, args.after),
    }
    breakdown["mu_cost"] = breakdown["question_bits"] + breakdown["information_gain"]

    if args.json:
        print(json.dumps(breakdown, indent=2))
    else:
        print(
            "claim: {claim}\ncanonical: {canonical}\nμ_question: {question_bits:.6f} bits\n"
            "μ_answer: {information_gain:.6f} bits\nμ_total: {mu_cost:.6f} bits".format(
                claim=args.claim,
                canonical=breakdown["canonical"],
                question_bits=breakdown["question_bits"],
                information_gain=breakdown["information_gain"],
                mu_cost=breakdown["mu_cost"],
            )
        )


if __name__ == "__main__":  # pragma: no cover - CLI entry point
    main()
