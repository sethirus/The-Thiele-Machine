#!/usr/bin/env python3
"""Scan CHSH vs μ-cost across a family of no-signaling boxes.

This is an *audit tool*, not a claim of a derived physical bound.
It answers two questions:

1) Under specific encodings, how does μ vary across a box family?
2) Does the current μ implementation itself encode IC/Tsirelson? (It should not.)

The scan family is a convex mixture grid between:
- best classical deterministic CHSH-saturating box
- the repo's supra-quantum S=16/5 box (CSV)
- a PR box (S=4)

Outputs a CSV suitable for plotting.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from pathlib import Path

from tools.bell_mu import (
    baseline_boxes,
    load_supra_table,
    mu_for_box,
    sample_mu_vs_chsh,
    write_mu_vs_chsh_csv,
)


DEFAULT_SUPRA_TABLE = Path("artifacts/bell/supra_quantum_16_5.csv")
DEFAULT_OUTPUT = Path("artifacts/bell/mu_vs_chsh.csv")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--supra-table", type=Path, default=DEFAULT_SUPRA_TABLE)
    parser.add_argument("--resolution", type=int, default=12)
    parser.add_argument(
        "--encoding",
        choices=["table_sexpr", "mixture_sexpr", "tag_sexpr"],
        default="mixture_sexpr",
        help="Which encoding to use as the μ-cost question string.",
    )
    parser.add_argument("--before", type=int, default=1)
    parser.add_argument("--after", type=int, default=1)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args()


def main() -> int:
    args = parse_args()

    supra_table = load_supra_table(args.supra_table)

    # Baseline μ-costs for three reference boxes
    boxes = baseline_boxes(supra_table)
    print("Reference boxes (CHSH, μ-cost):")
    for name, table in boxes.items():
        # For baselines, we show table-based μ and tag-based μ to demonstrate sensitivity.
        mu_table = mu_for_box(table, encoding="table_sexpr", before=args.before, after=args.after)
        mu_tag = mu_for_box(table, encoding="tag_sexpr", tag=name, before=args.before, after=args.after)
        from tools.compute_chsh_from_table import compute_chsh

        s_val = compute_chsh(table)
        print(f"  {name:14s}  S={float(s_val):.6f}  μ(table)={mu_table:.1f}  μ(tag)={mu_tag:.1f}")

    samples = sample_mu_vs_chsh(
        supra_table,
        resolution=args.resolution,
        encoding=args.encoding,
        before=args.before,
        after=args.after,
    )
    write_mu_vs_chsh_csv(args.output, samples)
    print(f"\nWrote {len(samples)} samples to {args.output}")

    # Quick derived curve: max CHSH achievable under μ threshold (for this encoding/family)
    sorted_samples = sorted(samples, key=lambda s: s.mu_total)
    thresholds = [
        sorted_samples[0].mu_total,
        sorted_samples[len(sorted_samples)//4].mu_total,
        sorted_samples[len(sorted_samples)//2].mu_total,
        sorted_samples[(3*len(sorted_samples))//4].mu_total,
        sorted_samples[-1].mu_total,
    ]
    print("\nMax CHSH under μ-thresholds (within this sampled family):")
    for th in thresholds:
        best = max((s.chsh for s in samples if s.mu_total <= th), default=Fraction(0, 1))
        print(f"  μ ≤ {th:.1f}  =>  max S ≈ {float(best):.6f}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
