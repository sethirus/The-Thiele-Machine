#!/usr/bin/env python3
"""Run the partition-scaling experiment in a disposable workspace.

This script exists to enforce the preregistered blind-versus-sighted
decision criteria without leaving any experiment artefacts in the
repository.  It spins up a temporary directory, runs the official
experiment harness with outputs pointed at that directory, and then
verifies that the resulting ``inference.md`` records PASS for every
criterion.  The temporary directory is removed automatically when the
process exits.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


EXPECTED_PASSES = [
    "- Blind fits exp better than poly by ΔAIC ≥ 10: PASS",
    "- Sighted μ_answer/|vars| slope 95% CI contains 0: PASS",
    "- Ratio slope > 0 and monotonic in ≥90% of bootstrap: PASS",
    "- Spearman ρ(μ_blind, runtime) ≥ 0.6 (p < 0.01): PASS",
]


def run_ephemeral_experiment(args: argparse.Namespace) -> None:
    """Execute the partition harness in a temporary workspace."""

    experiment_cmd = [
        sys.executable,
        "-m",
        "scripts.experiments.run_partition_experiments",
        "--problem",
        "tseitin",
        "--partitions",
        *[str(p) for p in args.partitions],
        "--repeat",
        str(args.repeat),
        "--save-outputs",
        "--experiment-name",
        args.experiment_name,
        "--plot-format",
        args.plot_format,
    ]

    if args.seed_grid:
        experiment_cmd.extend(["--seed-grid", *[str(seed) for seed in args.seed_grid]])
    if args.emit_receipts:
        experiment_cmd.append("--emit-receipts")

    with tempfile.TemporaryDirectory(prefix="thiele_partition_") as tmp:
        exp_dir = Path(tmp) / "experiment"
        exp_dir.mkdir(parents=True, exist_ok=True)
        cmd = experiment_cmd + ["--exp-dir", str(exp_dir)]
        print("Running partition experiment:")
        print(" ".join(cmd))
        subprocess.check_call(cmd, cwd=REPO_ROOT)

        inference_path = exp_dir / "inference.md"
        if not inference_path.exists():
            raise SystemExit(
                "inference.md was not produced by the experiment harness; "
                "ensure --save-outputs is provided."
            )

        inference_text = inference_path.read_text(encoding="utf-8")
        missing = [line for line in EXPECTED_PASSES if line not in inference_text]
        if missing:
            print("Ephemeral experiment FAILED. Missing PASS markers for:", file=sys.stderr)
            for line in missing:
                print(f"  {line}", file=sys.stderr)
            print("\n--- inference.md ---\n", inference_text, file=sys.stderr)
            raise SystemExit(1)

        print("Ephemeral experiment PASSED: all preregistered criteria satisfied.")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--partitions",
        nargs="+",
        type=int,
        default=[6, 8, 10, 12, 14],
        help="Partition sizes to test (default: 6 8 10 12 14)",
    )
    parser.add_argument(
        "--repeat",
        type=int,
        default=5,
        help="Number of instances per partition size (default: 5)",
    )
    parser.add_argument(
        "--seed-grid",
        nargs="+",
        type=int,
        help="Optional explicit seed list; overrides --repeat",
    )
    parser.add_argument(
        "--experiment-name",
        default="ephemeral",
        help="Name label recorded inside the experiment outputs",
    )
    parser.add_argument(
        "--plot-format",
        choices=["png", "svg"],
        default="svg",
        help="Plot format requested from the harness (default: svg)",
    )
    parser.add_argument(
        "--emit-receipts",
        action="store_true",
        help="Forward --emit-receipts to the underlying harness",
    )
    return parser


def main() -> None:
    parser = build_parser()
    args = parser.parse_args()
    run_ephemeral_experiment(args)


if __name__ == "__main__":
    main()
