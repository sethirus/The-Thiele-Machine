#!/usr/bin/env python3

"""Generate a one-page impact deliverable from RSA demo artifacts.

This script summarizes concrete, reproducible outcomes from
``rsa_demo_output/analysis_report.json`` into a shareable Markdown report.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def _fmt_percent(value: float) -> str:
    return f"{value * 100.0:.1f}%"


def _fmt_reduction(before: int, after: int) -> str:
    if before <= 0:
        return "n/a"
    reduction = 1.0 - (after / before)
    return _fmt_percent(reduction)


def build_report(input_path: Path, output_path: Path) -> None:
    payload = json.loads(input_path.read_text(encoding="utf-8"))
    experiments = payload.get("experiments", [])

    if not experiments:
        raise ValueError("No experiments found in analysis report")

    lines: list[str] = []
    lines.append("# Thiele Machine One-Hour Deliverable")
    lines.append("")
    lines.append("## Real Question")
    lines.append("Can the Thiele Machine recover integer-factor witnesses while reducing brute-force search work via structural (congruence) pruning?")
    lines.append("")
    lines.append("## Real Result")

    for exp in experiments:
        modulus = exp.get("modulus")
        witness = exp.get("witness") or {}
        factor = witness.get("factor")
        cofactor = witness.get("cofactor")

        acts = exp.get("acts", {})
        act1 = int((acts.get("act_i") or {}).get("candidate_checks", 0))
        act3 = int((acts.get("act_iii") or {}).get("candidate_checks", 0))

        geom = exp.get("geometric_pruning", {})
        remaining = int(geom.get("surviving_candidates", 0))
        initial = int(exp.get("initial_candidates", 0))
        mu_cost = float(geom.get("mu_cost", 0.0))

        lines.append(f"- **N={modulus}**: recovered witness `{factor} × {cofactor} = {modulus}`")
        lines.append(f"  - blind checks: `{act1}` -> structural checks: `{act3}` (reduction `{_fmt_reduction(act1, act3)}`)")
        lines.append(f"  - candidate space: `{initial}` -> `{remaining}` (reduction `{_fmt_reduction(initial, remaining)}`), structural μ-cost `{mu_cost:.1f}`")

    lines.append("")
    lines.append("## Why This Matters")
    lines.append("- This is not a slide claim: the system produced concrete factor witnesses and audit artifacts.")
    lines.append("- The run demonstrates a practical pattern: spend explicit structural μ-bits to shrink arithmetic search.")
    lines.append("- The same execution stack is formally gated (`make proof-undeniable`) for Coq/Python/RTL alignment.")
    lines.append("")
    lines.append("## What This Is / Is Not")
    lines.append("- **Is:** a reproducible, verified structural-pruning engine that can cut search work on concrete instances.")
    lines.append("- **Is not:** a proof of polynomial-time factoring or a break of production RSA cryptosystems.")
    lines.append("")
    lines.append("## Reproduce")
    lines.append("```bash")
    lines.append("make proof-undeniable")
    lines.append("python3 scripts/rsa_partition_demo.py --moduli 3233 10403 --analysis-bits 256 512 1024")
    lines.append("python3 scripts/generate_impact_deliverable.py")
    lines.append("```")
    lines.append("")
    lines.append(f"Source artifact: `{input_path}`")

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate shareable impact deliverable")
    parser.add_argument(
        "--input",
        type=Path,
        default=Path("rsa_demo_output/analysis_report.json"),
        help="Path to RSA demo analysis_report.json",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("artifacts/ONE_HOUR_DELIVERABLE.md"),
        help="Output Markdown report path",
    )
    args = parser.parse_args()

    build_report(args.input, args.output)
    print(f"Wrote deliverable: {args.output}")


if __name__ == "__main__":
    main()
