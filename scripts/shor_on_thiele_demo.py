#!/usr/bin/env python3
"""Three-act demonstration of Shor-style period reasoning on the Thiele Machine."""

from __future__ import annotations

import argparse
import json
import math
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from thielecpu.receipts import ensure_kernel_keys
from thielecpu.shor_oracle import PeriodOracleResult, find_period_with_claims


@dataclass
class ActRecord:
    """Structure capturing the outcome of a demo act."""

    label: str
    arithmetic_work: int
    mu_cost: float
    factor: int
    cofactor: int
    details: Dict[str, object]

    def to_summary(self) -> Dict[str, object]:
        payload: Dict[str, object] = {
            "label": self.label,
            "factor": self.factor,
            "cofactor": self.cofactor,
            "arithmetic_work": self.arithmetic_work,
            "mu_cost": self.mu_cost,
        }
        payload.update(self.details)
        return payload


def _act_i_trial_division(n: int) -> Tuple[ActRecord, List[Dict[str, int]]]:
    """Perform blind trial division to recover a factor of ``n``."""

    trace: List[Dict[str, int]] = []
    factor = 1
    for divisor in range(2, math.isqrt(n) + 1):
        remainder = n % divisor
        trace.append({"divisor": divisor, "remainder": remainder})
        if remainder == 0:
            factor = divisor
            break
    else:
        factor = n

    cofactor = n // factor
    record = ActRecord(
        label="Act I – Blind Trial Division",
        arithmetic_work=len(trace),
        mu_cost=0.0,
        factor=factor,
        cofactor=cofactor,
        details={
            "divisors_tested": len(trace),
            "trace_file": "division_trace.json",
        },
    )
    return record, trace


def _derivations_from_oracle(result: PeriodOracleResult) -> Dict[str, object]:
    """Extract arithmetic consequences from an oracle result."""

    half_period = result.period // 2
    return {
        "period": result.period,
        "half_period": half_period,
        "solver_queries": result.solver_queries,
        "claims_file": "reasoning_summary.json",
    }


def _act_ii_thiele(n: int, a: int, max_period: int | None) -> Tuple[ActRecord, PeriodOracleResult, Dict[str, int]]:
    """Use the Thiele oracle to derive a factor of ``n`` via period reasoning."""

    oracle_result = find_period_with_claims(n, a, max_period=max_period)
    if oracle_result.period % 2 != 0:
        raise RuntimeError("oracle returned an odd period; cannot complete reduction")

    exponent = oracle_result.period // 2
    first_term = pow(a, exponent, n)
    factor1 = math.gcd(first_term - 1, n)
    factor2 = math.gcd(first_term + 1, n)

    candidates = sorted(c for c in (factor1, factor2) if 1 < c < n)
    factor = candidates[0] if candidates else 1
    if factor == 1:
        raise RuntimeError("period discovery did not expose a non-trivial factor")

    cofactor = n // factor
    arithmetic_accounting = {
        "pow_calls": 1,
        "gcd_calls": 2,
    }
    record = ActRecord(
        label="Act II – Sighted Thiele Period Reasoning",
        arithmetic_work=0,
        mu_cost=oracle_result.mu_cost,
        factor=factor,
        cofactor=cofactor,
        details=_derivations_from_oracle(oracle_result) | {"arithmetic_ops": arithmetic_accounting},
    )
    return record, oracle_result, arithmetic_accounting


def _act_iii_verdict(act_i: ActRecord, act_ii: ActRecord) -> Dict[str, object]:
    """Summarise the comparison between the acts."""

    return {
        "label": "Act III – Comparative Verdict",
        "classical_arithmetic_work": act_i.arithmetic_work,
        "thiele_arithmetic_work": act_ii.arithmetic_work,
        "classical_mu_cost": act_i.mu_cost,
        "thiele_mu_cost": act_ii.mu_cost,
        "verdict": "Thiele run replaced divisor checks with paid reasoning to obtain the same factor.",
    }


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def run_demo(n: int, base: int, output_dir: Path, *, max_period: int | None = None) -> Dict[str, object]:
    """Execute the three-act demonstration and return the consolidated report."""

    ensure_kernel_keys()
    output_dir.mkdir(parents=True, exist_ok=True)

    act_i_dir = output_dir / "act_i"
    act_i_dir.mkdir(parents=True, exist_ok=True)
    act_i_record, act_i_trace = _act_i_trial_division(n)
    _write_json(act_i_dir / "summary.json", act_i_record.to_summary())
    _write_json(act_i_dir / "division_trace.json", {"trace": act_i_trace})

    act_ii_dir = output_dir / "act_ii"
    act_ii_dir.mkdir(parents=True, exist_ok=True)
    act_ii_record, oracle_result, arithmetic_ops = _act_ii_thiele(n, base, max_period)
    _write_json(act_ii_dir / "summary.json", act_ii_record.to_summary())
    _write_json(act_ii_dir / "reasoning_summary.json", oracle_result.reasoning_summary)

    act_iii_dir = output_dir / "act_iii"
    act_iii_dir.mkdir(parents=True, exist_ok=True)
    verdict = _act_iii_verdict(act_i_record, act_ii_record)
    _write_json(act_iii_dir / "summary.json", verdict)

    analysis = {
        "number": n,
        "base": base,
        "acts": [act_i_record.to_summary(), act_ii_record.to_summary(), verdict],
        "reasoning_mu_cost": act_ii_record.mu_cost,
        "classical_work": act_i_record.arithmetic_work,
        "thiele_work": act_ii_record.arithmetic_work,
        "arithmetic_accounting": arithmetic_ops,
    }
    _write_json(output_dir / "analysis_report.json", analysis)
    return analysis


def _parse_args(argv: List[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--number", type=int, default=21, help="Composite integer to factor (default: 21)")
    parser.add_argument("--base", type=int, default=2, help="Base a where gcd(a, N) = 1 (default: 2)")
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("results/shor"),
        help="Directory to store receipts and analysis.",
    )
    parser.add_argument(
        "--max-period",
        type=int,
        default=None,
        help="Optional cap on the explored period; defaults to 2N if omitted.",
    )
    return parser.parse_args(argv)


def main(argv: List[str]) -> int:
    args = _parse_args(argv)
    analysis = run_demo(args.number, args.base, args.output_dir, max_period=args.max_period)
    print("=== Shor-on-Thiele Demonstration ===")
    print(json.dumps(analysis, indent=2))
    return 0


if __name__ == "__main__":  # pragma: no cover - exercised via CLI
    raise SystemExit(main(sys.argv[1:]))
