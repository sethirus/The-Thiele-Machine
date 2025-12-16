#!/usr/bin/env python3
"""Adversarial search for CHSH violations in the *local* fragment.

Milestone 1B: Every theorem gets an adversarial test.

We exhaustively enumerate deterministic local hidden-variable strategies:
- Alice outputs a(x) where x∈{0,1}
- Bob outputs b(y) where y∈{0,1}

There are 4 choices for a(·) and 4 for b(·) => 16 strategies.
For each strategy we run a real VM program that emits exactly one CHSH_TRIAL per
setting (balanced N=1), then compute CHSH from receipts via the canonical
extractor in tools/chsh_receipts.py.

Expectation: for all local strategies, |CHSH| ≤ 2 under the repo convention.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, List, Tuple

from thielecpu.state import State
from thielecpu.vm import VM

from tools.chsh_receipts import chsh_from_receipts_path


@dataclass(frozen=True)
class LocalStrategy:
    a0: int
    a1: int
    b0: int
    b1: int

    def a(self, x: int) -> int:
        return self.a0 if x == 0 else self.a1

    def b(self, y: int) -> int:
        return self.b0 if y == 0 else self.b1

    def label(self) -> str:
        return f"a({self.a0},{self.a1})_b({self.b0},{self.b1})"


def enumerate_local_strategies() -> List[LocalStrategy]:
    return [
        LocalStrategy(a0=a0, a1=a1, b0=b0, b1=b1)
        for a0 in (0, 1)
        for a1 in (0, 1)
        for b0 in (0, 1)
        for b1 in (0, 1)
    ]


def program_for_strategy(strategy: LocalStrategy) -> List[Tuple[str, str]]:
    program: List[Tuple[str, str]] = [("PNEW", "{1,2}")]
    for x in (0, 1):
        for y in (0, 1):
            a = strategy.a(x)
            b = strategy.b(y)
            program.append(("CHSH_TRIAL", f"{x} {y} {a} {b}"))
    program.append(("EMIT", "done"))
    return program


def run_strategy_vm(*, strategy: LocalStrategy, outdir: Path) -> Fraction:
    outdir.mkdir(parents=True, exist_ok=True)

    vm = VM(State())
    vm.run(program_for_strategy(strategy), outdir)

    receipts_path = outdir / "step_receipts.json"
    return chsh_from_receipts_path(receipts_path)


def find_best_local_strategy(*, base_outdir: Path) -> Tuple[LocalStrategy, Fraction]:
    best_s = Fraction(-10, 1)
    best_strategy = enumerate_local_strategies()[0]

    for strat in enumerate_local_strategies():
        s = run_strategy_vm(strategy=strat, outdir=base_outdir / strat.label())
        if s > best_s:
            best_s = s
            best_strategy = strat

    return best_strategy, best_s


def main() -> None:
    import argparse
    import json

    parser = argparse.ArgumentParser(description="Exhaustively search deterministic local strategies for CHSH.")
    parser.add_argument(
        "--outdir",
        type=Path,
        default=Path("artifacts") / "chsh_local_adversary",
        help="Directory to write VM receipts per strategy",
    )
    args = parser.parse_args()

    best_strategy, best_s = find_best_local_strategy(base_outdir=args.outdir)
    report = {
        "best_strategy": best_strategy.label(),
        "best_chsh": str(best_s),
        "expected_bound": "<= 2",
    }
    print(json.dumps(report, indent=2, sort_keys=True))


__all__ = [
    "LocalStrategy",
    "enumerate_local_strategies",
    "program_for_strategy",
    "run_strategy_vm",
    "find_best_local_strategy",
    "main",
]


if __name__ == "__main__":
    main()
