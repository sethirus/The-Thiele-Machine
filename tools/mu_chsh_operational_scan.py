#!/usr/bin/env python3
"""Operational μ-vs-CHSH scan.

This tool measures μ from the *executed* Python VM state, not from any
serialization of a probability table.

It runs a fixed VM program shape:
    PNEW -> optional REVEAL (oracle/info charge) -> CHSH_TRIAL... -> EMIT
and computes CHSH from *receipts* (non-forgeable).

OUTPUT: artifacts/bell/mu_vs_chsh_operational.csv with columns:
  - mu_ledger_total: Canonical VM costs (discovery + execution)
  - mu_information: Information revelation charge
  - mu_total: mu_ledger_total + mu_information

POLICY DISCLOSURE (Dec 16, 2025):
    This scan is receipt-driven (CHSH_TRIAL opcodes), so it is constrained by VM
    semantics: supra-quantum CHSH from receipts sets CSR.ERR unless preceded by REVEAL.

    Current policy:
    - LHV (S≤2): No information charge (mu_information=0)
    - Tsirelson (S≈2.828): No information charge (mu_information=0)
    - Supra-quantum (S>2√2): Charged 64 bits by default via REVEAL opcode

    Falsifiable claim: Any receipt-authenticated program producing S>2.828 without
    an explicit revelation primitive should trigger CSR.ERR.
    See tests/test_supra_revelation_semantics.py for executable verification.
"""

from __future__ import annotations

import argparse
import csv
import datetime as _dt
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from thielecpu.state import State
from thielecpu.vm import VM
from thielecpu.isa import CSR

from tools.bell_receipts import load_probability_table_csv
from tools.chsh_receipts import chsh_from_receipts_path


DEFAULT_NONLOCAL_ORACLE_CHARGE_BITS = 64
NONLOCAL_STRATEGIES = {"supra_16_5", "pr"}

CountKey = Tuple[int, int, int, int]


@dataclass(frozen=True)
class OperationalSample:
    strategy: str
    chsh: Fraction
    mu_ledger_total: int
    mu_discovery: int
    mu_execution: int
    mu_information: float
    mu_total: float  # mu_ledger_total + mu_information
    mu_legacy_total: float
    n_per_setting: int
    seed: int
    oracle_charge_bits: int
    err: int
    steps: int


def _allocate_counts(weights: Dict[Tuple[int, int], Fraction], n: int) -> Dict[Tuple[int, int], int]:
    """Deterministically allocate integer counts summing to n from Fraction weights."""

    floors: Dict[Tuple[int, int], int] = {}
    remainders: List[Tuple[Fraction, Tuple[int, int]]] = []
    allocated = 0
    for outcome, w in weights.items():
        target = w * n
        base = int(target)  # floor
        floors[outcome] = base
        allocated += base
        remainders.append((target - base, outcome))
    left = n - allocated
    remainders.sort(key=lambda t: (t[0], t[1]), reverse=True)
    for i in range(left):
        floors[remainders[i][1]] += 1
    return floors


def _append_trials(program: List[Tuple[str, str]], *, x: int, y: int, counts: Dict[Tuple[int, int], int]) -> None:
    for (a, b), c in counts.items():
        for _ in range(int(c)):
            program.append(("CHSH_TRIAL", f"{x} {y} {a} {b}"))


def _program_for_strategy_receipts(*, strategy: str, n_per_setting: int) -> List[Tuple[str, str]]:
    program: List[Tuple[str, str]] = [("PNEW", "{1,2}")]

    if strategy == "lhv":
        for x in (0, 1):
            for y in (0, 1):
                counts = {(0, 0): n_per_setting, (0, 1): 0, (1, 0): 0, (1, 1): 0}
                _append_trials(program, x=x, y=y, counts=counts)
        return program

    if strategy == "pr":
        for x in (0, 1):
            for y in (0, 1):
                if x == 0 and y == 0:
                    weights = {(0, 1): Fraction(1, 2), (1, 0): Fraction(1, 2), (0, 0): Fraction(0, 1), (1, 1): Fraction(0, 1)}
                else:
                    weights = {(0, 0): Fraction(1, 2), (1, 1): Fraction(1, 2), (0, 1): Fraction(0, 1), (1, 0): Fraction(0, 1)}
                counts = _allocate_counts(weights, n_per_setting)
                _append_trials(program, x=x, y=y, counts=counts)
        return program

    if strategy == "tsirelson":
        # Deterministic approximate Tsirelson table aligned to the repo convention:
        #   S = E(1,1)+E(1,0)+E(0,1)-E(0,0)
        # Choose E(0,0)=-e and others +e with e≈0.7.
        e = Fraction(7, 10)
        for x in (0, 1):
            for y in (0, 1):
                expectation = -e if (x == 0 and y == 0) else e
                n_same = int(Fraction(1, 2) * (Fraction(1, 1) + expectation) * n_per_setting)
                n_same = max(0, min(n_per_setting, n_same))
                n_diff = n_per_setting - n_same
                same0 = n_same // 2
                same1 = n_same - same0
                diff0 = n_diff // 2
                diff1 = n_diff - diff0
                weights = {
                    (0, 0): Fraction(same0, n_per_setting),
                    (1, 1): Fraction(same1, n_per_setting),
                    (0, 1): Fraction(diff0, n_per_setting),
                    (1, 0): Fraction(diff1, n_per_setting),
                }
                counts = _allocate_counts(weights, n_per_setting)
                _append_trials(program, x=x, y=y, counts=counts)
        return program

    if strategy == "supra_16_5":
        prob_csv = Path(__file__).parents[1] / "artifacts" / "bell" / "supra_quantum_16_5.csv"
        table = load_probability_table_csv(prob_csv)
        for x in (0, 1):
            for y in (0, 1):
                weights: Dict[Tuple[int, int], Fraction] = {}
                for a in (0, 1):
                    for b in (0, 1):
                        weights[(a, b)] = Fraction(table.get((x, y, a, b), Fraction(0, 1)))
                counts = _allocate_counts(weights, n_per_setting)
                _append_trials(program, x=x, y=y, counts=counts)
        return program

    raise ValueError(f"unknown strategy: {strategy}")


def _parse_strategies(value: str) -> List[str]:
    raw = [part.strip() for part in value.split(",") if part.strip()]
    if not raw:
        return ["lhv", "tsirelson", "supra_16_5", "pr"]
    return raw


def run_one(
    *,
    strategy: str,
    n_per_setting: int,
    seed: int,
    oracle_charge_bits: Optional[int],
    outdir: Path,
) -> OperationalSample:
    outdir.mkdir(parents=True, exist_ok=True)
    program: List[Tuple[str, str]] = _program_for_strategy_receipts(strategy=strategy, n_per_setting=n_per_setting)

    # Oracle/revelation charge policy (operational, encoding-invariant):
    # - If oracle_charge_bits is None, use defaults: charge supra_16_5 + pr.
    # - If oracle_charge_bits is provided (including 0), apply it to nonlocal strategies.
    effective_charge_bits = 0
    if strategy in NONLOCAL_STRATEGIES:
        if oracle_charge_bits is None:
            effective_charge_bits = DEFAULT_NONLOCAL_ORACLE_CHARGE_BITS
        else:
            effective_charge_bits = int(oracle_charge_bits)

    # Use REVEAL to both charge μ_info and satisfy semantic enforcement for receipt-based CHSH.
    if effective_charge_bits > 0:
        program.insert(1, ("REVEAL", f"1 {effective_charge_bits} {strategy}"))

    program = list(program) + [("EMIT", "done")]

    vm = VM(State())
    vm.run(list(program), outdir)

    receipts_path = outdir / "step_receipts.json"
    s_value = chsh_from_receipts_path(receipts_path)

    state = vm.state
    return OperationalSample(
        strategy=strategy,
        chsh=s_value,
        mu_ledger_total=int(state.mu_ledger.total),
        mu_discovery=int(state.mu_ledger.mu_discovery),
        mu_execution=int(state.mu_ledger.mu_execution),
        mu_information=float(state.mu_information),
        mu_total=float(state.mu_ledger.total) + float(state.mu_information),
        mu_legacy_total=float(state.mu),
        n_per_setting=int(n_per_setting),
        seed=int(seed),
        oracle_charge_bits=int(effective_charge_bits),
        err=int(state.csr.get(CSR.ERR, 0)),
        steps=int(len(getattr(vm, "step_receipts", [])) or state.step_count),
    )


def write_csv(samples: Iterable[OperationalSample], output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)

    fieldnames = [
        "strategy",
        "chsh",
        "mu_ledger_total",
        "mu_discovery",
        "mu_execution",
        "mu_information",
        "mu_total",
        "mu_legacy_total",
        "n_per_setting",
        "seed",
        "oracle_charge_bits",
        "err",
        "steps",
    ]
    with output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for s in samples:
            row = {
                "strategy": s.strategy,
                "chsh": str(s.chsh),
                "mu_ledger_total": s.mu_ledger_total,
                "mu_discovery": s.mu_discovery,
                "mu_execution": s.mu_execution,
                "mu_information": f"{s.mu_information:.6f}",
                "mu_total": f"{s.mu_total:.6f}",
                "mu_legacy_total": f"{s.mu_legacy_total:.6f}",
                "n_per_setting": s.n_per_setting,
                "seed": s.seed,
                "oracle_charge_bits": s.oracle_charge_bits,
                "err": s.err,
                "steps": s.steps,
            }
            writer.writerow(row)


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--n-per-setting",
        type=int,
        default=2000,
        help="trials per (x,y) setting; total trials = 4*n-per-setting",
    )
    parser.add_argument("--seed", type=int, default=1337, help="RNG seed")
    parser.add_argument(
        "--strategies",
        type=str,
        default="lhv,tsirelson,supra_16_5,pr",
        help="comma-separated list: lhv, tsirelson, supra_16_5, pr",
    )
    parser.add_argument(
        "--oracle-charge-bits",
        type=int,
        default=None,
        help=(
            "oracle/info charge bits for nonlocal strategies (supra_16_5, pr). "
            "If omitted, uses default policy (charges supra_16_5 + pr). "
            "Set to 0 to disable charges."
        ),
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("artifacts/bell/mu_vs_chsh_operational.csv"),
        help="output CSV path",
    )
    parser.add_argument(
        "--run-root",
        type=Path,
        default=Path("artifacts/bell/operational_runs"),
        help="directory for per-strategy VM traces",
    )
    return parser.parse_args(list(argv) if argv is not None else None)


def main(argv: Iterable[str] | None = None) -> int:
    args = parse_args(argv)

    if args.n_per_setting <= 0:
        raise SystemExit("error: --n-per-setting must be positive")

    strategies = _parse_strategies(args.strategies)

    stamp = _dt.datetime.now(_dt.UTC).strftime("%Y%m%d_%H%M%S")
    run_root = args.run_root / stamp

    samples: List[OperationalSample] = []
    for strategy in strategies:
        outdir = run_root / strategy
        sample = run_one(
            strategy=strategy,
            n_per_setting=args.n_per_setting,
            seed=args.seed,
            oracle_charge_bits=args.oracle_charge_bits,
            outdir=outdir,
        )
        samples.append(sample)
        print(
            f"{strategy:>10}  S={float(sample.chsh):.6f}  "
            f"μ_ledger={sample.mu_ledger_total}  μ_info={sample.mu_information:.0f}  "
            f"μ_total={sample.mu_total:.0f}  run={outdir}"
        )

    write_csv(samples, args.output)
    print(f"Wrote {len(samples)} rows to {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
