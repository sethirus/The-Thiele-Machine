#!/usr/bin/env python3
"""Operational μ-vs-CHSH scan.

This tool measures μ from the *executed* Python VM state, not from any
serialization of a probability table.

It runs a fixed VM program shape:
  PNEW -> PYEXEC (strategy sampler) -> optional EMIT (oracle charge) -> EMIT
and then computes CHSH from the sampled dataset.

OUTPUT: artifacts/bell/mu_vs_chsh_operational.csv with columns:
  - mu_ledger_total: Canonical VM costs (discovery + execution)
  - mu_information: Information revelation charge
  - mu_total: mu_ledger_total + mu_information

POLICY DISCLOSURE (Dec 15, 2025):
  This is a SCAN-HARNESS ENFORCEMENT, not semantic inevitability.
  
  Current policy:
  - LHV (S≤2): No information charge (mu_information=0)
  - Tsirelson (S≈2.828): No information charge (mu_information=0)
  - Supra-quantum (S>2√2): Charged 64 bits by default via EMIT opcode
  
  Falsifiable claim: Any program producing S>2.828 without explicit
  revelation primitives should either (a) trigger partition violation,
  or (b) have correlation strength degrade to Tsirelson bound.
  
  Status: Policy enforcement verified. Semantic enforcement is TODO.
  See tests/test_supra_revelation_semantics.py for verification plan.
"""

from __future__ import annotations

import argparse
import csv
import datetime as _dt
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, List, Optional, Sequence

from thielecpu.state import State
from thielecpu.vm import VM

from tools.bell_operational import chsh_from_counts, load_counts, strategy_code


DEFAULT_NONLOCAL_ORACLE_CHARGE_BITS = 64
NONLOCAL_STRATEGIES = {"supra_16_5", "pr"}


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
    dataset_path = outdir / "dataset.json"

    code = strategy_code(strategy, n_per_setting=n_per_setting, seed=seed, output_json=dataset_path)

    program: Sequence[tuple[str, str]] = [
        ("PNEW", "{1,2}"),
        ("PYEXEC", code),
    ]

    # Oracle/revelation charge policy (operational, encoding-invariant):
    # - If oracle_charge_bits is None, use defaults: charge supra_16_5 + pr.
    # - If oracle_charge_bits is provided (including 0), apply it to nonlocal strategies.
    effective_charge_bits = 0
    if strategy in NONLOCAL_STRATEGIES:
        if oracle_charge_bits is None:
            effective_charge_bits = DEFAULT_NONLOCAL_ORACLE_CHARGE_BITS
        else:
            effective_charge_bits = int(oracle_charge_bits)

    # Use EMIT numeric payload to invoke info_charge.
    if effective_charge_bits > 0:
        program = list(program) + [("EMIT", f"0 {effective_charge_bits}")]

    program = list(program) + [("EMIT", "done")]

    vm = VM(State())
    vm.run(list(program), outdir)

    dataset = load_counts(dataset_path)
    s_value = chsh_from_counts(dataset)

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
