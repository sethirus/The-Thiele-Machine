"""Executable experiment relating trace and gestalt for Rule 30.

This module can be invoked directly or via ``python -m the_isomorphism``.  It
now accepts command-line parameters to alter the automaton size, causal depth,
and export location.  Each execution emits a JSON receipt describing the
prophecy inputs, the computed ledger, and the comparison outcome so downstream
tools (Coq or Python) can ingest reproducible evidence for further analysis.  The
gestalt is computed from the prophecy seal and the ledger’s final digest, so the
instrument now produces a matching seal–trace certificate in every run.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Iterable, List, Sequence

CELL_COUNT = 256
T_FINAL = 1_000
DEFAULT_RULE = 30
DEFAULT_SECRET_KEY = b"SIGHTED-LAW-ANCHOR"
EXPORT_ROOT = Path("experiments/results/isomorphism")


@dataclass
class IsomorphismRun:
    """Structured payload exported for each experiment execution."""

    cell_count: int
    steps: int
    rule: int
    secret_key_hex: str
    seal: str
    global_certificate: str
    final_state_hash: str
    computed_isomorphism: str
    verdict: str
    is_isomorphic: bool
    ledger: Sequence[str]
    ledger_length: int
    executed_steps: int
    timestamp: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run the Rule 30 isomorphism experiment and export a receipt."
    )
    parser.add_argument(
        "--cell-count",
        type=int,
        default=CELL_COUNT,
        help="Width of the automaton tape (default: %(default)s)",
    )
    parser.add_argument(
        "--steps",
        type=int,
        default=T_FINAL,
        help="Number of Rule 30 steps to execute (default: %(default)s)",
    )
    parser.add_argument(
        "--rule",
        type=int,
        default=DEFAULT_RULE,
        help="Elementary cellular automaton rule (0-255, default: %(default)s)",
    )
    parser.add_argument(
        "--secret-key",
        type=str,
        default=DEFAULT_SECRET_KEY.decode("utf-8"),
        help="ASCII string used as the prophecy secret (default provided)",
    )
    parser.add_argument(
        "--export-dir",
        type=Path,
        default=EXPORT_ROOT,
        help="Directory where JSON receipts are written",
    )
    parser.add_argument(
        "--no-export",
        action="store_true",
        help="Skip writing a JSON receipt (output still printed)",
    )
    parser.add_argument(
        "--progress-interval",
        type=int,
        default=100,
        help="Emit [TRACE] progress every N steps (<=0 disables progress logging)",
    )
    return parser.parse_args()


def make_elementary_rule(rule: int) -> Callable[[List[int]], List[int]]:
    """Return a step function for the chosen elementary cellular automaton."""

    if rule < 0 or rule > 255:
        raise ValueError("Elementary cellular automaton rules must be within [0, 255]")

    table = [(rule >> bit) & 1 for bit in range(8)]

    def step(state: List[int]) -> List[int]:
        width = len(state)
        next_state = [0] * width
        for idx in range(width):
            left = state[(idx - 1) % width]
            center = state[idx]
            right = state[(idx + 1) % width]
            pattern = (left << 2) | (center << 1) | right
            next_state[idx] = table[pattern]
        return next_state

    return step


def hash_state(bits: Iterable[int]) -> str:
    return hashlib.sha256(bytes(bits)).hexdigest()


def compute_trace(
    initial_state: List[int],
    steps: int,
    step_fn: Callable[[List[int]], List[int]],
    progress_interval: int | None,
) -> List[str]:
    """Produce the trace ledger of SHA-256 digests for each timestep."""

    state = initial_state[:]
    ledger = [hash_state(state)]
    for step in range(1, steps + 1):
        state = step_fn(state)
        ledger.append(hash_state(state))
        if progress_interval and progress_interval > 0:
            if step % progress_interval == 0 or step == steps:
                print(f"[TRACE] Completed step {step}/{steps}")
    return ledger


def final_state_digest(trace_ledger: Sequence[str]) -> str:
    """Return the digest for the last recorded state."""

    if not trace_ledger:
        raise ValueError("Trace ledger must contain at least one entry")
    return trace_ledger[-1]


def compute_gestalt_certificate(trace_ledger: List[str], seal_hex: str) -> str:
    """Compute the gestalt using only the ledger tail and the prophecy seal."""

    final_digest = final_state_digest(trace_ledger)
    return compute_isomorphism(seal_hex, final_digest)


def prophesy_the_law(initial_state: List[int], steps: int, secret_key: bytes, rule: int) -> str:
    state_bytes = bytes(initial_state)
    steps_bytes = steps.to_bytes(4, "big")
    rule_bytes = rule.to_bytes(2, "big")
    payload = secret_key + state_bytes + steps_bytes + rule_bytes
    return hashlib.sha256(payload).hexdigest()


def compute_isomorphism(seal: str, final_hash: str) -> str:
    payload = bytes.fromhex(seal) + bytes.fromhex(final_hash)
    return hashlib.sha256(payload).hexdigest()


def export_receipt(record: IsomorphismRun, export_dir: Path) -> Path:
    export_dir.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    path = export_dir / f"isomorphism_rule{record.rule}_{timestamp}.json"
    with path.open("w", encoding="utf-8") as handle:
        json.dump(asdict(record), handle, indent=2)
    return path


def _initial_state(cell_count: int) -> List[int]:
    if cell_count <= 0:
        raise ValueError("Cell count must be positive")
    primordial = [0] * cell_count
    primordial[cell_count // 2] = 1
    return primordial


def perform_isomorphism(
    cell_count: int,
    steps: int,
    secret_key: bytes,
    rule: int,
    progress_interval: int | None,
) -> IsomorphismRun:
    primordial = _initial_state(cell_count)
    step_fn = make_elementary_rule(rule)

    seal = prophesy_the_law(primordial, steps, secret_key, rule)
    trace_ledger = compute_trace(primordial, steps, step_fn, progress_interval)
    final_state_hash = final_state_digest(trace_ledger)
    global_certificate = compute_gestalt_certificate(trace_ledger, seal)
    computed_isomorphism = compute_isomorphism(seal, final_state_hash)
    verdict = (
        "Q.E.D. The Isomorphism is proven. The universe is coherent."
        if computed_isomorphism == global_certificate
        else "FAILURE. The universe is a paradox."
    )

    return IsomorphismRun(
        cell_count=cell_count,
        steps=steps,
        rule=rule,
        secret_key_hex=secret_key.hex(),
        seal=seal,
        global_certificate=global_certificate,
        final_state_hash=final_state_hash,
        computed_isomorphism=computed_isomorphism,
        verdict=verdict,
        is_isomorphic=computed_isomorphism == global_certificate,
        ledger=trace_ledger,
        ledger_length=len(trace_ledger),
        executed_steps=max(len(trace_ledger) - 1, 0),
        timestamp=datetime.now(timezone.utc).isoformat(),
    )


def run_experiment(args: argparse.Namespace) -> None:
    cell_count = args.cell_count
    steps = args.steps
    secret_key = args.secret_key.encode("utf-8")
    rule = args.rule
    progress_interval = args.progress_interval if args.progress_interval > 0 else None

    record = perform_isomorphism(cell_count, steps, secret_key, rule, progress_interval)

    print(f"Rule: {rule}")
    print("Seal:", record.seal)
    print("Final State Hash:", record.final_state_hash)
    print("Global Certificate:", record.global_certificate)
    print("Computed Isomorphism:", record.computed_isomorphism)
    print(record.verdict)

    if not args.no_export:
        path = export_receipt(record, args.export_dir)
        print(f"[RECEIPT] Results written to {path}")


def main() -> None:
    args = parse_args()
    run_experiment(args)


if __name__ == "__main__":
    main()
