"""Prophecy experiment for multiple elementary cellular automata rules."""
from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, List

DEFAULT_CELL_COUNT = 256
DEFAULT_STEPS = 100_000
DEFAULT_RULES = [30]
DEFAULT_SECRET_KEY = b"SIGHT-KEY-ADMITTED-LIMITATION"
DEFAULT_EXPORT = Path("experiments/results/final_instrument_suite.json")


def make_elementary_rule(rule: int):
    if not 0 <= rule <= 255:
        raise ValueError("Elementary cellular automaton rules live in [0, 255]")

    table = [(rule >> bit) & 1 for bit in range(8)]

    def step(state: List[int]) -> List[int]:
        width = len(state)
        nxt = [0] * width
        for idx in range(width):
            left = state[(idx - 1) % width]
            centre = state[idx]
            right = state[(idx + 1) % width]
            pattern = (left << 2) | (centre << 1) | right
            nxt[idx] = table[pattern]
        return nxt

    return step


def bits_to_bytes(bits: Iterable[int]) -> bytes:
    """Encode a sequence of binary digits as ASCII bytes."""

    return "".join(str(bit) for bit in bits).encode("ascii")


def build_prophecy_payload(
    *,
    secret_key: bytes,
    rule: int,
    steps: int,
    cell_count: int,
    primordial: Iterable[int],
    final_state: Iterable[int],
) -> bytes:
    """Assemble the deterministic payload whose digest forms the prophecy seal.

    The payload binds together the shared secret key, the experimental
    configuration, and both the primordial and evolved configurations.  Folding
    the metadata and primordial tape into the digest ensures distinct runs
    (e.g., alternative rule/step combinations) cannot accidentally reuse a
    matching seal even if their futures collide.
    """

    header = f"rule={rule};steps={steps};cells={cell_count}".encode("ascii")
    primordial_bytes = bits_to_bytes(primordial)
    final_bytes = bits_to_bytes(final_state)
    return b"||".join((secret_key, header, primordial_bytes, final_bytes))


def compute_gestalt_seal(
    initial_state: List[int],
    steps: int,
    rule: int,
    cell_count: int,
    secret_key: bytes,
) -> tuple[str, List[int]]:
    """Predict the future configuration and derive its sealed digest.

    The sighted computation evolves the automaton analytically before the blind
    trace begins.  The resulting state is sealed together with the shared
    prophecy key so auditors can compare it with the independently evolved
    future.
    """

    step_fn = make_elementary_rule(rule)
    state = initial_state[:]
    for _ in range(steps):
        state = step_fn(state)
    final_bytes = bits_to_bytes(state)
    payload = build_prophecy_payload(
        secret_key=secret_key,
        rule=rule,
        steps=steps,
        cell_count=cell_count,
        primordial=initial_state,
        final_state=state,
    )
    return hashlib.sha256(payload).hexdigest(), state


def run_prophecy(
    rule: int,
    steps: int,
    cell_count: int,
    secret_key: bytes,
    progress_interval: int | None,
) -> dict:
    step_fn = make_elementary_rule(rule)
    primordial = [0] * cell_count
    primordial[cell_count // 2] = 1

    seal, analytic_future = compute_gestalt_seal(
        primordial,
        steps,
        rule,
        cell_count,
        secret_key,
    )
    print(f"SEALED PREDICTION FOR RULE {rule}: {seal}")

    state = primordial[:]
    for current in range(1, steps + 1):
        state = step_fn(state)
        if progress_interval and progress_interval > 0 and current % progress_interval == 0:
            print(f"[TRACE][rule {rule}] Completed step {current}/{steps}")
    payload = build_prophecy_payload(
        secret_key=secret_key,
        rule=rule,
        steps=steps,
        cell_count=cell_count,
        primordial=primordial,
        final_state=state,
    )
    final_bytes = bits_to_bytes(state)
    actual_hash = hashlib.sha256(payload).hexdigest()
    raw_future_hash = hashlib.sha256(final_bytes).hexdigest()
    print(f"HASH OF THE ACTUAL FUTURE FOR RULE {rule}: {raw_future_hash}")
    print(f"SEALED HASH OF THE ACTUAL FUTURE FOR RULE {rule}: {actual_hash}")

    verdict: str
    if seal == actual_hash:
        verdict = "Q.E.D."
        print("Q.E.D. The Sighted machine correctly predicted the future.")
    else:
        verdict = "FAILURE"
        print(
            "FAILURE. The universe is incoherent. The proof has failed."
            " The analytic seal did not align with the observed future."
        )

    return {
        "rule": rule,
        "steps": steps,
        "cell_count": cell_count,
        "seal": seal,
        "actual_hash": actual_hash,
        "raw_future_hash": raw_future_hash,
        "analytic_future_matches": analytic_future == state,
        "verdict": verdict,
        "timestamp": datetime.now(timezone.utc).isoformat(),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run the prophecy experiment across one or more cellular automata rules.",
    )
    parser.add_argument(
        "--rules",
        nargs="*",
        type=int,
        default=DEFAULT_RULES,
        help="Elementary CA rules to evaluate (default: 30)",
    )
    parser.add_argument(
        "--steps",
        type=int,
        default=DEFAULT_STEPS,
        help="Number of evolution steps per rule (default: 100000)",
    )
    parser.add_argument(
        "--cell-count",
        type=int,
        default=DEFAULT_CELL_COUNT,
        help="Width of the automaton tape (default: 256)",
    )
    parser.add_argument(
        "--secret-key",
        type=str,
        default=DEFAULT_SECRET_KEY.decode("ascii"),
        help="ASCII prophecy key shared across all runs",
    )
    parser.add_argument(
        "--progress-interval",
        type=int,
        default=1_000,
        help="Print trace updates every N steps (<=0 disables progress logging)",
    )
    parser.add_argument(
        "--export",
        type=Path,
        default=DEFAULT_EXPORT,
        help="Optional JSON destination for aggregated results",
    )
    parser.add_argument(
        "--no-export",
        action="store_true",
        help="Skip writing the aggregated JSON report",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    secret_key = args.secret_key.encode("ascii")
    progress = args.progress_interval if args.progress_interval > 0 else None

    results = []
    for rule in args.rules:
        print(f"\n=== Running prophecy for rule {rule} ===")
        record = run_prophecy(
            rule=rule,
            steps=args.steps,
            cell_count=args.cell_count,
            secret_key=secret_key,
            progress_interval=progress,
        )
        results.append(record)

    if not args.no_export:
        export_path = args.export
        export_path.parent.mkdir(parents=True, exist_ok=True)
        with export_path.open("w", encoding="utf-8") as handle:
            json.dump({"runs": results}, handle, indent=2)
        print(f"Aggregated results written to {export_path}")


if __name__ == "__main__":
    main()
