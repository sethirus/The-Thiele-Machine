"""Produce a partition-native *impossibility certificate* (no-signaling).

This demo is intentionally simple and falsifiable:
- We encode a hidden bit by changing only a *different* module’s internal region.
- We run the same trace that never targets the victim module.
- We output a JSON certificate that the victim’s observable region is unchanged.

If this script ever prints a certificate with ok=false, the machine leaked
information across a partition boundary.
"""

from __future__ import annotations

import json
from dataclasses import dataclass

from thielecpu._types import ModuleId
from thielecpu.state import State


@dataclass(frozen=True)
class Certificate:
    ok: bool
    victim_mid: int
    obs_before: list[int]
    obs_after_a: list[int]
    obs_after_b: list[int]


def observable_region(state: State, mid: ModuleId) -> list[int]:
    return sorted(state.regions[mid])


def run_non_targeting_trace(state: State, *, hidden_mid: ModuleId) -> None:
    state.add_axiom(hidden_mid, "hidden: axiom 0")
    left, right = state.psplit(hidden_mid, lambda i: i % 2 == 0)
    state.add_axiom(left, "hidden: axiom 1")
    state.pmerge(left, right)


def build_state(hidden_bit: int) -> tuple[State, ModuleId, ModuleId]:
    state = State()
    victim = state.pnew({0, 1})

    # Same module id, different internal region encodes the hidden bit.
    if hidden_bit == 0:
        hidden = state.pnew({2, 3, 4, 5})
    else:
        hidden = state.pnew({10, 11, 12, 13})

    return state, victim, hidden


def main() -> None:
    print("INIT → setting up two worlds")
    s0, victim0, hidden0 = build_state(0)
    s1, victim1, hidden1 = build_state(1)

    print("DISCOVER → defining victim observable")
    obs_before = observable_region(s0, victim0)

    print("EXECUTE → running non-targeting traces")
    run_non_targeting_trace(s0, hidden_mid=hidden0)
    run_non_targeting_trace(s1, hidden_mid=hidden1)

    print("VERIFY → checking observational no-signaling")
    obs_after_a = observable_region(s0, victim0)
    obs_after_b = observable_region(s1, victim1)

    cert = Certificate(
        ok=(obs_before == obs_after_a == obs_after_b),
        victim_mid=int(victim0),
        obs_before=obs_before,
        obs_after_a=obs_after_a,
        obs_after_b=obs_after_b,
    )

    print("SUCCESS" if cert.ok else "FAIL")
    print(json.dumps(cert.__dict__, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
