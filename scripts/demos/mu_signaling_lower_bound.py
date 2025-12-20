"""Tight μ lower-bound certificate (partition-native signaling task).

Task family (n=1 bit):
- Two initial worlds differ only in a *hidden* module’s internal region.
- The "victim" module is the only observable output channel.

Lower bound (provable in Coq, partition-native):
- If the victim observable region changes across a trace, then the victim module
  id must be in the trace causal cone (i.e., targeted).

Upper bound (executable, falsifiable):
- One PMERGE(victim, hidden) makes victim’s observable region depend on the
  hidden world, with mu_execution = 4 (canonical State.pmerge cost).

This produces a JSON certificate and prints the requested phase banner.
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass

from thielecpu._types import ModuleId
from thielecpu.state import State


@dataclass(frozen=True)
class Step:
    op: str
    targets: list[int]
    mu_delta_execution: int


@dataclass(frozen=True)
class Certificate:
    ok: bool
    task: str
    victim_mid: int
    causal_cone: list[int]
    obs_before: list[int]
    obs_after_world0: list[int]
    obs_after_world1: list[int]
    mu_execution_delta_world0: int
    mu_execution_delta_world1: int
    achieved_mu_execution: int
    claimed_lower_bound_mu_execution: int


def observable_region(state: State, mid: ModuleId) -> list[int]:
    return sorted(state.regions[mid])


def build_world(hidden_region: set[int]) -> tuple[State, ModuleId, ModuleId]:
    s = State()
    victim = s.pnew({0, 1})
    hidden = s.pnew(hidden_region)
    return s, victim, hidden


def run_trace_non_targeting(state: State, hidden: ModuleId) -> list[Step]:
    steps: list[Step] = []

    # PSPLIT targets only the hidden module (never the victim).
    before = state.mu_ledger.mu_execution
    left, right = state.psplit(hidden, lambda i: i % 2 == 0)
    after = state.mu_ledger.mu_execution
    steps.append(
        Step(
            op="PSPLIT",
            targets=[int(hidden)],
            mu_delta_execution=int(after - before),
        )
    )

    # Merge back (still only hidden-side targeting).
    before = state.mu_ledger.mu_execution
    state.pmerge(left, right)
    after = state.mu_ledger.mu_execution
    steps.append(
        Step(
            op="PMERGE",
            targets=[int(left), int(right)],
            mu_delta_execution=int(after - before),
        )
    )

    return steps


def run_trace_signal_by_merge(state: State, victim: ModuleId, hidden: ModuleId) -> list[Step]:
    steps: list[Step] = []

    before = state.mu_ledger.mu_execution
    _out = state.pmerge(victim, hidden)
    after = state.mu_ledger.mu_execution
    steps.append(
        Step(
            op="PMERGE",
            targets=[int(victim), int(hidden)],
            mu_delta_execution=int(after - before),
        )
    )

    return steps


def causal_cone(steps: list[Step]) -> list[int]:
    cone: set[int] = set()
    for step in steps:
        cone.update(step.targets)
    return sorted(cone)


def demo(*, mode: str) -> Certificate:
    # Two worlds: hidden bit encoded as which singleton index exists.
    w0, victim0, hidden0 = build_world({2})
    w1, victim1, hidden1 = build_world({3})

    assert victim0 == victim1 == ModuleId(1)

    obs_before = observable_region(w0, victim0)

    mu0_before = w0.mu_ledger.mu_execution
    mu1_before = w1.mu_ledger.mu_execution

    if mode == "no_signal":
        steps0 = run_trace_non_targeting(w0, hidden0)
        steps1 = run_trace_non_targeting(w1, hidden1)
        steps = steps0
    elif mode == "signal":
        # In the current concrete State model, PMERGE removes the victim module id
        # and allocates a fresh module id for the merged region. We treat that
        # returned module as the output channel for this task.
        before0 = w0.mu_ledger.mu_execution
        out0 = w0.pmerge(victim0, hidden0)
        after0 = w0.mu_ledger.mu_execution

        before1 = w1.mu_ledger.mu_execution
        out1 = w1.pmerge(victim1, hidden1)
        after1 = w1.mu_ledger.mu_execution

        steps0 = [Step(op="PMERGE", targets=[int(victim0), int(hidden0)], mu_delta_execution=int(after0 - before0))]
        steps1 = [Step(op="PMERGE", targets=[int(victim1), int(hidden1)], mu_delta_execution=int(after1 - before1))]
        steps = steps0
    else:
        raise ValueError("mode must be 'no_signal' or 'signal'")

    if mode == "signal":
        obs_after0 = observable_region(w0, out0)
        obs_after1 = observable_region(w1, out1)
    else:
        obs_after0 = observable_region(w0, victim0)
        obs_after1 = observable_region(w1, victim1)

    mu0_after = w0.mu_ledger.mu_execution
    mu1_after = w1.mu_ledger.mu_execution

    cone = causal_cone(steps)

    # Claimed tight lower bound for *successful signaling* under the canonical
    # State cost model: the cheapest victim-targeting structural op is PMERGE=4.
    claimed_lb = 4
    achieved = int(mu0_after - mu0_before)

    ok = True
    if mode == "no_signal":
        # No victim targeting → must not be able to change victim observable.
        ok = ok and (int(victim0) not in cone)
        ok = ok and (obs_before == obs_after0 == obs_after1)
    else:
        # Successful signaling → victim observable differs between worlds,
        # and the causal cone includes the victim.
        ok = ok and (obs_after0 != obs_after1)
        ok = ok and (int(victim0) in cone)
        ok = ok and (achieved == claimed_lb)

    return Certificate(
        ok=ok,
        task=f"partition-native signaling ({mode})",
        victim_mid=int(victim0),
        causal_cone=cone,
        obs_before=obs_before,
        obs_after_world0=obs_after0,
        obs_after_world1=obs_after1,
        mu_execution_delta_world0=int(mu0_after - mu0_before),
        mu_execution_delta_world1=int(mu1_after - mu1_before),
        achieved_mu_execution=achieved,
        claimed_lower_bound_mu_execution=claimed_lb,
    )


def main() -> None:
    print("INIT → build two worlds")

    print("DISCOVER → define victim observable")
    print("CLASSIFY → choose task mode")

    print("DECOMPOSE → lower bound + upper bound")
    print("EXECUTE → run traces")
    print("MERGE → compute causal cone + μ deltas")
    print("VERIFY → emit certificate")

    cert_no_signal = demo(mode="no_signal")
    cert_signal = demo(mode="signal")

    print("SUCCESS" if (cert_no_signal.ok and cert_signal.ok) else "FAIL")
    print(
        json.dumps(
            {"no_signal": asdict(cert_no_signal), "signal": asdict(cert_signal)},
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
