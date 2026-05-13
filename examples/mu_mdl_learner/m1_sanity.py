"""Substrate sanity: period-k LASSERT certifies periodic streams, fails on others, charges µ either way."""
from __future__ import annotations

from typing import List

from examples.mu_mdl_learner.encoding import run_period_claim
from examples.mu_mdl_learner.streams import (
    LabeledStream,
    is_period_k,
    make_periodic,
    make_random,
    minimum_period,
)


N = 12
PERIODS_TO_CHECK = (2, 3, 4, 5, 6, 7, 8)
RANDOM_SEEDS = (101, 202, 303)


def _fmt_stream(bits) -> str:
    return "".join(str(int(b)) for b in bits)


def main() -> int:
    print(f"M1 sanity check  (N={N}, periods={list(PERIODS_TO_CHECK)})")
    print("-" * 72)

    # --- 1. Periodic streams with their correct period --------------------
    print("Case A: periodic stream + matching period claim. Expect verified=True.")
    print(f"{'k':>3} {'stream':<{N + 2}} {'min_period':>10} {'verified':>9} {'mu':>6} {'expected':>8}")
    a_failures: List[str] = []
    for k in PERIODS_TO_CHECK:
        bits = make_periodic(N, period=k, seed=1000 + k)
        # Sanity: don't bother if the random pattern collapsed to a smaller period.
        mp = minimum_period(bits, max(PERIODS_TO_CHECK))
        verified, mu, _, prog = run_period_claim(bits, k)
        ok_verified = verified is True
        ok_mu = mu == prog.expected_mu_delta
        flag = "" if (ok_verified and ok_mu) else "  <-- MISMATCH"
        print(f"{k:>3} {_fmt_stream(bits):<{N + 2}} {str(mp):>10} {str(verified):>9} {mu:>6} {prog.expected_mu_delta:>8}{flag}")
        if not ok_verified:
            a_failures.append(f"period-{k} stream failed LASSERT (mu={mu})")
        if not ok_mu:
            a_failures.append(f"period-{k} mu mismatch: got {mu}, expected {prog.expected_mu_delta}")

    # --- 2. Random streams should fail LASSERT for every k. ---------------
    print()
    print("Case B: random stream + any period claim. Expect verified=False, but mu still charged.")
    print(f"{'seed':>5} {'k':>3} {'stream':<{N + 2}} {'satisfies_pk':>12} {'verified':>9} {'mu':>6}")
    b_unexpected_certs: List[str] = []
    for seed in RANDOM_SEEDS:
        bits = make_random(N, seed=seed)
        for k in PERIODS_TO_CHECK:
            satisfies = is_period_k(bits, k)
            verified, mu, _, prog = run_period_claim(bits, k)
            # The honest truth: a random stream CAN coincidentally satisfy a
            # period-k constraint (especially for large k). We assert the
            # weaker, correct invariant: LASSERT certifies iff satisfies_pk.
            mismatch = (verified != satisfies)
            flag = "  <-- MISMATCH" if mismatch else ""
            print(f"{seed:>5} {k:>3} {_fmt_stream(bits):<{N + 2}} {str(satisfies):>12} {str(verified):>9} {mu:>6}{flag}")
            if mismatch:
                b_unexpected_certs.append(
                    f"seed={seed} k={k}: satisfies={satisfies} but verified={verified}"
                )
            # In all cases µ must equal the formula's natural cost; failed
            # checks should not skip charging.
            if mu != prog.expected_mu_delta:
                b_unexpected_certs.append(
                    f"seed={seed} k={k}: mu={mu} != expected {prog.expected_mu_delta}"
                )

    # --- Summary ----------------------------------------------------------
    print()
    print("-" * 72)
    if a_failures or b_unexpected_certs:
        print("M1 FAILED.")
        for line in a_failures + b_unexpected_certs:
            print(f"  - {line}")
        return 1
    print("M1 OK: substrate supports the period-k predicate exactly.")
    print("  - periodic streams certify with deterministic µ.")
    print("  - non-periodic streams fail LASSERT, µ still charged.")
    print("  - µ formula matches hw_flen * 8 + (delta + 1).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
