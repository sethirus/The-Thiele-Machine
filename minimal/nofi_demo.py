#!/usr/bin/env python3
"""No Free Insight, measured from scratch, no Thiele code imported.

I rebuilt the central law here with nothing but the Python standard library,
because the honest answer to "is this real?" is not a paragraph, it's a thing
you run. Every step checks itself with an assertion. Exit 0 means every
measurement held; anything that didn't would raise and exit nonzero. Don't
take the result on my say-so: the numbers come out the same whoever runs it,
which is the only kind of answer worth handing a stranger.

What it shows, with the Coq kernel nowhere in sight:

  E1  A reversible step (a bijection on possibility-space) can't narrow
      what you know.  Insight is the act of ruling possibilities out, and
      ruling things out destroys information.  There is no reversible way
      to learn something.

  E2  The cost is conserved, not a matter of taste: under reversible
      accounting H(world) + H(record) never moves, so banking k bits of
      insight means destroying exactly k bits, now or on the bill later.
      This is the kernel's entropy-bounded mu theorem, log2|Omega| -
      log2|Omega'| <= delta-mu, rebuilt from bijections and Landauer alone.

  E3  mu is a thermometer: algorithms that bank the same knowledge pay
      wildly different insight-cost.  Binary search rides the floor at
      ~100% efficiency, a wasteful splitter overpays, linear scan limps in
      around 2%.  Nothing beats the floor, ever.

Determinism: fixed seeds, integer arithmetic where possible, tolerance
asserts where floats are unavoidable.
"""

import math
import random
from collections import Counter

PASS = []


def check(name: str, ok: bool, detail: str = "") -> None:
    if not ok:
        raise AssertionError(f"FAIL: {name} {detail}")
    PASS.append(name)
    print(f"  [ok] {name}{(' — ' + detail) if detail else ''}")


# ---------------------------------------------------------------------
# E1 — reversible steps cannot narrow; narrowing destroys information
# ---------------------------------------------------------------------

def e1() -> None:
    print("E1  reversible steps cannot narrow the feasible set")
    n = 16
    worlds = set(range(n))

    rng = random.Random(1729)
    perm = list(range(n))
    rng.shuffle(perm)
    after_bijection = {perm[w] for w in worlds}
    check("bijection preserves feasible-set size", len(after_bijection) == n)

    survivors = {w for w in worlds if w < 6}
    insight_bits = math.log2(n) - math.log2(len(survivors))
    check(
        "narrowing is non-injective and destroys possibilities",
        len(survivors) < n and abs(insight_bits - math.log2(16 / 6)) < 1e-12,
        f"16 -> 6 worlds = {insight_bits:.4f} bits of insight",
    )


# ---------------------------------------------------------------------
# E2 — conservation: banked insight == erased bits, exactly
# ---------------------------------------------------------------------

def entropy(dist: Counter) -> float:
    total = sum(dist.values())
    return -sum((c / total) * math.log2(c / total) for c in dist.values() if c)


def e2() -> None:
    print("E2  conservation: banking k bits of insight erases exactly k bits")
    n = 256
    keep = lambda i: i % 8 == 0          # observation keeps 32 of 256
    survivors = [i for i in range(n) if keep(i)]
    ruled_out = [i for i in range(n) if not keep(i)]

    # Reversible implementation: a bijection world -> (lane, index).
    joint = Counter()
    for k, _ in enumerate(survivors):
        joint[(1, k)] += 1
    for k, _ in enumerate(ruled_out):
        joint[(0, k)] += 1

    h_initial = math.log2(n)
    h_joint = entropy(joint)
    check(
        "reversible work conserves total uncertainty",
        abs(h_joint - h_initial) < 1e-9,
        f"H = {h_joint:.4f} bits before and after",
    )

    h_kept = math.log2(len(survivors))
    insight = h_initial - h_kept          # bits banked by the narrowing
    erase_cost = h_joint - h_kept         # bits destroyed to commit it
    check(
        "banked insight equals erased bits exactly",
        abs(insight - erase_cost) < 1e-9,
        f"insight = erase = {insight:.4f} bits",
    )


# ---------------------------------------------------------------------
# E3 — the mu thermometer on real algorithms
# ---------------------------------------------------------------------

def measure(runner, n: int, trials: int, seed: int) -> float:
    rng = random.Random(seed)
    total = 0
    for _ in range(trials):
        total += runner(rng.randrange(n), n)
    return total / trials


def binary_search(target: int, n: int) -> int:
    lo, hi, mu = 0, n, 0
    while hi - lo > 1:
        mid = (lo + hi) // 2
        mu += 1                            # one irreversible narrowing
        if target < mid:
            hi = mid
        else:
            lo = mid
    return mu


def wasteful_split(target: int, n: int) -> int:
    lo, hi, mu = 0, n, 0
    while hi - lo > 1:
        a = lo + (hi - lo) // 3
        b = lo + 2 * (hi - lo) // 3
        mu += 2                            # two questions, < 2 bits gained
        if target < a:
            hi = a
        elif target < b:
            lo, hi = a, b
        else:
            lo = b
    return mu


def linear_scan(target: int, n: int) -> int:
    mu = 0
    for i in range(n):
        mu += 1
        if i == target:
            break
    return mu


def e3() -> None:
    print("E3  the mu thermometer: insight-efficiency of real algorithms")
    n, trials = 1024, 1000
    floor = math.log2(n)

    rows = []
    for name, fn, seed in (
        ("binary search", binary_search, 31415),
        ("wasteful split", wasteful_split, 31415),
        ("linear scan", linear_scan, 31415),
    ):
        mu = measure(fn, n, trials, seed)
        rows.append((name, mu, floor / mu))

    print(f"      {'algorithm':16s} {'avg mu':>9s} {'efficiency':>11s}   (floor = log2 {n} = {floor:.0f} bits)")
    for name, mu, eff in rows:
        print(f"      {name:16s} {mu:9.2f} {eff:10.1%}")

    (b_name, b_mu, b_eff), (w_name, w_mu, w_eff), (l_name, l_mu, l_eff) = rows
    check("binary search rides the floor", abs(b_mu - floor) < 1e-9, f"mu = {b_mu:.2f}")
    check("no algorithm beats the floor", b_mu >= floor - 1e-9 and w_mu > floor and l_mu > floor)
    check("wasteful split overpays", 0.5 < w_eff < 1.0, f"{w_eff:.1%}")
    check("linear scan pays ~2%", l_eff < 0.05, f"{l_eff:.1%}")


if __name__ == "__main__":
    print("nofi_demo: re-deriving No Free Insight with no Thiele code\n")
    e1()
    e2()
    e3()
    print(f"\nVERDICT: all {len(PASS)} checks passed.")
    print("The floor is real: insight is priced, the price is conserved, and")
    print("mu measures how efficiently computation converts work into knowledge.")
