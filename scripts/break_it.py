"""Try to break the book's Part II results on every small machine.

A proof that can't fail is no proof. This script tries to make each central
result of Part II fail. For each one it searches every deterministic machine on
a few states exhaustively (every step map, every reading, every set of starts
the statement talks about), and the random families where a statement is about
chances or amplitudes, looking for a case where the premises hold and the
conclusion doesn't. A false theorem would turn one up.

Each result also gets controls: the same search with one premise dropped. A
control has to find a counterexample. That shows the premise does work in the
statement, and that the search is able to catch a failure when there is one.

Nothing here is a proof and nothing here is warrant. The proofs are on the page
of the book. This is the other half: the place where a wrong statement would
have been caught.

Run:  python scripts/break_it.py            (full search, up to six states)
      python scripts/break_it.py --quick    (up to four states, for the tests)
      python scripts/break_it.py --markdown out.md
"""

from __future__ import annotations

import argparse
import cmath
import itertools
import json
import math
import random
import sys
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Callable, Iterable, Optional


# ---------------------------------------------------------------------------
# Small machines. States are 0..n-1, a move is a tuple f with f[s] the next
# state, and a reading is a bitmask Y: state s reads yes when bit s is set.
# ---------------------------------------------------------------------------


def maps(n: int) -> Iterable[tuple[int, ...]]:
    return itertools.product(range(n), repeat=n)


def masks(n: int) -> range:
    return range(1 << n)


def has(Y: int, s: int) -> bool:
    return (Y >> s) & 1 == 1


def injective(f: tuple[int, ...]) -> bool:
    return len(set(f)) == len(f)


def merges(f: tuple[int, ...]) -> bool:
    return not injective(f)


def permanent(f: tuple[int, ...], Y: int) -> bool:
    """No state reading yes is sent to a state reading no."""
    return all(has(Y, f[s]) for s in range(len(f)) if has(Y, s))


def raises_at(f: tuple[int, ...], Y: int) -> list[int]:
    return [s for s in range(len(f)) if not has(Y, s) and has(Y, f[s])]


def revokes(f: tuple[int, ...], Y: int) -> bool:
    return any(has(Y, s) and not has(Y, f[s]) for s in range(len(f)))


def run(f: tuple[int, ...], x0: int, steps: int) -> list[int]:
    xs = [x0]
    for _ in range(steps):
        xs.append(f[xs[-1]])
    return xs


def max_fibre(f: tuple[int, ...]) -> int:
    counts: dict[int, int] = {}
    for y in f:
        counts[y] = counts.get(y, 0) + 1
    return max(counts.values())


def halving_cost(f: tuple[int, ...]) -> int:
    """Least whole-number cost meeting the halving price for move f."""
    k = max_fibre(f)
    c = 0
    while (1 << c) < k:
        c += 1
    return c


def ceil_log2(x: int) -> int:
    c = 0
    while (1 << c) < x:
        c += 1
    return c


def fmt_map(f: tuple[int, ...]) -> str:
    return "[" + ",".join(f"{s}->{t}" for s, t in enumerate(f)) + "]"


def fmt_mask(Y: int, n: int) -> str:
    return "{" + ",".join(str(s) for s in range(n) if has(Y, s)) + "}"


# ---------------------------------------------------------------------------
# Bookkeeping
# ---------------------------------------------------------------------------


@dataclass
class Control:
    premise: str
    found: Optional[str] = None


@dataclass
class Result:
    name: str
    label: str
    searched: str
    cases: int = 0
    counterexample: Optional[str] = None
    controls: list[Control] = field(default_factory=list)
    note: str = ""

    def ok(self) -> bool:
        return self.counterexample is None and all(c.found for c in self.controls)


# ---------------------------------------------------------------------------
# The step law (thm:step-law)
# ---------------------------------------------------------------------------


def classify(xs: list[int], k: int) -> tuple[str, int]:
    """Classify the step from xs[k] to xs[k+1] the way the theorem does."""
    nxt = xs[k + 1]
    seen = xs[: k + 1]
    if nxt not in seen:
        return "fresh", -1
    j = seen.index(nxt)
    if j == 0:
        return "loop", j
    if xs[j - 1] != xs[k]:
        return "merge", j
    return "loop", j


def step_law_violation(xs: list[int]) -> Optional[str]:
    first_revisit_done = False
    for k in range(len(xs) - 1):
        kind, j = classify(xs, k)
        if kind == "merge":
            a, b = xs[j - 1], xs[k]
            if a == b or xs[j] != xs[k + 1]:
                return f"step {k} called a merge but {a},{b} do not share a next state"
        if kind != "fresh" and not first_revisit_done:
            first_revisit_done = True
            if not (j == 0 or kind == "merge"):
                return f"first revisit at step {k} is neither the start nor a merge"
        if kind == "loop":
            earlier = set(xs[: k + 1])
            later = xs[k + 2 :]
            if any(x not in earlier for x in later):
                return f"step {k} is a loop step but the run later reaches a new state"
    return None


def check_step_law(N: int) -> Result:
    r = Result("The step law", "thm:step-law",
               f"every map on 1..{N} states, every start, {2 * N + 2} steps")
    for n in range(1, N + 1):
        for f in maps(n):
            for x0 in range(n):
                xs = run(f, x0, 2 * n + 2)
                r.cases += 1
                bad = step_law_violation(xs)
                if bad and r.counterexample is None:
                    r.counterexample = f"{fmt_map(f)} from {x0}: {bad}"
    # Control: drop "one next state". A relation may offer several next states.
    c = Control("each state has exactly one next state")
    for n in range(1, 4):
        for xs in itertools.product(range(n), repeat=5):
            bad = step_law_violation(list(xs))
            if bad:
                c.found = f"path {list(xs)}: {bad}"
                break
        if c.found:
            break
    r.controls.append(c)
    return r


# ---------------------------------------------------------------------------
# Heat or room, part (1) (prop:heat-or-room)
# ---------------------------------------------------------------------------


def run_merges(xs: list[int], upto: int, nxt: Callable[[int], int]) -> bool:
    """Do two different states among xs[0..upto-1] have the same next state?"""
    states = list(dict.fromkeys(xs[:upto]))
    images = [nxt(s) for s in states]
    return len(set(images)) < len(images)


def path_merges(xs: list[int], upto: int) -> bool:
    """Same question along a path that may not follow one rule: two different
    states among xs[0..upto-1] that the path sends to the same next state."""
    seen: dict[int, int] = {}
    for k in range(upto):
        a, b = xs[k], xs[k + 1]
        for s, t in seen.items():
            if s != a and t == b:
                return True
        seen.setdefault(a, b)
    return False


def check_heat_or_room_1(N: int) -> Result:
    r = Result("Heat or room (1)", "prop:heat-or-room",
               f"every map, every reading kept by it, every start on 1..{N} states")
    for n in range(1, N + 1):
        for f in maps(n):
            for Y in masks(n):
                if not permanent(f, Y):
                    continue
                for x0 in range(n):
                    if has(Y, x0):
                        continue
                    xs = run(f, x0, n + 1)
                    raise_at = next((k for k in range(n + 1) if not has(Y, xs[k]) and has(Y, xs[k + 1])), None)
                    if raise_at is None:
                        continue
                    for L in range(raise_at + 1, n + 2):
                        r.cases += 1
                        if not run_merges(xs, L, lambda s: f[s]) and len(set(xs[: L + 1])) < L + 1:
                            if r.counterexample is None:
                                r.counterexample = (f"{fmt_map(f)} yes={fmt_mask(Y, n)} from {x0}: "
                                                    f"no merge in {L} steps yet a state repeats")
    # Control: drop permanence.
    c = Control("the reading never goes from yes back to no")
    for n in range(2, 4):
        for f in maps(n):
            for Y in masks(n):
                if permanent(f, Y):
                    continue
                for x0 in range(n):
                    if has(Y, x0):
                        continue
                    xs = run(f, x0, n + 1)
                    if any(not has(Y, xs[k]) and has(Y, xs[k + 1]) for k in range(n + 1)):
                        if not run_merges(xs, n + 1, lambda s: f[s]) and len(set(xs)) < len(xs):
                            c.found = f"{fmt_map(f)} yes={fmt_mask(Y, n)} from {x0}: raises, never merges, repeats"
                            break
                if c.found:
                    break
            if c.found:
                break
        if c.found:
            break
    r.controls.append(c)
    # Control: drop "one rule". A path through a relation that keeps the reading.
    c = Control("one rule (each state has one next state)")
    for n in range(2, 4):
        for Y in masks(n):
            for xs in itertools.product(range(n), repeat=4):
                xs = list(xs)
                if has(Y, xs[0]):
                    continue
                if any(has(Y, xs[k]) and not has(Y, xs[k + 1]) for k in range(3)):
                    continue
                if not any(not has(Y, xs[k]) and has(Y, xs[k + 1]) for k in range(3)):
                    continue
                if not path_merges(xs, 3) and len(set(xs)) < len(xs):
                    c.found = f"path {xs} with yes={fmt_mask(Y, n)}: raises and keeps, never merges, repeats"
                    break
            if c.found:
                break
        if c.found:
            break
    r.controls.append(c)
    return r


# ---------------------------------------------------------------------------
# Heat or room, part (2): the exact room a reset needs
# ---------------------------------------------------------------------------


def check_heat_or_room_2(N: int) -> Result:
    r = Result("Heat or room (2), the exact bound", "prop:heat-or-room",
               f"every map and reading on 1..{N} states, every set of starts with one already set, every T")
    worst: Optional[str] = None
    for M in range(1, N + 1):
        for f in maps(M):
            for Y in masks(M):
                inside = [s for s in range(M) if has(Y, s)]
                outside = [s for s in range(M) if not has(Y, s)]
                if not inside or not outside:
                    continue
                for z in inside:
                    for size in range(1, len(outside) + 1):
                        for others in itertools.combinations(outside, size):
                            starts = (z,) + others
                            Nst = len(starts)
                            runs = [run(f, s, M + 2) for s in starts]
                            # largest T with states 1..T of every run reading the fixed value
                            Tmax = min(next((t - 1 for t in range(1, M + 3) if not has(Y, xs[t])), M + 2)
                                       for xs in runs)
                            for T in range(0, Tmax + 1):
                                r.cases += 1
                                pool = {xs[t] for xs in runs for t in range(T)}
                                imgs = [f[s] for s in pool]
                                if len(set(imgs)) < len(imgs):
                                    continue  # a merge: the bound is not claimed
                                if M < 1 + (T + 1) * (Nst - 1) and r.counterexample is None:
                                    r.counterexample = (f"M={M} {fmt_map(f)} fixed={fmt_mask(Y, M)} starts={starts} T={T}")
    # The bound is reached: build the building from the book and test it.
    reached = True
    for Nst in range(2, 5):
        for T in range(0, 5):
            M = 1 + (T + 1) * (Nst - 1)
            # chair 0 holds the start that already reads the fixed value; it stays put.
            f = [0] * M
            Y = 1  # only chair 0 reads the fixed value... plus the path ends below
            starts = [0]
            for row in range(Nst - 1):
                base = 1 + row * (T + 1)
                starts.append(base)
                for t in range(T):
                    f[base + t] = base + t + 1
                f[base + T] = base + T
                for t in range(1, T + 1):
                    Y |= 1 << (base + t)
            f = tuple(f)
            runs = [run(f, s, T) for s in starts]
            okay = all(all(has(Y, xs[t]) for t in range(1, T + 1)) for xs in runs)
            pool = {xs[t] for xs in runs for t in range(T)}
            imgs = [f[s] for s in pool]
            okay = okay and len(set(imgs)) == len(imgs) and not has(Y, starts[1]) if Nst > 1 else okay
            reached = reached and okay
    r.note = "bound reached by the book's building for N<=4, T<=4: " + ("yes" if reached else "NO")
    if not reached and r.counterexample is None:
        r.counterexample = "the building that should reach the bound does not meet the premises"
    c = Control("no merge during the T repetitions")
    for M in range(2, 4):
        for f in maps(M):
            for Y in masks(M):
                inside = [s for s in range(M) if has(Y, s)]
                outside = [s for s in range(M) if not has(Y, s)]
                if not inside or not outside:
                    continue
                starts = (inside[0],) + tuple(outside)
                runs = [run(f, s, 2) for s in starts]
                if all(has(Y, xs[1]) for xs in runs) and M < 1 + 2 * (len(starts) - 1):
                    c.found = f"M={M} {fmt_map(f)} fixed={fmt_mask(Y, M)} starts={starts} T=1: the reset merges, bound broken"
                    break
            if c.found:
                break
        if c.found:
            break
    r.controls.append(c)
    return r


# ---------------------------------------------------------------------------
# A permanent flip merges; a raise with no merge takes endless room
# (thm:perm-flip-merges, prop:raise-needs-room, thm:toll-derived)
# ---------------------------------------------------------------------------


def shift_witness(K: int = 50) -> Optional[str]:
    """On the whole numbers, n -> n+1 with the reading 'n >= 1'. Checked on 0..K."""
    f = lambda n: n + 1  # noqa: E731
    yes = lambda n: n >= 1  # noqa: E731
    one_to_one = len({f(n) for n in range(K)}) == K
    kept = all(yes(f(n)) for n in range(K) if yes(n))
    raised = (not yes(0)) and yes(f(0))
    if one_to_one and kept and raised:
        return "on the whole numbers, n -> n+1 with yes = {n >= 1}: one-to-one, kept, raised at 0"
    return None


def check_perm_flip(N: int) -> Result:
    r = Result("A permanent flip merges; the toll from merge pricing", "thm:perm-flip-merges",
               f"every map and every reading it keeps, on 1..{N} states")
    for n in range(1, N + 1):
        for f in maps(n):
            inj = injective(f)
            for Y in masks(n):
                if not permanent(f, Y) or not raises_at(f, Y):
                    continue
                r.cases += 1
                if inj and r.counterexample is None:
                    r.counterexample = f"{fmt_map(f)} yes={fmt_mask(Y, n)}: raises, keeps, merges nothing"
                # The proposition's stronger shape: yes-states go one-to-one into
                # the yes-states with f(s) left out.
                if inj:
                    s = raises_at(f, Y)[0]
                    image = {f[t] for t in range(n) if has(Y, t)}
                    if f[s] in image and r.counterexample is None:
                        r.counterexample = f"{fmt_map(f)}: the raised state is also hit by a yes-state"
    c = Control("finitely many states")
    c.found = shift_witness()
    r.controls.append(c)
    c = Control("the reading is permanent")
    for n in range(2, 4):
        for f in maps(n):
            if not injective(f):
                continue
            for Y in masks(n):
                if raises_at(f, Y):
                    c.found = f"{fmt_map(f)} yes={fmt_mask(Y, n)}: one-to-one and raises, because it also revokes"
                    break
            if c.found:
                break
        if c.found:
            break
    r.controls.append(c)
    c = Control("merge pricing (for the toll)")
    for n in range(1, 4):
        for f in maps(n):
            for Y in masks(n):
                if permanent(f, Y) and raises_at(f, Y):
                    # without merge pricing nothing stops this move costing zero
                    c.found = f"{fmt_map(f)} yes={fmt_mask(Y, n)} at cost 0: raises for no marks"
                    break
            if c.found:
                break
        if c.found:
            break
    r.controls.append(c)
    return r


# ---------------------------------------------------------------------------
# Merge or revoke (thm:merge-or-revoke), reversible keeps nothing
# (thm:reversible-keeps-nothing)
# ---------------------------------------------------------------------------


def check_merge_or_revoke(N: int) -> Result:
    r = Result("Merge or revoke", "thm:merge-or-revoke",
               f"every map and every reading on 1..{N} states")
    for n in range(1, N + 1):
        for f in maps(n):
            inj = injective(f)
            for Y in masks(n):
                if not raises_at(f, Y):
                    continue
                r.cases += 1
                if inj and not revokes(f, Y) and r.counterexample is None:
                    r.counterexample = f"{fmt_map(f)} yes={fmt_mask(Y, n)}"
    c = Control("finitely many states")
    c.found = shift_witness()
    r.controls.append(c)
    return r


def check_reversible(N: int) -> Result:
    r = Result("Reversible keeps nothing", "thm:reversible-keeps-nothing",
               f"every one-to-one map on 1..{N} states, every reading, every start")
    for n in range(1, N + 1):
        for f in itertools.permutations(range(n)):
            for x0 in range(n):
                xs = run(f, x0, n)
                r.cases += 1
                if x0 not in xs[1:] and r.counterexample is None:
                    r.counterexample = f"{fmt_map(f)} from {x0}: never returns"
                for Y in masks(n):
                    if has(Y, x0) or not permanent(f, Y):
                        continue
                    if any(has(Y, x) for x in xs) and r.counterexample is None:
                        r.counterexample = f"{fmt_map(f)} yes={fmt_mask(Y, n)} from {x0}: reaches yes"
    c = Control("finitely many states")
    c.found = shift_witness()
    r.controls.append(c)
    c = Control("the step is one-to-one")
    for n in range(1, 4):
        for f in maps(n):
            if injective(f):
                continue
            for Y in masks(n):
                if not permanent(f, Y):
                    continue
                for x0 in range(n):
                    if not has(Y, x0) and any(has(Y, x) for x in run(f, x0, n)):
                        c.found = f"{fmt_map(f)} yes={fmt_mask(Y, n)} from {x0}: raises and keeps"
                        break
                if c.found:
                    break
            if c.found:
                break
        if c.found:
            break
    r.controls.append(c)
    return r


# ---------------------------------------------------------------------------
# The universal floor, one mark per crossing, and the ceiling (A1)
# ---------------------------------------------------------------------------


def systems(n: int, moves: int, prices: Iterable[int]):
    prices = list(prices)
    for fs in itertools.product(list(maps(n)), repeat=moves):
        for cs in itertools.product(prices, repeat=moves):
            for Y in masks(n):
                yield fs, cs, Y


def toll_holds(fs, cs, Y) -> bool:
    return all(cs[i] >= 1 for i, f in enumerate(fs) if raises_at(f, Y))


def min_cost_minus_crossings(fs, cs, Y, n: int, L: int) -> list[int]:
    """For each start, the least of cost - crossings over runs of length <= L."""
    best = [0] * n
    cur = [0] * n
    for _ in range(L):
        nxt = [10 ** 9] * n
        for s in range(n):
            for i, f in enumerate(fs):
                t = f[s]
                cross = 1 if (not has(Y, s) and has(Y, t)) else 0
                nxt[s] = min(nxt[s], cs[i] - cross + cur[t])
        cur = [min(0, v) for v in nxt]
        best = [min(b, v) for b, v in zip(best, nxt)]
    return best


def check_floor_and_count(N: int) -> Result:
    r = Result("The universal floor and one mark per crossing", "thm:per-crossing",
               f"every system with two moves on 1..{N} states, prices 0..2, runs up to 5 moves")
    ctrl = Control("the toll")
    for n in range(1, N + 1):
        for fs, cs, Y in systems(n, 2, range(3)):
            toll = toll_holds(fs, cs, Y)
            worst = min_cost_minus_crossings(fs, cs, Y, n, 5)
            r.cases += 1
            if toll and min(worst) < 0 and r.counterexample is None:
                r.counterexample = f"{[fmt_map(f) for f in fs]} costs={cs} yes={fmt_mask(Y, n)}"
            if not toll and min(worst) < 0 and ctrl.found is None:
                ctrl.found = f"{[fmt_map(f) for f in fs]} costs={cs} yes={fmt_mask(Y, n)}: a run crosses for less"
            # converse: every run paying for its crossings gives the toll
            if min(worst) >= 0 and not toll and r.counterexample is None:
                r.counterexample = f"converse fails at {[fmt_map(f) for f in fs]} costs={cs}"
    r.controls.append(ctrl)
    return r


def check_ceiling(N: int) -> Result:
    r = Result("Floor and ceiling with a price per move name", "sec:windows",
               f"every system with two moves on 1..{N} states, prices 0..2, runs up to 3 moves")
    for n in range(1, N + 1):
        for fs, cs, Y in systems(n, 2, range(3)):
            if not any(raises_at(f, Y) for f in fs):
                continue
            r.cases += 1
            if not toll_holds(fs, cs, Y):
                continue
            # ceiling: every run costs at most its number of raises
            ok = True
            for L in range(1, 4):
                for seq in itertools.product(range(2), repeat=L):
                    for s in range(n):
                        cost = cross = 0
                        x = s
                        for i in seq:
                            y = fs[i][x]
                            cross += 1 if (not has(Y, x) and has(Y, y)) else 0
                            cost += cs[i]
                            x = y
                        if cost > cross:
                            ok = False
                            break
                    if not ok:
                        break
                if not ok:
                    break
            if ok and r.counterexample is None:
                r.counterexample = f"{[fmt_map(f) for f in fs]} costs={cs} yes={fmt_mask(Y, n)} meets both"
    # Control: let the price depend on the state too. The exact schedule, one on
    # a raising step and zero otherwise, then meets floor and ceiling.
    c = Control("the price depends on the move name only")
    for n in range(1, N + 1):
        for fs in itertools.product(list(maps(n)), repeat=2):
            for Y in masks(n):
                if not any(raises_at(f, Y) for f in fs):
                    continue
                price = lambda x, i: 1 if (not has(Y, x) and has(Y, fs[i][x])) else 0  # noqa: E731
                ok = True
                for L in range(1, 4):
                    for seq in itertools.product(range(2), repeat=L):
                        for s0 in range(n):
                            cost = cross = 0
                            x = s0
                            for i in seq:
                                y = fs[i][x]
                                cross += 1 if (not has(Y, x) and has(Y, y)) else 0
                                cost += price(x, i)
                                x = y
                            if cost != cross:
                                ok = False
                if ok and c.found is None:
                    c.found = (f"{[fmt_map(f) for f in fs]} yes={fmt_mask(Y, n)}: one mark on a raising step "
                               "and none elsewhere meets both")
                if not ok:
                    c.found = None
                    r.counterexample = r.counterexample or "the exact schedule failed floor or ceiling"
    r.controls.append(c)
    r.note = "statement checked: with a per-name price no system whose flag rises meets both"
    return r


# ---------------------------------------------------------------------------
# The squeeze bound, the machine's own narrowing, halving and entropy
# ---------------------------------------------------------------------------


def check_squeeze(N: int) -> Result:
    r = Result("The squeeze bound", "thm:squeeze",
               f"every map and every reading it keeps on 1..{N} states, least halving cost")
    for n in range(1, N + 1):
        for f in maps(n):
            c = halving_cost(f)
            for Y in masks(n):
                if not permanent(f, Y):
                    continue
                m = bin(Y).count("1")
                k = len(raises_at(f, Y))
                r.cases += 1
                if m + k > (1 << c) * m and r.counterexample is None:
                    r.counterexample = f"{fmt_map(f)} yes={fmt_mask(Y, n)} m={m} k={k} cost={c}"
    ctrl = Control("the reading is permanent")
    for n in range(2, 4):
        for f in itertools.permutations(range(n)):
            for Y in masks(n):
                m = bin(Y).count("1")
                k = len(raises_at(f, Y))
                if m + k > m:
                    ctrl.found = f"{fmt_map(f)} yes={fmt_mask(Y, n)}: cost 0, m={m}, k={k}"
                    break
            if ctrl.found:
                break
        if ctrl.found:
            break
    r.controls.append(ctrl)
    return r


def check_halving_formula(N: int) -> Result:
    r = Result("The least halving price is the log of the largest pile", "thm:one-premise",
               f"every map on 1..{N} states, every list of states")
    for n in range(1, N + 1):
        for f in maps(n):
            c = halving_cost(f)
            for D in range(1, 1 << n):
                members = [s for s in range(n) if has(D, s)]
                img = len({f[s] for s in members})
                r.cases += 1
                if len(members) > (1 << c) * img and r.counterexample is None:
                    r.counterexample = f"{fmt_map(f)} D={members}: cost {c} too small"
            if c > 0:
                # one less fails on the largest pile
                k = max_fibre(f)
                if not (k > (1 << (c - 1))) and r.counterexample is None:
                    r.counterexample = f"{fmt_map(f)}: cost {c - 1} would do"
    return r


def check_narrowing(N: int) -> Result:
    r = Result("The machine's own narrowing is priced", "thm:machine-narrowing",
               f"every pair of moves on 1..{N} states at their least halving costs, runs up to 3, every list of starts")
    ctrl = Control("the halving price")
    for n in range(1, N + 1):
        for fs in itertools.product(list(maps(n)), repeat=2):
            cs = [halving_cost(f) for f in fs]
            for L in range(0, 4):
                for seq in itertools.product(range(2), repeat=L):
                    cost = sum(cs[i] for i in seq)
                    for D in range(1, 1 << n):
                        members = [s for s in range(n) if has(D, s)]
                        img = set()
                        for s in members:
                            x = s
                            for i in seq:
                                x = fs[i][x]
                            img.add(x)
                        r.cases += 1
                        lhs = ceil_log2(len(members))
                        if lhs > cost + ceil_log2(len(img)) and r.counterexample is None:
                            r.counterexample = f"{[fmt_map(f) for f in fs]} run={seq} D={members}"
                        if ctrl.found is None and lhs > ceil_log2(len(img)):
                            ctrl.found = f"{[fmt_map(f) for f in fs]} run={seq} D={members} priced at zero narrows"
    r.controls.append(ctrl)
    return r


def H(p: list[Fraction]) -> float:
    return -sum(float(x) * math.log2(float(x)) for x in p if x > 0)


def push(f: tuple[int, ...], p: list[Fraction]) -> list[Fraction]:
    q = [Fraction(0)] * len(f)
    for s, x in enumerate(p):
        q[f[s]] += x
    return q


def random_spread(rng: random.Random, n: int, support: Optional[list[int]] = None) -> list[Fraction]:
    support = list(range(n)) if support is None else support
    w = [rng.randint(0, 9) for _ in support]
    if sum(w) == 0:
        w[0] = 1
    tot = sum(w)
    p = [Fraction(0)] * n
    for s, x in zip(support, w):
        p[s] = Fraction(x, tot)
    return p


def check_entropy(N: int, rng: random.Random, trials: int) -> Result:
    r = Result("Entropy: no move removes more than the log of its largest pile; the ceiling after a flip",
               "thm:entropy-ceiling",
               f"every map on 1..{N} states, {trials} random spreads each, every kept reading")
    eps = 1e-9
    ctrl = Control("the reading is permanent (for the ceiling)")
    for n in range(1, N + 1):
        for f in maps(n):
            K = max_fibre(f)
            for _ in range(trials):
                p = random_spread(rng, n)
                drop = H(p) - H(push(f, p))
                r.cases += 1
                if drop > math.log2(K) + eps and r.counterexample is None:
                    r.counterexample = f"{fmt_map(f)} spread {p}: drops {drop} > log2 {K}"
            # the even spread on a largest pile drops exactly log2 K
            counts: dict[int, list[int]] = {}
            for s, y in enumerate(f):
                counts.setdefault(y, []).append(s)
            pile = max(counts.values(), key=len)
            p = [Fraction(0)] * n
            for s in pile:
                p[s] = Fraction(1, len(pile))
            if abs(H(p) - H(push(f, p)) - math.log2(K)) > eps and r.counterexample is None:
                r.counterexample = f"{fmt_map(f)}: even spread on the largest pile does not drop log2 K"
            for Y in masks(n):
                flips = raises_at(f, Y)
                if not flips:
                    continue
                m = bin(Y).count("1")
                support = [s for s in range(n) if has(Y, s)] + flips
                for _ in range(max(1, trials // 4)):
                    p = random_spread(rng, n, support)
                    q = push(f, p)
                    if permanent(f, Y):
                        r.cases += 1
                        if (m == 0 or H(q) > math.log2(m) + eps) and r.counterexample is None:
                            r.counterexample = f"{fmt_map(f)} yes={fmt_mask(Y, n)}: entropy {H(q)} above log2 {m}"
                    elif ctrl.found is None and m >= 1 and H(q) > math.log2(m) + eps:
                        ctrl.found = f"{fmt_map(f)} yes={fmt_mask(Y, n)}: entropy {H(q):.3f} above log2 {m}"
    r.controls.append(ctrl)
    return r


# ---------------------------------------------------------------------------
# Noisy chairs (thm:noisy-chairs), exact rational arithmetic
# ---------------------------------------------------------------------------


def random_doubly_stochastic(rng: random.Random, n: int) -> list[list[Fraction]]:
    perms = [rng.sample(range(n), n) for _ in range(rng.randint(1, 3))]
    w = [rng.randint(1, 5) for _ in perms]
    tot = sum(w)
    P = [[Fraction(0)] * n for _ in range(n)]
    for perm, x in zip(perms, w):
        for s in range(n):
            P[s][perm[s]] += Fraction(x, tot)
    return P


def closed(P, C: list[int]) -> bool:
    return all(sum(P[s][t] for t in C) == 1 for s in C)


def collision(p) -> Fraction:
    return sum(x * x for x in p)


def step_spread(P, p):
    n = len(p)
    return [sum(p[s] * P[s][t] for s in range(n)) for t in range(n)]


def check_noisy(N: int, rng: random.Random, trials: int) -> Result:
    r = Result("Noisy chairs", "thm:noisy-chairs",
               f"{trials} random tables per size, 2..{N} states, every closed set, exact fractions")
    ctrl = Control("every column adds to one")
    for n in range(2, N + 1):
        subsets = [list(C) for k in range(1, n) for C in itertools.combinations(range(n), k)]
        for _ in range(trials):
            P = random_doubly_stochastic(rng, n)
            for C in subsets:
                if not closed(P, C):
                    continue
                r.cases += 1
                outside = [s for s in range(n) if s not in C]
                if any(P[s][t] != 0 for s in outside for t in C) and r.counterexample is None:
                    r.counterexample = f"doubly stochastic {P} enters closed {C}"
            # (3) collision weight never rises
            for _ in range(3):
                p = random_spread(rng, n)
                r.cases += 1
                if collision(step_spread(P, p)) > collision(p) and r.counterexample is None:
                    r.counterexample = f"doubly stochastic {P} raises collision weight of {p}"
            # (2): a stochastic table with a closed set that is entered from outside
            C = list(range(rng.randint(1, n - 1)))
            Q = [[Fraction(0)] * n for _ in range(n)]
            for s in range(n):
                targets = C if s in C else list(range(n))
                w = [rng.randint(0, 5) for _ in targets]
                if s not in C:
                    w[0] = max(w[0], 1)  # enters C with positive chance
                if sum(w) == 0:
                    w[0] = 1
                tot = sum(w)
                for t, x in zip(targets, w):
                    Q[s][t] += Fraction(x, tot)
            even = [Fraction(1, n)] * n
            after = step_spread(Q, even)
            r.cases += 1
            cols_ok = all(sum(Q[s][t] for s in range(n)) == 1 for t in range(n))
            if cols_ok and r.counterexample is None:
                r.counterexample = f"table {Q} entered from outside yet every column adds to one"
            if not collision(after) > collision(even) and r.counterexample is None:
                r.counterexample = f"table {Q}: one step from the even spread does not raise collision weight"
            if not H(after) < math.log2(n) and r.counterexample is None:
                r.counterexample = f"table {Q}: entropy not below log n"
            if ctrl.found is None:
                ctrl.found = f"{n} states, closed set {C}: a row-stochastic table enters it from outside"
    r.controls.append(ctrl)
    return r


# ---------------------------------------------------------------------------
# Quantum chairs (thm:quantum-chairs), complex arithmetic in plain Python
# ---------------------------------------------------------------------------


def dot(u, v) -> complex:
    return sum(a.conjugate() * b for a, b in zip(u, v))


def gram_schmidt(cols):
    out = []
    for v in cols:
        w = list(v)
        for u in out:
            c = dot(u, w)
            w = [a - c * b for a, b in zip(w, u)]
        nrm = math.sqrt(sum(abs(a) ** 2 for a in w))
        out.append([a / nrm for a in w])
    return out


def mat_vec(cols, v):
    n = len(cols[0])
    return [sum(cols[j][i] * v[j] for j in range(len(cols))) for i in range(n)]


def check_quantum(N: int, rng: random.Random, trials: int) -> Result:
    r = Result("Quantum chairs", "thm:quantum-chairs",
               f"{trials} random unitaries per size, dimensions 2..{N}, every leading subspace")
    ctrl = Control("the step is unitary")
    eps = 1e-9
    for d in range(2, N + 1):
        for _ in range(trials):
            for k in range(1, d):
                # a random unitary that maps span(e_1..e_k) into itself: columns built
                # from a block upper-triangular matrix, then made orthonormal.
                cols = []
                for j in range(d):
                    col = [complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(d)]
                    if j < k:
                        col = [c if i < k else 0j for i, c in enumerate(col)]
                    cols.append(col)
                U = gram_schmidt(cols)
                r.cases += 1
                for j in range(k, d):
                    e = [0j] * d
                    e[j] = 1
                    img = mat_vec(U, e)
                    leak = math.sqrt(sum(abs(img[i]) ** 2 for i in range(k)))
                    if leak > eps and r.counterexample is None:
                        r.counterexample = f"dimension {d}, subspace {k}: complement leaks {leak}"
                # control: an invertible map, not unitary, that keeps the subspace
                if ctrl.found is None:
                    A = [list(c) for c in cols]
                    e = [0j] * d
                    e[k] = 1
                    img = mat_vec(A, e)
                    leak = math.sqrt(sum(abs(img[i]) ** 2 for i in range(k)))
                    if leak > eps:
                        ctrl.found = f"dimension {d}: a block-triangular invertible map keeps a {k}-dimensional subspace and moves its complement"
    r.controls.append(ctrl)
    r.note = "a unitary keeps inner products, so this search can only catch arithmetic slips; the control shows what fails without it"
    return r


# ---------------------------------------------------------------------------
# Time's bill (thm:time-bill)
# ---------------------------------------------------------------------------


def check_time_bill() -> Result:
    r = Result("Time's bill", "thm:time-bill", "p on a grid of 999 values in (0,1), distances 0..60")
    for k in range(1, 1000):
        p = k / 1000
        sigma = (2 * p - 1) * math.log(p / (1 - p))
        r.cases += 1
        if (k == 500 and abs(sigma) > 1e-12) or (k != 500 and not sigma > 0):
            r.counterexample = f"p={p}: sigma={sigma}"
        if p > 0.5:
            v = 2 * p - 1
            for Nd in range(0, 61):
                heat = Nd * math.log((1 + v) / (1 - v))
                r.cases += 1
                if heat * (Nd / v) < Nd * Nd - 1e-9 and r.counterexample is None:
                    r.counterexample = f"v={v} N={Nd}: heat*time below N^2"
    r.note = "a numeric sweep of a closed-form inequality; the proof is the page's"
    return r


# ---------------------------------------------------------------------------
# Teaching at zero marks (thm:three-states), no level holds its own questions
# ---------------------------------------------------------------------------


def knowledge(moves, window, Omega, seq, s0) -> list[int]:
    def trace(s):
        out = [window[s]]
        x = s
        for i in seq:
            x = moves[i][x]
            out.append(window[x])
        return out

    actual = trace(s0)
    return [s for s in Omega if trace(s) == actual]


def zero_mark_teacher(n: int) -> Optional[str]:
    free = [p for p in itertools.permutations(range(n))]  # cost 0 under halving = one-to-one
    for window in itertools.product(range(n), repeat=n):
        for size in range(1, n + 1):
            for Omega in itertools.combinations(range(n), size):
                for s0 in Omega:
                    first = knowledge(free, window, Omega, (), s0)
                    for L in range(1, 4):
                        for seq in itertools.product(range(len(free)), repeat=L):
                            if len(knowledge(free, window, Omega, seq, s0)) < len(first):
                                return f"{n} states, window {window}, candidates {Omega}, start {s0}, run {[free[i] for i in seq]}"
    return None


def check_three_states() -> Result:
    r = Result("Three states are the minimum for teaching at zero marks", "thm:three-states",
               "every machine of zero-mark moves on 1..3 states, every window, every candidate list, runs up to 3")
    for n in (1, 2):
        r.cases += 1
        found = zero_mark_teacher(n)
        if found and r.counterexample is None:
            r.counterexample = "a zero-mark teacher with too few states: " + found
    r.cases += 1
    three = zero_mark_teacher(3)
    if three is None and r.counterexample is None:
        r.counterexample = "no zero-mark teacher on three states"
    r.note = "found on three states: " + (three or "none")
    return r


def check_no_self_containment(N: int) -> Result:
    r = Result("No level holds its own questions", "thm:no-self-containment",
               f"every assignment of a reading to each state, 1..{N} states")
    for n in range(1, N + 1):
        for a in itertools.product(range(1 << n), repeat=n):
            r.cases += 1
            diag = sum(1 << s for s in range(n) if not has(a[s], s))
            if diag in a and r.counterexample is None:
                r.counterexample = f"assignment {a} holds its own diagonal"
    return r


# ---------------------------------------------------------------------------
# The certainty bill (thm:certainty-bill)
# ---------------------------------------------------------------------------


def H_of(dist: dict) -> float:
    return -sum(float(v) * math.log2(float(v)) for v in dist.values() if v > 0)


def cond_H(pairs: list[tuple[object, object, Fraction]]) -> float:
    """H(A | B) for a joint list of (a, b, chance)."""
    joint: dict = {}
    marg: dict = {}
    for a, b, w in pairs:
        joint[(a, b)] = joint.get((a, b), 0) + w
        marg[b] = marg.get(b, 0) + w
    return H_of(joint) - H_of(marg)


def check_certainty_bill(N: int, rng: random.Random, trials: int) -> Result:
    r = Result("The certainty bill", "thm:certainty-bill",
               f"every pair of moves on 1..{N} states at their least halving costs, runs up to 3, "
               f"every window, {trials} random spreads")
    eps = 1e-9
    ctrl = Control("the halving price")
    for n in range(1, N + 1):
        windows = list(itertools.product(range(2), repeat=n))
        for fs in itertools.product(list(maps(n)), repeat=2):
            cs = [halving_cost(f) for f in fs]
            for L in range(0, 4):
                for seq in itertools.product(range(2), repeat=L):
                    cost = sum(cs[i] for i in seq)
                    for _ in range(trials):
                        p = random_spread(rng, n)
                        w = rng.choice(windows)
                        rows = []
                        for x in range(n):
                            if p[x] == 0:
                                continue
                            z = x
                            seen = [w[z]]
                            for i in seq:
                                z = fs[i][z]
                                seen.append(w[z])
                            rows.append((x, z, tuple(seen), p[x]))
                        HX = H_of({x: q for x, _, _, q in rows})
                        HZ = H_of({})
                        zd: dict = {}
                        for _, z, _, q in rows:
                            zd[z] = zd.get(z, 0) + q
                        HZ = H_of(zd)
                        HXgZ = cond_H([(x, z, q) for x, z, _, q in rows])
                        HVgZ = cond_H([(v, z, q) for _, z, v, q in rows])
                        r.cases += 1
                        bad = None
                        if abs(HX - (HXgZ + HZ)) > eps:
                            bad = "split fails"
                        elif HXgZ > cost + eps:
                            bad = f"merges destroyed {HXgZ:.3f} bits for {cost} marks"
                        elif HVgZ > cost + eps:
                            bad = f"observer holds {HVgZ:.3f} bits the end state lost, for {cost} marks"
                        if bad and r.counterexample is None:
                            r.counterexample = f"{[fmt_map(f) for f in fs]} run={seq} spread={p}: {bad}"
                        if ctrl.found is None and HVgZ > eps:
                            ctrl.found = (f"{[fmt_map(f) for f in fs]} run={seq}: priced at zero, the observer keeps "
                                          f"{HVgZ:.3f} bits the end state no longer holds")
    r.controls.append(ctrl)
    return r


# ---------------------------------------------------------------------------
# The same bill at every scale (thm:every-scale)
# ---------------------------------------------------------------------------


def check_every_scale(N: int) -> Result:
    r = Result("The same bill at every scale", "thm:every-scale",
               f"every fine machine on 1..{N} states, every described set, every coarse description onto it")
    ctrl_room = Control("the fine step stays inside the described states")
    for n in range(1, N + 1):
        for F in maps(n):
            for A in range(1, 1 << n):
                members = [x for x in range(n) if has(A, x)]
                inside = all(has(A, F[x]) for x in members)
                inj = len({F[x] for x in members}) == len(members)
                for s in range(1, len(members) + 1):
                    for pi in itertools.product(range(s), repeat=n):
                        if {pi[x] for x in members} != set(range(s)):
                            continue
                        f: dict[int, int] = {}
                        ok = True
                        for x in members:
                            a, b = pi[x], pi[F[x]]
                            if f.setdefault(a, b) != b:
                                ok = False
                                break
                        if not ok:
                            continue
                        r.cases += 1
                        coarse_merges = len(set(f.values())) < s
                        if coarse_merges and inj and inside and r.counterexample is None:
                            r.counterexample = f"fine {fmt_map(F)} on {members}, coarse {pi}: coarse merge, fine neither"
                        if coarse_merges and inj and not inside and ctrl_room.found is None:
                            ctrl_room.found = (f"fine {fmt_map(F)} described on {members} by {pi}: the coarse rule "
                                               "merges, the fine step is one-to-one there and leaves the described states")
    r.controls.append(ctrl_room)
    c = Control("finitely many described states")
    K = 50
    F = lambda x: x + 1  # noqa: E731
    pi = lambda x: 0 if x == 0 else 1  # noqa: E731
    f = {0: 1, 1: 1}
    if all(pi(F(x)) == f[pi(x)] for x in range(K)) and len({F(x) for x in range(K)}) == K:
        c.found = "on the whole numbers, n -> n+1 described by 'is it 0': the coarse rule merges, the fine one never does"
    r.controls.append(c)
    return r


# ---------------------------------------------------------------------------


def run_all(quick: bool, seed: int = 20261014) -> list[Result]:
    rng = random.Random(seed)
    N = 4 if quick else 6
    N5 = 4 if quick else 5
    small = 3 if quick else 4
    out = [
        check_step_law(N),
        check_heat_or_room_1(N),
        check_heat_or_room_2(4 if quick else 5),
        check_perm_flip(N),
        check_merge_or_revoke(N),
        check_reversible(N),
        check_floor_and_count(3),
        check_ceiling(3),
        check_squeeze(N),
        check_halving_formula(N5),
        check_narrowing(3),
        check_entropy(small, rng, 4 if quick else 8),
        check_noisy(4, rng, 40 if quick else 400),
        check_quantum(4, rng, 20 if quick else 200),
        check_time_bill(),
        check_three_states(),
        check_no_self_containment(3),
        check_certainty_bill(3 if quick else 3, rng, 2 if quick else 6),
        check_every_scale(3 if quick else 4),
    ]
    return out


def markdown(results: list[Result]) -> str:
    lines = ["| Result | Searched | Cases | Counterexamples | Premise dropped: counterexample found |",
             "|---|---|---|---|---|"]
    for r in results:
        ctr = "; ".join(f"{c.premise}: {'yes' if c.found else 'NO'}" for c in r.controls) or "n/a"
        lines.append(f"| {r.name} ({r.label}) | {r.searched} | {r.cases} | "
                     f"{'none' if r.counterexample is None else r.counterexample} | {ctr} |")
    return "\n".join(lines) + "\n"


def main(argv: Optional[list[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--markdown")
    ap.add_argument("--json")
    args = ap.parse_args(argv)
    results = run_all(args.quick)
    text = markdown(results)
    sys.stdout.write(text)
    for r in results:
        for c in r.controls:
            if c.found:
                sys.stdout.write(f"  control [{r.label}] without '{c.premise}': {c.found}\n")
        if r.note:
            sys.stdout.write(f"  note [{r.label}]: {r.note}\n")
    if args.markdown:
        with open(args.markdown, "w", encoding="utf-8") as fh:
            fh.write(text)
    if args.json:
        with open(args.json, "w", encoding="utf-8") as fh:
            json.dump([{"name": r.name, "label": r.label, "searched": r.searched, "cases": r.cases,
                        "counterexample": r.counterexample, "note": r.note,
                        "controls": [{"premise": c.premise, "found": c.found} for c in r.controls]}
                       for r in results], fh, indent=2)
    return 0 if all(r.ok() for r in results) else 1


if __name__ == "__main__":
    sys.exit(main())
