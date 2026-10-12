#!/usr/bin/env python3
"""Independent check of C1 / Theorem 5 / C3 at keys other than the top partition.

Counts distinguishable permission states by behaviour (the set of claims a
COMMIT would accept), not by the formula, and compares with 1 + |{c(T)}|.
"""
from itertools import combinations_with_replacement


def partitions(n):
    out = []
    def ext(xs):
        if len(xs) == n:
            out.append(tuple(xs)); return
        for x in range(max(xs, default=-1) + 2):
            ext(xs + [x])
    ext([])
    return out


def refines(p, q):
    return all(p[i] != p[j] or q[i] == q[j] for i in range(len(p)) for j in range(len(p)))


def join(ps, n):
    parent = list(range(n))
    def find(i):
        while parent[i] != i:
            i = parent[i]
        return i
    for p in ps:
        for i in range(n):
            for j in range(n):
                if p[i] == p[j]:
                    a, b = find(i), find(j)
                    if a != b:
                        parent[a] = b
    roots = [find(i) for i in range(n)]
    names = {}
    return tuple(names.setdefault(r, len(names)) for r in roots)


def canonical(p):
    names = {}
    return tuple(names.setdefault(x, len(names)) for x in p)


def check(n):
    L = partitions(n)
    bell = len(L)
    for K in L:
        LK = [p for p in L if refines(p, K)]
        policies = {
            'exact': lambda T: frozenset(T),
            'inferred': lambda T: frozenset(h for h in L if refines(h, join(T, n))),
        }
        for name, c in policies.items():
            # Reachable permission states, explored by behaviour over successful CHECK sequences.
            # State = closed set; behaviour = acceptance signature over all claims in L.
            seen = {frozenset()}  # no-check state
            frontier = [frozenset()]
            closed = set()
            while frontier:
                T = frontier.pop()
                for p in LK:
                    U = c(set(T) | {p}) if T else c({p})
                    if U not in seen:
                        seen.add(U); frontier.append(U)
                        closed.add(U)
            signatures = {tuple(h in U for h in L) for U in closed}
            signatures.add(tuple(False for _ in L))
            formula = 1 + len({c(set(T)) for T in _nonempty_subsets(LK)}) if len(LK) <= 10 else None
            assert len(signatures) == 1 + len(closed), (n, K, name)
            if formula is not None:
                assert formula == len(signatures), (n, K, name, formula, len(signatures))
            if name == 'inferred' and K == tuple([0] * n):
                assert len(signatures) == bell + 1
            if name == 'exact' and K == tuple([0] * n):
                assert len(signatures) == 2 ** bell if bell <= 15 else True
            print(f"n={n} K={K} {name}: states={len(signatures)}"
                  + (f" formula={formula}" if formula is not None else " (formula subset count skipped)"))
    # Pair language, inferred policy at K=top: B_n + 1 states reachable by pair checks.
    n_items = n
    pairs = list(combinations_with_replacement(range(n_items), 2))
    def pair_part(i, j):
        lab = list(range(n_items)); lab[j] = lab[i]; return canonical(tuple(lab))
    seen = {None}
    frontier = [None]
    joins = set()
    while frontier:
        J = frontier.pop()
        for (i, j) in pairs:
            base = [] if J is None else [J]
            U = join(base + [pair_part(i, j)], n_items)
            if U not in seen:
                seen.add(U); frontier.append(U); joins.add(U)
    assert len(joins) == bell, (n, len(joins), bell)
    print(f"n={n} pair-inferred at top: {len(joins) + 1} states = B_n + 1")


def _nonempty_subsets(xs):
    xs = list(xs)
    for bits in range(1, 1 << len(xs)):
        yield [x for i, x in enumerate(xs) if bits >> i & 1]


if __name__ == '__main__':
    for n in (1, 2, 3, 4):
        check(n)
    print("C1 / Theorem 5 / C3 counts agree with behavioural distinguishability for n<=4 at every key.")
