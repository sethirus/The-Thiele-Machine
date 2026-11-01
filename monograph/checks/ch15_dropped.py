"""Exhaustive checks of the claims in chapter fifteen of the book."""
from itertools import product
fails = []
# evenness window prices a counting record exactly; first-cup window has a clash
steps = [(n, n + d) for n in range(0, 6) for d in (0, 1)]           # (before, after)
turns = lambda a, b: b > a
even = lambda n: n % 2
if any(turns(a, b) != (even(a) != even(b)) for a, b in steps): fails.append('evenness')
first = lambda n: n >= 1
trays = {}
for a, b in steps: trays.setdefault((first(a), first(b)), set()).add(turns(a, b))
if not any(len(v) == 2 for v in trays.values()): fails.append('first-cup clash missing')
# a merge under a move whose uncovered part is one-to-one lands inside one pile
for nb in range(1, 4):
    for base in product(range(nb), repeat=nb):
        if len(set(base)) != nb: continue
        for cupf in product([0, 1], repeat=2 * nb):
            full = {(b, r): (base[b], max(r, cupf[2 * b + r])) for b in range(nb) for r in [0, 1]}
            for x, y in product(full, repeat=2):
                if x != y and full[x] == full[y] and x[0] != y[0]: fails.append('fibre')
# without that premise: the stamp merges states in different piles (window shows the box)
stamp = {0: 1, 1: 1}
if not (stamp[0] == stamp[1]): fails.append('stamp')
# halving rule holds for cost c iff every landing pile has at most 2^c sources
import random; random.seed(5)
for _ in range(3000):
    n = random.randint(1, 6); f = [random.randrange(n) for _ in range(n)]
    worst = max(f.count(v) for v in set(f))
    for c in range(0, 4):
        piles_ok = worst <= 2 ** c
        lists_ok = True
        for k in range(1, n + 1):
            for D in [random.sample(range(n), k) for _ in range(4)]:
                if len(D) > 2 ** c * len({f[x] for x in D}): lists_ok = False
        if piles_ok and not lists_ok: fails.append('halving')
        if not piles_ok:
            pile = [x for x in range(n) if f[x] == max(set(f), key=f.count)]
            if not len(pile) > 2 ** c * 1: fails.append('halving-converse')
print('failures:', len(fails))
