"""Exhaustive checks of the claims in chapter five of the book on small cases."""
from itertools import product, combinations, permutations

def preorders(n):
    """All preorders on range(n) as sets of pairs (x, y) meaning x <= y."""
    pairs = [(x, y) for x in range(n) for y in range(n) if x != y]
    for bits in product([0, 1], repeat=len(pairs)):
        le = {(x, x) for x in range(n)} | {p for p, b in zip(pairs, bits) if b}
        if all((x, z) in le for (x, y) in le for (y2, z) in le if y == y2):
            yield le

def partial(le, n):
    return all(not ((x, y) in le and (y, x) in le) for x in range(n) for y in range(n) if x != y)

fails = []

# 1. k cups that only turn up: a chain of distinct arrangements has at most k+1 members.
for k in range(1, 6):
    words = list(range(2 ** k))
    best = 0
    # longest chain under strict subset = k+1 (check by DP)
    longest = {w: 1 for w in words}
    for w in sorted(words, key=lambda w: bin(w).count('1')):
        for v in words:
            if v != w and v & w == v:
                longest[w] = max(longest[w], longest[v] + 1)
    if max(longest.values()) != k + 1:
        fails.append(('chain', k))

# 2. Cups [a <= x] fix the place iff the order is partial.
for n in range(1, 5):
    for le in preorders(n):
        cups = lambda x: tuple((a, x) in le for a in range(n))
        fixes = len({cups(x) for x in range(n)}) == n
        if fixes != partial(le, n):
            fails.append(('cups-fix', n, sorted(le)))

# 3. A step from x to y turns up some cup iff y is not at or below x.
# 4. Toll per cup <=> toll on the whole order, for every machine on small preorders.
for n in range(1, 4):
    for le in preorders(n):
        for x, y in product(range(n), repeat=2):
            turns = any((a, x) not in le and (a, y) in le for a in range(n))
            if turns != ((y, x) not in le):
                fails.append(('turn', n, x, y))

def machines(nstates, nrec, nmoves):
    for rec in product(range(nrec), repeat=nstates):
        for steps in product(product(range(nstates), repeat=nstates), repeat=nmoves):
            for cost in product([0, 1], repeat=nmoves):
                yield rec, steps, cost

for n in range(1, 4):
    for le in preorders(n):
        for rec, steps, cost in machines(3, n, 2):
            whole = all(cost[i] >= 1 for i, f in enumerate(steps) for s in range(3)
                        if (rec[f[s]], rec[s]) not in le)
            per_cup = all(cost[i] >= 1 for a in range(n) for i, f in enumerate(steps) for s in range(3)
                          if (a, rec[s]) not in le and (a, rec[f[s]]) in le)
            if whole != per_cup:
                fails.append(('toll-per-cup', sorted(le), rec, steps, cost))

# 5. One latch cannot carry three places over one visible state (2 outcomes < 3).
# 6. The join rule breaks: strip 0<1<2, record jumps 0->2, stays at 1 and 2.
target = {0: 2, 1: 1, 2: 2}
join = lambda a, b: max(a, b)
if any(all(join(x, g) == target[x] for x in range(3)) for g in range(3)):
    fails.append(('join',))

# 7. Monotone, one-to-one cup encodings: how many cups a branching order needs.
def min_cups(n, lt):
    """Fewest cups k with a one-to-one code where x below y means x's cups are among y's."""
    for k in range(0, n + 1):
        for code in permutations(range(2 ** k), n):
            if all(code[x] & code[y] == code[x] for (x, y) in lt):
                return k
    return None
# three places above a bottom: 0 below 1, 2, 3
if min_cups(4, [(0, 1), (0, 2), (0, 3)]) != 2: fails.append(('fan', min_cups(4, [(0,1),(0,2),(0,3)])))
# two places each below two others: 0,1 below 2,3
if min_cups(4, [(0, 2), (0, 3), (1, 2), (1, 3)]) != 3: fails.append(('crown', min_cups(4, [(0,2),(0,3),(1,2),(1,3)])))
# keeping the order too (x below y exactly when x's cups are among y's): fan 3, crown 4
def min_cups_embed(n, lt):
    le = set(lt) | {(i, i) for i in range(n)}
    for k in range(0, n + 1):
        for code in permutations(range(2 ** k), n):
            if all(((code[x] & code[y] == code[x]) == ((x, y) in le)) for x in range(n) for y in range(n)):
                return k
if min_cups_embed(4, [(0, 1), (0, 2), (0, 3)]) != 3: fails.append(('fan-embed',))
if min_cups_embed(4, [(0, 2), (0, 3), (1, 2), (1, 3)]) != 4: fails.append(('crown-embed',))
# straight strip of n+1 stages needs exactly n cups
for n in range(1, 5):
    if min_cups(n + 1, [(i, j) for i in range(n + 1) for j in range(i + 1, n + 1)]) != n:
        fails.append(('strip', n))

# 8. Turning a cup up merges or revokes; with a growing record it merges.
for n in range(1, 4):
    for le in preorders(n):
        for rec in product(range(n), repeat=3):
            for f in product(range(3), repeat=3):
                injective = len(set(f)) == 3
                for s in range(3):
                    if (rec[f[s]], rec[s]) in le:
                        continue  # no cup turned up
                    a = rec[f[s]]  # the landing cup
                    revokes = any((a, rec[t]) in le and (a, rec[f[t]]) not in le for t in range(3))
                    if not (not injective or revokes):
                        fails.append(('merge-or-revoke', sorted(le), rec, f))
                    grows = all((rec[t], rec[f[t]]) in le for t in range(3))
                    if grows and injective:
                        fails.append(('grow-merges', sorted(le), rec, f))

# 9. Left/right: two places each below the other; a free swap never turns up a cup.
le = {(0, 0), (1, 1), (0, 1), (1, 0)}
if any((a, x) not in le and (a, 1 - x) in le for a in range(2) for x in range(2)):
    fails.append(('left-right',))

print('failures:', len(fails))
for f in fails[:10]:
    print(f)
