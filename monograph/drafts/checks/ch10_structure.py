"""Checks of the countable claims in drafts/10_what_structure_is.md."""
from itertools import product
fails = []
# sameness <-> sorting, on every relation on up to 4 things
for n in range(1, 5):
    pairs = [(a, b) for a in range(n) for b in range(n)]
    for bits in product([0, 1], repeat=len(pairs)):
        R = {p for p, b in zip(pairs, bits) if b}
        equiv = all((a, a) in R for a in range(n)) and all((b, a) in R for (a, b) in R) and \
            all((a, c) in R for (a, b) in R for (b2, c) in R if b == b2)
        if not equiv: continue
        groups = {frozenset(b for b in range(n) if (a, b) in R) for a in range(n)}
        # groups never half-overlap and cover everything
        if any(g & h and g != h for g in groups for h in groups) or set().union(*groups) != set(range(n)):
            fails.append(('sort', n, sorted(R)))
        # back to the relation
        R2 = {(a, b) for g in groups for a in g for b in g}
        if R2 != R: fails.append(('roundtrip', n))
# an order is buckets plus one-way doors: on every preorder of up to 4 places
for n in range(1, 5):
    pairs = [(x, y) for x in range(n) for y in range(n) if x != y]
    for bits in product([0, 1], repeat=len(pairs)):
        le = {(x, x) for x in range(n)} | {p for p, b in zip(pairs, bits) if b}
        if not all((x, z) in le for (x, y) in le for (y2, z) in le if y == y2): continue
        bucket = lambda x: frozenset(y for y in range(n) if (x, y) in le and (y, x) in le)
        # at or below depends only on buckets, and between distinct buckets goes one way
        for x, y in product(range(n), repeat=2):
            for x2 in bucket(x):
                for y2 in bucket(y):
                    if ((x, y) in le) != ((x2, y2) in le): fails.append('bucket-dep')
            if bucket(x) != bucket(y) and (x, y) in le and (y, x) in le: fails.append('one-way')
# the description-length numbers
def pattern_cost(block, exceptions, field=5): return 1 + 5 + len(block) + 5 + field * exceptions
if pattern_cost('01', 0) != 13 or pattern_cost('01', 2) != 23 or pattern_cost('01', 4) != 33 \
   or pattern_cost('01', 5) != 38 or pattern_cost('010100', 0) != 17 or pattern_cost('01', 3, 7) != 34 \
   or pattern_cost('0' * 32, 0) != 43:
    fails.append('mdl')
row = '01' * 16
flipped = list(row)
for i in [5, 11, 17, 23, 29]: flipped[i] = '1' if flipped[i] == '0' else '0'
if ''.join(flipped) != ('010100' * 6)[:32]: fails.append('flip-fit')
print('failures:', len(fails))
