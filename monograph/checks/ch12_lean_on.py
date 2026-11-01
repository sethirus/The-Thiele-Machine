"""Checks of the counting claims in chapter twelve of the book."""
from itertools import permutations, product
from math import ceil, log2, factorial
fails = []
# comparison-sort floors: 3 cards 3, 5 cards 7, 12 cards 29 (Wells: 30 needed)
for n, floor in [(3, 3), (5, 7), (12, 29)]:
    if ceil(log2(factorial(n))) != floor: fails.append(('floor', n))
if factorial(12) != 479001600: fails.append('12!')
# three cards: no 2-question tree sorts all 6 orders (4 < 6); three questions suffice
if 2 ** 2 >= 6 or 2 ** 3 < 6: fails.append('three cards')
# coins: 8 -> 4 -> 2
rows = list(product('HT', repeat=3))
r1 = [r for r in rows if r[0] == 'H']; r2 = [r for r in r1 if r[1] == 'T']
if (len(rows), len(r1), len(r2)) != (8, 4, 2): fails.append('coins')
# twenty questions about a million
if not (1_000_000 < 2 ** 20 < 1_100_000): fails.append('twenty')
# narrower test: the two card observations
orders = list(permutations([1, 2, 3]))
short = [o for o in orders if o.index(1) < o.index(2)]
obs1 = lambda o: o.index(1) < o.index(2)
obs2 = lambda o: o[0] == 3
t = lambda L, ob: {ob(o) for o in L}
if not (t(short, obs1) < t(orders, obs1)): fails.append('obs1 strict')
if t(short, obs2) != t(orders, obs2): fails.append('obs2 same')
# retention: a test keeping one of 2^(k+1) drops k+1 halvings for one paid step
for k in range(1, 6):
    drop = ceil(log2(2 ** (k + 1))) - ceil(log2(1))
    if not drop > k * 1: fails.append('retention')
# produced narrowing with share >= 2^-k: drop <= k * tests
import random; random.seed(3)
for _ in range(2000):
    k = random.randint(1, 3); n = random.randint(1, 64); L = n; tests = 0
    for _ in range(random.randint(0, 6)):
        L = random.randint(max(1, ceil(L / 2 ** k)), L); tests += 1
    if ceil(log2(n)) - ceil(log2(L)) > k * tests: fails.append('share')
# sound groupings: soundness transfers for every key exactly when h refines g (4 items)
items = range(4)
groupings = list(product(range(4), repeat=4))
keys = list(product(range(2), repeat=4))
sound = lambda k, g: all(k[x] == k[y] for x in items for y in items if g[x] == g[y])
refines = lambda h, g: all(g[x] == g[y] for x in items for y in items if h[x] == h[y])
for g in groupings[::7]:
    for h in groupings[::5]:
        transfers = all(sound(k, h) for k in keys if sound(k, g))
        if transfers != refines(h, g): fails.append(('grouping', g, h))
print('failures:', len(fails))
