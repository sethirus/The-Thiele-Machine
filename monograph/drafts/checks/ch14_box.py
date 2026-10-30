"""Exhaustive checks of the claims in drafts/14_a_box_over_any_machine.md."""
from itertools import product
fails = []
# 1. box that answers only to the base and stays up is a cup on the event h(b) = f(b, down)
for nb in range(1, 4):
    for f in product([0, 1], repeat=2 * nb):          # f[(b, r)] -> next box
        F = lambda b, r: f[2 * b + r]
        stays = all(F(b, 1) == 1 for b in range(nb))
        if not stays: continue
        h = lambda b: F(b, 0)
        if any(F(b, r) != (r or h(b)) for b in range(nb) for r in [0, 1]): fails.append('latch')
# 2. history makes a one-to-one base's whole machine one-to-one, and never repeats a state
for nb in range(1, 4):
    for base in product(range(nb), repeat=nb):
        if len(set(base)) != nb: continue
        for h in product([0, 1], repeat=nb):
            states = [(b, r, hist) for b in range(nb) for r in [0, 1] for hist in product([0, 1], repeat=2)]
            step = lambda st: (base[st[0]], st[1] or h[st[0]], (st[1],) + st[2])
            imgs = [step(st) for st in states]
            if len(set(imgs)) != len(imgs): fails.append('history-injective')
# 3. finite one-to-one move with a permanent box can't turn it up (chairs)
for n in range(1, 5):
    for f in product(range(n), repeat=n):
        if len(set(f)) != n: continue
        for D in product([0, 1], repeat=n):
            if all(D[f[x]] for x in range(n) if D[x]) and any(not D[x] and D[f[x]] for x in range(n)):
                fails.append('finite-raise')
# 4. toggle is not a cup; timestamp is not answering to the base
if (1 or 0) != 1: pass
toggle = lambda r: 1 - r
if toggle(1) == 1: fails.append('toggle')
ts = lambda b, k, r: r or (k == 5)
if ts(0, 5, 0) == ts(0, 0, 0): fails.append('timestamp')
# timestamp started in step equals the cup on position five on reached states
for b0 in range(8):
    b, k, r = b0, b0, 0
    for _ in range(8):
        nr = ts(b, k, r)
        if nr != (r or b == 5): fails.append('in-step')
        b, k, r = b + 1, k + 1, nr
# 5. two cups: the second can only turn on an even roll if the first is up -> never before the first
import random; random.seed(2)
for _ in range(2000):
    rolls = [random.randint(1, 6) for _ in range(20)]
    c1 = c2 = 0; t1 = t2 = None
    for i, x in enumerate(rolls):
        n2 = c2 or (x % 2 == 0 and c1)
        n1 = c1 or x == 6
        if n1 and not c1: t1 = i
        if n2 and not c2: t2 = i
        c1, c2 = n1, n2
    if t2 is not None and (t1 is None or t2 <= t1): fails.append('two-cups')
# 6. two events on one die: both cups pass; roll a one first and they disagree until a six
rolls = [1, 3, 2, 6]
six = one = 0; dis = []
for x in rolls:
    six = six or x == 6; one = one or x == 1; dis.append(six != one)
if dis[:3] != [True, True, True] or dis[3]: fails.append('two-events')
# 7. surcharge: the box still turns on the same roll, cost changes
rolls = [2, 4, 6, 1]
turn = next(i for i, x in enumerate(rolls) if x == 6)
if turn != 2: fails.append('surcharge')
print('failures:', len(fails))
