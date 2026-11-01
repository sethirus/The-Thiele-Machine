"""Checks of the countable claims in chapter sixteen of the book (the four doors)."""
import random
from itertools import product
fails = []
P = lambda x: x % 2 == 0          # the checked property: even
f = lambda x: x * 3               # the true answer
F = lambda x: x * 3 if P(x) else -1   # the shortcut: right only when the property holds
LONG = 1000

def rand_prog(rng, n=40, vals=6):
    out = []
    for _ in range(n):
        r = rng.random()
        out.append(('WRITE', rng.randrange(vals)) if r < .2 else ('CHECK', None) if r < .35 else ('ASK', None))
    return out
def answer(boxed, x, st):
    if boxed: st[0] += 1; return F(x)
    st[0] += LONG; return f(x)
def door1(prog, M):                       # permanent boxes, editions wrap around after M
    x, v, boxes, st, bad = 0, 0, set(), [0], 0
    for op, a in prog:
        if op == 'WRITE': x, v = a, (v + 1) % M
        elif op == 'CHECK' and P(x): boxes.add(v)
        elif op == 'ASK': bad += answer(v in boxes, x, st) != f(x)
    return st[0], bad
def door2(prog, M):                       # permanent boxes, editions never reused; then spent for good
    x, v, spent, boxes, st, bad = 0, 0, False, set(), [0], 0
    for op, a in prog:
        if op == 'WRITE':
            x = a
            if v + 1 < M and not spent: v += 1
            else: spent = True
        elif op == 'CHECK' and P(x) and not spent: boxes.add(v)
        elif op == 'ASK': bad += answer((not spent) and v in boxes, x, st) != f(x)
    return st[0], bad
def door2_fresh(prog):                    # editions never run out
    x, v, boxes, st, bad = 0, 0, set(), [0], 0
    for op, a in prog:
        if op == 'WRITE': x, v = a, v + 1
        elif op == 'CHECK' and P(x): boxes.add(v)
        elif op == 'ASK': bad += answer(v in boxes, x, st) != f(x)
    return st[0], bad
def door3(prog):                          # one box, knocked down by every write
    x, box, st, bad = 0, 0, [0], 0
    for op, a in prog:
        if op == 'WRITE': x, box = a, 0
        elif op == 'CHECK' and P(x): box = 1
        elif op == 'ASK': bad += answer(box, x, st) != f(x)
    return st[0], bad
def door4(prog):                          # boxes keyed to the value checked
    x, boxes, st, bad = 0, set(), [0], 0
    for op, a in prog:
        if op == 'WRITE': x = a
        elif op == 'CHECK' and P(x): boxes.add(x)
        elif op == 'ASK': bad += answer(x in boxes, x, st) != f(x)
    return st[0], bad, len(boxes)

rng = random.Random(2)
N = 20000
wrong = {1: 0, 2: 0, 3: 0, 4: 0, 'fresh': 0}; steps = {1: 0, 2: 0, 3: 0, 4: 0, 'plain': 0}; most = 0
for _ in range(N):
    p = rand_prog(rng)
    s1, b1 = door1(p, 4); s2, b2 = door2(p, 4); s3, b3 = door3(p); s4, b4, nb = door4(p); sf, bf = door2_fresh(p)
    wrong[1] += b1; wrong[2] += b2; wrong[3] += b3; wrong[4] += b4; wrong['fresh'] += bf
    steps[1] += s1; steps[2] += s2; steps[3] += s3; steps[4] += s4
    steps['plain'] += sum(LONG for o, _ in p if o == 'ASK'); most = max(most, nb)
table = {k: (wrong[k], steps[k] // N) for k in (1, 2, 3, 4)}
print('plain long way, average steps:', steps['plain'] // N)
for k in (1, 2, 3, 4): print('door', k, 'wrong answers:', table[k][0], 'average steps:', table[k][1])
print('door 2 with editions that never run out, wrong answers:', wrong['fresh'])
print('door 4, most boxes any program used:', most)
if wrong[1] == 0 or wrong[2] or wrong[3] or wrong[4] or wrong['fresh']: fails.append('doors')
if most > 3: fails.append('door 4 boxes')            # only 0, 2, 4 are even

# the four-move failure with two editions
if door1([('CHECK', None), ('WRITE', 1), ('WRITE', 3), ('ASK', None)], 2)[1] != 1: fails.append('four moves')
# door 3 merges at the wipe even when the write alone is one-to-one, and at the passing check
write = lambda s: (1 - s[0], 0)
states = list(product([0, 1], [0, 1]))
if len({write(s) for s in states}) == len(states): fails.append('wipe merges')
check = lambda s: (s[0], 1) if P(s[0]) else s
if check((0, 0)) != check((0, 1)): fails.append('check merges')
# the soundness argument for door 2, exhaustively on short programs: wrong answers never happen
for L in range(1, 7):
    for prog in product([('WRITE', 0), ('WRITE', 1), ('CHECK', None), ('ASK', None)], repeat=L):
        if door2_fresh(prog)[1]: fails.append('door 2 sound')

# big data: a list of n numbers; finding a value-keyed box means reading the list
n = 1000
look_by_value = n          # read every entry to know which list this is
look_by_container = 1      # one glance at the container's box
check_sorted = n - 1       # comparisons to check "sorted"
if not (look_by_value >= check_sorted): fails.append('value lookup costs a check')
# a short fingerprint lets two different lists share a box
fp = lambda lst: sum(lst) % 7
a, b = [1, 2, 3], [3, 2, 1]
if not (fp(a) == fp(b) and a == sorted(a) and b != sorted(b)): fails.append('fingerprint collision')

# ---------------- the theorem: under the two conditions, wrong or at most (E+1)//2 unlocked rounds ----------------
def up_maps(E):
    S = list(range(1 << E))
    return [[t for t in S if t & s == s] for s in S]
def play(guard, wg, chk, wb, rounds):
    c, u, wrong = 0, 0, False
    for _ in range(rounds):
        c = chk[wg[c]]
        if guard[c]: u += 1
        c = wb[c]
        if guard[c]: wrong = True
    return u, wrong
for E in (1, 2):
    opts = up_maps(E)
    for guard in product([0, 1], repeat=1 << E):
        for wg in product(*opts):
            for chk in product(*opts):
                for wb in product(*opts):
                    u, w = play(guard, wg, chk, wb, E + 3)
                    if not w and 2 * u > E + 1: fails.append('doors theorem E=%d' % E)
rng2 = random.Random(16)
reached = {}
for E in (3, 4):
    opts = up_maps(E)
    for _ in range(100000):
        guard = [rng2.randint(0, 1) for _ in range(1 << E)]
        wg, chk, wb = ([rng2.choice(o) for o in opts] for _ in range(3))
        u, w = play(guard, wg, chk, wb, E + 3)
        if not w:
            reached[E] = max(reached.get(E, 0), u)
            if 2 * u > E + 1: fails.append('doors theorem E=%d' % E)
# a box that comes down unlocks every round, honestly
if play([0, 1], [0, 1], [1, 1], [0, 0], 10) != (10, False): fails.append('toggle every round')
# door four's room: keeping every checked value unlocked at once needs a distinct memory state per set
for k in range(1, 6):
    sets = list(product([0, 1], repeat=k))
    for a, b in [(x, y) for x in sets for y in sets if x != y]:
        if not any(a[i] != b[i] for i in range(k)): fails.append('2^k')
    if len(sets) != 2 ** k: fails.append('2^k count')
print('doors theorem bound reached by random machines:', reached)

print('failures:', len(fails), fails[:10])
