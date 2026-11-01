"""Checks of the countable claims in chapter twenty of the book."""
import math, random
from itertools import product
random.seed(19)
fails = []
log2 = math.log2

def H(p):
    return -sum(x * log2(x) for x in p.values() if x > 0)
def push(p, f):
    q = {}
    for x, px in p.items():
        q[f[x]] = q.get(f[x], 0) + px
    return q

# four equally likely cards: A, B -> X, C -> Y, D -> Z loses half a bit
p4 = {c: 0.25 for c in 'ABCD'}
if abs(H(p4) - H(push(p4, {'A': 'X', 'B': 'X', 'C': 'Y', 'D': 'Z'})) - 0.5) > 1e-12: fails.append('four cards')
# eight equally likely cards to one box: three bits
p8 = {i: 1 / 8 for i in range(8)}
if abs(H(p8) - H(push(p8, {i: 0 for i in range(8)})) - 3) > 1e-12: fails.append('eight cards')

def rand_spread(xs):
    w = [random.random() ** 3 for _ in xs]
    s = sum(w)
    return {x: wi / s for x, wi in zip(xs, w)}

for _ in range(4000):
    n = random.randint(1, 7)
    xs = list(range(n))
    p = rand_spread(xs)
    # a reshuffle keeps the bits
    perm = xs[:]; random.shuffle(perm)
    if abs(H(p) - H(push(p, dict(zip(xs, perm))))) > 1e-9: fails.append('reshuffle')
    # a move never adds bits; per-state sum; max loss = log2 of biggest pile
    f = {x: random.randrange(n) for x in xs}
    q = push(p, f)
    terms = [p[x] * (log2(q[f[x]]) - log2(p[x])) for x in xs if p[x] > 0]
    loss = H(p) - H(q)
    if abs(loss - sum(terms)) > 1e-9 or min(terms) < -1e-12: fails.append('per-state sum')
    piles = {}
    for x in xs: piles.setdefault(f[x], []).append(x)
    K = max(len(v) for v in piles.values())
    if loss > log2(K) + 1e-9: fails.append('loss <= log2 K')
    if K > 1 and loss < 1e-12: fails.append('merge loses something')
    big = max(piles.values(), key=len)
    even = {x: (1 / K if x in big else 0) for x in xs}
    if abs(H(even) - H(push(even, f)) - log2(K)) > 1e-9: fails.append('even pile reaches log2 K')
    # no spread on m places holds more than log2 m
    m = random.randint(1, 6)
    if H(rand_spread(range(m))) > log2(m) + 1e-9: fails.append('H <= log2 m')
    # the one-line reason on the page: q ln((1/m)/q) <= 1/m - q, summed
    qs = list(rand_spread(range(random.randint(1, m))).values())
    lhs = sum(x * math.log((1 / m) / x) for x in qs if x > 0)
    if lhs > sum(1 / m - x for x in qs) + 1e-12 or sum(1 / m - x for x in qs) > 1e-12: fails.append('log line')

# a permanent flip from the even spread on m + k states into m yes-states
for m in range(1, 5):
    for k in range(1, 5):
        best = None
        for f in product(range(m), repeat=k):          # old yes-states stay put? no: any map into yes
            for g in product(range(m), repeat=m):
                fmap = {('y', i): g[i] for i in range(m)}
                fmap.update({('n', j): f[j] for j in range(k)})
                p = {x: 1 / (m + k) for x in fmap}
                loss = H(p) - H(push(p, fmap))
                best = loss if best is None else min(best, loss)
                if loss < max(log2((m + k) / m), 2 * k / (m + k)) - 1e-9: fails.append('flip bound %d %d' % (m, k))
        if k % m == 0 and abs(best - log2((m + k) / m)) > 1e-9: fails.append('first bound reached %d %d' % (m, k))
        if k <= m and abs(best - 2 * k / (m + k)) > 1e-9: fails.append('second bound reached %d %d' % (m, k))
# worst case: half on each of a merging pair is a full bit
if abs(H({0: .5, 1: .5}) - H(push({0: .5, 1: .5}, {0: 0, 1: 0})) - 1) > 1e-12: fails.append('full bit')
# a known state loses nothing
if H(push({3: 1.0}, {3: 0})) != 0: fails.append('known')

# the numbers
kB, T = 1.380649e-23, 300
floor = kB * T * math.log(2)
if not (2.8e-21 < floor < 3.0e-21): fails.append('three zeptojoules')
thin = 2 * math.log(2) / 1001                      # in units of kT
if round(1 / thin) != 722 or round(math.log(2) / thin) != 500: fails.append('one newcomer, a thousand yes')
if not (log2(1001 / 1000) < 2 / 1001): fails.append('which bound is bigger')
if not (30000 < 100e-18 / floor < 40000): fails.append('CMOS ratio')

# four states, first reads no: entering state collides with nobody, yet a collision happens
f4 = {0: 1, 1: 2, 2: 2, 3: 3}; yes4 = {1, 2, 3}
if not all(f4[s] in yes4 for s in yes4): fails.append('stays up')
if [x for x in f4 if f4[x] == f4[0]] != [0] or len(set(f4.values())) == 4: fails.append('entering state')

# (the Ladyman/Sagawa identity is a physics premise, argued on the page; nothing to count here)

# Bennett's walker: (2p-1) ln(p/(1-p)) >= 0, zero only at 1/2; ln((1+v)/(1-v)) >= 2v
for i in range(1, 1000):
    p = i / 1000
    r = (2 * p - 1) * math.log(p / (1 - p))
    if r < 0 or (i != 500 and r <= 0): fails.append('walker rate')
    v = abs(2 * p - 1)
    if 0 < v < 1 and math.log((1 + v) / (1 - v)) < 2 * v: fails.append('walker floor')

# experiments: within error bars
if not (abs(0.71 - math.log(2)) <= 0.03 and 0.05 - 2 * 0.03 <= 0): fails.append('Jun et al.')
# Hong et al. 2016: 1.45 +- 0.35 kT against ln 2 is about 2.2 of their deviations, so the page
# quotes "within two standard deviations" as their report, not as a fact of its own
if not (2.1 < (1.45 - math.log(2)) / 0.35 < 2.3): fails.append('Hong arithmetic')
# Jarzynski numbers for nine in ten successes
p = 0.9
if round(math.log(2 * p), 3) != 0.588 or round(math.log(2) + p * math.log(p) + (1 - p) * math.log(1 - p), 3) != 0.368:
    fails.append('Jarzynski')
# Murashita et al.: a tenth of the box gives log 10
if abs(math.log(1 / 0.1) - math.log(10)) > 1e-12: fails.append('log ten')

# every scale pays the same way: exhaustive on small fine machines
def orbit_repeats(F, A, x):
    seen = set()
    while x in A and x not in seen:
        seen.add(x); x = F[x]
    return x in seen
for n in range(1, 5):
    A = list(range(n)); X = A + ['out']
    for Fv in product(X, repeat=n):
        F = dict(zip(A, Fv))
        merges = len(set(Fv)) < n
        leaves = 'out' in Fv
        for c in range(1, n + 1):
            for piv in product(range(c), repeat=n):
                if set(piv) != set(range(c)): continue
                pi = dict(zip(A, piv))
                f = {}
                ok = True
                for x in A:
                    if F[x] == 'out': continue
                    if f.setdefault(pi[x], pi[F[x]]) != pi[F[x]]: ok = False; break
                if not ok or len(f) < c: continue      # coarse rule must be defined on every coarse state
                if len(set(f.values())) < c and not (merges or leaves):
                    fails.append('every scale')

print('failures:', len(fails), sorted(set(fails))[:10])
