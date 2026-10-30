"""Checks of the countable claims in drafts/18_five_real_systems.md."""
import random
from itertools import product, combinations
random.seed(17)
fails = []

# ---------------- Casper: accountable safety on small trees ----------------
def casper(parent, epoch, validators, stake, votes, q1, q2):
    """votes: set of (validator, target, t, u). Returns (fork?, slashed set, quorum_slashed?)."""
    total = sum(stake[v] for v in validators)
    def anc(h, k):                      # k-th ancestor
        for _ in range(k):
            h = parent.get(h)
            if h is None: return None
        return h
    def is_anc(a, b):                    # a ancestor-or-equal of b
        while b is not None:
            if a == b: return True
            b = parent.get(b)
        return False
    links = {}
    for (v, h, t, u) in votes:
        links.setdefault((h, t, u), set()).add(v)
    def quorum(vs): return q1(sum(stake[v] for v in vs), total)
    just = {('g', 0)}
    changed = True
    while changed:
        changed = False
        for (h, t, u), vs in links.items():
            if t <= u or epoch[h] != t or not quorum(vs): continue
            p = anc(h, t - u)
            if p is not None and (p, u) in just and (h, t) not in just:
                just.add((h, t)); changed = True
    final = set()
    for (h, v) in just:
        for c, pc in parent.items():
            if pc == h and (c, v + 1) in just and quorum(links.get((c, v + 1, v), set())):
                final.add(h)
    fork = any(not is_anc(a, b) and not is_anc(b, a) for a, b in combinations(final, 2))
    slashed = set()
    vl = list(votes)
    for (v1, h1, t1, u1) in vl:
        for (v2, h2, t2, u2) in vl:
            if v1 != v2: continue
            if t1 == t2 and h1 != h2: slashed.add(v1)
            if t1 > t2 and u2 > u1: slashed.add(v1)
    qs = q2(sum(stake[v] for v in slashed), total)
    return fork, slashed, qs

two_thirds = lambda s, T: 3 * s >= 2 * T
one_third = lambda s, T: 3 * s >= T
parent = {'L1': 'g', 'R1': 'g', 'L2': 'L1', 'R2': 'R1'}
epoch = {'g': 0, 'L1': 1, 'R1': 1, 'L2': 2, 'R2': 2}
cand = [('L1', 1, 0), ('R1', 1, 0), ('L2', 2, 0), ('R2', 2, 0), ('L2', 2, 1), ('R2', 2, 1)]
V3 = ['A', 'B', 'C']; st3 = {v: 1 for v in V3}
nfork = 0
for bits in product([0, 1], repeat=len(cand) * 3):
    votes = {(V3[i // 6], *cand[i % 6]) for i, b in enumerate(bits) if b}
    fork, sl, qs = casper(parent, epoch, V3, st3, votes, two_thirds, one_third)
    if fork:
        nfork += 1
        if not qs: fails.append('casper exhaustive')
if nfork == 0: fails.append('casper: no forks found')
# deeper tree, four validators, random
parent3 = dict(parent, L3='L2', R3='R2', M2='L1')
epoch3 = dict(epoch, L3=3, R3=3, M2=2)
def cands(parent, epoch):
    out = []
    for h in parent:
        t = epoch[h]; p = h; u = t
        while p in parent:
            p = parent[p]; u = epoch[p]; out.append((h, t, u))
    return out
cand3 = cands(parent3, epoch3)
V4 = ['A', 'B', 'C', 'D']; st4 = {'A': 1, 'B': 2, 'C': 1, 'D': 3}
nfork3 = 0
for _ in range(60000):
    votes = {(v, *c) for v in V4 for c in cand3 if random.random() < 0.35}
    fork, sl, qs = casper(parent3, epoch3, V4, st4, votes, two_thirds, one_third)
    if fork:
        nfork3 += 1
        if not qs: fails.append('casper random')
if nfork3 == 0: fails.append('casper: no deep forks')
# the three-validator example in the chapter
ex = {('A', 'L1', 1, 0), ('B', 'L1', 1, 0), ('A', 'L2', 2, 1), ('B', 'L2', 2, 1),
      ('B', 'R1', 1, 0), ('C', 'R1', 1, 0), ('B', 'R2', 2, 1), ('C', 'R2', 2, 1)}
fork, sl, qs = casper(parent, epoch, V3, st3, ex, two_thirds, one_third)
if not (fork and sl == {'B'} and qs): fails.append('casper example')
# one validator: one vote finalizes genesis, nobody slashed
fork, sl, qs = casper({'c': 'g'}, {'g': 0, 'c': 1}, ['A'], {'A': 1}, {('A', 'c', 1, 0)}, two_thirds, one_third)
if sl: fails.append('one validator')
# take away the overlap (quorum = half): a fork with nobody slashed
fork, sl, qs = casper(parent, epoch, ['A', 'B'], {'A': 1, 'B': 1},
                      {('A', 'L1', 1, 0), ('A', 'L2', 2, 1), ('B', 'R1', 1, 0), ('B', 'R2', 2, 1)},
                      lambda s, T: 2 * s >= T, one_third)
if not (fork and not sl): fails.append('overlap needed')

# ---------------- Gas: one slot in one transaction ----------------
def sstore(slot, new):
    orig, cur, warm, gas, ref = slot
    if not warm: gas += 2100
    if cur == new: gas += 100
    elif cur == orig: gas += 20000 if orig == 0 else 2900
    else: gas += 100
    if cur != new:
        if orig != 0 and cur != 0 and new == 0: ref += 4800
        if orig != 0 and cur == 0: ref -= 4800
        if new == orig: ref += 19900 if orig == 0 else 2800
    return (orig, new, True, gas, ref)
def pencil(cur, new):          # the chapter's simplified rule from a zero original
    cost = 20000 if (cur == 0 and new != 0) else 100
    back = 19900 if (cur != 0 and new == 0) else 0
    return cost, back
for warm0 in [False, True]:
    for n in range(1, 7):
        for seq in product([0, 1, 2], repeat=n):
            s = (0, 0, warm0, 0, 0)
            for x in seq:
                g0, r0, c0 = s[3], s[4], s[1]
                s = sstore(s, x)
                cost, back = pencil(c0, x)
                extra = 0 if (warm0 or g0 > 0) else 2100
                if s[3] - g0 != cost + extra or s[4] - r0 != back: fails.append('pencil rule')
                net = s[3] - s[4]
                # the two lines on the sheet
                if s[1] == 0 and net < 0: fails.append('line zero')
                if s[1] != 0 and net < 20000: fails.append('line nonzero')
            if s[1] != 0 and s[3] - s[4] < (20000 if warm0 else 22100): fails.append('floor')
s = sstore(sstore((0, 0, False, 0, 0), 1), 0)
if (s[3], s[4], s[3] - s[4]) != (22200, 19900, 2300): fails.append('2300')
s1 = sstore((0, 0, False, 0, 0), 1)
if s1[3] - s1[4] != 22100: fails.append('22100')
used = 21000 + 22200
cap = used // 5
pays = used - min(19900, cap)
if (used, cap, pays, pays - 21000) != (43200, 8640, 34560, 13560): fails.append('cap arithmetic')
if 22200 - min(19900, 22200 // 5) != 17760: fails.append('17760')
if not (100000 / 3600 < 28): fails.append('memoir hours')

# ---------------- The wrapper: floor and no overcharge iff unit pricing ----------------
for _ in range(3000):
    S, I = 3, 2
    step = {(s, i): random.randrange(S) for s in range(S) for i in range(I)}
    flag = [random.randint(0, 1) for _ in range(S)]
    cost = {(s, i): random.choice([0, 0, 1, 1, 2]) for s in range(S) for i in range(I)}
    commits = lambda s, i: (not flag[s]) and flag[step[(s, i)]]
    floor_ok = ceil_ok = True
    for s0 in range(S):
        for n in range(1, 5):
            for prog in product(range(I), repeat=n):
                s, c, k = s0, 0, 0
                for i in prog:
                    c += cost[(s, i)]; k += commits(s, i); s = step[(s, i)]
                if c < k: floor_ok = False
                if c > k: ceil_ok = False
    unit = all(cost[(s, i)] == (1 if commits(s, i) else 0) for s in range(S) for i in range(I))
    if (floor_ok and ceil_ok) != unit: fails.append('wrapper')

# ---------------- A permanent write merges on its own yes side ----------------
for n in range(1, 5):
    for f in product(range(n), repeat=n):
        for read in product([0, 1], repeat=n):
            if any(read[s] and not read[f[s]] for s in range(n)): continue   # never turns off
            raised = [s for s in range(n) if not read[s] and read[f[s]]]
            for s in raised:
                src = [t for t in range(n) if read[t]] + [s]
                if not all(read[f[t]] for t in src): fails.append('yes side lands')
                if len({f[t] for t in src}) == len(src): fails.append('merge')

# ---------------- The quote can't recover an unmeasured flag ----------------
H = lambda a, b: (a * 31 + b * 7 + 3) % 101
def quote(log, nonce):
    r = 0
    for m in log: r = H(r, m)
    return (r * 13 % 97, nonce)
if quote([], 5) != quote([], 5): fails.append('quote')       # flag never enters
# always-yes check fits sign/verify
sign = lambda k, m: 0
verify = lambda pk, m, sig: True
if not verify('nokey', 'msg', 12345): fails.append('always yes')

# ---------------- Certificate transparency, RFC 9162 ----------------
def leaf(x): return ('leaf', x)
def node(a, b): return ('node', a, b)
def k_of(n):
    k = 1
    while k * 2 < n: k *= 2
    return k
def mth(D):
    if len(D) == 1: return leaf(D[0])
    k = k_of(len(D)); return node(mth(D[:k]), mth(D[k:]))
def path(m, D):
    if len(D) == 1: return []
    k = k_of(len(D))
    return path(m, D[:k]) + [mth(D[k:])] if m < k else path(m - k, D[k:]) + [mth(D[:k])]
def subproof(m, D, b):
    n = len(D)
    if m == n: return [] if b else [mth(D)]
    k = k_of(n)
    return subproof(m, D[:k], b) + [mth(D[k:])] if m <= k else subproof(m - k, D[k:], False) + [mth(D[:k])]
def verify_incl(m, N, h, root, P, sides=None):
    if m >= N: return False
    fn, sn, r = m, N - 1, h
    for p in P:
        if sn == 0: return False
        if fn & 1 or fn == sn:
            r = node(p, r)
            if sides is not None: sides.append('L')
            if not fn & 1:
                while not fn & 1 and fn != 0: fn >>= 1; sn >>= 1
        else:
            r = node(r, p)
            if sides is not None: sides.append('R')
        fn >>= 1; sn >>= 1
    return sn == 0 and r == root
def verify_cons(M, N, u, v, P):
    if not (0 < M < N): return False
    if M & (M - 1) == 0: P = [u] + P
    if not P: return False
    fn, sn = M - 1, N - 1
    while fn & 1: fn >>= 1; sn >>= 1
    fr = sr = P[0]
    for c in P[1:]:
        if sn == 0: return False
        if fn & 1 or fn == sn:
            fr = node(c, fr); sr = node(c, sr)
            if not fn & 1:
                while not fn & 1 and fn != 0: fn >>= 1; sn >>= 1
        else:
            sr = node(sr, c)
        fn >>= 1; sn >>= 1
    return sn == 0 and fr == u and sr == v
for N in range(1, 21):
    D = list(range(N)); R = mth(D)
    for m in range(N):
        P = path(m, D)
        if not verify_incl(m, N, leaf(m), R, P): fails.append('incl %d %d' % (m, N))
        if len(P) > 1 and P[0] != P[1]:
            if verify_incl(m, N, leaf(m), R, [P[1], P[0]] + P[2:]): fails.append('order matters')
    if verify_incl(N, N, leaf(0), R, []): fails.append('m=N')
    for M in range(1, N):
        if not verify_cons(M, N, mth(D[:M]), R, subproof(M, D, True)): fails.append('cons %d %d' % (M, N))
        if verify_cons(M, N, mth(D[:M] [:-1] + [99]) if M > 1 else leaf(99), R, subproof(M, D, True)):
            fails.append('cons tamper')
# the seven cards
D7 = list(range(7)); d = leaf
a, b, c = node(d(0), d(1)), node(d(2), d(3)), node(d(4), d(5))
L, R = node(a, b), node(c, d(6))
root = node(L, R)
if mth(D7) != root: fails.append('seven root')
expect = {3: ([d(2), a, R], 'LLR'), 0: ([d(1), b, R], 'RRR'), 4: ([d(5), d(6), L], 'RRL'), 6: ([c, L], 'LL')}
for m, (P, sd) in expect.items():
    sides = []
    if path(m, D7) != P or not verify_incl(m, 7, d(m), root, P, sides) or ''.join(sides) != sd:
        fails.append('card leaf %d' % m)
if mth(D7[:4]) != L or subproof(4, D7, True) != [R] or not verify_cons(4, 7, L, root, [R]):
    fails.append('four to seven')
if node(d(3), d(2)) == b: fails.append('swap')

print('casper forks checked:', nfork, '+', nfork3)
print('failures:', len(fails), sorted(set(fails))[:10])
