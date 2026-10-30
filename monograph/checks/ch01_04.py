"""Exhaustive checks of the claims in the first chapters on small machines."""
from itertools import product
import math
fails = []
def runs(f, s, n):
    seq = [s]
    for _ in range(n): seq.append(f[seq[-1]])
    return seq

for n in range(1, 6):
    for f in product(range(n), repeat=n):
        inj = len(set(f)) == n
        for s in range(n):
            seq = runs(f, s, 2 * n + 2)
            # step law: first repeat lands on start, or two distinct visited states share the landing
            seen = {}
            for t, x in enumerate(seq):
                if x in seen:
                    j = seen[x]
                    if j > 0 and not (seq[j - 1] != seq[t - 1] and f[seq[j - 1]] == f[seq[t - 1]]):
                        fails.append(('step', f, s))
                    break
                seen[x] = t
            # keeping: done set D closed, start outside, run enters D -> never back to start (merge)
        for D in product([0, 1], repeat=n):
            closed = all(D[f[x]] for x in range(n) if D[x])
            if not closed: continue
            for s in range(n):
                if D[f[s]] and not D[s]:
                    # chairs: finite, permanent, flip -> the move merges
                    if inj: fails.append(('chairs', f, D, s))
            # reversible keeps nothing: injective f never takes a not-done start into D
            if inj and any(not D[s] and any(D[x] for x in runs(f, s, n)) for s in range(n)):
                fails.append(('reversible', f, D))
        # merge or revoke, no permanence assumed
        for D in product([0, 1], repeat=n):
            if any(not D[s] and D[f[s]] for s in range(n)):
                if inj and not any(D[t] and not D[f[t]] for t in range(n)):
                    fails.append(('merge-or-revoke', f, D))

# room to hold: u outside H, F(H) in H, |H| = K; within K+1 steps from u two distinct states share a successor
for n in range(2, 6):
    for f in product(range(n), repeat=n):
        for H in product([0, 1], repeat=n):
            K = sum(H)
            if K == 0 or not all(H[f[x]] for x in range(n) if H[x]): continue
            for u in range(n):
                if H[u] or not H[f[u]]: continue
                seq = runs(f, u, K + 1)
                srcs = seq[:K + 1]
                if not any(a != b and f[a] == f[b] for a in srcs for b in srcs):
                    fails.append(('hold', f, H, u))

# eight-box strip: nine strips, stay-full rule merges 7 and 8 marks
strips = [(1,) * k + (0,) * (8 - k) for k in range(9)]
nxt = {s: strips[min(strips.index(s) + 1, 8)] for s in strips}
if nxt[strips[7]] != nxt[strips[8]]: fails.append(('strip',))

# smallest machine: on 2 states (0 NO, 1 YES), the only one-move tables that settle with done staying done
ok = [f for f in product(range(2), repeat=2) if f[1] == 1 and f[0] == 1]
good = [f for f in product(range(2), repeat=2) if f[1] == 1 and any(f[s] == 1 and s == 0 for s in range(2))]
if good != [(1, 1)]: fails.append(('latch', good))

# squeeze: m+k into m chairs puts at least ceil((m+k)/m) on one chair
for m in range(1, 9):
    for k in range(0, 9):
        for g in product(range(m), repeat=m + k):
            if max(g.count(c) for c in range(m)) < math.ceil((m + k) / m):
                fails.append(('squeeze', m, k)); break
        if m + k > 7: break

# fitting a coin: x some move lands on -> coin machine settles; window can't tell (x,NO) start from (x,YES)
for n in range(1, 5):
    for f in product(range(n), repeat=n):
        for x in range(n):
            lands = any(f[s] == x for s in range(n))
            g = lambda st: (f[st[0]], st[1] or f[st[0]] == x)
            settles = any(any(g_st[1] for g_st in [g((s, False))]) for s in range(n))
            if lands != settles: fails.append(('coin', f, x))
            if lands:
                reach_up = any(g((s, False)) == (x, True) for s in range(n))
                if not reach_up: fails.append(('coin-up', f, x))

print('failures:', len(fails))
for f in fails[:10]: print(f)
