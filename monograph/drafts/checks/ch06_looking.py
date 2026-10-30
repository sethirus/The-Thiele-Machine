"""Exhaustive checks of the claims in drafts/06_looking_isnt_keeping.md."""
from itertools import product, combinations
from math import log2
import random
fails = []
S = ['00', '01', '10', '11']
MEASURE = {'00': '00', '01': '01', '10': '11', '11': '10'}
WIPE = {'00': '00', '01': '00', '10': '10', '11': '10'}
if len(set(MEASURE.values())) != 4: fails.append('measure not one-to-one')
if len(set(WIPE.values())) == 4: fails.append('wipe one-to-one')
# blank-display starts are copied
if [MEASURE[s] for s in ['00', '10']] != ['00', '11']: fails.append('copy')
# prepared cases stay apart under WIPE
if WIPE['00'] == WIPE['11']: fails.append('prepared merge')
# watcher learns: candidates 00,10 show different displays after MEASURE
if MEASURE['00'][1] == MEASURE['10'][1]: fails.append('no learning')
# machine's row stays two
if len({MEASURE['00'], MEASURE['10']}) != 2: fails.append('row shrank')
# MEASURE twice is the identity
if any(MEASURE[MEASURE[s]] != s for s in S): fails.append('measure twice')
# the only one-to-one map that copies onto blank and keeps the hidden bit is MEASURE
copies = []
for img in product(S, repeat=4):
    f = dict(zip(S, img))
    if len(set(img)) == 4 and f['00'] == '00' and f['10'] == '11' and all(f[s][0] == s[0] for s in S):
        copies.append(f)
if copies != [MEASURE]: fails.append(('copy unique', copies))
# card under cup: toggle rule undoes itself; erase rule merges for each card
toggle = lambda c, n: (c, n ^ (c == 'red'))
if any(toggle(*toggle(c, n)) != (c, n) for c in ['red', 'blue'] for n in [0, 1]): fails.append('toggle')
# teaching after first look: none with <=2 states, one with 3 (all windows, all maps)
def teaches(n):
    for f in product(range(n), repeat=n):
        if len(set(f)) != n: continue  # zero cost under halving needs one-to-one
        for w in product([0, 1], repeat=n):
            for a, b in combinations(range(n), 2):
                if w[a] == w[b]:
                    x, y = a, b
                    for _ in range(2 * n):
                        x, y = f[x], f[y]
                        if w[x] != w[y]: return True
    return False
if teaches(1) or teaches(2) or not teaches(3): fails.append('teach')
# halving along a run: |D| <= 2^cost |img| when each move's worst pile-up <= 2^cost
random.seed(1)
for _ in range(3000):
    n = random.randint(1, 6)
    moves = [tuple(random.randrange(n) for _ in range(n)) for _ in range(random.randint(1, 4))]
    cost = [max(0, (max(m.count(v) for v in set(m)) - 1).bit_length()) for m in moves]
    D = set(random.sample(range(n), random.randint(1, n)))
    img = set(D)
    for m in moves: img = {m[x] for x in img}
    if len(D) > 2 ** sum(cost) * len(img): fails.append(('halving-run', moves, D))
sync_cases = 0
# finishing together: N starts, first finish at T, one-to-one per column -> N(T+1) distinct
for n in range(1, 6):
    for f in product(range(n), repeat=n):
        for H in product([0, 1], repeat=n):
            for T in range(0, n + 1):
                def orbit(a): 
                    o = [a]
                    for _ in range(T): o.append(f[o[-1]])
                    return o
                A = [a for a in range(n) if H[orbit(a)[T]] and not any(H[x] for x in orbit(a)[:T])]
                if len(A) < 2: continue
                cols_ok = all(len({f[orbit(a)[t]] for a in A}) == len({orbit(a)[t] for a in A}) for t in range(T))
                if cols_ok:
                    sync_cases += 1
                    allst = [orbit(a)[t] for a in A for t in range(T + 1)]
                    if len(set(allst)) != len(A) * (T + 1): fails.append(('sync', f, H, T))
# certainty count: H(p) = H(start|end) + H(q); H(start|end) <= sum of log2 worst pile-ups
def H(p): return -sum(x * log2(x) for x in p if x > 0)
for _ in range(3000):
    n = random.randint(1, 6)
    w = [random.random() for _ in range(n)]; p = [x / sum(w) for x in w]
    moves = [tuple(random.randrange(n) for _ in range(n)) for _ in range(random.randint(1, 3))]
    end = list(range(n))
    for m in moves: end = [m[e] for e in end]
    q = [sum(p[x] for x in range(n) if end[x] == z) for z in range(n)]
    cond = sum(q[z] * H([p[x] / q[z] for x in range(n) if end[x] == z]) for z in range(n) if q[z] > 0)
    if abs(H(p) - (cond + H(q))) > 1e-9: fails.append('chain rule')
    bound = sum(log2(max(m.count(v) for v in set(m))) for m in moves)
    if cond > bound + 1e-9: fails.append('certainty bound')
print('synchronized cases tested:', sync_cases)
print('failures:', len(fails))
for f in fails[:10]: print(f)
