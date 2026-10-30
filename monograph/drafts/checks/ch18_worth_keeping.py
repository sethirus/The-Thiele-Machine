"""Checks of the countable claims in drafts/18_which_box_is_worth_keeping.md."""
import random
from fractions import Fraction as F
from itertools import product, permutations
random.seed(18)
fails = []

# ---------------- three states: blank, once, twice ----------------
S = ['blank', 'once', 'twice']
yes = {'blank': 0, 'once': 1, 'twice': 1}
step = {'flip': {'blank': 'once', 'once': 'once', 'twice': 'twice'},
        'smooth': {'blank': 'blank', 'once': 'twice', 'twice': 'twice'}}
def merges(i): return len(set(step[i].values())) < len(S)
if not (merges('flip') and merges('smooth')): fails.append('both forget')
if [s for s in S if step['flip'][s] == 'once'] != ['blank', 'once']: fails.append('flip lands')
raises = lambda s, i: (not yes[s]) and yes[step[i][s]]
if any(raises(s, 'smooth') for s in S): fails.append('smooth raises nothing')
# only renaming that respects the moves is the identity
autos = [p for p in permutations(S) if all(dict(zip(S, p))[step[i][s]] == step[i][dict(zip(S, p))[s]]
                                            for i in step for s in S)]
if autos != [tuple(S)]: fails.append('automorphisms')
keys = [(s, i) for s in S for i in step]
def runs(n):
    for s0 in S:
        for prog in product(step, repeat=n):
            yield s0, prog
naming_free, with_record = [], []
for vals in product([0, 1, 2], repeat=len(keys)):
    c = dict(zip(keys, vals))
    ok = all(c[(s, i)] == 0 for (s, i) in keys if step[i][s] == s)            # changes nothing: free
    ok &= all(c[(s, i)] == 0 for (s, i) in keys if not merges(i))             # forgets nothing: free (vacuous here)
    ok &= c[('blank', 'flip')] == 1
    # renaming: only the identity, so nothing to check beyond it
    if not ok: continue
    naming_free.append(c)
    floor = ceil = True
    for n in range(1, 5):
        for s0, prog in runs(n):
            s, cost, k = s0, 0, 0
            for i in prog:
                cost += c[(s, i)]; k += raises(s, i); s = step[i][s]
            floor &= cost >= k; ceil &= cost <= k
    if floor and ceil: with_record.append(c)
rise_only = {k: (1 if k == ('blank', 'flip') else 0) for k in keys}
merge_price = dict(rise_only); merge_price[('once', 'smooth')] = 1
if rise_only not in naming_free or merge_price not in naming_free: fails.append('both meet the list')
if with_record != [rise_only]: fails.append('record requirement picks rise-only')
if merge_price[('once', 'smooth')] == rise_only[('once', 'smooth')]: fails.append('they disagree on smooth')

# ---------------- a pointer, when it exists, is unique on reachable states ----------------
for _ in range(5000):
    n = random.randint(1, 6)
    reach = [x for x in range(n) if random.random() < 0.7] or [0]
    events = [frozenset(x for x in range(n) if random.random() < 0.5) for _ in range(random.randint(1, 5))]
    meets = [e for e in events if random.random() < 0.6]
    r = set(reach)
    pointers = [p for p in meets if all((p & r) <= (e & r) for e in meets)]
    for p in pointers:
        for q in pointers:
            if p & r != q & r: fails.append('pointer unique')

# ---------------- EIP-1559: last block's gas sets the next base fee ----------------
def next_base(base, used, target):
    return base + base * (used - target) // target // 8
if next_base(800, 30_000_000, 15_000_000) != 900: fails.append('full block +1/8')
if next_base(800, 0, 15_000_000) != 700: fails.append('empty block -1/8')
if next_base(800, 15_000_000, 15_000_000) != 800: fails.append('on target')

# ---------------- three observers on one bit vs three bits ----------------
# one carrier: every observer reads bit 0; the event proliferates with no independence
for st in product([0, 1], repeat=3):
    event = st[0] == 1
    if not all((st[0] == 1) == event for _ in range(3)): fails.append('one carrier')
# separate carriers: underlying states where they disagree exist; reachable copies agree
disagree = [st for st in product([0, 1], repeat=3) if len(set(st)) > 1]
reachable = [(0, 0, 0), (1, 1, 1)]                     # a copying process put them in step
if not disagree or any(len(set(st)) > 1 for st in reachable): fails.append('independent carriers')

# ---------------- complete dephasing merges phase on the dial alone ----------------
plus = [[F(1, 2), F(1, 2)], [F(1, 2), F(1, 2)]]
minus = [[F(1, 2), F(-1, 2)], [F(-1, 2), F(1, 2)]]
deph = lambda m: [[m[0][0], 0], [0, m[1][1]]]
if plus == minus or deph(plus) != deph(minus): fails.append('dephasing')
# before dephasing they are perfectly distinguishable: trace of product is 0
if sum(plus[i][j] * minus[j][i] for i in range(2) for j in range(2)) != 0: fails.append('orthogonal')

print('prices meeting the naming-free list:', len(naming_free))
print('failures:', len(fails), fails[:10])
