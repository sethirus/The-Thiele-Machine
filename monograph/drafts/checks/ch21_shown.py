"""Checks of the countable claims in drafts/21_shown_chosen_argued.md."""
import random
from itertools import product
random.seed(21)
fails = []

# ---------------- two machines side by side ----------------
# each machine: states, moves (maps), costs, a 0/1 reading that never falls, toll obeyed
def rand_machine():
    n = random.randint(2, 3)
    read = [0] + [random.randint(0, 1) for _ in range(n - 1)]
    if 1 not in read: read[-1] = 1
    moves, costs = [], []
    for _ in range(random.randint(1, 2)):
        f = []
        for s in range(n):
            choices = [t for t in range(n) if read[t] >= read[s]]     # never falls
            f.append(random.choice(choices))
        moves.append(f)
        raises = any(read[s] == 0 and read[f[s]] == 1 for s in range(n))
        costs.append(random.randint(1, 2) if raises else random.randint(0, 2))
    return n, read, moves, costs
for _ in range(3000):
    A, B = rand_machine(), rand_machine()
    nA, rA, mA, cA = A; nB, rB, mB, cB = B
    pair_moves = [(0, i) for i in range(len(mA))] + [(1, j) for j in range(len(mB))]
    def step(s, mv):
        a, b = s
        return (mA[mv[1]][a], b) if mv[0] == 0 else (a, mB[mv[1]][b])
    def cost(mv): return cA[mv[1]] if mv[0] == 0 else cB[mv[1]]
    for name, R in [('either', lambda s: rA[s[0]] or rB[s[1]]), ('both', lambda s: rA[s[0]] and rB[s[1]])]:
        for s in product(range(nA), range(nB)):
            for mv in pair_moves:
                t = step(s, mv)
                if R(t) < R(s): fails.append(name + ' falls')
                if R(t) > R(s) and cost(mv) < 1: fails.append(name + ' toll')
    # "both" from a clean start: any run from (no, no) to (yes, yes) costs at least two
    for s0 in [(a, b) for a in range(nA) for b in range(nB) if not rA[a] and not rB[b]]:
        for L in range(1, 5):
            for run in product(pair_moves, repeat=L):
                s, c = s0, 0
                for mv in run: c += cost(mv); s = step(s, mv)
                if rA[s[0]] and rB[s[1]] and c < 2: fails.append('both costs two')
# "first up, second down" can fall
rA, rB = [0, 1], [0, 1]
if not ((rA[1] and not rB[0]) and not (rA[1] and not rB[1])): fails.append('first-not-second falls')

# ---------------- branching steps ----------------
# (1) finite yes side closed, each yes-state has a next state, some no-state steps in: two share
for _ in range(3000):
    n = random.randint(2, 6); read = [random.randint(0, 1) for _ in range(n)]
    yes = [s for s in range(n) if read[s]]; no = [s for s in range(n) if not read[s]]
    if not yes or not no: continue
    nxt = {s: random.sample(yes, random.randint(1, len(yes))) for s in yes}
    entry = (random.choice(no), random.choice(yes))
    picks = [(s, random.choice(nxt[s])) for s in yes] + [entry]
    lands = [t for _, t in picks]
    if len(set(lands)) == len(lands): fails.append('branching chairs')
# (2) along one run, after the raise: two arrows meet or no repeats
for _ in range(5000):
    n = random.randint(2, 6); read = [random.randint(0, 1) for _ in range(n)]
    nxt = {s: random.sample(range(n), random.randint(1, n)) for s in range(n)}
    nxt = {s: ([t for t in v if read[t] >= read[s]] or ([s] if read[s] else v)) for s, v in nxt.items()}
    x = random.choice([s for s in range(n) if not read[s]] or [0])
    if read[x]: continue
    run = [x]
    for _ in range(12): run.append(random.choice(nxt[run[-1]]))
    ups = [i for i in range(len(run)) if read[run[i]]]
    if not ups or not all(read[run[i]] for i in range(ups[0], len(run))): continue
    k = ups[0]
    after = run[k:]
    if len(set(after)) < len(after):
        steps = [(run[i], run[i + 1]) for i in range(len(run) - 1)]
        if not any(a != b and a2 == b2 for (a, a2) in steps for (b, b2) in steps): fails.append('branching run')
# lambda: (\x.x)N and (\z.N)M are different terms with the same next term N
N, M = ('var', 'y'), ('var', 'w')
t1 = ('app', ('lam', 'x', ('var', 'x')), N)
t2 = ('app', ('lam', 'z', N), M)
def subst(body, v, arg):
    if body[0] == 'var': return arg if body[1] == v else body
    if body[0] == 'lam': return body if body[1] == v else ('lam', body[1], subst(body[2], v, arg))
    return ('app', subst(body[1], v, arg), subst(body[2], v, arg))
def beta(t): return subst(t[1][2], t[1][1], t[2])
if t1 == t2 or beta(t1) != N or beta(t2) != N: fails.append('lambda')

# ---------------- listing what a never-turned-off reading accepts ----------------
# toy "descriptions": each input runs a little machine whose reading, once yes, stays yes
def make(i):
    rnd = random.Random(i)
    t = rnd.choice([None, rnd.randint(0, 9)])      # step at which it says yes, or never
    return lambda step: t is not None and step >= t
progs = [make(i) for i in range(30)]
accepted = {i for i, p in enumerate(progs) if p(10 ** 6)}
listed, order = set(), []
for rnd_ in range(40):                              # take turns: one step of each started input
    for i in range(min(rnd_ + 1, len(progs))):
        if i not in listed and progs[i](rnd_ - i):
            listed.add(i); order.append(i)
if listed != accepted: fails.append('dovetail lists exactly the accepted')
# the reading that falls: yes while running, no for good once it stops; yes forever on non-stoppers
def falls(stop_at):
    return lambda step: stop_at is None or step < stop_at
for stop_at in [None, 0, 3, 7]:
    r = falls(stop_at)
    final = r(10 ** 6)
    if final != (stop_at is None): fails.append('falling reading')

print('failures:', len(fails), sorted(set(fails))[:10])
