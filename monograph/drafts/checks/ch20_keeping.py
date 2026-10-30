"""Checks of the countable claims in drafts/20_keeping_without_heat.md."""
import random, math
from itertools import product
random.seed(20)
fails = []

# ---------------- the write-once cell ----------------
cell = {'blank': 'zero', 'zero': 'zero', 'one': 'one'}
if cell['blank'] != cell['zero']: fails.append('write merges')
# any write on finitely many states, where written stays written and blank gets written, merges
for n_written in range(1, 5):
    states = ['blank'] + ['w%d' % i for i in range(n_written)]
    for img in product(range(n_written), repeat=n_written + 1):
        f = {s: 'w%d' % i for s, i in zip(states, img)}
        if len(set(f.values())) == len(states): fails.append('remembering state escapes')
# endless tape stepped one cell along: one-to-one, onto, raises "past the start" and keeps it
for k in range(1, 50):
    if (lambda x: x + 1)(0) != 1 or k == 0: fails.append('shift')

# ---------------- noisy steps ----------------
def rand_stoch(n, closed, doubly):
    if doubly:  # a mix of permutation matrices keeps every column summing to one
        M = [[0.0] * n for _ in range(n)]
        perms = []
        for _ in range(3):
            p = list(range(n)); random.shuffle(p); perms.append(p)
        w = [random.random() for _ in perms]; s = sum(w)
        for p, wi in zip(perms, w):
            for i in range(n): M[i][p[i]] += wi / s
        return M
    M = [[random.random() ** 3 for _ in range(n)] for _ in range(n)]
    for i in range(n):
        if i in closed:
            for j in range(n):
                if j not in closed: M[i][j] = 0.0
        s = sum(M[i]); M[i] = [x / s for x in M[i]]
    return M
def cw(p): return sum(x * x for x in p)
def H(p): return -sum(x * math.log(x) for x in p if x > 0)
for _ in range(3000):
    n = random.randint(2, 6)
    M = rand_stoch(n, set(), True)
    # columns add to one: a closed set can't be entered from outside
    closed = {j for j in range(n) if all(M[j][k] == 0 or k == j for k in range(n))}
    for S in [set(c) for c in [range(r) for r in range(1, n)]]:
        if all(sum(M[i][j] for j in S) > 1 - 1e-9 for i in S):     # S closed
            if any(M[i][j] > 1e-12 for i in range(n) if i not in S for j in S): fails.append('doubly enters')
    # never raises collision weight
    p = [random.random() for _ in range(n)]; s = sum(p); p = [x / s for x in p]
    q = [sum(p[i] * M[i][j] for i in range(n)) for j in range(n)]
    if cw(q) > cw(p) + 1e-12: fails.append('doubly raises collision weight')
    # a step that can enter a closed set bunches the even spread (exact fractions: the
    # effect can be smaller than floating point resolves)
    from fractions import Fraction as Fr
    k = random.randint(1, n - 1)
    S = set(range(k))
    M2 = []
    for i in range(n):
        row = [Fr(random.randint(0, 5)) for _ in range(n)]
        if i in S: row = [r if j in S else Fr(0) for j, r in enumerate(row)]
        if sum(row) == 0: row[i] = Fr(1)
        t = sum(row); M2.append([r / t for r in row])
    if any(M2[i][j] > 0 for i in range(k, n) for j in S):
        q = [sum(M2[i][j] for i in range(n)) / n for j in range(n)]
        if not (sum(x * x for x in q) > Fr(1, n)): fails.append('bunches')
        if all(x == Fr(1, n) for x in q): fails.append('entropy drops')   # not even, so H < log n
if abs(cw([.5, .5]) - .5) > 1e-12 or abs(cw([.75, .25]) - 10 / 16) > 1e-12: fails.append('match chances')

# ---------------- unitary steps keep the perpendicular directions out ----------------
def qr_unitary(n):
    A = [[complex(random.gauss(0, 1), random.gauss(0, 1)) for _ in range(n)] for _ in range(n)]
    Q = []
    for col in range(n):
        v = [A[r][col] for r in range(n)]
        for u in Q:
            d = sum(u[r].conjugate() * v[r] for r in range(n))
            v = [v[r] - d * u[r] for r in range(n)]
        nv = math.sqrt(sum(abs(x) ** 2 for x in v)); Q.append([x / nv for x in v])
    return [[Q[c][r] for c in range(n)] for r in range(n)]
for _ in range(300):
    m, k = random.randint(1, 3), random.randint(1, 3)
    UY, UN = qr_unitary(m), qr_unitary(k)
    # any unitary carrying YES into itself is block diagonal in a YES/NO basis
    U = [[0j] * (m + k) for _ in range(m + k)]
    for i in range(m):
        for j in range(m): U[i][j] = UY[i][j]
    for i in range(k):
        for j in range(k): U[m + i][m + j] = UN[i][j]
    x = [0j] * m + [complex(random.gauss(0, 1), 0) for _ in range(k)]
    Ux = [sum(U[r][c] * x[c] for c in range(m + k)) for r in range(m + k)]
    if max(abs(Ux[r]) for r in range(m)) > 1e-9: fails.append('perpendicular stays out')
# the bilateral shift on an endless ladder raises "past the start" and keeps it (checked as +1 above)

# ---------------- how much room: N starts, T repetitions, one resting value ----------------
def survives(F, starts, T):
    visited = set()
    for s in starts:
        x = s
        for t in range(T):
            visited.add(x); x = F[x]
    vis = sorted(visited)
    return len({F[v] for v in vis}) == len(vis)
def min_room(N, T, Mmax):
    for M in range(1, Mmax + 1):
        for F in product(range(M), repeat=M):
            for read in product([0, 1], repeat=M):         # 1 = the fixed value
                if not all(read[F[x]] == 1 for x in range(M)): continue
                ones = [x for x in range(M) if read[x]]
                zeros = [x for x in range(M) if not read[x]]
                if len(ones) < 1 or len(zeros) < N - 1: continue
                # starts: one resting, N-1 not; resting start must be fixed by F
                for r in ones:
                    if F[r] != r: continue
                    from itertools import combinations
                    for others in combinations(zeros, N - 1):
                        if survives(F, (r,) + others, T): return M
    return None
for N, T in [(2, 1), (2, 2), (3, 1), (2, 3), (3, 2)]:
    want = 1 + (T + 1) * (N - 1)
    got = min_room(N, T, want)
    if got != want: fails.append('room %d %d got %s want %d' % (N, T, got, want))
# the exact build: one state plus a row of T + 1 for each other start
for N in range(2, 6):
    for T in range(1, 6):
        M = 1 + (T + 1) * (N - 1)
        F = {0: 0}; starts = [0]
        idx = 1
        for _ in range(N - 1):
            row = list(range(idx, idx + T + 1)); idx += T + 1
            starts.append(row[0])
            for a, b in zip(row, row[1:]): F[a] = b
            F[row[-1]] = 0
        if idx != M or not survives(F, starts, T): fails.append('build')
        if survives(F, starts, T + 1): fails.append('build merges next')
if abs(math.log2(1 + 2 * 1) - math.log2(3)) > 1e-12: fails.append('bits')

# ---------------- two levers ----------------
fmap = {0: 0, 1: 0, 2: 2}; gmap = {0: 0, 1: 1, 2: 0}
def reach(F, G, starts, t):
    R = set(starts); frontier = set(starts)
    for _ in range(t):
        frontier = {F[x] for x in frontier} | {G[x] for x in frontier}
        R |= frontier
    return R
def lever_ok(F, G, read, starts, T, commute):
    R = reach(F, G, starts, T - 1)
    Rl = sorted(R)
    if len({F[x] for x in Rl}) < len(Rl) or len({G[x] for x in Rl}) < len(Rl): return False
    if commute and any(F[G[x]] != G[F[x]] for x in range(len(read))): return False
    return True
def min_lever(T, commute, nmax):
    for n in range(3, nmax + 1):
        for read in product([0, 1, 2], repeat=n - 3):
            rd = (0, 1, 2) + read
            optF = [[y for y in range(n) if rd[y] == fmap[rd[x]]] for x in range(n)]
            optG = [[y for y in range(n) if rd[y] == gmap[rd[x]]] for x in range(n)]
            for Fv in product(*optF):
                for Gv in product(*optG):
                    if lever_ok(Fv, Gv, rd, (0, 1, 2), T, commute): return n
    return None
if min_lever(1, False, 4) != 4: fails.append('levers T+3 at 1')
if min_lever(2, False, 5) != 5: fails.append('levers T+3 at 2')
if min_lever(1, True, 4) != 4: fails.append('commuting 2T+2 at 1')
if min_lever(2, True, 6) != 6: fails.append('commuting 2T+2 at 2')
# the simple case on the page, tested on every valid commuting box of six places at horizon two
# where the second lever holds the start above 1 still and the first holds the start above 2 still
T, n, seen = 2, 6, 0
for read in product([0, 1, 2], repeat=n - 3):
    rd = (0, 1, 2) + read
    optF = [[y for y in range(n) if rd[y] == fmap[rd[x]]] for x in range(n)]
    optG = [[y for y in range(n) if rd[y] == gmap[rd[x]]] for x in range(n)]
    for Fv in product(*optF):
        if Fv[2] != 2: continue
        for Gv in product(*optG):
            if Gv[1] != 1 or not lever_ok(Fv, Gv, rd, (0, 1, 2), T, True): continue
            seen += 1
            c1 = [1]
            for _ in range(T): c1.append(Fv[c1[-1]])
            c2 = [2]
            for _ in range(T): c2.append(Gv[c2[-1]])
            c1, c2 = c1[1:], c2[1:]
            if len(set(c1)) < T or len(set(c2)) < T: fails.append('chains repeat')
            if any(Gv[x] != x for x in c1) or any(Fv[x] != x for x in c2): fails.append('other lever holds still')
            shared = set(c1) & set(c2)
            if shared - ({c1[-1]} & {c2[-1]}): fails.append('share only the ends')
            if shared and (0 in c1 or 0 in c2): fails.append('zero start off the chains')
if seen == 0: fails.append('no simple-case boxes found')
# the four-place box at horizon one, every arrow
rd = {'a0': 1, 'b0': 2, 'b1': 0, 'end': 0}
F4 = {'a0': 'end', 'b0': 'b0', 'b1': 'b1', 'end': 'end'}
G4 = {'a0': 'a0', 'b0': 'b1', 'b1': 'end', 'end': 'end'}
st = ['a0', 'b0', 'b1']
if len({F4[s] for s in st}) != 3 or len({G4[s] for s in st}) != 3: fails.append('three starts apart')
if len(set(F4.values())) == 4 or len(set(G4.values())) == 4: fails.append('whole carrier repeats')
if any(F4[G4[s]] != G4[F4[s]] for s in rd): fails.append('box commutes')
# the grid: |R_t| = 1 + (t+2)(t+3)/2
for t in range(0, 8):
    starts = {('blank',), (0, 0), (1, 0), (0, 1)}
    R = set(starts); fr = set(starts)
    for _ in range(t):
        nf = set()
        for x in fr:
            if x == ('blank',): nf.add(x); continue
            nf.add((x[0] + 1, x[1])); nf.add((x[0], x[1] + 1))
        R |= nf; fr = nf
    if len(R) != 1 + (t + 2) * (t + 3) // 2: fails.append('grid %d' % t)

# ---------------- keeping every history ----------------
for _ in range(500):
    n = random.randint(1, 5); step = [random.randrange(n) for _ in range(n)]
    hist = lambda pair: (step[pair[0]], (pair[0],) + pair[1])
    pairs = [(s, h) for s in range(n) for h in [(), (0,), (1 % n, 0)]]
    imgs = [hist(p) for p in pairs]
    if len(set(imgs)) != len(pairs): fails.append('history one-to-one')

# ---------------- receipts cover the mergers a run shows ----------------
for _ in range(3000):
    n = random.randint(1, 6); F = [random.randrange(n) for _ in range(n)]
    a = [0] * n
    for x in range(n):
        for y in range(x + 1, n):
            if F[x] == F[y] and a[x] == 0 and a[y] == 0:
                (a.__setitem__(x, 1) if random.random() < .5 else a.__setitem__(y, 1))
    u = random.randrange(n); L = random.randint(0, 8)
    src = [u]
    for _ in range(L - 1 if L else 0): src.append(F[src[-1]])
    src = src[:L]
    distinct = set(src)
    marked = {F[x] for x in distinct if any(F[x] == F[y] and x != y for y in distinct)}
    if len(marked) > sum(a[x] for x in src): fails.append('receipts')

# ---------------- the eight-state machine ----------------
S8 = [(slot, flag) for slot in range(4) for flag in (0, 1)]
stamp = lambda s: ((s[0] + 1) % 4, 1)
nxt = lambda s: ((s[0] + 1) % 4, s[1])
def pile(f):
    c = {}
    for s in S8: c[f(s)] = c.get(f(s), 0) + 1
    return max(c.values())
if pile(stamp) != 2 or pile(nxt) != 1: fails.append('eight-state piles')
for j in range(4):
    if pile(lambda s: (j, s[1])) != 4: fails.append('jump pile')
for f in [stamp, nxt] + [lambda s, j=j: (j, s[1]) for j in range(4)]:
    if any(s[1] == 1 and f(s)[1] == 0 for s in S8): fails.append('flag falls')
if not all(2 ** c >= p for c, p in [(1, 2), (2, 4), (0, 1)]): fails.append('price = halvings')

# ---------------- one move repeated forever merges states the run visits ----------------
for _ in range(5000):
    n = random.randint(2, 7); F = [random.randrange(n) for _ in range(n)]
    up = [random.randint(0, 1) for _ in range(n)]
    x = random.randrange(n)
    if up[x]: continue
    run = [x]
    for _ in range(3 * n): run.append(F[run[-1]])
    tail = run[n:]
    if all(up[y] for y in tail):           # goes up and stays up along this run
        vis = set(run)
        if not any(F[p] == F[q] and p != q for p in vis for q in vis): fails.append('repeat merges')
# moves picked from outside: swap once, then idle, flag up for good, nothing merges
swap = {0: 1, 1: 0}; idle = {0: 0, 1: 1}
if len(set(swap.values())) != 2 or len(set(idle.values())) != 2: fails.append('swap example')

print('failures:', len(fails), fails[:10])
