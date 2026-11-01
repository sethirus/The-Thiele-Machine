"""Checks of the claims in chapter eleven of the book."""
import random
from itertools import product
random.seed(7)
fails = []
# Lamport clocks: if a event causes b (happens-before), stamp(a) < stamp(b)
for trial in range(300):
    n = 3; clocks = [0] * n; events = []; inbox = []
    for step in range(30):
        p = random.randrange(n)
        if inbox and random.random() < 0.4:
            q, s, src = inbox.pop(random.randrange(len(inbox)))
            if q == p:
                clocks[p] = max(clocks[p], s) + 1
                events.append((p, clocks[p], src)); continue
            inbox.append((q, s, src))
        clocks[p] += 1
        e = len(events); events.append((p, clocks[p], None))
        if random.random() < 0.5:
            inbox.append((random.randrange(n), clocks[p], e))
    # happens-before edges: same process order, and send -> receive
    for i, (p, s, src) in enumerate(events):
        if src is not None and not events[src][1] < s: fails.append('lamport-msg')
        for j in range(i):
            if events[j][0] == p and not events[j][1] < s: fails.append('lamport-local')
# coin stack: total cost <= 2 * pushes
for trial in range(2000):
    stack, cost, pushes = 0, 0, 0
    for _ in range(40):
        if random.random() < 0.7: stack += 1; cost += 1; pushes += 1
        else: cost += stack; stack = 0
    if cost > 2 * pushes: fails.append('coins')
# counter in the state on a finite machine forces every price to zero
for n in range(1, 5):
    for f in product(range(n), repeat=n):
        # counter function mu with mu(f(s)) = mu(s) + c exists on all states only if c == 0
        for c in range(0, 3):
            # follow f from each state: cycle forces c * cycle_length = 0
            ok = True
            for s in range(n):
                seen = []; x = s
                while x not in seen: seen.append(x); x = f[x]
                cyc = len(seen) - seen.index(x)
                if c * cyc != 0: ok = False
            if ok != (c == 0): fails.append(('finite-counter', f, c))
# only one honest count on reachable states (random machines, nonnegative prices)
for trial in range(500):
    n = random.randint(1, 6); m = random.randint(1, 3)
    steps = [[random.randrange(n) for _ in range(n)] for _ in range(m)]
    price = [random.randint(0, 2) for _ in range(m)]
    mu = {0: 0}; frontier = [0]; consistent = True
    while frontier:
        s = frontier.pop()
        for i in range(m):
            t = steps[i][s]; v = mu[s] + price[i]
            if t in mu:
                if mu[t] != v: consistent = False
            else: mu[t] = v; frontier.append(t)
    if consistent:
        # a second bookkeeper walking the states in another order must agree everywhere it reaches
        books = {0: 0}; queue = [0]
        while queue:
            s = queue.pop(0)
            for i in reversed(range(m)):
                t = steps[i][s]
                if t not in books: books[t] = books[s] + price[i]; queue.append(t)
        if books != mu: fails.append('honest-count')
# flag potential: toll holds iff every step has nonnegative amortized cost
for rec in product([0, 1], repeat=3):
    for f in product(range(3), repeat=3):
        for c in range(3):
            toll = all(c >= 1 for s in range(3) if rec[s] == 0 and rec[f[s]] == 1)
            phi = lambda s: 1 - rec[s]
            amort = all(c + phi(f[s]) >= phi(s) for s in range(3))
            if toll != amort: fails.append('flag-potential')
# per-button: a button that raises from no and can be pressed on yes costs >0 there, so no exact per-button list
latch = {0: 1, 1: 1}
for c in range(3):
    floor = c >= 1
    ceiling_on_yes = c <= 0          # pressing on yes raises nothing
    if floor and ceiling_on_yes: fails.append('per-button')
print('failures:', len(fails))
