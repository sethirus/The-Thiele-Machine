"""Exhaustive checks of the claims in drafts/07_what_a_window_cant_see.md."""
from itertools import product
fails = []
# four readers: none recovers the flag from the position when both results show position 1
results = [(1, True), (1, False)]
readers = list(product([False, True], repeat=2))  # reader[pos] -> flag
if any(all(r[p] == fl for p, fl in results) for r in readers): fails.append('reader')
if len(readers) != 4: fails.append('count')
# a reader exists iff the question is constant on each pile (all windows/questions on 4 states)
for w in product(range(3), repeat=4):
    for q in product([0, 1], repeat=4):
        const = all(q[a] == q[b] for a in range(4) for b in range(4) if w[a] == w[b])
        exists = any(all(d[w[s]] == q[s] for s in range(4)) for d in product([0, 1], repeat=3))
        if const != exists: fails.append(('pile', w, q))
# tile moves that follow the picture keep two same-picture boxes the same picture
for h in product(range(3), repeat=3):          # tile move on pictures 0..2
    for pic in range(3):
        a, b = (pic, 1), (pic, 0)
        for _ in range(5):
            a, b = (h[a[0]], a[1]), (h[b[0]], b[1])
            if a[0] != b[0] or a[1] == b[1]: fails.append('tiles')
# exact clerk price exists iff no colliding pair (steps on a small state space)
states = [(t, s) for t in range(2) for s in range(2)]
win = lambda st: st[0]
for img in product(range(4), repeat=4 * 2):
    moves = [dict(zip(states, [states[i] for i in img[4 * m:4 * m + 4]])) for m in range(2)]
    steps = [(st, moves[m][st]) for m in range(2) for st in states]
    raise_ = lambda st, nx: st[1] == 0 and nx[1] == 1
    trays = {}
    for st, nx in steps: trays.setdefault((win(st), win(nx)), set()).add(raise_(st, nx))
    collision = any(len(v) == 2 for v in trays.values())
    exact = all(len(v) == 1 for v in trays.values())
    if collision == exact: fails.append('clerk')
# the running AND bit says exactly whether all checks so far passed
for checks in product([0, 1], repeat=6):
    bit = 1
    for i, c in enumerate(checks):
        bit = bit & c
        if bit != all(checks[:i + 1]): fails.append('and')
# no checker of the bare transcript is sound and complete for "count is 1"
runs = [('tau', 1), ('tau', 0)]
for verdict in [True, False]:
    sound = all(cnt == 1 for t, cnt in runs if verdict)
    complete = all(verdict for t, cnt in runs if cnt == 1)
    if sound and complete: fails.append('verifier')
# Ali Baba: a cheat survives k rounds with chance 2^-k; 20 rounds about one in a million
if not (0.9e-6 < 2 ** -20 < 1e-6 * 1.0): fails.append('cave')
print('failures:', len(fails))
for f in fails[:10]: print(f)
