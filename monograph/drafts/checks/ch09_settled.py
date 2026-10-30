"""Checks of the counting claims in drafts/09_settled.md."""
fails = []
# three ballots: each voter consistent, majorities on premises say owed, majority on verdict says not owed
voters = [(True, True), (True, False), (False, True)]
verdicts = [s and m for s, m in voters]
maj = lambda xs: sum(xs) * 2 > len(xs)
if not (maj([v[0] for v in voters]) and maj([v[1] for v in voters]) and not maj(verdicts)):
    fails.append('ballots')
# a chain of reasons where each reason has at most one next reason: new forever, loops, or stops
from itertools import product
for n in range(1, 6):
    for nxt in product(list(range(n)) + [None], repeat=n):
        for s in range(n):
            seen, x, outcome = set(), s, None
            for _ in range(n + 1):
                if x is None: outcome = 'stops'; break
                if x in seen: outcome = 'loops'; break
                seen.add(x); x = nxt[x]
            if outcome is None: fails.append(('chain', nxt, s))   # finite chains can't go on forever
print('failures:', len(fails))
