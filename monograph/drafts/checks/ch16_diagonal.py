"""Checks of the countable claims in drafts/16_what_a_machine_cant_decide_about_itself.md."""
import random
from itertools import product
random.seed(11)
fails = []
# the flipped diagonal differs from every row at that row's own place
for _ in range(2000):
    n = random.randint(1, 8)
    table = [[random.randint(0, 1) for _ in range(n)] for _ in range(n)]
    diag = [1 - table[i][i] for i in range(n)]
    if any(diag == row for row in table): fails.append('diagonal')
# Berry phrase syllables: 18
syll = {'the': 1, 'least': 1, 'integer': 3, 'not': 1, 'nameable': 3, 'in': 1, 'fewer': 2, 'than': 1,
        'nineteen': 2, 'syllables': 3}
phrase = 'the least integer not nameable in fewer than nineteen syllables'.split()
if sum(syll[w] for w in phrase) != 18: fails.append('berry')
# two index cards: no checker answer is right about the contrarian
for checker_says_stops in [True, False]:
    contrarian_stops = not checker_says_stops
    if checker_says_stops == contrarian_stops: fails.append('cards')
# the shortcut wall on a toy: behaviours are labels; a fixed point of the flip defeats every judge
behaviours = range(4)
for A in product([0, 1], repeat=4):
    if len(set(A)) < 2: continue
    y = A.index(1); n = A.index(0)
    for d in product([0, 1], repeat=4):           # judge on behaviours
        # a program p behaving like its own flip: behaviour b with b == (n if d[b] else y)
        fixed = [b for b in behaviours if b == (n if d[b] else y)]
        for b in fixed:
            if d[b] == A[b]: fails.append('wall')
print('failures:', len(fails))
