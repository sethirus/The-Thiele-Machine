from itertools import permutations, product
from math import comb
from pathlib import Path
import json
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from monitors import Eager, BoundedLazy, history_answer
from interval_monitor import IntervalMonitor, multiphase_answers

counts = dict(interval_prefixes=0, interval_queries=0, random_events=0,
              random_queries=0, multiphase_cases=0, encoding_checks=0)

for n in range(1, 5):
    intervals = [(lo, hi) for lo in range(n + 1) for hi in range(lo, n + 1)]
    deps = [{j for j, (lo, hi) in enumerate(intervals) if lo <= i < hi}
            for i in range(n)]
    actions = [('pass', i) for i in range(n)] + [('write', j) for j in range(len(intervals))]
    for w in (1, 2, 3, 4, 8):
        monitor, history = IntervalMonitor(n, intervals, w), []

        def explore(depth):
            counts['interval_prefixes'] += 1
            monitor.check_representation()
            for i in range(n):
                assert monitor.use(i) == history_answer(history, deps, i), (n, w, history, i)
                assert monitor.visits <= monitor.height + 1
                counts['interval_queries'] += 1
            if not depth:
                return
            for kind, x in actions:
                state = monitor.snapshot()
                history.append((kind, x))
                (monitor.passed if kind == 'pass' else monitor.write)(x)
                assert monitor.visits <= 8 * (monitor.height + 1)
                explore(depth - 1)
                history.pop()
                monitor.restore(state)

        explore(4)
    print('interval exhaustive', n, 'passed', flush=True)

rng = random.Random(1202612)
for trial in range(150):
    n, w = rng.randint(1, 160), rng.choice((2, 3, 8, 16, 32, 64))
    intervals = [(0, n), (0, 0), (n, n)]
    for _ in range(30):
        a, b = sorted((rng.randrange(n + 1), rng.randrange(n + 1)))
        intervals.append((a, b))
    monitor = IntervalMonitor(n, intervals, w)
    deps = [{j for j, (lo, hi) in enumerate(intervals) if lo <= i < hi}
            for i in range(n)]
    history = []
    for step in range(400):
        kind = 'pass' if rng.random() < .6 else 'write'
        x = rng.randrange(n if kind == 'pass' else len(intervals))
        history.append((kind, x))
        (monitor.passed if kind == 'pass' else monitor.write)(x)
        assert monitor.visits <= 8 * (monitor.height + 1)
        monitor.check_representation()
        counts['random_events'] += 1
        for i in range(n):
            assert monitor.use(i) == history_answer(history, deps, i), (trial, history, i)
            counts['random_queries'] += 1
print('interval randomized histories passed', flush=True)

# The rectangular multiphase reduction, including duplicate writes and empty sets.
for n, m in ((1, 1), (2, 3), (3, 2), (3, 3), (4, 2)):
    for matrix in product((0, 1), repeat=n * m):
        deps = [{j for j in range(m) if matrix[i * m + j]} for i in range(n)]
        for bits in product((0, 1), repeat=m):
            written = [j for j, bit in enumerate(bits) if bit]
            expected = [not (deps[i] & set(written)) for i in range(n)]
            for constructor in (Eager, BoundedLazy):
                assert multiphase_answers(deps, m, written + written, constructor) == expected
            counts['multiphase_cases'] += 1
print('rectangular multiphase reduction passed', flush=True)

# For every bijective encoding through n=3, every nonempty clearing set, and
# several cell widths, each 2^k-element predecessor fibre must fit in a cell
# Hamming ball about its unique target. This checks the generalized counting
# lemma; it is not an asymptotic proof or a check of the cited CGL theorem.
for n in range(1, 4):
    size = 1 << n
    for encoding in permutations(range(size)):
        for clear in range(1, size):
            k = clear.bit_count()
            for w in range(1, n + 1):
                cells = (n + w - 1) // w
                cellmask = (1 << w) - 1
                worst = 0
                for x in range(size):
                    diff = encoding[x] ^ encoding[x & ~clear]
                    distance = sum(bool((diff >> (j * w)) & cellmask) for j in range(cells))
                    worst = max(worst, distance)
                volume = sum(comb(cells, r) * ((1 << w) - 1) ** r
                             for r in range(worst + 1))
                assert volume >= 1 << k
                assert (1 + cells * ((1 << w) - 1)) ** worst >= 1 << k
                counts['encoding_checks'] += 1
print('exact-space encoding lemma passed', flush=True)

result = {'status': 'passed', **counts,
          'scope': 'Finite algorithm/reduction/cell-distance checks; proofs and cited lower bounds are separate.'}
Path(__file__).with_name('verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2), flush=True)
