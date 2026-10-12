from pathlib import Path
import json
import random
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from monitors import history_answer
from interval_monitor import WideIntervalMonitor

counts = dict(exhaustive_prefixes=0, exhaustive_queries=0, random_events=0,
              random_queries=0, single_reset_cases=0)

def resource_checks(mon, operation):
    if operation == 'write':
        assert mon.visits <= 2 * mon.height
        assert mon.word_touches <= 2 * mon.leaf_words
    else:
        assert mon.visits <= mon.height
        assert mon.word_touches <= (mon.leaf_words + 1 if operation == 'pass' else 1)
    mon.check_representation()

for n in range(1, 5):
    intervals = [(a, b) for a in range(n + 1) for b in range(a, n + 1)]
    deps = [{j for j, (a, b) in enumerate(intervals) if a <= i < b} for i in range(n)]
    actions = [('pass', i) for i in range(n)] + [('write', j) for j in range(len(intervals))]
    for w, block in ((2, 1), (2, 2), (3, 1), (4, 1), (4, 3), (8, 2)):
        mon, history = WideIntervalMonitor(n, intervals, w, block), []
        def explore(depth):
            counts['exhaustive_prefixes'] += 1
            for i in range(n):
                assert mon.use(i) == history_answer(history, deps, i), (n, w, block, history, i)
                resource_checks(mon, 'use')
                counts['exhaustive_queries'] += 1
            if not depth:
                return
            for kind, x in actions:
                state = mon.snapshot()
                history.append((kind, x))
                (mon.passed if kind == 'pass' else mon.write)(x)
                resource_checks(mon, kind)
                explore(depth - 1)
                history.pop()
                mon.restore(state)
        explore(4)
    print('wide exhaustive', n, 'passed', flush=True)

# Every status vector and interval through n=9; includes resurrecting each
# individual claim after clearing, with all other old leaf contents preserved.
for n in range(1, 10):
    intervals = [(a, b) for a in range(n + 1) for b in range(a, n + 1)]
    for w, block in ((2, 1), (3, 2), (4, 1), (4, 3)):
        for bits in range(1 << n):
            mon = WideIntervalMonitor(n, intervals, w, block)
            for i in range(n):
                if (bits >> i) & 1:
                    mon.passed(i)
            state = mon.snapshot()
            for j, (lo, hi) in enumerate(intervals):
                mon.restore(state)
                mon.write(j)
                resource_checks(mon, 'write')
                expected = bits & ~(((1 << (hi - lo)) - 1) << lo)
                assert all(mon.use(i) == bool((expected >> i) & 1) for i in range(n))
                if n:
                    x = (lo + hi) % n
                    mon.passed(x)
                    expected |= 1 << x
                    assert all(mon.use(i) == bool((expected >> i) & 1) for i in range(n))
                counts['single_reset_cases'] += 1
print('wide all-state interval/reset cases passed', flush=True)

rng = random.Random(261012)
for trial in range(160):
    n = rng.randint(1, 360)
    w, block = rng.choice((2, 3, 4, 8, 16, 32, 64)), rng.choice((1, 2, 3, 7, 17))
    intervals = [(0, n), (0, 0), (n, n)]
    for _ in range(35):
        a, b = sorted((rng.randrange(n + 1), rng.randrange(n + 1)))
        intervals.append((a, b))
    deps = [{j for j, (a, b) in enumerate(intervals) if a <= i < b} for i in range(n)]
    mon, history = WideIntervalMonitor(n, intervals, w, block), []
    for step in range(350):
        kind = 'pass' if rng.random() < .65 else 'write'
        x = rng.randrange(n if kind == 'pass' else len(intervals))
        history.append((kind, x))
        (mon.passed if kind == 'pass' else mon.write)(x)
        resource_checks(mon, kind)
        counts['random_events'] += 1
        for i in range(n):
            assert mon.use(i) == history_answer(history, deps, i), (trial, history, i)
            counts['random_queries'] += 1
print('wide randomized histories passed', flush=True)
result = {'status': 'passed', **counts, 'scope': 'Wide interval construction only; asymptotic bounds require the written proof.'}
Path(__file__).with_name('wide-verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2), flush=True)
