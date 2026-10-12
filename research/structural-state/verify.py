from itertools import product
from pathlib import Path
import json
import random
from monitors import Eager, BoundedLazy, GlobalSparseSet, history_answer, omv_round

counts = dict(exhaustive_prefixes=0, exhaustive_queries=0, omv_rounds=0,
              random_events=0, random_queries=0, compactions=0,
              sparse_set_prefixes=0)


def dependencies(n, matrix):
    return [{j for j in range(n) if matrix[i*n+j]} for i in range(n)]


def explore(deps, objects, depth):
    eager, lazy = Eager(deps, objects), BoundedLazy(deps, objects)
    history = []
    actions = [('pass', i) for i in range(len(deps))] + [('write', j) for j in range(objects)]

    def visit(left):
        counts['exhaustive_prefixes'] += 1
        lazy.check_representation()
        for i in range(len(deps)):
            expected = history_answer(history, deps, i)
            assert eager.use(i) == lazy.use(i) == expected, (deps, history, i)
            counts['exhaustive_queries'] += 1
        if left == 0:
            return
        for kind, x in actions:
            snapshot = (eager.bits, lazy.stamps[:], lazy.slots[:], lazy.clock,
                        lazy.updates, lazy.compactions, lazy.compaction_cells)
            history.append((kind, x))
            for monitor in (eager, lazy):
                (monitor.passed if kind == 'pass' else monitor.write)(x)
            visit(left-1)
            history.pop()
            (eager.bits, lazy.stamps, lazy.slots, lazy.clock,
             lazy.updates, lazy.compactions, lazy.compaction_cells) = snapshot
    visit(depth)


for n in range(1, 4):
    for matrix in product((False, True), repeat=n*n):
        deps = dependencies(n, matrix)
        explore(deps, n, 4)
        # Successive rounds reuse the monitor; the reduction must survive resets.
        eager, lazy = Eager(deps, n), BoundedLazy(deps, n)
        for vector in product((False, True), repeat=n):
            expected = [any(matrix[i*n+j] and vector[j] for j in range(n)) for i in range(n)]
            assert omv_round(eager, vector) == expected
            assert omv_round(lazy, vector) == expected
            lazy.check_representation()
            counts['omv_rounds'] += 1
        counts['compactions'] += lazy.compactions
    print('exhaustive claim/object count', n, 'passed', flush=True)

rng = random.Random(12026)
for trial in range(300):
    n, m = rng.randint(1, 24), rng.randint(1, 24)
    deps = [{j for j in range(m) if rng.random() < 0.4} for _ in range(n)]
    eager, lazy, history = Eager(deps, m), BoundedLazy(deps, m), []
    for step in range(500):
        if rng.random() < 0.5:
            event = ('pass', rng.randrange(n))
            eager.passed(event[1]); lazy.passed(event[1])
        else:
            event = ('write', rng.randrange(m))
            eager.write(event[1]); lazy.write(event[1])
        history.append(event)
        counts['random_events'] += 1
        for i in range(n):
            expected = history_answer(history, deps, i)
            assert eager.use(i) == lazy.use(i) == expected
            counts['random_queries'] += 1
        lazy.check_representation()
    assert lazy.compactions > 0
    counts['compactions'] += lazy.compactions

# Global reset must not resurrect stale sparse-array entries.
for n in range(1, 7):
    monitor = GlobalSparseSet(n)
    def visit_sparse(expected, left):
        counts['sparse_set_prefixes'] += 1
        assert [monitor.use(i) for i in range(n)] == [i in expected for i in range(n)]
        if left == 0:
            return
        for x in range(n+1):
            old = (monitor.dense[:], monitor.sparse[:], monitor.count)
            if x == n:
                monitor.reset(); new = set()
            else:
                monitor.passed(x); new = expected | {x}
            visit_sparse(new, left-1)
            monitor.dense, monitor.sparse, monitor.count = old
    visit_sparse(set(), 5)

# A naive modular timestamp is unsound: PASS at 1, then writes at 2, 3, 0.
checked, written = 1, 0
for t in [2, 3, 0]:
    written = t
assert written <= checked
assert history_answer([('pass', 0)] + [('write', 0)]*3, [{0}], 0) is False

# At exactly n bits, every encoding is a bijection and RESET has a unique code.
# Exhaustively test every encoding for n <= 3, not only ordinary bit vectors.
from itertools import permutations
encodings = 0
for n in range(1, 4):
    for codes in permutations(range(1 << n)):
        reset_code = codes[0]
        assert max((x ^ reset_code).bit_count() for x in codes) == n
        encodings += 1

result = dict(status='passed', **counts, exact_space_encodings_checked=encodings,
              naive_wraparound_counterexample='confirmed',
              scope='Finite differential and reduction checks; general proofs are in Results.txt. No novelty claim.')
Path(__file__).with_name('verification.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
