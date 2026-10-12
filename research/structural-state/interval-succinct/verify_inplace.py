from itertools import product
from pathlib import Path
import ast
import json
import random
from inplace_monitor import InplaceIntervalMonitor

counts = dict(bit_history_prefixes=0, block_history_prefixes=0,
              all_state_range_cases=0, random_events=0,
              adversarial_events=0, metadata_block_renewals=0,
              maximum_accesses=0, maximum_tree_nodes=0,
              arbitrary_memory_initializations=0)


def record(mon, expected, kind):
    accesses = mon.steps
    counts['maximum_accesses'] = max(counts['maximum_accesses'], accesses)
    # A deliberately loose finite-check envelope, not an asymptotic proof.
    assert accesses <= 500 * (1 + mon.q.bit_length()), (kind, mon.q, accesses)
    nodes = mon.check_representation(expected)
    counts['maximum_tree_nodes'] = max(counts['maximum_tree_nodes'], nodes)
    assert len(mon.words) * mon.w + mon.w < mon.n + 7 * mon.w


# Independent backward event interpretation rather than the implementation's tree.
def history_value(history, i):
    for kind, a, b in reversed(history):
        if kind == 'pass' and a == i:
            return True
        if kind == 'clear' and a <= i < b:
            return False
    return False


for n in range(1, 5):
    mon = InplaceIntervalMonitor(n, word_bits=max(2, n.bit_length()))
    actions = [('pass', i, i + 1) for i in range(n)]
    actions += [('clear', a, b) for a in range(n + 1) for b in range(a, n + 1)]
    history = []

    def visit(depth):
        counts['bit_history_prefixes'] += 1
        expected = sum(1 << i for i in range(n) if history_value(history, i))
        mon.check_representation(expected)
        if not depth:
            return
        for kind, a, b in actions:
            snap = mon.snapshot()
            history.append((kind, a, b))
            if kind == 'pass':
                mon.passed(a)
            else:
                mon.clear_range(a, b)
            visit(depth - 1)
            history.pop()
            mon.restore(snap)

    visit(4)
print('exhaustive individual-bit histories passed', flush=True)

# Each logical status is now in a separate physical block, exercising the
# intrusive tree rather than only a one-block raw representation.
for blocks in range(1, 5):
    w, block_bits = 12, 72
    n = blocks * block_bits
    mon = InplaceIntervalMonitor(n, word_bits=w)
    actions = [('pass', i * block_bits, 0) for i in range(blocks)]
    actions += [('clear', a * block_bits, b * block_bits)
                for a in range(blocks + 1) for b in range(a, blocks + 1)]

    def visit_blocks(expected, depth):
        counts['block_history_prefixes'] += 1
        mon.check_representation(expected)
        if not depth:
            return
        for kind, a, b in actions:
            snap = mon.snapshot()
            if kind == 'pass':
                mon.passed(a)
                after = expected | (1 << a)
            else:
                mon.clear_range(a, b)
                after = expected & ~(((1 << (b - a)) - 1) << a)
            visit_blocks(after, depth - 1)
            mon.restore(snap)

    visit_blocks(0, 3)
print('exhaustive multi-block histories passed', flush=True)

rng = random.Random(2026101203)
# All 256 block-status vectors, alternative construction orders, all ranges,
# then renewal at the root's physical block (the delicate self-overwrite case).
for blocks in range(1, 9):
    w, size = 12, 72
    n = blocks * size - 3
    mon = InplaceIntervalMonitor(n, word_bits=w)
    for bits in range(1 << blocks):
        for order in (list(range(blocks)), list(reversed(range(blocks)))):
            mon.clear_range(0, n)
            expected = 0
            for block in order:
                if (bits >> block) & 1:
                    i = block * size
                    mon.passed(i)
                    expected |= 1 << i
            state = mon.snapshot()
            for a in range(blocks + 1):
                for b in range(a, blocks + 1):
                    mon.restore(state)
                    lo, hi = min(a * size, n), min(b * size, n)
                    mon.clear_range(lo, hi)
                    after = expected & ~(((1 << (hi - lo)) - 1) << lo)
                    record(mon, after, 'range')
                    if mon.root:
                        i = (mon.root - 1) * size
                        mon.passed(i)
                        after |= 1 << i
                        record(mon, after, 'root renewal')
                        counts['metadata_block_renewals'] += 1
                    counts['all_state_range_cases'] += 1
print('all block states / range clears / root renewals passed', flush=True)

for trial in range(100):
    n = rng.randrange(1, 2200)
    w = max(12, n.bit_length())
    mon, expected = InplaceIntervalMonitor(n, word_bits=w), 0
    # Initialization is independent of the old bits in the allocated words.
    mon.words[:] = [rng.getrandbits(w) for _ in mon.words]
    mon._new(1, mon.q)
    mon.root = 1
    mon.check_representation(0)
    counts['arbitrary_memory_initializations'] += 1
    for step in range(300):
        if rng.random() < .68:
            i = rng.randrange(n)
            mon.passed(i)
            expected |= 1 << i
            kind = 'pass'
        else:
            lo, hi = sorted((rng.randrange(n + 1), rng.randrange(n + 1)))
            mon.clear_range(lo, hi)
            expected &= ~(((1 << (hi - lo)) - 1) << lo)
            kind = 'write'
        record(mon, expected, kind)
        counts['random_events'] += 1
print('random histories and arbitrary initial memory passed', flush=True)

# Fragmentation, large bulk deletion, first/last/middle node materialization,
# ascending and descending point insertions, and rotated tree shapes.
for blocks in (17, 65, 129):
    w, size = 16, 96
    n = blocks * size - 5
    for ordering in (list(range(blocks)), list(reversed(range(blocks))),
                     rng.sample(range(blocks), blocks)):
        mon, expected = InplaceIntervalMonitor(n, word_bits=w), 0
        for repeat in range(4):
            for block in ordering:
                i = block * size
                mon.passed(i); expected |= 1 << i
                record(mon, expected, 'fragment setup')
                counts['adversarial_events'] += 1
            for block in ordering[::2]:
                lo, hi = block * size, min((block + 1) * size, n)
                mon.clear_range(lo, hi)
                expected &= ~(((1 << (hi - lo)) - 1) << lo)
                record(mon, expected, 'fragment holes')
                counts['adversarial_events'] += 1
            lo, hi = size + 3, n - size - 3
            mon.clear_range(lo, hi)
            expected &= ~(((1 << (hi - lo)) - 1) << lo)
            record(mon, expected, 'bulk clear fragmented tree')
            counts['adversarial_events'] += 1
            # Start a later phase with every status fresh, so full blocks
            # contain arbitrary data bits, not merely one representative bit.
            for block in (0, blocks // 2, blocks - 1):
                for i in range(block * size, min((block + 1) * size, n)):
                    mon.passed(i); expected |= 1 << i
                    counts['adversarial_events'] += 1
                record(mon, expected, 'dense boundary block')
print('fragmentation and node-storage reuse adversaries passed', flush=True)

# Verify that the production operation call graph has no recursion. Debug
# helpers are deliberately excluded: their independent invariant checks use
# temporary sets and lists that are not part of the representation.
tree = ast.parse(Path('inplace_monitor.py').read_text())
methods = {n.name: n for c in tree.body if isinstance(c, ast.ClassDef)
           for n in c.body if isinstance(n, ast.FunctionDef)}
excluded = {'snapshot', 'restore', 'check_representation'}
edges = {name: {x.func.attr for x in ast.walk(node)
                if isinstance(x, ast.Call) and isinstance(x.func, ast.Attribute)
                and isinstance(x.func.value, ast.Name) and x.func.value.id == 'self'
                and x.func.attr in methods and x.func.attr not in excluded}
         for name, node in methods.items() if name not in excluded}

def depth(name, active=()):
    assert name not in active, ('recursive operation', name, active)
    return 1 + max((depth(child, active + (name,)) for child in edges[name]), default=0)

counts['operation_call_depth'] = max(depth(name) for name in edges)
result = {'status': 'passed', **counts,
          'scope': 'Semantic, tree-invariant, storage-reuse and finite access checks; general bounds require the proof.'}
Path('verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2), flush=True)
