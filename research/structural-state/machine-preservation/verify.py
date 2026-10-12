from itertools import combinations, product
from pathlib import Path
import hashlib
import json
import random

from machine_models import (Reference, abstract, reference_step, reduced_step,
                            run, program_step, boundary_family, reset_cycle,
                            edition_abstract, edition_step, gap_history, edition_gaps)

counts = dict(differential_prefixes=0, random_steps=0, program_steps=0,
              boundary_states=0, separating_pairs=0, reset_maps=0,
              retention_functions=0, tight_retention_examples=0,
              edition_gap_histories=0, edition_gap_patterns=0)


def compare(s, instruction):
    after = reference_step(s, instruction)
    assert abstract(after) == reduced_step(abstract(s), instruction), (s, instruction)
    assert edition_abstract(after) == edition_step(edition_abstract(s), instruction)
    return after


actions = (('inc', 0), ('inc', 1), ('dec', 0, 1), ('dec', 1, 3),
           ('halt',), ('certify',), ('check', ('zero', 0), 0),
           ('check', ('even', 0), 1), ('check', ('ge', 1), 0),
           ('commit', ('zero', 0), 0), ('commit', ('even', 0), 1),
           ('commit', ('ge', 1), 0))


def visit(s, depth):
    counts['differential_prefixes'] += 1
    abstract(s)
    if depth:
        for instruction in actions:
            visit(compare(s, instruction), depth - 1)


for values in ((0, 0), (1, 0), (0, 2), (3, 4)):
    visit(Reference(values=values), 4)
print('short histories: all instruction types, traps and latch passed', flush=True)

rng = random.Random(20261012)
for trial in range(160):
    s = Reference(values=(rng.randrange(12), rng.randrange(12)))
    for _ in range(100):
        c = rng.randrange(2)
        prop = rng.choice((('zero', 0), ('even', 0), ('ge', rng.randrange(15))))
        instruction = rng.choice((('inc', c), ('dec', c, rng.randrange(8)),
                                  ('check', prop, c), ('commit', prop, c),
                                  ('certify',), ('halt',)))
        s = compare(s, instruction)
        counts['random_steps'] += 1

# Curated long histories reach capacity and all channel/latch combinations.
for a in range(17):
    _, family = boundary_family(a, 16 - a)
    for s, trace in family.values():
        for c in (0, 1):
            for instruction in (('check', ('ge', 0), c),
                                ('commit', ('ge', 0), c), ('certify',)):
                compare(s, instruction)
        for instruction in reset_cycle(s.pc) * 5:
            s = compare(s, instruction)

for _ in range(150):
    program = tuple(rng.choice(actions) for _ in range(12))
    s = Reference(values=(rng.randrange(4), rng.randrange(4)))
    q = abstract(s)
    for _ in range(60):
        s = program_step(s, program, reference_step)
        q = program_step(q, program, reduced_step)
        assert abstract(s) == q
        counts['program_steps'] += 1
print('long and stored-program correspondence passed', flush=True)

# Explicit semantic boundary: historical commitment survives a later mutation.
s = Reference()
for instruction in (('check', ('zero', 0), 0), ('commit', ('zero', 0), 0),
                    ('inc', 0), ('certify',)):
    s = compare(s, instruction)
assert s.certified and not s.error and s.ledger == 3
assert s.channel == (('zero', 0), 0, 0) and s.versions[0] == 1
blocked = compare(s, ('commit', ('zero', 0), 0))
assert blocked.error and blocked.certified and blocked.ledger == 4
frozen = compare(blocked, ('check', ('ge', 0), 0))
assert frozen.facts == blocked.facts and frozen.ledger == 5
assert program_step(blocked, (('check', ('ge', 0), 0),), reference_step) == blocked

# Duplicate CHECKs occupy slots, and the seventeenth traps even if true.
s = Reference()
for _ in range(16):
    s = compare(s, ('check', ('ge', 0), 0))
assert len(s.facts) == 16 and not s.error
assert compare(s, ('check', ('ge', 0), 0)).error
print('historical commitment, duplicate capacity and ledger corner cases passed', flush=True)

_, family = boundary_family()
fixed = set()
for s, _ in family.values():
    fixed.add((s.values, s.versions, s.pc, tuple((p, c) for p, c, _ in s.facts),
               s.channel, s.error, s.ledger, s.certified))
assert len(fixed) == 1 and len(family) == 81
counts['boundary_states'] = len(family)
witnesses = []
for (cuts1, (s1, _)), (cuts2, (s2, _)) in combinations(family.items(), 2):
    witness = None
    for c in (0, 1):
        for threshold in range(1, 9):
            instruction = ('commit', ('ge', threshold), c)
            a, b = compare(s1, instruction), compare(s2, instruction)
            if a.error != b.error:
                witness = instruction
                break
        if witness:
            break
    assert witness is not None
    counts['separating_pairs'] += 1
    if len(witnesses) < 3:
        witnesses.append(dict(cuts1=cuts1, cuts2=cuts2, next_instruction=witness))

outputs = set()
for s, _ in family.values():
    after = run(s, reset_cycle(s.pc), reference_step)
    q = abstract(after)
    assert q.live == (0, 0) and q.values == s.values and q.pc == s.pc
    assert q.ledger == s.ledger
    outputs.add(q)
    counts['reset_maps'] += 1
assert len(outputs) == 1
print('81 states, 3240 separating continuations, zero-ledger reset passed', flush=True)

gap_cases = {(i, 0) for i in range(256)} | {(0, i) for i in range(256)}
gap_cases |= {(rng.randrange(256), rng.randrange(256)) for _ in range(600)}
for a, b in sorted(gap_cases):
    s = Reference(values=(8, 8))
    for instruction in gap_history(a, b):
        s = compare(s, instruction)
    assert (s.values, s.versions, s.pc, s.ledger) == ((8, 8), (16, 16), 49, 16)
    assert edition_gaps(edition_abstract(s)) == (a, b)
    for instruction in reset_cycle(s.pc):
        s = compare(s, instruction)
    assert edition_gaps(edition_abstract(s)) == (a | 128, b | 128)
    counts['edition_gap_histories'] += 1

fibres = {}
for bits in range(1 << 16):
    after = bits | (1 << 7) | (1 << 15)
    fibres[after] = fibres.get(after, 0) + 1
    counts['edition_gap_patterns'] += 1
assert len(fibres) == (1 << 14) and set(fibres.values()) == {4}
print('edition equality/order preservation and 65536-to-16384 reset passed', flush=True)

# Exhaustive finite reset systems. N-1 distinct nonzero-output start states,
# one zero-output start state; every transition maps into the zero fibre.
# Extra nonzero-labelled states cannot help: all post-reset states are zero.
def injective_horizon(mapping, starts, cap):
    domain = set()
    frontier = set(starts)
    for depth in range(1, cap + 1):
        domain.update(frontier)
        if len({mapping[x] for x in domain}) != len(domain):
            return depth - 1
        frontier = {mapping[x] for x in frontier}
    return cap


for n in (2, 3, 4):
    for m in range(n, 7):
        best = 0
        for mapping in product(range(n - 1, m), repeat=m):
            horizon = injective_horizon(mapping, range(n), m)
            assert m >= 1 + (horizon + 1) * (n - 1)
            best = max(best, horizon)
            counts['retention_functions'] += 1
        expected = (m - 1) // (n - 1) - 1
        assert best == expected, (n, m, best, expected)

for n in (2, 3, 9, 81):
    for horizon in range(1, 9):
        # One fixed zero state, N-1 disjoint paths of T+1 states each.
        m = 1 + (n - 1) * (horizon + 1)
        mapping, starts = list(range(m)), [0]
        for path in range(n - 1):
            start = 1 + path * (horizon + 1)
            starts.append(start)
            for offset in range(horizon):
                mapping[start + offset] = start + offset + 1
        assert injective_horizon(mapping, starts, horizon + 1) == horizon
        counts['tight_retention_examples'] += 1
print('finite retention lower bound and matching reset-only constructions passed', flush=True)

source = Path(__file__).resolve().parents[3] / 'minimal' / 'EarnedCore.v'
result = dict(status='passed', **counts, sample_separators=witnesses,
              reference_commit='e4c234627651f1b12eb649148a051d5a252ed6b4',
              reference_sha256=(hashlib.sha256(source.read_bytes()).hexdigest()
                                if source.exists() else None),
              scope='Independent executable models and finite cases; general theorems require the written proofs.')
Path('verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2), flush=True)
