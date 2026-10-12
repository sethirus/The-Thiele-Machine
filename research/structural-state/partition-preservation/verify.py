#!/usr/bin/env python3
"""Finite checks accompanying Result.txt. Standard library only.

Reference rules correspond to minimal/PartitionReading.v at
e4c234627651f1b12eb649148a051d5a252ed6b4. Proofs are in the plaintext note.
"""
from dataclasses import dataclass, replace
from itertools import combinations
from pathlib import Path
import hashlib
import json
import random


def partitions(n):
    out = []
    def extend(xs):
        if len(xs) == n:
            out.append(tuple(xs))
            return
        for x in range(max(xs, default=-1) + 2):
            extend(xs + [x])
    extend([])
    return out


def relation(labels):
    return sum(1 << b for b, (i, j) in enumerate(combinations(range(len(labels)), 2))
               if labels[i] == labels[j])


def finer(p, q):
    return p & ~q == 0


def join(ps, n):
    parent = list(range(n))
    def root(i):
        while i != parent[i]:
            i = parent[i]
        return i
    union = 0
    for p in ps:
        union |= p
    for b, (i, j) in enumerate(combinations(range(n), 2)):
        if union & (1 << b):
            parent[root(i)] = root(j)
    return relation(tuple(root(i) for i in range(n)))


@dataclass(frozen=True)
class State:
    key: object
    table: object
    channel: object = None
    record: object = None
    error: bool = False
    ledger: int = 0


def reference_step(s, action):
    op, p = action
    paid = replace(s, ledger=s.ledger + (op != 'SET'))
    if s.error:
        return paid
    if op == 'SET':
        return replace(paid, key=p, table=(), channel=None)
    if op == 'CHECK':
        sound = all(p[i] != p[j] or s.key[i] == s.key[j]
                    for i in range(len(p)) for j in range(len(p)))
        return (replace(paid, table=(p,) + s.table) if sound
                else replace(paid, error=True))
    if op == 'COMMIT':
        same = any(all((p[i] == p[j]) == (q[i] == q[j])
                       for i in range(len(p)) for j in range(len(p)))
                   for q in s.table)
        return (replace(paid, channel=p) if same
                else replace(paid, error=True))
    assert op == 'CERTIFY'
    if s.channel is None:
        return replace(paid, error=True)
    if s.record is None:
        return replace(paid, record=(s.channel, s.key))
    return paid


def reduced_step(s, action):
    op, p = action
    paid = replace(s, ledger=s.ledger + (op != 'SET'))
    if s.error:
        return paid
    if op == 'SET':
        return replace(paid, key=p, table=frozenset(), channel=None)
    if op == 'CHECK':
        return (replace(paid, table=s.table | {p}) if finer(p, s.key)
                else replace(paid, error=True))
    if op == 'COMMIT':
        return (replace(paid, channel=p) if p in s.table
                else replace(paid, error=True))
    assert op == 'CERTIFY'
    if s.channel is None:
        return replace(paid, error=True)
    if s.record is None:
        return replace(paid, record=(s.channel, s.key))
    return paid


def canonical(s):
    return State(relation(s.key), frozenset(map(relation, s.table)),
                 None if s.channel is None else relation(s.channel),
                 None if s.record is None else tuple(map(relation, s.record)),
                 s.error, s.ledger)


def action_partition(action):
    op, p = action
    return op, None if p is None else relation(p)


@dataclass(frozen=True)
class InferenceState(State):
    evidence: bool = False


def policy_step(s, action, close, anchored=True):
    """Alternative policy, retaining the full checked set as reference."""
    op, p = action
    if not s.error and op == 'COMMIT':
        paid = replace(s, ledger=s.ledger + 1)
        allowed = (bool(s.table) or not anchored) and p in close(s.table)
        return replace(paid, channel=p) if allowed else replace(paid, error=True)
    return reduced_step(s, action)


def closure_state(s, close):
    return InferenceState(s.key, close(s.table), s.channel, s.record,
                          s.error, s.ledger, bool(s.table))


def closure_step(s, action, close):
    """Implementation retaining only a closed claim set and evidence flag."""
    op, p = action
    paid = replace(s, ledger=s.ledger + (op != 'SET'))
    if s.error:
        return paid
    if op == 'SET':
        return replace(paid, key=p, table=close(frozenset()),
                       channel=None, evidence=False)
    if op == 'CHECK':
        if not finer(p, s.key):
            return replace(paid, error=True)
        return replace(paid, table=close(s.table | {p}), evidence=True)
    if op == 'COMMIT':
        if not s.evidence or p not in s.table:
            return replace(paid, error=True)
        return replace(paid, channel=p)
    assert op == 'CERTIFY'
    if s.channel is None:
        return replace(paid, error=True)
    return replace(paid, record=s.record if s.record is not None
                   else (s.channel, s.key))


def check_step(s, a):
    result = reference_step(s, a)
    assert canonical(result) == reduced_step(canonical(s), action_partition(a))
    return result


def main():
    counts = {}
    expected_bell = [1, 2, 5, 15, 52]
    for n, bell in enumerate(expected_bell, 1):
        ps = partitions(n)
        assert len(ps) == len(set(map(relation, ps))) == bell
    counts['bell_numbers_n1_to_n5'] = expected_bell

    # Every checked family, candidate conclusion, and possible key for n<=3.
    cases = 0
    for n in range(1, 4):
        ps = list(map(relation, partitions(n)))
        for bits in range(1 << len(ps)):
            family = [p for i, p in enumerate(ps) if bits >> i & 1]
            j = join(family, n)
            for h in ps:
                entails = all(not all(finer(p, k) for p in family) or finer(h, k)
                              for k in ps)
                assert entails == finer(h, j)
                cases += 1
    counts['exhaustive_family_entailment_cases_n1_to_n3'] = cases

    # Every pair of premises on five objects, each conclusion, each key.
    ps = list(map(relation, partitions(5)))
    cases = 0
    for p in ps:
        for q in ps:
            j = join([p, q], 5)
            compatible_keys = [k for k in ps if finer(p, k) and finer(q, k)]
            for h in ps:
                assert all(finer(h, k) for k in compatible_keys) == finer(h, j)
                cases += 1
    counts['pair_entailment_cases_n5'] = cases

    # Exhaustive reachable raw states through four actions, starting at each key.
    ps = partitions(3)
    actions = [(op, p) for op in ('SET', 'CHECK', 'COMMIT') for p in ps]
    actions += [('CERTIFY', None)]
    frontier = {State(p, ()) for p in ps}
    seen = set(frontier)
    checks = 0
    for _ in range(4):
        following = set()
        for s in frontier:
            for a in actions:
                following.add(check_step(s, a))
                checks += 1
        frontier = following - seen
        seen |= following
    counts['exhaustive_transition_checks_n3_depth4'] = checks
    counts['exhaustive_reachable_reference_states'] = len(seen)

    # Random labels, longer traces, and successful as well as failing actions.
    rng = random.Random(20261012)
    checks = 0
    for trial in range(600):
        n = rng.randrange(1, 7)
        ps = partitions(n)
        def renamed(p):
            names = rng.sample(range(100, 1000), n)
            return tuple(names[i] for i in p)
        s = State(renamed(rng.choice(ps)), ())
        for step in range(50):
            op = rng.choices(['SET', 'CHECK', 'COMMIT', 'CERTIFY'], [2, 5, 4, 2])[0]
            if op == 'CERTIFY':
                a = (op, None)
            elif op == 'COMMIT' and s.table and rng.random() < .85:
                p = rng.choice(s.table)
                # Independently rename its equivalence classes.
                ids = {x: i for i, x in enumerate(dict.fromkeys(p))}
                a = (op, renamed(tuple(ids[x] for x in p)))
            elif op == 'CHECK' and rng.random() < .85:
                valid = [p for p in ps if finer(relation(p), relation(s.key))]
                a = (op, renamed(rng.choice(valid)))
            else:
                a = (op, renamed(rng.choice(ps)))
            s = check_step(s, a)
            checks += 1
            if s.error and rng.random() < .3:
                s = State(renamed(rng.choice(ps)), ())
    counts['random_transition_checks'] = checks

    # Every lower-bound history for n<=4, every possible distinguishing request.
    families = requests = 0
    for n in range(1, 5):
        ps = list(map(relation, partitions(n)))
        top = relation((0,) * n)
        others = [p for p in ps if p != top]
        signatures = set()
        for bits in range(1 << len(others)):
            chosen = [p for i, p in enumerate(others) if bits >> i & 1]
            history = [top] + chosen + [top] * (len(ps) - 1 - len(chosen))
            s = State(top, frozenset())
            for p in history:
                s = reduced_step(s, ('CHECK', p))
            assert s.ledger == len(ps) and join(s.table, n) == top
            assert not s.error and s.channel is None and s.record is None
            signature = 0
            for i, p in enumerate(others):
                succeeds = not reduced_step(s, ('COMMIT', p)).error
                signature |= int(succeeds) << i
                requests += 1
            assert not reduced_step(s, ('COMMIT', top)).error
            requests += 1
            assert signature == bits
            signatures.add(signature)
            families += 1
        assert len(signatures) == 1 << (len(ps) - 1)
    counts['equal_consequence_history_states_n1_to_n4'] = families
    counts['membership_separation_requests'] = requests

    # Explicit counterexamples and source-specific corner cases.
    top, h = (0, 0, 0), (0, 0, 1)
    initial = State(top, ())
    a = check_step(check_step(initial, ('CHECK', top)), ('CHECK', top))
    b = check_step(check_step(initial, ('CHECK', top)), ('CHECK', h))
    assert a.ledger == b.ledger == 2
    assert join(canonical(a).table, 3) == join(canonical(b).table, 3)
    assert check_step(a, ('COMMIT', h)).error
    assert not check_step(b, ('COMMIT', h)).error
    once = canonical(check_step(initial, ('CHECK', top)))
    twice = canonical(a)
    assert replace(once, ledger=0) == replace(twice, ledger=0)
    assert (once.ledger, twice.ledger) == (1, 2)
    first = check_step(check_step(a, ('COMMIT', top)), ('CERTIFY', None))
    changed = check_step(first, ('SET', h))
    assert changed.channel is None and changed.table == ()
    assert changed.record == first.record
    changed = check_step(check_step(changed, ('CHECK', h)), ('COMMIT', h))
    changed = check_step(changed, ('CERTIFY', None))
    assert changed.record == first.record
    trapped = check_step(initial, ('CERTIFY', None))
    assert check_step(trapped, ('SET', h)) == trapped
    assert check_step(trapped, ('CHECK', h)).ledger == trapped.ledger + 1
    counts['explicit_examples_and_corner_cases'] = 'passed'

    # Closure-policy implementations, including the evidence-presence flag.
    ps = tuple(map(relation, partitions(3)))
    def semantic_close(table):
        j = join(table, 3)
        return frozenset(p for p in ps if finer(p, j))
    actions = [(op, p) for op in ('SET', 'CHECK', 'COMMIT') for p in ps]
    actions += [('CERTIFY', None)]
    transition_checks = closure_identities = 0
    for close in (frozenset, semantic_close):
        for bits in range(1 << len(ps)):
            table = frozenset(p for i, p in enumerate(ps) if bits >> i & 1)
            assert table <= close(table)
            assert close(close(table)) == close(table)
            for p in ps:
                assert close(table | {p}) == close(close(table) | {p})
                closure_identities += 1
        frontier = {State(k, frozenset()) for k in ps}
        seen = set(frontier)
        for _ in range(4):
            following = set()
            for s in frontier:
                for action in actions:
                    result = policy_step(s, action, close)
                    assert closure_state(result, close) == closure_step(
                        closure_state(s, close), action, close)
                    if result.record is not None:
                        claim, historical_key = result.record
                        assert finer(claim, historical_key)
                        assert result.ledger >= 3
                    following.add(result)
                    transition_checks += 1
            frontier = following - seen
            seen |= following
    counts['closure_update_identities_n3'] = closure_identities
    counts['closure_policy_transition_checks_n3_depth4'] = transition_checks
    clean = State(relation((0, 0, 0)), frozenset())
    unanchored = policy_step(clean, ('COMMIT', 0), semantic_close, anchored=False)
    unanchored = policy_step(unanchored, ('CERTIFY', None), semantic_close, anchored=False)
    assert not unanchored.error and unanchored.record is not None
    assert unanchored.ledger == 2
    anchored = policy_step(clean, ('COMMIT', 0), semantic_close)
    assert anchored.error
    established_bottom = policy_step(clean, ('CHECK', 0), semantic_close)
    assert semantic_close(clean.table) == semantic_close(established_bottom.table)
    assert not policy_step(established_bottom, ('COMMIT', 0), semantic_close).error
    counts['empty_evidence_counterexample'] = 'passed'

    # Full exact-policy state bound, equal ledgers and action counts even for empty T.
    exact_histories = inference_states = 0
    for n in range(1, 5):
        ps = tuple(map(relation, partitions(n)))
        t, top = len(ps), relation((0,) * n)
        signatures = set()
        summaries = set()
        for bits in range(1 << t):
            table = frozenset(p for i, p in enumerate(ps) if bits >> i & 1)
            if table:
                ordered = sorted(table)
                hist = [('SET', top)] + [('CHECK', p) for p in ordered]
                hist += [('CHECK', ordered[0])] * (t - len(table))
            else:
                hist = [('CHECK', top)] * t + [('SET', top)]
            s = State(top, frozenset())
            for action in hist:
                s = reduced_step(s, action)
            assert len(hist) == t + 1 and s.ledger == t and s.table == table
            assert s.key == top and not s.error and s.channel is None and s.record is None
            signature = tuple(not reduced_step(s, ('COMMIT', p)).error for p in ps)
            assert signature == tuple(bool(bits >> i & 1) for i in range(t))
            signatures.add(signature)
            summaries.add((bool(table), join(table, n)))
            exact_histories += 1
        assert len(signatures) == 1 << t
        assert len(summaries) == t + 1
        # The alternate policy's B_n+1 summaries have distinct guard vectors.
        inferred_signatures = {tuple(active and finer(p, j) for p in ps)
                               for active, j in summaries}
        assert len(inferred_signatures) == t + 1
        inference_states += len(summaries)
    counts['full_exact_policy_equal_field_histories_n1_to_n4'] = exact_histories
    counts['distinct_anchored_entailment_states_n1_to_n4'] = inference_states

    root = Path(__file__).resolve().parent
    source = Path(__file__).resolve().parents[3] / 'minimal' / 'PartitionReading.v'
    result = {'status': 'passed', 'counts': counts,
              'reference_commit': 'e4c234627651f1b12eb649148a051d5a252ed6b4',
              'reference_sha256': hashlib.sha256(source.read_bytes()).hexdigest()
              if source.exists() else None,
              'scope': 'Finite checks; general proofs and limitations in Result.txt.'}
    (root / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
