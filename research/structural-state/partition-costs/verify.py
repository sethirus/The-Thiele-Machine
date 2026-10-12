#!/usr/bin/env python3
"""Independent relation-matrix reference, model checks, and workload checks."""
from copy import deepcopy
from dataclasses import dataclass, replace
from itertools import combinations_with_replacement
from pathlib import Path
import hashlib
import json
import random
import time

from monitors import (BulkMonitor, PairMonitor, ConnectivityViaMonitor,
                      WordMemory, Work, join_linear, pair_partition)


def canonical(labels):
    names = {}
    return tuple(names.setdefault(x, len(names)) for x in labels)


def partitions(n):
    result = []
    def extend(xs):
        if len(xs) == n:
            result.append(tuple(xs))
            return
        for x in range(max(xs, default=-1) + 2):
            extend(xs + [x])
    extend([])
    return result


def sound(p, key):
    return all(p[i] != p[j] or key[i] == key[j]
               for i in range(len(p)) for j in range(len(p)))


def closure(table, n):
    matrix = [[i == j for j in range(n)] for i in range(n)]
    for p in table:
        for i in range(n):
            for j in range(n):
                matrix[i][j] |= p[i] == p[j]
    for k in range(n):
        for i in range(n):
            for j in range(n):
                matrix[i][j] |= matrix[i][k] and matrix[k][j]
    return tuple(next(j for j in range(n) if matrix[i][j]) for i in range(n))


@dataclass(frozen=True)
class Reference:
    key: tuple
    table: tuple = ()
    channel: object = None
    record: object = None
    error: bool = False
    ledger: int = 0

    def step(self, op, p=None, exact=False):
        paid = replace(self, ledger=self.ledger + (op != 'SET'))
        if self.error:
            return paid
        if op == 'SET':
            return replace(paid, key=tuple(p), table=(), channel=None)
        if op == 'CHECK':
            return (replace(paid, table=(tuple(p),) + self.table) if sound(p, self.key)
                    else replace(paid, error=True))
        if op == 'COMMIT':
            if exact:
                allowed = any(canonical(p) == canonical(q) for q in self.table)
            else:
                allowed = bool(self.table) and sound(p, closure(self.table, len(self.key)))
            return replace(paid, channel=tuple(p)) if allowed else replace(paid, error=True)
        assert op == 'CERTIFY'
        if self.channel is None:
            return replace(paid, error=True)
        return replace(paid, record=self.record if self.record is not None
                       else (self.channel, self.key))


def observed(key, channel, record, error, ledger):
    return (canonical(key), None if channel is None else canonical(channel),
            None if record is None else tuple(map(canonical, record)), error, ledger)


def compare(monitor, reference):
    channel, record = monitor.channel, monitor.record
    if isinstance(monitor, PairMonitor):
        channel = None if channel is None else pair_partition(monitor.n, channel)
        record = None if record is None else (pair_partition(monitor.n, record[0]), record[1])
    assert observed(monitor.key, channel, record, monitor.error, monitor.ledger) == observed(
        reference.key, reference.channel, reference.record, reference.error, reference.ledger)
    assert monitor.evidence == bool(reference.table)
    if isinstance(monitor, BulkMonitor):
        assert canonical(monitor.join) == canonical(closure(reference.table, monitor.n))
        assert monitor.work.arcs_built <= 4 * (monitor.n - 1)
        assert monitor.work.arcs_scanned == monitor.work.arcs_built
    elif not monitor.exact:
        def root(i):
            while monitor.parent[i] != i:
                i = monitor.parent[i]
            return i
        assert canonical(tuple(root(i) for i in range(monitor.n))) == canonical(
            closure(reference.table, monitor.n))
        assert monitor.work.parent_reads <= 2 * monitor.n.bit_length()
    else:
        assert all(word.bit_length() <= monitor.word_bits for word in monitor.words)
        for pair in combinations_with_replacement(range(monitor.n), 2):
            index = monitor._index(pair)
            stored = bool(monitor.words[index // monitor.word_bits] & (1 << (index % monitor.word_bits)))
            expected = canonical(pair_partition(monitor.n, pair)) in set(map(canonical, reference.table))
            assert stored == expected


def exercise(monitor, reference, op, p=None):
    reference_p = p
    exact = False
    if isinstance(monitor, PairMonitor):
        exact = monitor.exact
        if op in ('CHECK', 'COMMIT'):
            reference_p = pair_partition(monitor.n, p)
    monitor.step(op, p)
    reference = reference.step(op, reference_p, exact=exact)
    compare(monitor, reference)
    return reference


def exhaustive(model, n=3, depth=4):
    ps = partitions(n)
    initial = [(model(k), Reference(k)) for k in ps]
    args = ps if model is BulkMonitor else list(combinations_with_replacement(range(n), 2))
    actions = [('SET', p) for p in ps]
    actions += [(op, p) for op in ('CHECK', 'COMMIT') for p in args]
    actions += [('CERTIFY', None)]
    frontier = {r: m for m, r in initial}
    seen = set(frontier)
    calls = 0
    for _ in range(depth):
        following = {}
        for reference, monitor in frontier.items():
            for op, p in actions:
                m = deepcopy(monitor)
                r = exercise(m, reference, op, p)
                if r not in seen:
                    following[r] = m
                calls += 1
        seen.update(following)
        frontier = following
    return {'transitions': calls, 'reference_states': len(seen)}


def main():
    counts = {}
    joins = 0
    for n in range(1, 6):
        ps = partitions(n)
        for p in ps:
            for q in ps:
                work = Work()
                result = join_linear(p, q, work)
                assert canonical(result) == canonical(closure((p, q), n))
                assert work.arcs_built == work.arcs_scanned <= 4 * (n - 1)
                joins += 1
    counts['exhaustive_joins_n1_to_n5'] = joins

    # General closure-state formula at K=top: three sound closure policies.
    ps = tuple(partitions(3))
    bottom = tuple(range(3))
    policies = {
        'exact': lambda table: frozenset(table),
        'add_tautology': lambda table: frozenset(table) | {bottom},
        'full_inference': lambda table: frozenset(p for p in ps if sound(p, closure(table, 3)))
    }
    formula_counts = {}
    for name, close in policies.items():
        active = set()
        for bits in range(1 << len(ps)):
            table = frozenset(p for i, p in enumerate(ps) if bits >> i & 1)
            assert table <= close(table) and close(close(table)) == close(table)
            for p in ps:
                assert close(table | {p}) == close(close(table) | {p})
            if table:
                active.add(close(table))
        signatures = {tuple(p in closed for p in ps) for closed in active}
        signatures.add((False,) * len(ps))  # Inactive guard rejects every claim.
        assert len(signatures) == 1 + len(active)
        formula_counts[name] = len(signatures)
    assert formula_counts == {'exact': 32, 'add_tautology': 17, 'full_inference': 6}
    counts['closure_policy_state_counts_n3'] = formula_counts

    counts['bulk_exhaustive'] = exhaustive(BulkMonitor)
    counts['pair_inferred_exhaustive'] = exhaustive(PairMonitor)
    counts['pair_exact_exhaustive'] = exhaustive(lambda k: PairMonitor(k, exact=True))

    rng = random.Random(20261013)
    calls = 0
    def refinement(key):
        p, prior = [], {}
        for i, k in enumerate(key):
            candidates = prior.setdefault(k, [])
            p.append(p[rng.choice(candidates)] if candidates and rng.random() < .7 else i)
            candidates.append(i)
        return tuple(p)
    for kind in ('bulk', 'pair_inferred', 'pair_exact'):
        for trial in range(180):
            n = rng.randrange(1, 9)
            key = tuple(rng.randrange(n) for _ in range(n))
            m = BulkMonitor(key) if kind == 'bulk' else PairMonitor(key, exact=kind == 'pair_exact')
            r = Reference(key)
            for _ in range(45):
                op = rng.choices(['SET', 'CHECK', 'COMMIT', 'CERTIFY'], [2, 6, 4, 2])[0]
                if op == 'SET':
                    p = tuple(rng.randrange(n) for _ in range(n))
                elif op == 'CERTIFY':
                    p = None
                elif kind == 'bulk':
                    basis = r.key if op == 'CHECK' else closure(r.table, n)
                    p = refinement(basis) if rng.random() < .85 else tuple(rng.randrange(n) for _ in range(n))
                else:
                    basis = r.key if op == 'CHECK' else closure(r.table, n)
                    candidates = [(i, j) for i in range(n) for j in range(i, n) if basis[i] == basis[j]]
                    p = rng.choice(candidates) if rng.random() < .85 else (rng.randrange(n), rng.randrange(n))
                r = exercise(m, r, op, p)
                calls += 1
                if r.error and rng.random() < .4:
                    m = BulkMonitor(key) if kind == 'bulk' else PairMonitor(key, exact=kind == 'pair_exact')
                    r = Reference(key)
    counts['random_model_transition_checks'] = calls

    # Input-coordinate witnesses for the deterministic probe lower bound.
    witnesses = 0
    for n in range(2, 13):
        bottom = tuple(range(n))
        for i in range(n):
            j = (i + 1) % n
            altered = list(bottom)
            altered[i] = altered[j]
            assert sum(x != y for x, y in zip(bottom, altered)) == 1
            for op in ('CHECK', 'COMMIT'):
                a, b = BulkMonitor(bottom), BulkMonitor(bottom)
                if op == 'COMMIT':
                    a.step('CHECK', bottom)
                    b.step('CHECK', bottom)
                a.step(op, bottom)
                b.step(op, altered)
                assert not a.error and b.error
                assert a.work.input_reads == n
                witnesses += 1
            a, b = BulkMonitor(bottom), BulkMonitor(bottom)
            a.step('SET', bottom)
            b.step('SET', altered)
            claim = pair_partition(n, (i, j))
            a.step('CHECK', claim)
            b.step('CHECK', claim)
            assert a.error and not b.error
            witnesses += 1
    counts['single_coordinate_input_lower_bound_witnesses'] = witnesses

    # Owned snapshots survive mutation of caller arrays and future SET/COMMIT.
    key, p = [0, 0, 0], [0, 0, 1]
    m = BulkMonitor(key)
    key[1] = 2
    m.step('CHECK', p)
    m.step('COMMIT', p)
    p[1] = 2
    m.step('CERTIFY')
    first = m.record
    assert first == ((0, 0, 1), (0, 0, 0))
    m.step('SET', [0, 1, 2])
    m.step('CHECK', [0, 1, 2])
    m.step('COMMIT', [0, 1, 2])
    m.step('CERTIFY')
    assert m.record is first and m.work.input_reads == 0
    counts['immutable_historical_snapshot_checks'] = 'passed'

    # A=B and B=C entails A=C; the exact policy still requires that pair itself.
    for exact in (False, True):
        m = PairMonitor([0, 0, 0], exact=exact)
        m.step('CHECK', (0, 1))
        m.step('CHECK', (1, 2))
        m.step('COMMIT', (0, 2))
        assert m.error == exact
        assert m.ledger == 3
        if not exact:
            m.step('CERTIFY')
            first = m.record
            assert first == ((0, 2), (0, 0, 0))
            m.step('SET', [0, 1, 2])
            assert m.record == first and m.channel is None and not m.evidence
            m.step('COMMIT', (0, 2))
            assert m.error and m.record == first
    counts['transitive_entitlement_and_mutation_checks'] = 'passed'

    # Reverse logging must restore repeated writes to the same address too.
    memory = WordMemory([4, 5, 6])
    memory.begin()
    memory.write(1, 9)
    memory.write(1, 10)
    memory.write(2, 99)
    memory.rollback()
    assert memory.words == [4, 5, 6] and memory.last_undo_words == 3
    queries = negatives = updates = 0
    for n in (2, 3, 8, 17, 64):
        wrapper = ConnectivityViaMonitor(n)
        graph = [set() for _ in range(n)]
        for _ in range(1400):
            i, j = rng.randrange(n), rng.randrange(n)
            if rng.random() < .16:
                wrapper.insert(i, j)
                graph[i].add(j)
                graph[j].add(i)
                updates += 1
            else:
                reached, stack = {i}, [i]
                while stack:
                    u = stack.pop()
                    for v in graph[u] - reached:
                        reached.add(v)
                        stack.append(v)
                before = tuple(wrapper.machine.memory.words)
                answer = wrapper.connected(i, j)
                assert answer == (j in reached)
                assert tuple(wrapper.machine.memory.words) == before
                assert not wrapper.machine.memory.read(0)
                queries += 1
                negatives += not answer
    counts['rollback_connectivity_queries'] = queries
    counts['rollback_negative_queries'] = negatives
    counts['rollback_connectivity_updates'] = updates

    # Scale checks exercise the proved linear graph-work bound, not timing claims.
    scale = []
    for n in (128, 512, 2048, 8192, 32768):
        m = BulkMonitor([0] * n)
        p = tuple(i // 2 for i in range(n))
        q = tuple((i + 1) // 2 for i in range(n))
        started = time.perf_counter()
        m.step('CHECK', p)
        first_arcs = m.work.arcs_scanned
        m.step('CHECK', q)
        elapsed = time.perf_counter() - started
        assert len(set(m.join)) == 1
        assert m.work.arcs_scanned <= 4 * (n - 1)
        scale.append({'n': n, 'two_check_seconds_observed': round(elapsed, 6),
                      'first_check_arc_scans': first_arcs,
                      'second_check_arc_scans': m.work.arcs_scanned})
    counts['bulk_scale_checks'] = scale

    # Build balanced union trees to exercise logarithmic depths (no compression).
    for n in (2, 4, 8, 16, 64, 256, 1024):
        m = PairMonitor([0] * n)
        width = 1
        while width < n:
            for start in range(0, n, 2 * width):
                m.step('CHECK', (start, start + width))
                assert m.work.parent_reads <= 2 * n.bit_length()
            width *= 2
        for i in range(n):
            m.step('COMMIT', (0, i))
            assert not m.error and m.work.parent_reads <= 2 * n.bit_length()
    counts['balanced_union_tree_checks'] = 'passed'

    root = Path(__file__).resolve().parent
    source = Path(__file__).resolve().parents[3] / 'minimal' / 'PartitionReading.v'
    result = {'status': 'passed', 'counts': counts,
              'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()
              if source.exists() else None,
              'scope': 'Algorithm checks support the separate proofs; timings are local observations.'}
    (root / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
