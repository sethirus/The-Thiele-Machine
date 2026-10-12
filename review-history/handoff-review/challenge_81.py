#!/usr/bin/env python3
"""Independent re-implementation of minimal/EarnedCore.v direct instruction
semantics (cexec/exec), used to re-derive the 81-history witness and the
zero-ledger reset cycle claimed in research/structural-state/machine-preservation.
Written from the Coq text, not from machine_models.py.
"""
from dataclasses import dataclass, replace
from itertools import product

CAP = 16


@dataclass(frozen=True)
class Core:
    a: int; b: int; va: int; vb: int; pc: int
    facts: tuple  # newest first, entries (prop, ctr, version)
    chan: object  # None or fact
    err: bool


@dataclass(frozen=True)
class State:
    core: Core; mu: int; cert: bool


def val(k, c): return k.a if c == 'A' else k.b
def ver(k, c): return k.va if c == 'A' else k.vb


def write(k, c, n, j):
    if c == 'A':
        return replace(k, a=n, va=k.va + 1, pc=j)
    return replace(k, b=n, vb=k.vb + 1, pc=j)


def evalp(p, v):
    kind, arg = p
    if kind == 'Zero': return v == 0
    if kind == 'Even': return v % 2 == 0
    if kind == 'Ge': return v >= arg
    raise ValueError(p)


def cost(i):
    return 1 if i[0] in ('CHECK', 'COMMIT', 'CERTIFY') else 0


def cexec(k, i):
    if k.err:
        return k
    op = i[0]
    if op == 'INC':
        c = i[1]; return write(k, c, val(k, c) + 1, k.pc + 1)
    if op == 'DEC':
        c, j = i[1], i[2]
        v = val(k, c)
        return replace(k, pc=k.pc + 1) if v == 0 else write(k, c, v - 1, j)
    if op == 'HALT':
        return k
    if op == 'CHECK':
        p, c = i[1], i[2]
        if evalp(p, val(k, c)) and len(k.facts) < CAP:
            return replace(k, pc=k.pc + 1, facts=((p, c, ver(k, c)),) + k.facts)
        return replace(k, err=True)
    if op == 'COMMIT':
        p, c = i[1], i[2]
        f = (p, c, ver(k, c))
        if f in k.facts:
            return replace(k, pc=k.pc + 1, chan=f)
        return replace(k, err=True)
    if op == 'CERTIFY':
        if k.chan is not None:
            return replace(k, pc=k.pc + 1)
        return replace(k, err=True)
    raise ValueError(i)


def fires(k, i):
    return i[0] == 'CERTIFY' and not k.err and k.chan is not None


def exec_(s, i):
    return State(cexec(s.core, i), s.mu + cost(i), s.cert or fires(s.core, i))


def run(tr, s):
    for i in tr:
        s = exec_(s, i)
    return s


def start(a, b):
    return State(Core(a, b, 0, 0, 1, (), None, False), 0, False)


def interface(s):
    k = s.core
    return (k.a, k.b, k.pc, k.err, s.mu, s.cert,
            tuple((p, c) for p, c, _ in k.facts),
            None if k.chan is None else (k.chan[0], k.chan[1]))


def history(r_a, r_b):
    """Eight Ge checks per counter; one INC/DEC pair placed after 8-r checks."""
    tr = []
    pc = 1
    for c, r in (('A', r_a), ('B', r_b)):
        for t in range(1, 9):
            if t == 8 - r + 1:
                tr.append(('INC', c)); pc += 1
                tr.append(('DEC', c, pc + 1)); pc += 1
            tr.append(('CHECK', ('Ge', t), c)); pc += 1
        if r == 0:
            tr.append(('INC', c)); pc += 1
            tr.append(('DEC', c, pc + 1)); pc += 1
    return tr


def main():
    # Two-history case from the note.
    s = start(8, 0)
    h1 = [('INC', 'A'), ('DEC', 'A', 3), ('CHECK', ('Ge', 8), 'A')]
    h2 = [('CHECK', ('Ge', 8), 'A'), ('INC', 'A'), ('DEC', 'A', 4)]
    e1, e2 = run(h1, s), run(h2, s)
    assert interface(e1) == interface(e2)
    assert e1.core.va == e2.core.va == 2 and e1.mu == e2.mu == 1
    c1, c2 = exec_(e1, ('COMMIT', ('Ge', 8), 'A')), exec_(e2, ('COMMIT', ('Ge', 8), 'A'))
    assert not c1.core.err and c2.core.err
    # Historical channel survives a write; re-commit fails.
    s0 = start(0, 0)
    t = run([('CHECK', ('Zero', None), 'A'), ('COMMIT', ('Zero', None), 'A'), ('INC', 'A'), ('CERTIFY',)], s0)
    assert t.cert and t.core.a == 1 and t.core.chan == (('Zero', None), 'A', 0)
    assert exec_(t, ('COMMIT', ('Zero', None), 'A')).core.err
    # Trapped machine still pays under direct semantics.
    assert exec_(exec_(t, ('COMMIT', ('Zero', None), 'A')), ('CERTIFY',)).mu == t.mu + 2

    # The 81 histories.
    ends = {}
    for r_a, r_b in product(range(9), repeat=2):
        tr = history(r_a, r_b)
        assert len(tr) == 20, len(tr)
        e = run(tr, start(8, 8))
        assert not e.core.err
        assert interface(e) == (8, 8, 21, False, 16, False,
                                tuple((('Ge', 8 - i % 8), 'B' if i < 8 else 'A') for i in range(16)), None)
        assert e.core.va == e.core.vb == 2
        ends[(r_a, r_b)] = e
    assert len({interface(e) for e in ends.values()}) == 1
    # Live prefix lengths actually are (r_a, r_b).
    for (r_a, r_b), e in ends.items():
        live_a = sum(1 for p, c, v in e.core.facts if c == 'A' and v == e.core.va)
        live_b = sum(1 for p, c, v in e.core.facts if c == 'B' and v == e.core.vb)
        assert (live_a, live_b) == (r_a, r_b)
    # Every pair is separated by a single COMMIT.
    keys = list(ends)
    separated = 0
    for x in range(len(keys)):
        for y in range(x + 1, len(keys)):
            ex, ey = ends[keys[x]], ends[keys[y]]
            found = False
            for c in ('A', 'B'):
                for t in range(1, 9):
                    i = ('COMMIT', ('Ge', t), c)
                    if exec_(ex, i).core.err != exec_(ey, i).core.err:
                        found = True; break
                if found: break
            assert found, (keys[x], keys[y])
            separated += 1
    assert separated == 81 * 80 // 2
    # Reset cycle R: zero ledger, all 81 collapse to one reduced state.
    R = [('INC', 'A'), ('DEC', 'A', 21), ('INC', 'B'), ('DEC', 'B', 21)]
    after = set()
    for e in ends.values():
        f = run(R, e)
        assert f.mu == e.mu and interface(f) == interface(e)
        live = (sum(1 for p, c, v in f.core.facts if c == 'A' and v == f.core.va),
                sum(1 for p, c, v in f.core.facts if c == 'B' and v == f.core.vb))
        assert live == (0, 0)
        for c in ('A', 'B'):
            for t in range(1, 9):
                assert exec_(f, ('COMMIT', ('Ge', t), c)).core.err
        after.add((interface(f), live))
    assert len(after) == 1
    print("81 pairwise COMMIT-separated histories with identical interface, versions 2/2, ledger 16: confirmed")
    print("Four-instruction cycle R collapses all 81 to one reduced state at zero ledger: confirmed")
    print("Numeric versions after R: ", sorted({(run(R, e).core.va, run(R, e).core.vb) for e in ends.values()}))


if __name__ == '__main__':
    main()
