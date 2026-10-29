#!/usr/bin/env python3
"""Reproduce the bounded checks in the root-text review.

Run: python scripts/audit_root_review.py
These finite enumerations check examples, not every theorem in the monograph.
The publication check uses the repository's native execution semantics; only
the external publication set is added here.
"""

from itertools import product
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from thiele_small.small import CA, exec_, fires, run, start  # noqa: E402


def holding_graphs():
    total = 0
    for k in range(1, 6):
        # Holding states 0..k-1, unfinished entrant k. All images lie in H.
        immediate = 0
        maximum = 0
        for f in product(range(k), repeat=k + 1):
            total += 1
            immediate += f[k] in f[:k]
            targets = {}
            source = k
            for collision_at in range(1, k + 2):
                target = f[source]
                if target in targets:
                    assert targets[target] != source
                    break
                targets[target] = source
                source = target
            else:
                raise AssertionError("finite holding orbit escaped collision")
            maximum = max(maximum, collision_at - 1)
        assert maximum == k
        if k == 3:
            assert immediate == 57
        print(f"H={k}: {k ** (k + 1)} graphs; {immediate} entry collisions; "
              f"maximum collision-free prefix {maximum}")
    assert total == 16739
    # An entry can collide even when the holding restriction is not onto.
    f = (0, 0, 1, 0)
    assert f[3] in f[:3] and set(f[:3]) != set(range(3))
    # Finite holding can also delay the collision after entry.
    f = (1, 2, 2, 0)
    assert f[3] not in f[:3]
    print("PASS: 16,739 graphs; review's entry-collision iff refuted")


def sliced_example_and_traps():
    for b, k in product(range(4), range(3)):
        r = k == 2
        rotate = ((b + 1) % 4, k)
        advance = (b, min(k + 1, 2))
        assert rotate[0] == (b + 1) % 4 and (rotate[1] == 2) == r
        assert advance[0] == b and r <= (advance[1] == 2)
        for successor, cost in ((rotate, 0), (advance, 1)):
            assert r or successor[1] != 2 or cost >= 1
    # A trapped representative in EVERY fibre forces h(b)=b on all B.
    surviving = [h for h in product(range(3), repeat=3)
                 if all(h[b] == b for b in range(3))]
    assert surviving == [(0, 1, 2)]
    print("PASS: 12-state sliced example; 1/27 base maps survives trapped fibres")


def publication_fibre():
    prepared = run([("CHECK", ("PGe", j), CA) for j in range(16)], start(16, 0))
    assert (prepared.pc, prepared.mu, prepared.va, prepared.vb) == (17, 16, 0, 0)
    assert prepared.facts == [(("PGe", j), CA, 0) for j in reversed(range(16))]
    nonempty_endpoint = None
    archives = set()
    for mask in range(1 << 16):
        state = prepared
        published = set()
        for j in range(16):
            commit = ("COMMIT", ("PGe", j), CA)
            state = exec_(state, commit)
            instruction = ("CERTIFY",) if mask & (1 << j) else commit
            if fires(state, instruction):
                published.add(state.chan)
            state = exec_(state, instruction)
        expected = frozenset((("PGe", j), CA, 0)
                             for j in range(16) if mask & (1 << j))
        assert frozenset(published) == expected
        assert (state.pc, state.mu, state.chan, state.err) == (
            49, 48, (("PGe", 15), CA, 0), False)
        assert state.cert == bool(mask)
        if mask:
            if nonempty_endpoint is None:
                nonempty_endpoint = state.key()
            assert state.key() == nonempty_endpoint
            archives.add(expected)
        else:
            empty_endpoint = state.copy()
    assert len(archives) == 65535
    empty_endpoint.cert = True
    assert empty_endpoint.key() == nonempty_endpoint
    print("PASS: 65,536 native runs; 65,535 nonempty archives above one full state")


if __name__ == "__main__":
    holding_graphs()
    sliced_example_and_traps()
    publication_fibre()
