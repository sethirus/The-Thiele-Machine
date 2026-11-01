"""Regression examples for what the record does and does not establish.

Each test pins one boundary the book states in words. Several of them show
a run that succeeds: the point is that the success means exactly what the
book says it means and no more. The machine is thiele_small/small.py, which
tests/test_realize.py compares step for step with minimal/EarnedCore.v.
"""

from __future__ import annotations

from thiele_small import small as E

ZERO = ("PZero",)
EVEN = ("PEven",)
AT_LEAST_0 = ("PGe", 0)
A, B = E.CA, E.CB


def _states(trace, s0):
    """Every state of a run of a trace, the start included."""
    out = [s0]
    for i in trace:
        out.append(E.exec_(out[-1], i))
    return out


def _first_raise(trace, s0):
    states = _states(trace, s0)
    for n in range(1, len(states)):
        if states[n].cert and not states[n - 1].cert:
            return n, states[n].chan
    return None


def test_the_collision_can_be_among_insiders_only():
    # Three states, two of them yes. The raising move sends 0 to 1, 1 to 2
    # and 2 to 2: the reading is permanent and the move merges, but the two
    # states that collide are both yes-states, and the entering state 0
    # lands where nothing else does (nec_f_collision_avoids_s).
    yes = {1, 2}
    move = {0: 1, 1: 2, 2: 2}
    assert all(move[s] in yes for s in yes)
    assert 0 not in yes and move[0] in yes
    preimages = {t: [s for s in move if move[s] == t] for t in set(move.values())}
    colliding = [ps for ps in preimages.values() if len(ps) > 1]
    assert colliding == [[1, 2]]
    assert preimages[move[0]] == [0]


def test_two_runs_end_alike_with_different_first_certifications():
    first = [("CHECK", ZERO, A), ("CHECK", ZERO, B), ("COMMIT", ZERO, A),
             ("CERTIFY",), ("COMMIT", ZERO, B)]
    second = [("CHECK", ZERO, A), ("CHECK", ZERO, B), ("COMMIT", ZERO, A),
              ("COMMIT", ZERO, B), ("CERTIFY",)]
    s0 = E.start(0, 0)
    end1, end2 = E.run(first, s0), E.run(second, s0)
    assert end1 == end2
    assert end1.cert and end1.mu == 5 and end1.chan == (ZERO, B, 0)
    assert _first_raise(first, s0) == (4, (ZERO, A, 0))
    assert _first_raise(second, s0) == (5, (ZERO, B, 0))


def test_a_check_that_cannot_fail_is_sound_and_certifies_from_every_start():
    prog = [("CHECK", AT_LEAST_0, A), ("COMMIT", AT_LEAST_0, A), ("CERTIFY",)]
    for a in range(6):
        for b in range(3):
            end = E.run(prog, E.start(a, b))
            assert end.cert and end.mu == 3 and not end.err
            assert E.eval_prop(AT_LEAST_0, end.ca)


def test_repeated_commitments_bill_without_raising_the_flag():
    trace = [("CHECK", ZERO, A)] + [("COMMIT", ZERO, A)] * 6
    end = E.run(trace, E.start(0, 0))
    assert E.total_cost(trace) == 7 and end.mu == 7
    assert not end.cert and not end.err
    assert len(end.facts) == 1 and end.chan == (ZERO, A, 0)


def test_a_write_after_the_commitment_still_certifies_a_claim_now_false():
    trace = [("CHECK", EVEN, A), ("COMMIT", EVEN, A), ("INC", A), ("CERTIFY",)]
    end = E.run(trace, E.start(0, 0))
    assert end.cert and end.mu == 3
    assert end.chan == (EVEN, A, 0) and end.va == 1
    assert not E.eval_prop(EVEN, end.ca)


def test_repeated_checks_of_one_claim_use_up_the_table():
    trace = [("CHECK", ZERO, A)] * E.FACT_CAP
    full = E.run(trace, E.start(0, 0))
    assert len(full.facts) == E.FACT_CAP and len(set(full.facts)) == 1
    assert not full.err
    over = E.exec_(full, ("CHECK", ZERO, A))
    assert over.err and over.facts == full.facts
    # A CHECK of a true property that doesn't pass says nothing about the property.
    assert E.eval_prop(ZERO, over.ca)
    after = E.run([("COMMIT", ZERO, A), ("CERTIFY",)], over)
    assert not after.cert and after.facts == full.facts and after.chan is None


def test_a_cheap_raising_instruction_can_follow_earlier_payments():
    trace = [("CHECK", ZERO, A), ("COMMIT", ZERO, A), ("CERTIFY",)]
    states = _states(trace, E.start(0, 0))
    raise_at, _ = _first_raise(trace, E.start(0, 0))
    assert E.cost(trace[raise_at - 1]) == 1
    assert states[raise_at - 1].mu == 2 and states[raise_at].mu == 3
