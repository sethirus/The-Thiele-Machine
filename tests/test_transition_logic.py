import sys
import os

import pytest
from pysat.solvers import Glucose4

sys.path.append(os.path.dirname(os.path.dirname(__file__)))
from archive.scripts.busy_beaver_cnf_provider import BusyBeaverCnfProvider


def build_solver(prov):
    s = Glucose4()
    s.append_formula(prov.clauses)
    return s


def seed_machine(s, prov):
    # transition: state0 reading0 -> write1, move right, goto state1
    s.add_clause([prov.next_state[0][0][1]])
    s.add_clause([prov.write_symbol[0][0][1]])
    s.add_clause([prov.move_direction[0][0]])  # right
    # initial configuration
    s.add_clause([prov.current_state[0][0]])
    s.add_clause([prov.head_pos[0][1]])
    for idx in range(prov.tape_size):
        s.add_clause([prov.tape[0][idx][0]])


def test_single_step_transition():
    prov = BusyBeaverCnfProvider(states=2, symbols=2, tape_size=3)
    prov.add_transition_logic_clauses(0)
    prov.constrain_halting(1)

    solver = build_solver(prov)
    seed_machine(solver, prov)
    assert solver.solve()
    model = set(solver.get_model())

    assert prov.current_state[1][1] in model
    assert prov.tape[1][1][1] in model
    assert prov.head_pos[1][2] in model
    assert prov.tape[1][0][0] in model
    assert prov.tape[1][2][0] in model

    # contradictory assumption on written symbol should make instance unsat
    solver2 = build_solver(prov)
    seed_machine(solver2, prov)
    solver2.add_clause([-prov.tape[1][1][1]])
    assert not solver2.solve()
