# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import sys
import os

import pytest

# Import BusyBeaver provider if available; otherwise skip the module
try:
    from tools.busybeaver import BusyBeaverCnfProvider  # type: ignore
except Exception:
    pytest.skip("BusyBeaverCnfProvider module not available", allow_module_level=True)

# Require a SAT solver (PySAT Glucose4) for CNF solving
try:
    from pysat.solvers import Glucose4
except Exception:
    pytest.skip("PySAT Glucose4 solver not available", allow_module_level=True)


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
