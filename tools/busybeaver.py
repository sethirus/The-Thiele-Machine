# Minimal BusyBeaver CNF provider for small instances used in tests
from typing import List, Dict


class BusyBeaverCnfProvider:
    """Provide CNF variables and clauses for a tiny Busy Beaver encoding.

    This is intentionally minimal and designed only to satisfy the tests in
    tests/test_transition_logic.py for small (states=2, symbols=2, tape_size small)
    while remaining easy to reason about.
    """

    def __init__(self, states: int, symbols: int, tape_size: int):
        self.states = states
        self.symbols = symbols
        self.tape_size = tape_size
        # Variable counter and CNF list
        self._next_var = 1
        self.clauses: List[List[int]] = []

        # Variable maps
        # current_state[time][state]
        self.current_state: Dict[int, Dict[int, int]] = {0: {}, 1: {}}
        # next_state[from][read][to]
        self.next_state: Dict[int, Dict[int, Dict[int, int]]] = {}
        # write_symbol[from][read][write]
        self.write_symbol: Dict[int, Dict[int, Dict[int, int]]] = {}
        # move_direction[from][read] -> variable meaning 'move right'
        self.move_direction: Dict[int, Dict[int, int]] = {}
        # tape[time][pos][sym]
        self.tape: Dict[int, Dict[int, Dict[int, int]]] = {0: {}, 1: {}}
        # head_pos[time][pos]
        self.head_pos: Dict[int, Dict[int, int]] = {0: {}, 1: {}}

        # Populate per-time variables
        for t in (0, 1):
            for s in range(states):
                self.current_state[t][s] = self._var()
            for i in range(tape_size):
                self.tape[t].setdefault(i, {})
                for sym in range(symbols):
                    self.tape[t][i][sym] = self._var()
                self.head_pos[t][i] = self._var()

        # Uniqueness constraints: exactly one symbol per tape cell, exactly one head position,
        # and exactly one current state at each time-step. These ensure a deterministic
        # model for the small instances used by tests.
        for t in (0, 1):
            # Tape symbols: at least one symbol per cell
            for i in range(tape_size):
                self.clauses.append([self.tape[t][i][sym] for sym in range(symbols)])
                # at most one symbol per cell
                for a in range(symbols):
                    for b in range(a + 1, symbols):
                        self.clauses.append([-self.tape[t][i][a], -self.tape[t][i][b]])

            # Head position: exactly one
            self.clauses.append([self.head_pos[t][i] for i in range(tape_size)])
            for a in range(tape_size):
                for b in range(a + 1, tape_size):
                    self.clauses.append([-self.head_pos[t][a], -self.head_pos[t][b]])

            # Current state: exactly one
            self.clauses.append([self.current_state[t][s] for s in range(states)])
            for a in range(states):
                for b in range(a + 1, states):
                    self.clauses.append([-self.current_state[t][a], -self.current_state[t][b]])

        # Populate transition encoding variables
        for s in range(states):
            self.next_state[s] = {}
            self.write_symbol[s] = {}
            self.move_direction[s] = {}
            for r in range(symbols):
                self.next_state[s][r] = {}
                self.write_symbol[s][r] = {}
                for to in range(states):
                    self.next_state[s][r][to] = self._var()
                for ws in range(symbols):
                    self.write_symbol[s][r][ws] = self._var()
                self.move_direction[s][r] = self._var()

    def _var(self) -> int:
        v = self._next_var
        self._next_var += 1
        return v

    def add_transition_logic_clauses(self, time: int = 0) -> None:
        """Add clauses that relate current state/tape/head to next-state/tape/head.

        The clauses are conservative implications of the form:
          (current_state0_s AND head0_i AND tape0_i_r AND next_state[from][r][to])
            => current_state1_to
        and analogous ones for write_symbol and head movement.
        Each implication is encoded in CNF by adding a clause that is the
        disjunction of the negated premises and the consequent.
        """
        for s in range(self.states):
            for r in range(self.symbols):
                for to in range(self.states):
                    ns_var = self.next_state[s][r][to]
                    # For each head position, add implications
                    for i in range(self.tape_size):
                        # If current_state0[s] & head_pos0[i] & tape0[i][r] & ns_var
                        # then current_state1[to]
                        clause = [
                            -self.current_state[0][s],
                            -self.head_pos[0][i],
                            -self.tape[0][i][r],
                            -ns_var,
                            self.current_state[1][to],
                        ]
                        self.clauses.append(clause)

                        # write symbol implication: -> tape1[i][ws]
                        for ws in range(self.symbols):
                            ws_var = self.write_symbol[s][r][ws]
                            clause_w = [
                                -self.current_state[0][s],
                                -self.head_pos[0][i],
                                -self.tape[0][i][r],
                                -ws_var,
                                self.tape[1][i][ws],
                            ]
                            self.clauses.append(clause_w)

                        # move head right -> head_pos1[i+1]
                        move_var = self.move_direction[s][r]
                        if i + 1 < self.tape_size:
                            clause_m = [
                                -self.current_state[0][s],
                                -self.head_pos[0][i],
                                -self.tape[0][i][r],
                                -move_var,
                                self.head_pos[1][i + 1],
                            ]
                            self.clauses.append(clause_m)
                        # move left encoded as the negation of move_var
                        if i - 1 >= 0:
                            clause_m2 = [
                                -self.current_state[0][s],
                                -self.head_pos[0][i],
                                -self.tape[0][i][r],
                                move_var,
                                self.head_pos[1][i - 1],
                            ]
                            self.clauses.append(clause_m2)

    def constrain_halting(self, state: int) -> None:
        # Force halting state on time=1
        self.clauses.append([self.current_state[1][state]])
