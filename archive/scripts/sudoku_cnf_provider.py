# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

from typing import List

# Define Clause type locally since multiplier_cnf_provider was removed
Clause = List[int]

class SudokuCnfProvider:
    def __init__(self, puzzle_string: str):
        self.puzzle_string = puzzle_string
        self.var_counter = 0
        self._clauses: List[Clause] = []
        self._var_map = {}  # (r, c, d) -> var

        # Create variables
        for r in range(1, 10):
            for c in range(1, 10):
                for d in range(1, 10):
                    self._var_map[(r, c, d)] = self.new_var()

        # Add rules
        self._add_sudoku_rules()
        self._add_puzzle_constraints()

    def new_var(self) -> int:
        self.var_counter += 1
        return self.var_counter

    def add_clause(self, clause: Clause) -> None:
        self._clauses.append(clause)

    def get_var(self, r: int, c: int, d: int) -> int:
        return self._var_map[(r, c, d)]

    def clauses_for_var(self, var: int) -> List[Clause]:
        return [clause for clause in self._clauses if var in [abs(lit) for lit in clause]]

    def _add_sudoku_rules(self) -> None:
        # Rule 0: Each cell has at most one digit
        for r in range(1, 10):
            for c in range(1, 10):
                for d1 in range(1, 10):
                    for d2 in range(d1 + 1, 10):
                        self.add_clause([-self.get_var(r, c, d1), -self.get_var(r, c, d2)])

        # Rule 1: Each cell has at least one digit
        for r in range(1, 10):
            for c in range(1, 10):
                clause = [self.get_var(r, c, d) for d in range(1, 10)]
                self.add_clause(clause)

        # Rule 2: Each digit appears at most once in each row
        for r in range(1, 10):
            for d in range(1, 10):
                for c1 in range(1, 10):
                    for c2 in range(c1 + 1, 10):
                        self.add_clause([-self.get_var(r, c1, d), -self.get_var(r, c2, d)])

        # Rule 3: Each digit appears at most once in each column
        for c in range(1, 10):
            for d in range(1, 10):
                for r1 in range(1, 10):
                    for r2 in range(r1 + 1, 10):
                        self.add_clause([-self.get_var(r1, c, d), -self.get_var(r2, c, d)])

        # Rule 4: Each digit appears at most once in each 3x3 box
        for br in range(0, 3):
            for bc in range(0, 3):
                for d in range(1, 10):
                    cells = []
                    for r in range(br * 3 + 1, br * 3 + 4):
                        for c in range(bc * 3 + 1, bc * 3 + 4):
                            cells.append((r, c))
                    for i in range(len(cells)):
                        for j in range(i + 1, len(cells)):
                            r1, c1 = cells[i]
                            r2, c2 = cells[j]
                            self.add_clause([-self.get_var(r1, c1, d), -self.get_var(r2, c2, d)])

    def _add_puzzle_constraints(self) -> None:
        for i, char in enumerate(self.puzzle_string):
            if char != '0':
                r = i // 9 + 1
                c = i % 9 + 1
                d = int(char)
                self.add_clause([self.get_var(r, c, d)])

    def get_all_clauses(self) -> List[Clause]:
        return self._clauses