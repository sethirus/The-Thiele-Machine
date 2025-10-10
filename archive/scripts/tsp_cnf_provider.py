# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

from typing import List, Tuple
import math

class TspCnfProvider:
    def __init__(self, cities: List[Tuple[float, float]], max_length: int = None):
        self.cities = cities
        self.n = len(cities)
        self.var_counter = 0
        self._clauses: List[List[int]] = []
        self._var_map = {}  # (i, p) -> var

        # Create variables x[i][p]: city i at position p
        for i in range(self.n):
            for p in range(self.n):
                self._var_map[(i, p)] = self.new_var()

        # Add TSP constraints
        self._add_tsp_constraints()

        # If max_length is given, add length constraint
        if max_length is not None:
            self._add_length_constraint(max_length)

    def new_var(self) -> int:
        self.var_counter += 1
        return self.var_counter

    def add_clause(self, clause: List[int]) -> None:
        self._clauses.append(clause)

    def get_var(self, i: int, p: int) -> int:
        return self._var_map[(i, p)]

    def clauses_for_var(self, var: int) -> List[List[int]]:
        return [clause for clause in self._clauses if var in [abs(lit) for lit in clause]]

    def get_all_clauses(self) -> List[List[int]]:
        return self._clauses

    def _add_tsp_constraints(self) -> None:
        # Rule 1: Each position has exactly one city
        for p in range(self.n):
            # At least one
            self.add_clause([self.get_var(i, p) for i in range(self.n)])
            # At most one
            for i in range(self.n):
                for j in range(i + 1, self.n):
                    self.add_clause([-self.get_var(i, p), -self.get_var(j, p)])

        # Rule 2: Each city appears in exactly one position
        for i in range(self.n):
            # At least one
            self.add_clause([self.get_var(i, p) for p in range(self.n)])
            # At most one
            for p in range(self.n):
                for q in range(p + 1, self.n):
                    self.add_clause([-self.get_var(i, p), -self.get_var(i, q)])

    def _distance(self, i: int, j: int) -> float:
        x1, y1 = self.cities[i]
        x2, y2 = self.cities[j]
        return math.sqrt((x1 - x2)**2 + (y1 - y2)**2)

    def _add_length_constraint(self, max_length: int) -> None:
        # This is simplified; for demo, we skip the complex sum encoding
        # In a full implementation, we would add variables for the sum and constrain it
        pass

    def decode_tour(self, model: List[int]) -> List[int]:
        pos = {v for v in model if v > 0}
        tour = [-1] * self.n
        for i in range(self.n):
            for p in range(self.n):
                if self.get_var(i, p) in pos:
                    tour[p] = i
                    break
        return tour

    def calculate_length(self, tour: List[int]) -> float:
        length = 0
        for p in range(self.n):
            i = tour[p]
            j = tour[(p + 1) % self.n]
            length += self._distance(i, j)
        return length