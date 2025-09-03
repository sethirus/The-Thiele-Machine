from __future__ import annotations
from typing import Dict, List, Set, Optional, Any
from pysat.solvers import Minisat22, Glucose4

class ThieleSimulator:
    def __init__(self, provider: Any):
        self.provider = provider
        self.solver = Minisat22()
        self._seen_clauses: Set[tuple] = set()
        self._var_processed: Dict[int, int] = {}

    def _add_var(self, var: int) -> None:
        # (Implementation remains the same as before)
        stack: List[int] = [var]
        while stack:
            v = stack.pop()
            clauses = self.provider.clauses_for_var(v)
            start = self._var_processed.get(v, 0)
            if start >= len(clauses): continue
            for clause in clauses[start:]:
                key = tuple(sorted(clause, key=abs))
                if key in self._seen_clauses: continue
                self._seen_clauses.add(key)
                self.solver.add_clause(clause)
                for lit in clause: stack.append(abs(lit))
            self._var_processed[v] = len(clauses)

    def deduce_frontier_with_lookahead(self,
                                       current_model: List[int],
                                       frontier_vars: List[int],
                                       lookahead_depth: int) -> Optional[List[int]]:
        """The core of the new engine. Solves for the frontier with temporary lookahead."""
        with Glucose4() as temp_solver:
            # 1. Load the known truth (the final model so far)
            temp_solver.append_formula([[l] for l in current_model])
            
            # 2. Load the logic for the current frontier
            for var in frontier_vars:
                # This uses a *temporary* simulator instance to avoid polluting the main one
                temp_sim = ThieleSimulator(self.provider)
                temp_sim._add_var(var)
                for clause in temp_sim._seen_clauses:
                    temp_solver.add_clause(list(clause))

            # 3. The Lookahead: Add future constraints to resolve ambiguity
            frontier_bit_index = self.provider.p_bits.index(frontier_vars[0])
            for i in range(1, lookahead_depth + 1):
                lookahead_idx = frontier_bit_index + i
                if lookahead_idx < self.provider.output_count():
                    temp_sim_lookahead = ThieleSimulator(self.provider)
                    temp_sim_lookahead._add_var(self.provider.output_var(lookahead_idx))
                    for clause in temp_sim_lookahead._seen_clauses:
                        temp_solver.add_clause(list(clause))

            # Add constraints for the product to equal N
            for i in range(self.provider.output_count()):
                bit_val = (self.provider.N >> i) & 1
                if bit_val:
                    temp_solver.add_clause([self.provider.output_var(i)])
                else:
                    temp_solver.add_clause([-self.provider.output_var(i)])

            # 4. Find all unique solutions for ONLY the frontier
            valid_assignments = []
            num_frontier = len(frontier_vars)
            for assignment in range(1 << num_frontier):
                assumptions = current_model[:]
                for j in range(num_frontier):
                    var = frontier_vars[j]
                    if assignment & (1 << j):
                        assumptions.append(var)
                    else:
                        assumptions.append(-var)
                if temp_solver.solve(assumptions=assumptions):
                    valid_assignments.append([var if assignment & (1 << j) else -var for j, var in enumerate(frontier_vars)])

            if len(valid_assignments) == 1:
                return valid_assignments[0] # Success: Unambiguous deduction
            else:
                return None # Failure: Ambiguity persists

    def solve(self) -> Optional[List[int]]:
        """Solve the entire problem by adding all clauses."""
        # For small problems like Sudoku, add all clauses
        if hasattr(self.provider, 'get_all_clauses'):
            for clause in self.provider.get_all_clauses():
                self.solver.add_clause(clause)
        else:
            # For lazy providers, add all variables
            for var in range(1, self.provider.var_counter + 1):
                self._add_var(var)
        if self.solver.solve():
            return self.solver.get_model()
        return None
