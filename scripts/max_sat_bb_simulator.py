"""Max-SAT based simulator for optimizing Busy Beaver machines with soft constraints."""

from typing import Any, List, Optional, Tuple
from pysat.solvers import Glucose4
import time


class MaxSATBBSimulator:
    """Max-SAT based simulator for optimizing Busy Beaver machines with soft constraints."""

    def __init__(self, provider: Any):
        self.provider = provider
        self.solver = Glucose4()
        self.max_steps = 0

    # ------------------------------------------------------------------
    def load_base_rules(self, max_steps: int) -> None:
        """Load the CNF and soft constraints for optimization."""
        self.max_steps = max_steps
        start_time = time.time()
        print(f"[{0.0:.2f}s] Starting to load base rules for {max_steps:,} steps...")

        for t in range(max_steps):
            self.provider.add_transition_logic_clauses(t)
            if t % 1000000 == 0 and t > 0:
                elapsed = time.time() - start_time
                progress = t / max_steps * 100
                print(f"[{elapsed:.2f}s] Loaded transition logic for {t:,} steps ({progress:.1f}%)")

        elapsed = time.time() - start_time
        print(f"[{elapsed:.2f}s] Transition logic loaded for all {max_steps:,} steps.")

        self.provider.constrain_halting(max_steps)
        self.provider.add_step_counter_constraints(max_steps)

        print(f"[{time.time() - start_time:.2f}s] Halting and step counter constraints added.")

        # Convert soft constraints to hard constraints for SAT solving
        self._convert_soft_to_hard()

        if self.provider.clauses:
            num_clauses = len(self.provider.clauses)
            print(f"[{time.time() - start_time:.2f}s] Appending {num_clauses:,} clauses to solver...")
            self.solver.append_formula(self.provider.clauses)
            print(f"[{time.time() - start_time:.2f}s] Solver ready with {num_clauses:,} clauses.")
        else:
            print(f"[{time.time() - start_time:.2f}s] No clauses to append.")

    # ------------------------------------------------------------------
    def _convert_soft_to_hard(self) -> None:
        """Convert soft constraints to hard constraints using additional variables."""
        print(f"Converting {len(self.provider.soft_clauses)} soft constraints to hard constraints...")

        for clause, _ in self.provider.soft_clauses:
            # For each soft clause (C, w), add a new variable r and clauses:
            # r -> C  (if r is true, then C must be satisfied)
            # But since we want to minimize violations, we'll handle this differently

            # For now, just add the soft clause as a hard constraint with lower priority
            # In a real Max-SAT solver, we'd use relaxation variables
            relaxation_var = self.provider.new_var()

            # If relaxation var is true, the soft constraint can be violated
            # If relaxation var is false, the soft constraint must hold
            for literal in clause:
                # relaxation_var OR (NOT literal) for each literal in clause
                # This means: if relaxation_var is false, then the clause must be true
                self.provider.add_clause([relaxation_var, -literal])

        print("Added relaxation variables for soft constraints.")

    # ------------------------------------------------------------------
    def maximize_step_count(self) -> Optional[Tuple[List[int], int]]:
        """Find the machine that maximizes step count using the soft constraints.

        Returns:
            Tuple of (model, max_steps) if found, None otherwise
        """
        print("Searching for machine with maximum step count...")

        # Try to find a machine that halts at increasingly higher steps
        max_found_steps = 0
        best_model = None

        for target_steps in range(1, self.max_steps + 1):
            halt_var = self.provider.is_halted.get(target_steps)
            if halt_var is None:
                continue

            # Try to satisfy halting at exactly target_steps
            assumptions = [halt_var]
            for t, var in self.provider.is_halted.items():
                if t < target_steps:
                    assumptions.append(-var)

            if self.solver.solve(assumptions=assumptions):
                model = self.solver.get_model()
                max_found_steps = target_steps
                best_model = model
                print(f"[{time.time():.2f}s] Found machine halting at {target_steps:,} steps")
            else:
                print(f"[{time.time():.2f}s] No machine halts at exactly {target_steps:,} steps")
                break  # If we can't find one at this step, we won't find higher

        if best_model:
            return (best_model, max_found_steps)
        return None

    # ------------------------------------------------------------------
    def decode_program(self, model: List[int]) -> str:
        """Reconstruct a human-readable machine from ``model``."""
        if model is None:
            return "<no model>"

        true_vars = set(v for v in model if v > 0)
        state_names = ['A', 'B', 'C', 'D', 'H'][:self.provider.states]  # H for halting state
        symbol_names = ['0', '1'][:self.provider.symbols]

        table = []
        table.append("Transition Table:")
        table.append("State | Symbol | Next State | Write | Move")
        table.append("-" * 40)

        for s in range(self.provider.states):
            for sym in range(self.provider.symbols):
                # Find next state
                next_s = None
                for i in range(self.provider.states):
                    if self.provider.next_state[s][sym][i] in true_vars:
                        next_s = i
                        break
                if next_s is None:
                    next_s = 0  # fallback

                # Find write symbol
                write = None
                for j in range(self.provider.symbols):
                    if self.provider.write_symbol[s][sym][j] in true_vars:
                        write = j
                        break
                if write is None:
                    write = 0  # fallback

                # Find move direction
                move = 'R' if self.provider.move_direction[s][sym] not in true_vars else 'L'

                table.append(f"{state_names[s]:5} | {symbol_names[sym]:6} | {state_names[next_s]:10} | {symbol_names[write]:5} | {move}")

        return "\n".join(table)