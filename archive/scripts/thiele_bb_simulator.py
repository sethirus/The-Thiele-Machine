# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Simplified simulator for the Busy Beaver census.

This module provides a tiny wrapper around the PySAT ``Glucose4`` solver
that interacts with :class:`BusyBeaverCnfProvider`.  The implementation
is intentionally lightweight and does not attempt to encode the full Busy
Beaver transition logic.  Instead it focuses on offering the minimal
interfaces required by the top level ``bb_census.py`` script.

The real project described in the specification would need a far more
sophisticated encoding and solver strategy.  This file merely mirrors the
API so that example code and unit tests can be executed in a constrained
environment.
"""
from __future__ import annotations

from typing import Any, List, Optional

from pysat.solvers import Glucose4
import time


class ThieleBBSimulator:
    """SAT based simulator for Busy Beaver machines (demonstrational)."""

    def __init__(self, provider: Any):
        self.provider = provider
        self.solver = Glucose4()
        self.max_steps = 0

    # ------------------------------------------------------------------
    def load_base_rules(self, max_steps: int) -> None:
        """Load the CNF describing the machine for ``max_steps`` steps."""
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
        print(f"[{time.time() - start_time:.2f}s] Halting constraints added.")
        if self.provider.clauses:
            num_clauses = len(self.provider.clauses)
            print(f"[{time.time() - start_time:.2f}s] Appending {num_clauses:,} clauses to solver...")
            self.solver.append_formula(self.provider.clauses)
            print(f"[{time.time() - start_time:.2f}s] Solver ready with {num_clauses:,} clauses.")
        else:
            print(f"[{time.time() - start_time:.2f}s] No clauses to append.")

    # ------------------------------------------------------------------
    def solve_for_exact_steps(self, target_steps: int) -> Optional[List[int]]:
        """Return a model if a machine halts at ``target_steps``.

        The solver is queried with assumptions that the ``is_halted``
        variable for ``target_steps`` is true and all earlier halting
        variables are false.  If the instance is satisfiable, a model is
        returned; otherwise ``None`` is returned.
        """
        halt_var = self.provider.is_halted.get(target_steps)
        if halt_var is None:
            return None
        assumptions = [halt_var]
        for t, var in self.provider.is_halted.items():
            if t < target_steps:
                assumptions.append(-var)
        if self.solver.solve(assumptions=assumptions):
            return self.solver.get_model()
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
