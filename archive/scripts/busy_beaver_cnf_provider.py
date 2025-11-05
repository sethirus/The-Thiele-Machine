# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Simplified Busy Beaver CNF provider.

This file provides a very small stub of the interface described in the
project specification.  It does **not** implement the real Busy Beaver
logic; instead it only provides the minimal data structures required for
``ThieleBBSimulator`` to operate in a demonstrational fashion.  The
complete SAT encoding of the Busy Beaver problem would be extremely
large and is outside the scope of this lightweight example.

The class tracks a variable counter and exposes helper methods for
creating CNF clauses.  Runtime variables such as ``is_halted`` are
allocated so that callers can reason about halting times, but no actual
transition logic is generated.

This stub exists so that the rest of the codebase can run unit tests and
illustrate how the interface would look.  A full implementation would
need to translate the entire behaviour of a Turing machine into CNF.
"""
from __future__ import annotations

from typing import Dict, List, Optional, Tuple

Clause = List[int]
SoftClause = Tuple[List[int], int]  # (clause, weight)


class BusyBeaverCnfProvider:
    """CNF provider for Busy Beaver style Turing machines.

    The implementation is intentionally compact and only encodes a very
    small, fixed tape.  It nevertheless captures the essential transition
    semantics required by :class:`ThieleBBSimulator` so that tests can
    reason about single‑step behaviour.
    """

    def __init__(self, states: int = 6, symbols: int = 2, tape_size: int = 3, max_steps: int = 100):
        self.states = states
        self.symbols = symbols
        self.tape_size = tape_size
        self.max_steps = max_steps
        self.var_counter = 0
        self.clauses: List[Clause] = []
        self.soft_clauses: List[SoftClause] = []  # For Max-SAT optimization

        # Transition table variables (one-hot encodings)
        self.next_state: Dict[int, Dict[int, List[int]]] = {}
        self.write_symbol: Dict[int, Dict[int, List[int]]] = {}
        self.move_direction: Dict[int, Dict[int, int]] = {}

        for s in range(states):
            self.next_state[s] = {}
            self.write_symbol[s] = {}
            self.move_direction[s] = {}
            for sym in range(symbols):
                self.next_state[s][sym] = [self.new_var() for _ in range(states)]
                self.write_symbol[s][sym] = [self.new_var() for _ in range(symbols)]
                self.move_direction[s][sym] = self.new_var()
                # Enforce one-hot on transition table variables
                self.constrain_to_one_hot(self.next_state[s][sym])
                self.constrain_to_one_hot(self.write_symbol[s][sym])
                
                # Special constraints for halting state (state 4, the last state)
                if s == states - 1:  # Last state is halting
                    # From halting state, always transition back to halting state
                    self.add_clause([self.next_state[s][sym][states - 1]])  # Must go to last state
                    # Can write anything and move anywhere (doesn't matter since halted)
        
        # Additional constraint: ensure halting state transitions are consistent
        # If any transition goes to the halting state (last state), it should be treated as halting
        halting_state = states - 1
        for s in range(states - 1):  # Non-halting states
            for sym in range(symbols):
                # If transitioning to halting state, ensure it's the only possible next state
                for other_s in range(states - 1):
                    if other_s != halting_state:
                        # Cannot transition to both halting state and other_s
                        self.add_clause([-self.next_state[s][sym][halting_state], -self.next_state[s][sym][other_s]])

        # Runtime variables indexed by time step
        self.tape: Dict[int, Dict[int, List[int]]] = {}
        self.head_pos: Dict[int, List[int]] = {}
        self.current_state: Dict[int, List[int]] = {}
        self.is_halted: Dict[int, int] = {}
        
        # Step counter for optimization (binary encoded)
        self.step_counter_bits: List[int] = []

    # ------------------------------------------------------------------
    # Variable/Clause helpers
    # ------------------------------------------------------------------
    def new_var(self) -> int:
        self.var_counter += 1
        return self.var_counter

    def add_clause(self, clause: Clause) -> None:
        self.clauses.append(clause)

    # ------------------------------------------------------------------
    def constrain_to_one_hot(self, variables: List[int]) -> None:
        """Add clauses enforcing that exactly one variable is True."""
        # At least one
        self.add_clause(variables[:])
        # At most one (pairwise)
        for i in range(len(variables)):
            for j in range(i + 1, len(variables)):
                self.add_clause([-variables[i], -variables[j]])

    # ------------------------------------------------------------------
    def _ensure_runtime_vars(self, t: int) -> None:
        """Allocate one-hot variables for runtime entities at step ``t``."""
        if t not in self.tape:
            self.tape[t] = {}
            for cell_idx in range(self.tape_size):
                vars_ = [self.new_var() for _ in range(self.symbols)]
                self.tape[t][cell_idx] = vars_
                self.constrain_to_one_hot(vars_)
        if t not in self.head_pos:
            vars_ = [self.new_var() for _ in range(self.tape_size)]
            self.head_pos[t] = vars_
            self.constrain_to_one_hot(vars_)
        if t not in self.current_state:
            vars_ = [self.new_var() for _ in range(self.states)]
            self.current_state[t] = vars_
            self.constrain_to_one_hot(vars_)

    # ------------------------------------------------------------------
    def add_transition_logic_clauses(self, t: int) -> None:
        """Encode the state evolution from time ``t`` to ``t+1``."""

        # Ensure runtime variables exist for both time steps
        self._ensure_runtime_vars(t)
        self._ensure_runtime_vars(t + 1)

        for s in range(self.states):
            for sym_read in range(self.symbols):
                for cell_idx in range(self.tape_size):
                    state_var = self.current_state[t][s]
                    head_var = self.head_pos[t][cell_idx]
                    tape_var = self.tape[t][cell_idx][sym_read]

                    pre = self.new_var()

                    # precondition_true <-> state_var & head_var & tape_var
                    self.add_clause([-pre, state_var])
                    self.add_clause([-pre, head_var])
                    self.add_clause([-pre, tape_var])
                    self.add_clause([-state_var, -head_var, -tape_var, pre])
                    self.add_clause([state_var, -pre])
                    self.add_clause([head_var, -pre])
                    self.add_clause([tape_var, -pre])

                    # Consequence 1: next state
                    for next_s in range(self.states):
                        ns_var = self.next_state[s][sym_read][next_s]
                        cs_next = self.current_state[t + 1][next_s]
                        self.add_clause([-pre, -ns_var, cs_next])
                        self.add_clause([-pre, ns_var, -cs_next])

                    # Consequence 2: symbol written to current cell
                    for sym_write in range(self.symbols):
                        ws_var = self.write_symbol[s][sym_read][sym_write]
                        tape_next = self.tape[t + 1][cell_idx][sym_write]
                        self.add_clause([-pre, -ws_var, tape_next])
                        self.add_clause([-pre, ws_var, -tape_next])

                    # Consequence 3: head movement
                    move_var = self.move_direction[s][sym_read]
                    if cell_idx + 1 < self.tape_size:
                        hp_right = self.head_pos[t + 1][cell_idx + 1]
                        self.add_clause([-pre, -move_var, hp_right])
                        self.add_clause([-pre, -hp_right, move_var])
                    if cell_idx - 1 >= 0:
                        hp_left = self.head_pos[t + 1][cell_idx - 1]
                        self.add_clause([-pre, move_var, hp_left])
                        self.add_clause([-pre, -hp_left, -move_var])

                    # Frame axioms: cells not under the head remain unchanged
                    for other_cell in range(self.tape_size):
                        if other_cell == cell_idx:
                            continue
                        head_here = head_var
                        for sym in range(self.symbols):
                            cur_sym = self.tape[t][other_cell][sym]
                            next_sym = self.tape[t + 1][other_cell][sym]
                            self.add_clause([-head_here, -cur_sym, next_sym])
                            self.add_clause([-head_here, cur_sym, -next_sym])

    # ------------------------------------------------------------------
    def constrain_halting(self, max_steps: int) -> None:
        """Ensure the machine eventually halts within ``max_steps``.
        
        A machine halts when it transitions to state 0 (the halting state).
        We add constraints that:
        1. At least one halting event occurs
        2. Once halted, the machine stays in the halting state
        3. The halting variables are tied to reaching the halting state
        """
        halting_vars = []
        for t in range(1, max_steps + 1):
            var = self.new_var()
            self.is_halted[t] = var
            halting_vars.append(var)
            
            # Ensure runtime vars exist for this step
            self._ensure_runtime_vars(t)
            
            # Machine halts at step t if it enters the halting state (last state)
            halt_condition = self.current_state[t][self.states - 1]  # Last state is halting
            
            # is_halted[t] <-> current_state[t][states-1]
            self.add_clause([-var, halt_condition])
            self.add_clause([var, -halt_condition])
            
            # If halted at t, stay halted at t+1 (if t+1 exists)
            if t + 1 <= max_steps:
                self._ensure_runtime_vars(t + 1)
                # If halted at t, then at t+1 must be in halting state
                self.add_clause([-var, self.current_state[t + 1][self.states - 1]])
        
        # At least one halting event must occur
        if halting_vars:
            self.add_clause(halting_vars)

    # ------------------------------------------------------------------
    def apply_template_as_soft_constraint(self, template_machine: Dict, penalty_weight: int = 10) -> None:
        """Apply a template machine as soft constraints for Max-SAT optimization.
        
        Args:
            template_machine: Dict with keys 'next_state', 'write_symbol', 'move_direction'
            penalty_weight: Weight penalty for deviating from template
        """
        print(f"Applying template as soft constraints with penalty weight {penalty_weight}...")
        
        # Add soft constraints for next state transitions
        for s in range(self.states):
            for sym in range(self.symbols):
                if s in template_machine.get('next_state', {}) and sym in template_machine['next_state'][s]:
                    template_next = template_machine['next_state'][s][sym]
                    if template_next < self.states:
                        # Penalize if we don't choose the template's next state
                        penalty_var = self.new_var()
                        self.soft_clauses.append(([-penalty_var], penalty_weight))
                        
                        # penalty_var -> next_state[s][sym][template_next]
                        self.add_clause([-penalty_var, self.next_state[s][sym][template_next]])
        
        # Add soft constraints for write symbol
        for s in range(self.states):
            for sym in range(self.symbols):
                if s in template_machine.get('write_symbol', {}) and sym in template_machine['write_symbol'][s]:
                    template_write = template_machine['write_symbol'][s][sym]
                    if template_write < self.symbols:
                        # Penalize if we don't choose the template's write symbol
                        penalty_var = self.new_var()
                        self.soft_clauses.append(([-penalty_var], penalty_weight))
                        
                        # penalty_var -> write_symbol[s][sym][template_write]
                        self.add_clause([-penalty_var, self.write_symbol[s][sym][template_write]])
        
        # Add soft constraints for move direction
        for s in range(self.states):
            for sym in range(self.symbols):
                if s in template_machine.get('move_direction', {}) and sym in template_machine['move_direction'][s]:
                    template_move = template_machine['move_direction'][s][sym]
                    # template_move should be 0 (left) or 1 (right)
                    move_var = self.move_direction[s][sym]
                    
                    if template_move == 0:  # Should move left (move_var = True)
                        penalty_var = self.new_var()
                        self.soft_clauses.append(([-penalty_var], penalty_weight))
                        self.add_clause([-penalty_var, move_var])
                    elif template_move == 1:  # Should move right (move_var = False)
                        penalty_var = self.new_var()
                        self.soft_clauses.append(([-penalty_var], penalty_weight))
                        self.add_clause([-penalty_var, -move_var])
        
        print(f"Added {len(self.soft_clauses)} soft constraints to guide optimization toward template.")

    # ------------------------------------------------------------------
    def add_step_counter_constraints(self, max_steps: int) -> None:
        """Add binary-encoded step counter for optimization."""
        # Use binary encoding for efficiency
        bits_needed = (max_steps).bit_length()
        self.step_counter_bits = [self.new_var() for _ in range(bits_needed)]
        
        # No additional constraints needed for binary encoding
        
        # Link step counter to halting: if machine halts at step t, then step_counter should represent t
        for t in range(1, max_steps + 1):
            if t in self.is_halted:
                halt_var = self.is_halted[t]
                # Add clauses to enforce that if halted at t, then binary bits match t's binary representation
                t_binary = format(t, f'0{bits_needed}b')
                for i, bit in enumerate(t_binary):
                    bit_var = self.step_counter_bits[i]
                    if bit == '1':
                        self.add_clause([-halt_var, bit_var])  # If halted at t, bit must be 1
                    else:
                        self.add_clause([-halt_var, -bit_var])  # If halted at t, bit must be 0
