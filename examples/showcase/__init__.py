# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Showcase programs demonstrating the Thiele Machine capabilities."""

from .sudoku_partition_solver import solve_sudoku_partitioned
from .prime_factorization_verifier import verify_factorization, factor_with_mu_accounting
from .blind_mode_turing import run_turing_compatible, run_thiele_sighted
from . import falsification_tests

__all__ = [
    'solve_sudoku_partitioned',
    'verify_factorization',
    'factor_with_mu_accounting',
    'run_turing_compatible',
    'run_thiele_sighted',
    'falsification_tests',
]
