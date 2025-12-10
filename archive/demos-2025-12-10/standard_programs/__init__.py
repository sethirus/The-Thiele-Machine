# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Standard Programs Package

Normal programs that run in both:
1. Standard Python interpreter
2. Thiele VM

Demonstrates structural isomorphism between the two execution environments.
"""

from . import number_guessing
from . import sorting_algorithms
from . import sudoku_solver
from . import graph_coloring
from . import password_cracker

__all__ = [
    'number_guessing',
    'sorting_algorithms', 
    'sudoku_solver',
    'graph_coloring',
    'password_cracker',
]
