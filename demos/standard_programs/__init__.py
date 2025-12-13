"""Standard Programs Package.

This package contains normal programs that run in both:
1) Standard Python interpreter
2) Thiele VM
"""

from . import graph_coloring
from . import number_guessing
from . import password_cracker
from . import sorting_algorithms
from . import sudoku_solver

__all__ = [
	"number_guessing",
	"sorting_algorithms",
	"sudoku_solver",
	"graph_coloring",
	"password_cracker",
]
