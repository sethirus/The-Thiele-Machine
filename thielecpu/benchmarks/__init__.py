"""
Benchmark module for blind vs sighted Thiele Machine comparison.

This module provides:
1. Problem generators for families with known structure
2. Blind and sighted solvers with μ-cost accounting
3. Benchmark harness for reproducible scaling studies

USAGE:
    from thielecpu.benchmarks import generate_tseitin_instance, BlindSolver, SightedSolver
    
    instance = generate_tseitin_instance(n=10, seed=42)
    blind_result = BlindSolver().solve(instance)
    sighted_result = SightedSolver().solve(instance)
"""

from .problem_families import (
    BenchmarkInstance,
    generate_instance,
    generate_tseitin_instance,
    generate_planted_sat_instance,
    generate_period_finding_instance,
    list_families,
    PROBLEM_FAMILIES,
)

from .solvers import (
    SolverResult,
    BlindSolver,
    SightedSolver,
    run_both_solvers,
)

__all__ = [
    # Problem families
    "BenchmarkInstance",
    "generate_instance",
    "generate_tseitin_instance",
    "generate_planted_sat_instance",
    "generate_period_finding_instance",
    "list_families",
    "PROBLEM_FAMILIES",
    # Solvers
    "SolverResult",
    "BlindSolver",
    "SightedSolver",
    "run_both_solvers",
]
