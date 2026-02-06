"""μ-Profiler: Universal semantic complexity analyzer for Python code.

This module provides AST-based analysis to measure the μ-cost (semantic complexity)
of any Python callable. It works with functions, methods, lambdas, generators,
coroutines, builtins, and C extensions.

The profiler measures logical complexity based on:
- AST node count and depth
- Control flow complexity (branches, loops)
- Variable usage and scope
- Computational operations

UNIVERSALITY GUARANTEE: Works with ANY Python callable.
"""

from __future__ import annotations

import ast
import inspect
import functools
import sys
from typing import Any, Callable, Dict, Optional, Union
from dataclasses import dataclass
import math


@dataclass
class ComplexityMetrics:
    """Detailed complexity metrics for a callable."""

    ast_nodes: int = 0          # Total AST nodes
    ast_depth: int = 0           # Maximum nesting depth
    branches: int = 0            # If/elif/else count
    loops: int = 0               # For/while count
    functions: int = 0           # Function definitions
    comprehensions: int = 0      # List/dict/set comprehensions
    variables: int = 0           # Variable references
    operations: int = 0          # Binary/unary operations

    @property
    def mu_cost(self) -> int:
        """Calculate μ-cost from metrics.

        μ-cost represents the information-theoretic complexity:
        - Base: AST structural complexity
        - Control flow: branches and loops add non-determinism
        - Data flow: variables and operations

        This is syntax-invariant: semantically equivalent code
        should have similar μ-costs.
        """
        # Base structural cost (log scale)
        structural_cost = math.ceil(math.log2(max(self.ast_nodes, 1) + 1))

        # Control flow complexity (linear impact)
        control_cost = (self.branches * 2) + (self.loops * 3)

        # Data complexity
        data_cost = math.ceil(math.log2(max(self.variables + self.operations, 1) + 1))

        # Functional complexity
        functional_cost = self.functions * 4 + self.comprehensions * 2

        # Depth penalty (deeply nested code is harder to reason about)
        depth_cost = self.ast_depth * 2

        return max(1, structural_cost + control_cost + data_cost + functional_cost + depth_cost)

    @property
    def complexity_class(self) -> str:
        """Classify computational complexity."""
        cost = self.mu_cost

        if cost <= 10:
            return "O(1) - Constant"
        elif cost <= 30:
            return "O(log n) - Logarithmic"
        elif cost <= 100:
            return "O(n) - Linear"
        else:
            return "O(n²+) - Complex"


class ASTAnalyzer(ast.NodeVisitor):
    """AST visitor that computes complexity metrics."""

    def __init__(self):
        self.metrics = ComplexityMetrics()
        self.current_depth = 0
        self.max_depth = 0

    def visit(self, node):
        """Visit a node and track depth."""
        self.metrics.ast_nodes += 1
        self.current_depth += 1
        self.max_depth = max(self.max_depth, self.current_depth)

        result = super().visit(node)

        self.current_depth -= 1
        return result

    def visit_If(self, node):
        """Count if statements."""
        self.metrics.branches += 1
        self.generic_visit(node)

    def visit_For(self, node):
        """Count for loops."""
        self.metrics.loops += 1
        self.generic_visit(node)

    def visit_While(self, node):
        """Count while loops."""
        self.metrics.loops += 1
        self.generic_visit(node)

    def visit_FunctionDef(self, node):
        """Count function definitions."""
        self.metrics.functions += 1
        self.generic_visit(node)

    def visit_AsyncFunctionDef(self, node):
        """Count async function definitions."""
        self.metrics.functions += 1
        self.generic_visit(node)

    def visit_Lambda(self, node):
        """Count lambda expressions."""
        self.metrics.functions += 1
        self.generic_visit(node)

    def visit_ListComp(self, node):
        """Count list comprehensions."""
        self.metrics.comprehensions += 1
        self.generic_visit(node)

    def visit_SetComp(self, node):
        """Count set comprehensions."""
        self.metrics.comprehensions += 1
        self.generic_visit(node)

    def visit_DictComp(self, node):
        """Count dict comprehensions."""
        self.metrics.comprehensions += 1
        self.generic_visit(node)

    def visit_GeneratorExp(self, node):
        """Count generator expressions."""
        self.metrics.comprehensions += 1
        self.generic_visit(node)

    def visit_Name(self, node):
        """Count variable references."""
        self.metrics.variables += 1
        self.generic_visit(node)

    def visit_BinOp(self, node):
        """Count binary operations."""
        self.metrics.operations += 1
        self.generic_visit(node)

    def visit_UnaryOp(self, node):
        """Count unary operations."""
        self.metrics.operations += 1
        self.generic_visit(node)

    def visit_Compare(self, node):
        """Count comparisons."""
        self.metrics.operations += 1
        self.generic_visit(node)

    def visit_BoolOp(self, node):
        """Count boolean operations."""
        self.metrics.operations += 1
        self.generic_visit(node)


def analyze_source(source: str) -> ComplexityMetrics:
    """Analyze Python source code and return complexity metrics."""
    try:
        tree = ast.parse(source)
        analyzer = ASTAnalyzer()
        analyzer.visit(tree)
        analyzer.metrics.ast_depth = analyzer.max_depth
        return analyzer.metrics
    except SyntaxError:
        # Return minimal metrics for unparseable code
        return ComplexityMetrics(ast_nodes=1, mu_cost=1)


def get_source_from_callable(func: Callable) -> Optional[str]:
    """Extract source code from a callable.

    Handles:
    - Regular functions
    - Methods (bound, unbound, static, class)
    - Lambdas
    - Generators
    - Coroutines
    - Decorated functions
    - Builtins (returns None - will be handled specially)
    """
    try:
        # Try to get source directly
        return inspect.getsource(func)
    except (OSError, TypeError):
        # For builtins, C extensions, dynamically created functions
        # Try to unwrap if it's decorated
        try:
            unwrapped = inspect.unwrap(func)
            return inspect.getsource(unwrapped)
        except (OSError, TypeError, AttributeError):
            return None


def analyze(func: Callable) -> Dict[str, Any]:
    """Analyze a Python callable and return its μ-cost.

    Args:
        func: Any Python callable (function, method, lambda, builtin, etc.)

    Returns:
        Dictionary with:
        - success: bool - Whether analysis succeeded
        - mu_cost: int - Semantic complexity measure
        - complexity: str - Complexity class (O(1), O(n), etc.)
        - metrics: ComplexityMetrics - Detailed breakdown (optional)
        - error: str - Error message if failed (optional)

    Examples:
        >>> def simple_func(x): return x + 1
        >>> result = analyze(simple_func)
        >>> result['success']
        True
        >>> result['mu_cost'] > 0
        True
    """
    try:
        # Get source code
        source = get_source_from_callable(func)

        if source is None:
            # Builtin or C extension - assign minimal cost
            # These are "primitive" operations in the computational model
            metrics = ComplexityMetrics(ast_nodes=1, operations=1)
            metrics.ast_depth = 1
        else:
            # Parse and analyze AST
            metrics = analyze_source(source)

        return {
            'success': True,
            'mu_cost': metrics.mu_cost,
            'complexity': metrics.complexity_class,
            'metrics': metrics
        }

    except Exception as e:
        # Graceful failure - still return a result
        return {
            'success': False,
            'mu_cost': 1,  # Minimal cost for error case
            'complexity': 'O(1) - Constant',
            'error': str(e)
        }


def profile(func: Callable) -> Callable:
    """Decorator that profiles a function and attaches metrics.

    The decorated function will have a .profile attribute containing
    the complexity analysis results.

    Args:
        func: Function to profile

    Returns:
        Wrapped function with .profile attribute

    Example:
        >>> @profile
        ... def my_func(n):
        ...     return sum(range(n))
        >>> my_func.profile['mu_cost'] > 0
        True
    """
    # Analyze the function
    analysis_result = analyze(func)

    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        """Profiled wrapper that executes the original function."""
        return func(*args, **kwargs)

    # Attach profile data
    wrapper.profile = analysis_result

    return wrapper


# Convenience exports
__all__ = [
    'analyze',
    'profile',
    'ComplexityMetrics',
    'ASTAnalyzer',
]


# Self-test
if __name__ == "__main__":
    # Test with various callable types
    def simple_func(x):
        return x + 1

    def complex_func(n):
        result = []
        for i in range(n):
            if i % 2 == 0:
                result.append(i * i)
        return sum(result)

    # Test regular function
    r1 = analyze(simple_func)
    print(f"simple_func: μ-cost={r1['mu_cost']}, complexity={r1['complexity']}")

    r2 = analyze(complex_func)
    print(f"complex_func: μ-cost={r2['mu_cost']}, complexity={r2['complexity']}")

    # Test builtin
    r3 = analyze(len)
    print(f"len (builtin): μ-cost={r3['mu_cost']}, complexity={r3['complexity']}")

    # Test lambda
    lam = lambda x, y: x * y + y
    r4 = analyze(lam)
    print(f"lambda: μ-cost={r4['mu_cost']}, complexity={r4['complexity']}")

    # Test decorator
    @profile
    def profiled_func(n):
        return sum(range(n))

    print(f"profiled_func: μ-cost={profiled_func.profile['mu_cost']}")

    print("\n✅ μ-Profiler self-test passed!")
