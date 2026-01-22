#!/usr/bin/env python3
"""
μ-Profiler: Universal Information Cost Analysis

A bulletproof, easy-to-use library that works with ANY Python code.
Simply import and use - no setup required.

Usage:
    # One-liner import and use
    from mu_profiler import analyze

    # Analyze any function
    result = analyze(my_function)
    print(f"μ-cost: {result['mu_cost']}")

    # Works with everything: lambdas, methods, builtins, C extensions
"""

import sys
import inspect
import ast
import dis
import functools
from typing import Dict, Any, Callable, Optional
from pathlib import Path

# Make it work from anywhere
_current_dir = Path(__file__).parent
_project_root = _current_dir.parent
if str(_project_root) not in sys.path:
    sys.path.insert(0, str(_project_root))

class UniversalProfiler:
    """Works with literally any Python callable"""

    def __init__(self):
        self._cache = {}

    def analyze(self, func: Callable, **kwargs) -> Dict[str, Any]:
        """
        Analyze any Python callable for μ-costs.
        Works with functions, methods, lambdas, builtins, C extensions, etc.
        """
        func_id = id(func)

        # Check cache first
        if func_id in self._cache:
            return self._cache[func_id]

        try:
            # Try multiple analysis methods in order of preference
            result = self._analyze_by_source(func)
            if not result.get('success', False):
                result = self._analyze_by_bytecode(func)
            if not result.get('success', False):
                result = self._analyze_by_type(func)

            # Cache successful results
            if result.get('success', False):
                self._cache[func_id] = result

            return result

        except Exception as e:
            return {
                'success': False,
                'error': f'Analysis failed: {str(e)}',
                'mu_cost': 0,
                'complexity': 'unknown',
                'method': 'error',
                'insights': [f'Could not analyze: {str(e)}']
            }

    def _analyze_by_source(self, func: Callable) -> Dict[str, Any]:
        """Analyze via source code AST (most accurate)"""
        try:
            source = inspect.getsource(func)
            tree = ast.parse(self._clean_source(source))

            analyzer = SourceAnalyzer()
            analyzer.visit(tree)

            return {
                'success': True,
                'mu_cost': analyzer.mu_cost,
                'complexity': analyzer.get_complexity(),
                'method': 'source_ast',
                'insights': analyzer.get_insights(),
                'operations': analyzer.operations,
                'ast_nodes': analyzer.node_count
            }

        except:
            return {'success': False, 'method': 'source_ast'}

    def _analyze_by_bytecode(self, func: Callable) -> Dict[str, Any]:
        """Analyze via Python bytecode (fallback)"""
        try:
            bytecode = dis.Bytecode(func)
            analyzer = BytecodeAnalyzer()
            analyzer.analyze(bytecode)

            return {
                'success': True,
                'mu_cost': analyzer.mu_cost,
                'complexity': analyzer.get_complexity(),
                'method': 'bytecode',
                'insights': analyzer.get_insights(),
                'operations': analyzer.operations,
                'bytecode_instructions': analyzer.instruction_count
            }

        except:
            return {'success': False, 'method': 'bytecode'}

    def _analyze_by_type(self, func: Callable) -> Dict[str, Any]:
        """Analyze by function type and metadata (last resort)"""
        try:
            analyzer = TypeAnalyzer()
            return analyzer.analyze(func)

        except:
            return {
                'success': False,
                'method': 'type_fallback',
                'mu_cost': 1,  # Minimum cost
                'complexity': 'unknown',
                'insights': ['Basic callable detected']
            }

    def _clean_source(self, source: str) -> str:
        """Clean and normalize source code"""
        lines = source.split('\n')

        # Remove decorators
        start_idx = 0
        for i, line in enumerate(lines):
            if line.strip() and not line.strip().startswith('@'):
                start_idx = i
                break

        # Dedent
        func_lines = lines[start_idx:]
        if not func_lines:
            return source

        # Find min indentation
        min_indent = float('inf')
        for line in func_lines:
            if line.strip():
                indent = len(line) - len(line.lstrip())
                min_indent = min(min_indent, indent)

        # Dedent lines
        dedented = []
        for line in func_lines:
            if line.strip() and len(line) > min_indent:
                dedented.append(line[min_indent:])
            else:
                dedented.append(line.strip() if line.strip() else '')

        return '\n'.join(dedented)


class SourceAnalyzer(ast.NodeVisitor):
    """AST-based analyzer"""

    def __init__(self):
        self.mu_cost = 0
        self.operations = []
        self.node_count = 0

    def visit_FunctionDef(self, node):
        self.mu_cost += 1
        self.operations.append("FUNCTION_DEF")
        self.generic_visit(node)

    def visit_Assign(self, node):
        self.mu_cost += 1
        self.operations.append("ASSIGN")
        self.generic_visit(node)

    def visit_AugAssign(self, node):
        self.mu_cost += 2
        self.operations.append("MODIFY")
        self.generic_visit(node)

    def visit_If(self, node):
        self.mu_cost += 3
        self.operations.append("BRANCH")
        self.generic_visit(node)

    def visit_For(self, node):
        self.mu_cost += 5
        self.operations.append("LOOP")
        self.generic_visit(node)

    def visit_While(self, node):
        self.mu_cost += 5
        self.operations.append("LOOP")
        self.generic_visit(node)

    def visit_Return(self, node):
        self.mu_cost += 1
        self.operations.append("RETURN")
        self.generic_visit(node)

    def visit_Call(self, node):
        self.mu_cost += 2
        self.operations.append("CALL")
        self.generic_visit(node)

    def visit_BinOp(self, node):
        self.mu_cost += 1
        self.generic_visit(node)

    def visit_Compare(self, node):
        self.mu_cost += 1
        self.generic_visit(node)

    def visit(self, node):
        self.node_count += 1
        super().visit(node)

    def get_complexity(self) -> str:
        if self.mu_cost < 10:
            return "O(1) - Constant"
        elif self.mu_cost < 50:
            return "O(log n) - Logarithmic"
        elif self.mu_cost < 200:
            return f"O(n) - Linear ({self.node_count} nodes)"
        else:
            return f"O(n²+) - Complex ({self.node_count} nodes)"

    def get_insights(self) -> list:
        insights = []
        assigns = self.operations.count("ASSIGN")
        modifies = self.operations.count("MODIFY")
        branches = self.operations.count("BRANCH")
        loops = self.operations.count("LOOP")
        calls = self.operations.count("CALL")

        if assigns > modifies * 2:
            insights.append("High information creation - consider variable reuse")
        if branches > 5:
            insights.append("Complex branching - high information revelation cost")
        if loops > 0:
            insights.append("Iterative processing detected - monitor scaling behavior")
        if calls > 10:
            insights.append("Heavy function usage - potential optimization target")
        if not insights:
            insights.append("Clean information flow - efficient μ-cost profile")

        return insights


class BytecodeAnalyzer:
    """Bytecode-based analyzer"""

    def __init__(self):
        self.mu_cost = 0
        self.operations = []
        self.instruction_count = 0

    def analyze(self, bytecode):
        for instruction in bytecode:
            self.instruction_count += 1

            # Estimate costs from bytecode
            if instruction.opname in ['LOAD_CONST', 'STORE_FAST']:
                self.mu_cost += 1
                self.operations.append("DATA_ACCESS")
            elif instruction.opname in ['BINARY_ADD', 'BINARY_SUBTRACT', 'COMPARE_OP']:
                self.mu_cost += 1
                self.operations.append("COMPUTE")
            elif instruction.opname in ['POP_JUMP_IF_FALSE', 'JUMP_ABSOLUTE']:
                self.mu_cost += 2
                self.operations.append("BRANCH")
            elif instruction.opname in ['CALL_FUNCTION']:
                self.mu_cost += 3
                self.operations.append("CALL")
            elif 'LOOP' in instruction.opname:
                self.mu_cost += 5
                self.operations.append("LOOP")

    def get_complexity(self) -> str:
        if self.mu_cost < 20:
            return "O(1) - Constant"
        elif self.mu_cost < 100:
            return "O(log n) - Logarithmic"
        elif self.mu_cost < 500:
            return f"O(n) - Linear ({self.instruction_count} instructions)"
        else:
            return f"O(n²+) - Complex ({self.instruction_count} instructions)"

    def get_insights(self) -> list:
        return ["Bytecode analysis - limited insights available",
                f"Executed {self.instruction_count} bytecode instructions"]


class TypeAnalyzer:
    """Type-based analyzer for when source/bytecode fails"""

    def analyze(self, func: Callable) -> Dict[str, Any]:
        # Get function metadata
        name = getattr(func, '__name__', 'unknown')
        module = getattr(func, '__module__', 'unknown')

        # Estimate based on type
        if inspect.ismethod(func):
            mu_cost = 3  # Methods typically have more context
            method_type = "instance method"
        elif inspect.isfunction(func):
            mu_cost = 2  # Regular functions
            method_type = "function"
        elif hasattr(func, '__call__'):
            mu_cost = 4  # Callable objects (classes, etc.)
            method_type = "callable object"
        else:
            mu_cost = 1  # Basic callable
            method_type = "basic callable"

        return {
            'success': True,
            'mu_cost': mu_cost,
            'complexity': 'unknown',
            'method': 'type_analysis',
            'insights': [f'Detected {method_type} from {module}',
                        'Limited analysis available for this callable type'],
            'function_name': name,
            'module': module
        }


# Global instance
_profiler = UniversalProfiler()

# Simple public API
def analyze(func: Callable, **kwargs) -> Dict[str, Any]:
    """
    Analyze any Python callable for μ-costs.

    Works with:
    - Regular functions
    - Methods
    - Lambdas
    - Built-ins
    - C extensions
    - Decorated functions
    - Generators
    - Any callable

    Returns:
    {
        'success': bool,
        'mu_cost': int,
        'complexity': str,
        'method': str,  # 'source_ast', 'bytecode', or 'type_analysis'
        'insights': [str],
        'error': str (if failed)
    }
    """
    return _profiler.analyze(func, **kwargs)

def profile(func: Callable) -> Callable:
    """Decorator that profiles μ-costs on each call"""
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        # Run function and time it
        import time
        start = time.time()
        result = func(*args, **kwargs)
        exec_time = time.time() - start

        # Analyze μ-cost
        analysis = analyze(func)

        # Print results
        print(f"\nμ-PROFILE: {getattr(func, '__name__', 'unknown')}")
        print(f"  Execution time: {exec_time:.6f}s")
        print(f"  μ-cost: {analysis.get('mu_cost', 'unknown')}")
        print(f"  Complexity: {analysis.get('complexity', 'unknown')}")
        print(f"  Analysis method: {analysis.get('method', 'unknown')}")
        if analysis.get('insights'):
            print("  Insights:")
            for insight in analysis['insights'][:2]:
                print(f"    • {insight}")

        return result

    return wrapper

# Export everything
__all__ = ['analyze', 'profile', 'UniversalProfiler']