"""
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
Copyright 2025 Devon Thiele

See the LICENSE file in the repository root for full terms.
Virtual machine execution loop.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
import json
from typing import List, Dict, Any, Optional, Tuple
import ast
import sys
from io import StringIO
import hashlib
import string
import math
import builtins
import zlib
import z3

# Safety: maximum allowed classical combinations for brute-force searches.
# Can be overridden by the environment variable THIELE_MAX_COMBINATIONS.
import os
SAFE_COMBINATION_LIMIT = int(os.environ.get('THIELE_MAX_COMBINATIONS', 10_000_000))

SAFE_IMPORTS = {"math", "json"}
SAFE_FUNCTIONS = {
    "abs",
    "all",
    "any",
    "bool",
    "divmod",
    "enumerate",
    "float",
    "int",
    "len",
    "list",
    "max",
    "min",
    "pow",
    "print",
    "range",
    "round",
    "sorted",
    "sum",
    "tuple",
    "zip",
    "str",
    "set",
    "dict",
    "map",
    "filter",
    "placeholder",
    "open",
}
SAFE_METHOD_CALLS = {"append", "extend", "items", "keys", "values", "get", "update", "add"}
SAFE_MODULE_CALLS = {
    "math": {"ceil", "floor", "sqrt", "log", "log2", "exp", "fabs", "copysign", "isfinite"},
    "json": {"loads", "dumps", "load"},
}
SAFE_MODULE_ATTRIBUTES = {
    "math": {"pi", "e"},
}
SAFE_NODE_TYPES = {
    ast.Module,
    ast.FunctionDef,
    ast.ClassDef,
    ast.arguments,
    ast.arg,
    ast.Expr,
    ast.Assign,
    ast.AugAssign,
    ast.AnnAssign,
    ast.Name,
    ast.Load,
    ast.Store,
    ast.Del,
    ast.Constant,
    ast.BinOp,
    ast.UnaryOp,
    ast.BoolOp,
    ast.Compare,
    ast.If,
    ast.IfExp,
    ast.For,
    ast.While,
    ast.Break,
    ast.Continue,
    ast.Pass,
    ast.List,
    ast.Tuple,
    ast.Dict,
    ast.Set,
    ast.ListComp,
    ast.SetComp,
    ast.DictComp,
    ast.GeneratorExp,
    ast.comprehension,
    ast.Subscript,
    ast.Slice,
    ast.ExtSlice,
    ast.Index,
    ast.Call,
    ast.Attribute,
    ast.keyword,
    ast.alias,
    ast.With,
    ast.withitem,
    ast.Return,
    ast.JoinedStr,
    ast.FormattedValue,
    ast.Try,
    ast.ExceptHandler,
    ast.Raise,
    ast.Assert,
}
SAFE_NODE_TYPES.update(
    {
        ast.Add,
        ast.Sub,
        ast.Mult,
        ast.Div,
        ast.Mod,
        ast.Pow,
        ast.FloorDiv,
        ast.LShift,
        ast.RShift,
        ast.BitAnd,
        ast.BitOr,
        ast.BitXor,
        ast.UAdd,
        ast.USub,
        ast.Not,
        ast.Invert,
        ast.And,
        ast.Or,
        ast.Eq,
        ast.NotEq,
        ast.Lt,
        ast.LtE,
        ast.Gt,
        ast.GtE,
        ast.Is,
        ast.IsNot,
        ast.In,
        ast.NotIn,
    }
)

SAFE_BUILTINS = {name: getattr(builtins, name) for name in SAFE_FUNCTIONS if hasattr(builtins, name)}


def _safe_import(name, globals=None, locals=None, fromlist=(), level=0):
    """Constrain dynamic imports to the vetted module list."""

    base = name.split(".")[0]
    if base not in SAFE_IMPORTS:
        raise SecurityError(f"Import of {name} is not permitted")
    return builtins.__import__(name, globals, locals, fromlist, level)


SAFE_BUILTINS["__import__"] = _safe_import


class SecurityError(RuntimeError):
    """Raised when a PYEXEC payload violates sandbox policy."""


class SafeNodeVisitor(ast.NodeVisitor):
    """AST visitor enforcing a restrictive whitelist of constructs."""

    def generic_visit(self, node: ast.AST) -> None:
        if type(node) not in SAFE_NODE_TYPES:
            raise SecurityError(f"Disallowed construct: {type(node).__name__}")
        super().generic_visit(node)

    def visit_Import(self, node: ast.Import) -> None:  # pragma: no cover - simple check
        for alias in node.names:
            if alias.name not in SAFE_IMPORTS:
                raise SecurityError(f"Import of {alias.name} is not permitted")
        super().generic_visit(node)

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:  # pragma: no cover - simple check
        module = node.module or ""
        if module not in SAFE_IMPORTS:
            raise SecurityError(f"Import from {module} is not permitted")
        super().generic_visit(node)

    def visit_Attribute(self, node: ast.Attribute) -> None:
        if not isinstance(node.value, ast.Name):
            raise SecurityError("Attribute access is restricted to named objects")
        base = node.value.id
        attr = node.attr
        if base in SAFE_MODULE_CALLS:
            allowed = SAFE_MODULE_CALLS[base] | SAFE_MODULE_ATTRIBUTES.get(base, set())
            if attr not in allowed:
                raise SecurityError(f"Attribute {base}.{attr} not permitted")
        elif attr not in SAFE_METHOD_CALLS:
            raise SecurityError(f"Method {attr} is not permitted")
        super().generic_visit(node)

    def visit_Call(self, node: ast.Call) -> None:
        func = node.func
        if isinstance(func, ast.Name):
            if func.id not in SAFE_FUNCTIONS:
                raise SecurityError(f"Function {func.id} is not permitted")
        elif isinstance(func, ast.Attribute):
            if not isinstance(func.value, ast.Name):
                raise SecurityError("Chained attribute calls are not permitted")
            base = func.value.id
            attr = func.attr
            if base in SAFE_MODULE_CALLS and attr in SAFE_MODULE_CALLS[base]:
                pass
            elif attr in SAFE_METHOD_CALLS:
                pass
            else:
                raise SecurityError(f"Call to {base}.{attr} is not permitted")
        else:
            raise SecurityError("Dynamic function calls are not permitted")
        super().generic_visit(node)


def safe_eval(code: str, scope: Dict[str, Any]) -> Any:
    tree = ast.parse(code, mode="eval")
    SafeNodeVisitor().visit(tree)
    compiled = compile(tree, "<pyexec>", "eval")
    return eval(compiled, scope)


def safe_execute(code: str, scope: Dict[str, Any]) -> Any:
    tree = ast.parse(code, mode="exec")
    SafeNodeVisitor().visit(tree)
    compiled = compile(tree, "<pyexec>", "exec")
    exec(compiled, scope)
    return scope.get("__result__")


def mu_cost_from_text(text: str) -> int:
    """Return μ-bit cost using compressed size as a Kolmogorov proxy."""

    # Using compressed byte-length as a computable approximation of Kolmogorov complexity (information content) for μ-bit cost.
    return len(zlib.compress(text.encode("utf-8"))) * 8


def _empty_cert() -> Dict[str, Any]:
    return {
        "smt_query": "",
        "solver_reply": "",
        "metadata": "",
        "timestamp": 0,
        "sequence": 0,
    }


def _cert_for_query(query: str) -> Dict[str, Any]:
    cert = _empty_cert()
    cert["smt_query"] = query
    return cert

try:
    from .assemble import Instruction, parse
    from .logic import lassert, ljoin
    from .mdl import mdlacc, info_charge
    from .state import State
    from .isa import CSR
    from .memory import RegionGraph
    from ._types import LedgerEntry, ModuleId
    from .receipts import (
        WitnessState,
        StepObservation,
        InstructionWitness,
        StepReceipt,
        ensure_kernel_keys,
    )
    from .logger import get_thiele_logger
except ImportError:
    # Handle running as script
    import sys
    import os
    # Add the parent directory to the path to allow for relative imports
    sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
    from thielecpu.assemble import Instruction, parse
    from thielecpu.logic import lassert, ljoin
    from thielecpu.mdl import mdlacc, info_charge
    from thielecpu.state import State
    from thielecpu.isa import CSR
    from thielecpu.memory import RegionGraph
    from thielecpu._types import LedgerEntry, ModuleId
    from thielecpu.receipts import (
        WitnessState,
        StepObservation,
        InstructionWitness,
        StepReceipt,
        ensure_kernel_keys,
    )
    from thielecpu.logger import get_thiele_logger


@dataclass
class SymbolicVariable:
    """Represents a symbolic variable that needs to be solved for."""
    name: str
    domain: List[str]  # Possible values this variable can take

    def __str__(self):
        return f"SymbolicVar({self.name})"

    def __repr__(self):
        return self.__str__()

    def __hash__(self):
        return hash(self.name)

    def __eq__(self, other):
        if isinstance(other, SymbolicVariable):
            return self.name == other.name
        return False


# Global counter for symbolic variables
_symbolic_var_counter = 0

def extract_target_modulus(code: str) -> Optional[int]:
    """Extract the target modulus n from Python factoring code."""
    try:
        tree = ast.parse(code)
        for node in ast.walk(tree):
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Name) and target.id == 'n':
                        if isinstance(node.value, ast.Constant) and isinstance(node.value.value, int):
                            return node.value.value
    except:
        pass
    return None

def placeholder(domain: Optional[List[str]] = None) -> SymbolicVariable:
    """Create a symbolic variable placeholder for logical deduction."""
    global _symbolic_var_counter
    if domain is None:
        # Default domain: lowercase letters and digits
        domain = list(string.ascii_lowercase + string.digits)

    var_name = f"var_{_symbolic_var_counter}"
    _symbolic_var_counter += 1

    return SymbolicVariable(var_name, domain)

def search_chunk(chunk_combinations, var_names, code_to_run):
    """Worker function for parallel brute force search."""
    import hashlib

    # Minimal globals for the subprocess
    python_globals = {
        '__builtins__': __builtins__,
        'print': print,
        'len': len,
        'range': range,
        'enumerate': enumerate,
        'zip': zip,
        'sum': sum,
        'max': max,
        'min': min,
        'abs': abs,
        'pow': pow,
        'divmod': divmod,
        'round': round,
        'int': int,
        'float': float,
        'str': str,
        'bool': bool,
        'list': list,
        'dict': dict,
        'set': set,
        'tuple': tuple,
        'hashlib': hashlib,
    }

    for combination in chunk_combinations:
        assignment = dict(zip(var_names, combination))

        solved_globals = python_globals.copy()
        solved_globals.update(assignment)

        # Capture output in subprocess
        from io import StringIO
        import sys
        old_stdout = sys.stdout
        sys.stdout = captured_output = StringIO()

        success = False
        output = ""

        try:
            exec(code_to_run, solved_globals)
            success = True
        except AssertionError:
            pass
        except Exception:
            pass

        output = captured_output.getvalue()
        sys.stdout = old_stdout

        if success:
            return assignment, output
    return None, None

@dataclass
class VM:
    state: State
    python_globals: Dict[str, Any] = None  # type: ignore
    witness_state: WitnessState = field(default_factory=WitnessState)
    step_receipts: List[StepReceipt] = field(default_factory=list)

    def __post_init__(self):
        ensure_kernel_keys()
        if self.python_globals is None:
            globals_scope: Dict[str, Any] = {
                "__builtins__": SAFE_BUILTINS,
                "placeholder": placeholder,
                "hashlib": hashlib,
                "math": math,
                "json": json,
                "self": self,
            }
            for name in SAFE_FUNCTIONS:
                if name in globals_scope:
                    continue
                if name in SAFE_BUILTINS:
                    globals_scope[name] = SAFE_BUILTINS[name]
                elif hasattr(builtins, name):
                    globals_scope[name] = getattr(builtins, name)
            self.python_globals = globals_scope
        self.witness_state = WitnessState()
        self.step_receipts = []

    def _simulate_witness_step(
        self, instruction: InstructionWitness, pre_state: WitnessState
    ) -> Tuple[WitnessState, StepObservation]:
        op = instruction.op
        if op == "LASSERT":
            query = str(instruction.payload)
            mu_delta = mu_cost_from_text(query)
            post_state = WitnessState(
                pc=pre_state.pc + 1,
                status=pre_state.status,
                mu_acc=pre_state.mu_acc + mu_delta,
                cert_addr=pre_state.cert_addr,
            )
            observation = StepObservation(
                event={"tag": "PolicyCheck", "value": query},
                mu_delta=mu_delta,
                cert=_cert_for_query(query),
            )
        elif op == "MDLACC":
            post_state = WitnessState(
                pc=pre_state.pc + 1,
                status=pre_state.status,
                mu_acc=pre_state.mu_acc,
                cert_addr=pre_state.cert_addr,
            )
            observation = StepObservation(event=None, mu_delta=0, cert=_empty_cert())
        elif op == "PNEW":
            post_state = WitnessState(
                pc=pre_state.pc + 1,
                status=pre_state.status,
                mu_acc=pre_state.mu_acc,
                cert_addr=pre_state.cert_addr,
            )
            observation = StepObservation(
                event={"tag": "InferenceComplete"}, mu_delta=0, cert=_empty_cert()
            )
        elif op == "PYEXEC":
            code = str(instruction.payload)
            post_state = WitnessState(
                pc=pre_state.pc + 1,
                status=pre_state.status,
                mu_acc=pre_state.mu_acc,
                cert_addr=pre_state.cert_addr,
            )
            observation = StepObservation(
                event={"tag": "PolicyCheck", "value": code},
                mu_delta=0,
                cert=_empty_cert(),
            )
        elif op == "EMIT":
            payload = str(instruction.payload)
            post_state = WitnessState(
                pc=pre_state.pc + 1,
                status=pre_state.status,
                mu_acc=pre_state.mu_acc,
                cert_addr=pre_state.cert_addr,
            )
            observation = StepObservation(
                event={"tag": "ErrorOccurred", "value": payload},
                mu_delta=0,
                cert=_empty_cert(),
            )
        else:
            raise ValueError(f"Unsupported instruction for receipts: {op}")
        return post_state, observation

    def _record_receipt(
        self, step: int, pre_state: WitnessState, instruction: InstructionWitness
    ) -> None:
        post_state, observation = self._simulate_witness_step(instruction, pre_state)
        receipt = StepReceipt.assemble(
            step,
            instruction,
            pre_state,
            post_state,
            observation,
        )
        self.step_receipts.append(receipt)
        self.witness_state = post_state

    def execute_python(self, code_or_path: str) -> Any:
        """Execute Python code or file in a sandboxed environment."""
        try:
            # Check if it's a file path
            if code_or_path.endswith('.py') or ('\n' not in code_or_path.strip() and Path(code_or_path).exists()):
                try:
                    # Try to read as file
                    code = Path(code_or_path).read_text(encoding='utf-8')
                    source_info = f"file: {code_or_path}"
                except (FileNotFoundError, OSError):
                    # Not a file, treat as inline code
                    code = code_or_path
                    source_info = "inline"
            else:
                # Inline code
                code = code_or_path
                source_info = "inline"

            # Check if code contains symbolic variables
            if 'placeholder(' in code:
                return self.execute_symbolic_python(code, source_info)

            # Capture stdout
            old_stdout = sys.stdout
            sys.stdout = captured_output = StringIO()

            try:
                result = safe_execute(code, self.python_globals)
                output = captured_output.getvalue()
                return result, output
            except SyntaxError:
                result = safe_eval(code, self.python_globals)
                output = captured_output.getvalue()
                return result, output
            except SecurityError as exc:
                output = captured_output.getvalue()
                return None, output + f"\nSecurityError: {exc}"
            finally:
                sys.stdout = old_stdout
        except Exception as e:
            output = captured_output.getvalue()
            sys.stdout = old_stdout
            return None, output + f"\nError: {str(e)}"

    def execute_symbolic_python(self, code: str, source_info: str) -> Any:
        """Execute Python code with symbolic variables using Z3 SMT solver."""

        # 1. Parse the code and find symbolic assignments
        try:
            tree = ast.parse(code)
        except SyntaxError as exc:
            return None, f"Syntax Error: {exc}"

        # Log where the symbolic code originated to aid debugging
        print(f"Executing symbolic code from: {source_info}")

        symbolic_assignments = {}  # maps var_name -> domain

        class PlaceholderVisitor(ast.NodeVisitor):
            def visit_Assign(self, node):
                if isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name) and node.value.func.id == 'placeholder':
                    # This is an assignment like `p1 = placeholder(...)`
                    if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
                        var_name = node.targets[0].id
                        # Default domain
                        domain = list(string.ascii_lowercase + string.digits)
                        # Try to evaluate the domain argument if present
                        if node.value.keywords:
                            for kw in node.value.keywords:
                                if kw.arg == 'domain':
                                    domain_val = None
                                    if (isinstance(kw.value, ast.Call) and
                                        isinstance(kw.value.func, ast.Name) and
                                        kw.value.func.id == 'list' and
                                        len(kw.value.args) == 1):

                                        arg_node = kw.value.args[0]
                                        str_val = None

                                        if isinstance(arg_node, ast.Constant) and isinstance(arg_node.value, str):
                                            str_val = arg_node.value
                                        elif hasattr(ast, 'Str') and isinstance(arg_node, ast.Str):
                                            str_val = arg_node.s

                                        if str_val is not None:
                                            domain_val = list(str(str_val))

                                    if domain_val is None:
                                        try:
                                            domain_val = ast.literal_eval(kw.value)
                                        except Exception:
                                            pass

                                    if isinstance(domain_val, list):
                                        domain = domain_val
                        symbolic_assignments[var_name] = domain
                self.generic_visit(node)

        PlaceholderVisitor().visit(tree)

        if not symbolic_assignments:
            return self.execute_python(code)

        var_names = list(symbolic_assignments.keys())
        print(f"Found {len(var_names)} symbolic variables: {var_names}")

        # Set default domain if not specified
        for var_name in var_names:
            if symbolic_assignments[var_name] is None:
                symbolic_assignments[var_name] = list('abcdefghijklmnopqrstuvwxyz0123456789')

        total_combinations = 1
        for domain in symbolic_assignments.values():
            total_combinations *= len(domain)
        print(f"Classical search space: {total_combinations} combinations")

        # Check if this is arithmetic (integer) or string-based symbolic execution
        is_arithmetic = False
        class ArithmeticChecker(ast.NodeVisitor):
            def visit_BinOp(self, node):
                if isinstance(node.op, (ast.Mult, ast.Add, ast.Sub, ast.Div, ast.Mod)):
                    self.is_arithmetic = True
                self.generic_visit(node)
            def visit_Compare(self, node):
                if any(isinstance(op, (ast.Lt, ast.LtE, ast.Gt, ast.GtE)) for op in node.ops):
                    self.is_arithmetic = True
                self.generic_visit(node)

        checker = ArithmeticChecker()
        checker.visit(tree)
        is_arithmetic = checker.is_arithmetic

        # Use AST transformer to remove symbolic assignments
        class SymbolicAssignmentRemover(ast.NodeTransformer):
            def visit_Assign(self, node):
                if (isinstance(node.value, ast.Call) and
                    isinstance(node.value.func, ast.Name) and
                    node.value.func.id == 'placeholder'):
                    return None
                return node

        remover = SymbolicAssignmentRemover()
        new_tree = remover.visit(tree)
        ast.fix_missing_locations(new_tree)
        code_to_run = ast.unparse(new_tree)

        # 2. Set up Z3 solver
        if is_arithmetic:
            solver = z3.Solver()
            z3_vars = {}
            # Create Z3 integer variables
            for var_name in var_names:
                z3_vars[var_name] = z3.Int(var_name)
        else:
            solver = z3.SolverFor("QF_S")
            z3_vars = {}
            # Create Z3 string variables
            for var_name, domain in symbolic_assignments.items():
                z3_var = z3.String(var_name)
                z3_vars[var_name] = z3_var

        # Check if constraints involve unsupported operations (e.g., cryptography)
        has_unsupported_assertions = 'hashlib' in code

        if has_unsupported_assertions:
            # Fall back to brute force for cryptographic constraints
            print("Cryptographic constraints detected - using brute force search")
            return self.execute_symbolic_brute_force(code, symbolic_assignments, var_names, code_to_run)
        else:
            # Use Z3 for logical constraints
            if is_arithmetic:
                print("Using Z3 SMT solver for arithmetic constraints...")
            else:
                print("Using Z3 SMT solver for logical constraints...")

            # Find assertions and convert to Z3 constraints
            class AssertionVisitor(ast.NodeVisitor):
                def visit_Assert(self, node):
                    constraint = self.convert_expr_to_z3(node.test, is_arithmetic)
                    if constraint is not None:
                        solver.add(constraint)

                def convert_expr_to_z3(self, expr, is_arithmetic):
                    if isinstance(expr, ast.Compare):
                        if len(expr.ops) == 1:
                            op = expr.ops[0]
                            left = self.convert_expr_to_z3(expr.left, is_arithmetic)
                            right = self.convert_expr_to_z3(expr.comparators[0], is_arithmetic)
                            if left is not None and right is not None:
                                if isinstance(op, ast.Eq):
                                    return left == right
                                elif isinstance(op, ast.Lt):
                                    return left < right
                                elif isinstance(op, ast.LtE):
                                    return left <= right
                                elif isinstance(op, ast.Gt):
                                    return left > right
                                elif isinstance(op, ast.GtE):
                                    return left >= right
                    elif isinstance(expr, ast.BinOp):
                        left = self.convert_expr_to_z3(expr.left, is_arithmetic)
                        right = self.convert_expr_to_z3(expr.right, is_arithmetic)
                        if left is not None and right is not None:
                            if isinstance(expr.op, ast.Add):
                                if is_arithmetic:
                                    return left + right
                                else:
                                    return z3.Concat(left, right)
                            elif isinstance(expr.op, ast.Sub):
                                return left - right
                            elif isinstance(expr.op, ast.Mult):
                                return left * right
                            elif isinstance(expr.op, ast.Div):
                                return left / right
                            elif isinstance(expr.op, ast.Mod):
                                return left % right
                    elif isinstance(expr, ast.Call):
                        if isinstance(expr.func, ast.Attribute) and expr.func.attr == 'startswith':
                            obj = self.convert_expr_to_z3(expr.func.value, is_arithmetic)
                            if obj is not None and expr.args:
                                arg = self.convert_expr_to_z3(expr.args[0], is_arithmetic)
                                if arg is not None:
                                    # Model Python's str.startswith(x) as z3 PrefixOf(x, obj)
                                    return z3.PrefixOf(arg, obj)
                    elif isinstance(expr, ast.Name):
                        if expr.id in z3_vars:
                            return z3_vars[expr.id]
                    elif isinstance(expr, ast.Constant):
                        if is_arithmetic and isinstance(expr.value, int):
                            return z3.IntVal(expr.value)
                        else:
                            return z3.StringVal(str(expr.value))
                    return None

            AssertionVisitor().visit(new_tree)

            if solver.check() == z3.sat:
                model = solver.model()
                assignment = {}
                for var_name, z3_var in z3_vars.items():
                    val = model[z3_var]
                    if val is not None:
                        if is_arithmetic:
                            assignment[var_name] = int(str(val))
                        else:
                            if z3.is_string_value(val):
                                assignment[var_name] = str(val).strip('"')
                            else:
                                assignment[var_name] = str(val)
                    else:
                        assignment[var_name] = 0 if is_arithmetic else ""

                print(f"✓ Found satisfying assignment: {assignment}")

                solved_globals = self.python_globals.copy()
                solved_globals.update(assignment)

                old_stdout = sys.stdout
                sys.stdout = captured_output = StringIO()

                try:
                    exec(code_to_run, solved_globals)
                    output = captured_output.getvalue()
                    sys.stdout = old_stdout
                    return None, f"Symbolic execution successful!\nAssignment: {assignment}\nOutput:\n{output}"
                except Exception as e:
                    sys.stdout = old_stdout
                    return None, f"Execution failed with solution: {e}"
            else:
                return None, "No satisfying assignment found (unsatisfiable constraints)"

    def execute_symbolic_brute_force(self, _code: str, symbolic_assignments: dict, var_names: list, code_to_run: str) -> Any:
        """Brute force search for symbolic variables when Z3 cannot handle constraints.

        This implementation streams combinations in chunks to avoid allocating
        the entire Cartesian product in memory. It also enforces a safety limit
        (SAFE_COMBINATION_LIMIT) to prevent accidental large-scale cryptanalytic
        workloads.
        """
        import itertools
        import multiprocessing as mp
        from concurrent.futures import ProcessPoolExecutor, as_completed
        from itertools import islice

        domains = [symbolic_assignments[name] for name in var_names]

        total_combinations = 1
        for domain in domains:
            total_combinations *= len(domain)
        print(f"Parallel brute force search through {total_combinations} combinations...")

        # Safety check: avoid extremely large searches
        if total_combinations > SAFE_COMBINATION_LIMIT:
            return None, f"Workload too large: {total_combinations} combinations exceeds safe limit of {SAFE_COMBINATION_LIMIT}. Reduce domains or set THIELE_MAX_COMBINATIONS to a smaller value for experimentation."

        # Determine worker count and chunk sizing
        num_workers = min(mp.cpu_count(), 4)  # Use up to 4 cores by default
        # Aim for a modest number of chunks per worker; ensure chunk_size >=1
        chunk_size = max(1, total_combinations // (num_workers * 64))

        print(f"Using up to {num_workers} parallel workers with chunk size {chunk_size}...")

        # Generator that yields chunks lazily using islice
        def chunked_product(domains, chunk_size):
            product_iter = itertools.product(*domains)
            while True:
                chunk = list(islice(product_iter, chunk_size))
                if not chunk:
                    break
                yield chunk

        # Use the existing search_chunk worker which accepts a list of combinations
        with ProcessPoolExecutor(max_workers=num_workers) as executor:
            pending = []  # list of futures
            chunk_iter = chunked_product(domains, chunk_size)

            # Submit initial batch up to num_workers
            try:
                for _ in range(num_workers):
                    chunk = next(chunk_iter, None)
                    if chunk is None:
                        break
                    fut = executor.submit(search_chunk, chunk, var_names, code_to_run)
                    pending.append(fut)

                # Iterate over futures as they complete and submit new chunks
                for fut in as_completed(pending):
                    assignment, output = fut.result()
                    if assignment:
                        # Cancel remaining futures
                        for other in pending:
                            if not other.done():
                                other.cancel()
                        print(f"✓ Found satisfying assignment: {assignment}")
                        return None, f"Symbolic execution successful!\nAssignment: {assignment}\nOutput:\n{output}"
                    # If this future didn't find a solution, submit next chunk if available
                    next_chunk = next(chunk_iter, None)
                    if next_chunk is not None:
                        new_fut = executor.submit(search_chunk, next_chunk, var_names, code_to_run)
                        pending.append(new_fut)
                # If we get here, no futures returned a solution
                return None, "No satisfying assignment found for symbolic variables"
            finally:
                # Attempt best-effort cancellation of pending futures
                for fut in pending:
                    try:
                        fut.cancel()
                    except Exception:
                        # Swallow cancellation errors
                        pass

    def test_combined_satisfiability(self, axioms: str) -> bool:
        """Test if combined axioms are satisfiable. Returns True if satisfiable, False if unsatisfiable."""
        from z3 import Solver, parse_smt2_string, sat
        
        solver = Solver()
        try:
            solver.add(*parse_smt2_string(axioms))
            result = solver.check()
            return result == sat
        except Exception:
            # If parsing fails, consider it unsatisfiable
            return False

    def pdiscover(self, module_id: ModuleId, axioms_list: List[str], cert_dir: Path, trace_lines: List[str], step: int) -> str:
        """Perform brute-force partition discovery on module with given axioms."""
        print(f"PDISCOVER: Starting partition discovery on module {module_id}")
        
        region = self.state.regions[module_id]
        if not region:
            print("PDISCOVER: Empty region, nothing to partition")
            return "empty region"
        
        # For paradox demonstration, try different partition strategies
        region_list = list(region)
        n = len(region_list)
        
        print(f"PDISCOVER: Region has {n} elements: {region_list}")
        
        if n < 2:
            print("PDISCOVER: Region too small for partitioning (need at least 2 elements)")
            return "region too small for partitioning"
        
        print(f"PDISCOVER: Exploring {n//2} possible partition splits...")
        
        # Try different split points and test for paradoxes
        found_paradox = False
        paradox_partition = None
        partitions_explored = 0
        
        # Use threading for parallel partition testing
        from concurrent.futures import ThreadPoolExecutor, as_completed
        
        def test_partition(i):
            """Test a single partition split."""
            part1 = set(region_list[:i])
            part2 = set(region_list[i:])
            
            # Create temporary state for testing
            temp_state = State()
            temp_state.axioms = {}  # Fresh axioms dict
            
            # Create submodules in temp state
            m1 = temp_state.pnew(part1)
            m2 = temp_state.pnew(part2)
            
            # Add axioms to partitions
            if len(axioms_list) >= 2:
                temp_state.add_axiom(m1, axioms_list[0])
                temp_state.add_axiom(m2, axioms_list[1])
            else:
                for axioms in axioms_list:
                    temp_state.add_axiom(m1, axioms)
                    temp_state.add_axiom(m2, axioms)
            
            # Test satisfiability
            combined_axioms = "\n".join(temp_state.get_module_axioms(m1) + temp_state.get_module_axioms(m2))
            is_satisfiable = self.test_combined_satisfiability(combined_axioms)
            
            return i, part1, part2, is_satisfiable
        
        # Test partitions in parallel
        print(f"PDISCOVER: Testing {n//2} partitions in parallel...")
        
        with ThreadPoolExecutor(max_workers=min(4, n//2)) as executor:
            # Submit all partition tests
            future_to_partition = {
                executor.submit(test_partition, i): i 
                for i in range(1, n//2 + 1)
            }
            
            # Process results as they complete
            for future in as_completed(future_to_partition):
                partitions_explored += 1
                
                if partitions_explored % 5 == 0:
                    print(f"PDISCOVER: Completed {partitions_explored}/{n//2} partitions...")
                
                i, part1, part2, is_satisfiable = future.result()
                
                if not is_satisfiable:
                    # Paradox found!
                    found_paradox = True
                    paradox_partition = (part1, part2)
                    print(f"PDISCOVER: PARADOX FOUND in partition {part1} | {part2}")
                    trace_lines.append(f"{step}: PDISCOVER found paradox in partition: {part1} | {part2}")
                    # Cancel remaining tasks
                    for f in future_to_partition:
                        if not f.done():
                            f.cancel()
                    break
        
        print(f"PDISCOVER: Exploration complete. Explored {partitions_explored} partitions.")
        
        if found_paradox:
            print(f"PDISCOVER: Result - Paradox found in partition {paradox_partition}")
            return f"paradox found in partition {paradox_partition}"
        else:
            print("PDISCOVER: Result - No paradoxes found in explored partitions")
            return "no paradox found"

    def run(self, program: List[Instruction], outdir: Path) -> None:
        outdir.mkdir(parents=True, exist_ok=True)
        trace_lines: List[str] = []
        ledger: List[LedgerEntry] = []
        cert_dir = outdir / "certs"
        modules: Dict[str, int] = {}  # For tracking named modules
        current_module = self.state.pnew({0})  # Use region {0} for initial module
        step = 0
        self.step_receipts = []
        self.witness_state = WitnessState()

        print("Thiele Machine VM starting execution...")
        print(f"Program has {len(program)} instructions")
        print(f"Output directory: {outdir}")
        print()
        # Log VM run start
        logger = get_thiele_logger()
        try:
            logger.info("vm.run.start", {"program_len": len(program), "outdir": str(outdir)})
        except Exception:
            pass

        for op, arg in program:
            step += 1
            print(f"Step {step:3d}: {op} {arg}")
            step += 1
            pre_witness = WitnessState(**self.witness_state.snapshot())
            receipt_instruction: Optional[InstructionWitness] = None
            halt_after_receipt = False
            if op == "PNEW":
                # PNEW region_spec - create new module for region
                if arg and arg.strip().startswith('{') and arg.strip().endswith('}'):
                    # It's a region specification like {1,2,3}
                    region_str = arg.strip()[1:-1]  # Remove {}
                    if region_str:
                        region = set(map(int, region_str.split(',')))
                    else:
                        region = set()
                else:
                    # Default region
                    region = {1}
                new_module = self.state.pnew(region)
                modules[f"m{len(modules)}"] = new_module
                current_module = new_module
                trace_lines.append(f"{step}: PNEW {arg} -> module {new_module}")
                receipt_instruction = InstructionWitness("PNEW", sorted(region))
            elif op == "PSPLIT":
                # PSPLIT module_id pred_expr - split module using predicate
                parts = arg.split()
                module_id = ModuleId(int(parts[0]))
                pred_expr = parts[1] if len(parts) > 1 else "lambda x: x % 2 == 0"
                # Simple predicate: even/odd based on first element
                def pred(x): return x % 2 == 0
                m1, m2 = self.state.psplit(module_id, pred)
                trace_lines.append(f"{step}: PSPLIT {module_id} ({pred_expr}) -> {m1}, {m2}")
                receipt_instruction = InstructionWitness("PYEXEC", f"PSPLIT {arg}")
            elif op == "PMERGE":
                # PMERGE m1 m2 - merge two modules
                parts = arg.split()
                m1 = ModuleId(int(parts[0]))
                m2 = ModuleId(int(parts[1]))
                merged = self.state.pmerge(m1, m2)
                trace_lines.append(f"{step}: PMERGE {m1}, {m2} -> {merged}")
                current_module = merged
                receipt_instruction = InstructionWitness("PYEXEC", f"PMERGE {arg}")
            elif op == "LASSERT":
                # LASSERT formula_file - add formula as axiom to current module and check satisfiability
                formula = Path(arg).read_text(encoding='utf-8')
                digest = lassert(self.state, current_module, formula, cert_dir)
                if self.state.csr[CSR.STATUS] == 0:
                    self.state.csr[CSR.ERR] = 1
                trace_lines.append(f"{step}: LASSERT {arg} -> {digest}")
                if self.state.csr[CSR.STATUS] == 0:
                    self.state.csr[CSR.ERR] = 1
                    trace_lines.append(f"{step}: LASSERT unsat - halting VM")
                    halt_after_receipt = True
                receipt_instruction = InstructionWitness("LASSERT", formula)
            elif op == "LJOIN":
                # LJOIN cert1 cert2 - join two certificates
                parts = arg.split()
                cert1 = parts[0]
                cert2 = parts[1]
                digest = ljoin(self.state, cert1, cert2, cert_dir)
                trace_lines.append(f"{step}: LJOIN {cert1}, {cert2} -> {digest}")
                receipt_instruction = InstructionWitness("PYEXEC", f"LJOIN {arg}")
            elif op == "MDLACC":
                # MDLACC module - accumulate mu for module
                module_id = ModuleId(int(arg)) if arg else current_module
                consistent = self.state.csr[CSR.ERR] == 0
                prev_operational = self.state.mu_operational
                mu = mdlacc(self.state, module_id, consistent=consistent)
                delta_operational = self.state.mu_operational - prev_operational
                ledger.append({
                    "step": step,
                    "delta_mu_operational": delta_operational,
                    "delta_mu_information": 0,
                    "total_mu_operational": self.state.mu_operational,
                    "total_mu_information": self.state.mu_information,
                    "total_mu": self.state.mu,
                    "reason": f"mdlacc_module{module_id}",
                })
                trace_lines.append(f"{step}: MDLACC {module_id} -> mu={mu}")
                receipt_instruction = InstructionWitness("MDLACC", int(module_id))
            elif op == "EMIT":
                # EMIT value - emit value to output
                trace_lines.append(f"{step}: EMIT {arg}")
                receipt_instruction = InstructionWitness("EMIT", arg)
                try:
                    logger.info("vm.emit", {"value": arg, "step": step, "module": current_module})
                except Exception:
                    pass
            elif op == "PDISCOVER":
                # PDISCOVER module_id axioms_file1 [axioms_file2] - brute-force partition discovery
                parts = arg.split()
                if len(parts) < 2:
                    raise ValueError(f"PDISCOVER requires module_id and at least one axioms_file, got: {arg}")
                module_id = ModuleId(int(parts[0]))
                axioms_files = parts[1:]
                axioms_list = [Path(f).read_text(encoding='utf-8') for f in axioms_files]

                # Perform brute-force partition search
                result = self.pdiscover(module_id, axioms_list, cert_dir, trace_lines, step)
                trace_lines.append(f"{step}: PDISCOVER {arg} -> {result}")
                receipt_instruction = InstructionWitness("PYEXEC", f"PDISCOVER {arg}")
            elif op == "PYEXEC":
                if arg.startswith('"') and arg.endswith('"'):
                    python_code = arg[1:-1]  # Remove quotes
                else:
                    python_code = arg

                result, output = self.execute_python(python_code)
                if output:
                    # Split output into lines for better readability
                    for line in output.strip().split('\n'):
                        if line.strip():
                            trace_lines.append(f"{step}: PYEXEC output: {line}")
                try:
                    logger.info(
                        "vm.pyexec",
                        {
                            "code": (python_code if len(python_code) < 256 else python_code[:256] + "..."),
                            "output": (output if output else ""),
                            "step": step,
                        },
                    )
                except Exception:
                    pass
                
                # Check for result in multiple ways
                actual_result = result
                if actual_result is None and '__result__' in self.python_globals:
                    actual_result = self.python_globals['__result__']
                
                if actual_result is not None:
                    trace_lines.append(f"{step}: PYEXEC result: {actual_result}")
                    # Store result in python globals for later use
                    self.python_globals['_last_result'] = actual_result

                    # Charge for information revealed by PYEXEC
                    # Check if this looks like factoring output (p, q tuple)
                    if isinstance(actual_result, tuple) and len(actual_result) == 2:
                        p, q = actual_result
                        if isinstance(p, int) and isinstance(q, int):
                            # Try to extract the target modulus from the code
                            code_to_parse = python_code
                            if python_code.endswith('.py') or Path(python_code).exists():
                                try:
                                    code_to_parse = Path(python_code).read_text(encoding='utf-8')
                                except:
                                    pass
                            n_target = extract_target_modulus(code_to_parse)
                            if n_target is not None and p * q == n_target:
                                # Validate proper factorization
                                if 1 < p < n_target and 1 < q < n_target:
                                    witness_repr = f"{p}:{q}"
                                    bits_revealed = mu_cost_from_text(witness_repr)
                                    prev_info = self.state.mu_information
                                    info_charge(self.state, bits_revealed)
                                    ledger.append({
                                        "step": step,
                                        "delta_mu_operational": 0,
                                        "delta_mu_information": bits_revealed,
                                        "total_mu_operational": self.state.mu_operational,
                                        "total_mu_information": self.state.mu_information,
                                        "total_mu": self.state.mu,
                                        "reason": f"factoring_revelation_p{p}_q{q}",
                                    })
                                    trace_lines.append(
                                        f"{step}: PYEXEC charged {bits_revealed} μ-bits for factoring revelation"
                                    )
                                else:
                                    trace_lines.append(f"{step}: PYEXEC invalid factors detected (p={p}, q={q} for n={n_target})")

                # Show what was executed (truncated for readability)
                if len(python_code) > 50:
                    trace_lines.append(f"{step}: PYEXEC {python_code[:47]}...")
                else:
                    trace_lines.append(f"{step}: PYEXEC {python_code}")
                if "Error:" in output:
                    self.state.csr[CSR.ERR] = 1
                    trace_lines.append(f"{step}: PYEXEC error detected - halting VM")
                    halt_after_receipt = True
                receipt_instruction = InstructionWitness("PYEXEC", python_code)
            else:
                raise ValueError(f"unknown opcode {op}")

            if receipt_instruction is None:
                receipt_instruction = InstructionWitness("PYEXEC", f"{op} {arg}".strip())
            self._record_receipt(step, pre_witness, receipt_instruction)

            if self.state.csr[CSR.ERR] == 1 or halt_after_receipt:
                trace_lines.append(f"{step}: ERR flag set - halting VM")
                break
        # Final accounting and output
        mdlacc(self.state, current_module, consistent=self.state.csr[CSR.ERR] == 0)

        ledger.append({
            "step": step + 1,
            "delta_mu_operational": 0,
            "delta_mu_information": 0,
            "total_mu_operational": self.state.mu_operational,
            "total_mu_information": self.state.mu_information,
            "total_mu": self.state.mu,
            "reason": "final",
        })

        # Write outputs
        (outdir / "trace.log").write_text("\n".join(trace_lines), encoding='utf-8')
        (outdir / "mu_ledger.json").write_text(json.dumps(ledger), encoding='utf-8')

        summary = {
            "mu_operational": self.state.mu_operational,
            "mu_information": self.state.mu_information,
            "mu_total": self.state.mu,
            "cert": self.state.csr[CSR.CERT_ADDR],
        }
        (outdir / "summary.json").write_text(json.dumps(summary), encoding='utf-8')

        receipts_path = outdir / "step_receipts.json"
        receipts_json = [receipt.to_dict() for receipt in self.step_receipts]
        receipts_path.write_text(json.dumps(receipts_json, indent=2), encoding='utf-8')

        # Log VM run finish
        try:
            logger.info("vm.run.finish", {"outdir": str(outdir), "steps": step, "receipts": len(self.step_receipts)})
        except Exception:
            pass


def main():
    """Run Python files directly through the Thiele CPU VM."""
    if len(sys.argv) < 2:
        print("Usage: python3 vm.py <python_file.py> [output_dir]")
        print("Example: python3 vm.py scripts/solve_sudoku.py")
        sys.exit(1)

    python_file = sys.argv[1]
    if not python_file.endswith('.py'):
        print(f"Error: {python_file} is not a Python file")
        sys.exit(1)

    if not Path(python_file).exists():
        print(f"Error: {python_file} not found")
        sys.exit(1)

    # Create output directory
    if len(sys.argv) > 2:
        outdir = Path(sys.argv[2])
    else:
        outdir = Path('out') / Path(python_file).stem

    # Create a simple Thiele program to execute the Python file
    program_text = f"""; Auto-generated Thiele program to execute {python_file}
PNEW {{10,11,12,13,14,15,16,17,18}}
PYEXEC {python_file}
MDLACC
EMIT "Python execution completed"
"""

    # Parse the program
    program_lines = program_text.split('\n')
    program = parse(program_lines, Path(python_file).parent)

    # Run the VM
    vm = VM(State())
    vm.run(program, outdir)

    print(f"Execution completed. Output written to {outdir}/")


if __name__ == "__main__":
    main()


__all__ = ["VM"]
