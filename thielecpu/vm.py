"""Virtual machine execution loop."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import json
from typing import List, Dict, Any, Optional
import ast
import sys
from io import StringIO
import hashlib
import string
import z3

# Safety: maximum allowed classical combinations for brute-force searches.
# Can be overridden by the environment variable THIELE_MAX_COMBINATIONS.
import os
SAFE_COMBINATION_LIMIT = int(os.environ.get('THIELE_MAX_COMBINATIONS', 10_000_000))

try:
    from .assemble import Instruction, parse
    from .logic import lassert, ljoin
    from .mdl import mdlacc, info_charge
    from .state import State
    from .isa import CSR
    from ._types import LedgerEntry, ModuleId
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
    from thielecpu._types import LedgerEntry, ModuleId


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

    def __post_init__(self):
        if self.python_globals is None:
            self.python_globals = {
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
                'placeholder': placeholder,
                'hashlib': hashlib,
                'self': self,
            }

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

            # Parse the code to check for syntax errors
            ast.parse(code)

            # Check if code contains symbolic variables
            if 'placeholder(' in code:
                return self.execute_symbolic_python(code, source_info)

            # Capture stdout
            old_stdout = sys.stdout
            sys.stdout = captured_output = StringIO()

            try:
                # Try exec first for statements (most common case)
                exec(code, self.python_globals)
                output = captured_output.getvalue()
                return None, output
            except SyntaxError:
                # If exec fails, try eval for expressions
                result = eval(code, self.python_globals)
                output = captured_output.getvalue()
                return result, output
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

    def run(self, program: List[Instruction], outdir: Path) -> None:
        outdir.mkdir(parents=True, exist_ok=True)
        trace_lines: List[str] = []
        ledger: List[LedgerEntry] = []
        cert_dir = outdir / "certs"
        modules: Dict[str, int] = {}  # For tracking named modules
        current_module = self.state.pnew({0})  # Use region {0} for initial module
        step = 0
        for op, arg in program:
            step += 1
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
            elif op == "PSPLIT":
                # PSPLIT module_id pred_expr - split module using predicate
                parts = arg.split()
                module_id = ModuleId(int(parts[0]))
                pred_expr = parts[1] if len(parts) > 1 else "lambda x: x % 2 == 0"
                # Simple predicate: even/odd based on first element
                def pred(x): return x % 2 == 0
                m1, m2 = self.state.psplit(module_id, pred)
                trace_lines.append(f"{step}: PSPLIT {module_id} ({pred_expr}) -> {m1}, {m2}")
            elif op == "PMERGE":
                # PMERGE m1 m2 - merge two modules
                parts = arg.split()
                m1 = ModuleId(int(parts[0]))
                m2 = ModuleId(int(parts[1]))
                merged = self.state.pmerge(m1, m2)
                trace_lines.append(f"{step}: PMERGE {m1}, {m2} -> {merged}")
                current_module = merged
            elif op == "LASSERT":
                formula = Path(arg).read_text(encoding='utf-8')
                digest = lassert(self.state, current_module, formula, cert_dir)
                if self.state.csr[CSR.STATUS] == 0:
                    self.state.csr[CSR.ERR] = 1
                trace_lines.append(f"{step}: LASSERT {arg} -> {digest}")
                if self.state.csr[CSR.STATUS] == 0:
                    self.state.csr[CSR.ERR] = 1
                    trace_lines.append(f"{step}: LASSERT unsat - halting VM")
                    break
            elif op == "LJOIN":
                # LJOIN cert1 cert2 - join two certificates
                parts = arg.split()
                cert1 = parts[0]
                cert2 = parts[1]
                digest = ljoin(self.state, cert1, cert2, cert_dir)
                trace_lines.append(f"{step}: LJOIN {cert1}, {cert2} -> {digest}")
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
            elif op == "EMIT":
                # EMIT value - emit value to output
                trace_lines.append(f"{step}: EMIT {arg}")
            elif op == "XFER":
                # XFER src dest - transfer data
                trace_lines.append(f"{step}: XFER {arg}")
            elif op == "PYEXEC":
                # PYEXEC python_code - execute Python code or file
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
                                    # Charge for revealed bits: sum of bit lengths (≈ log₂ n)
                                    bits_revealed = p.bit_length() + q.bit_length()
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
                                    trace_lines.append(f"{step}: PYEXEC charged {bits_revealed} bits for factoring revelation (p={p.bit_length()} bits, q={q.bit_length()} bits)")
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
                    break
            else:
                raise ValueError(f"unknown opcode {op}")

            if self.state.csr[CSR.ERR] == 1:
                trace_lines.append(f"{step}: ERR flag set - halting VM")
                break
        mdlacc(self.state, current_module, consistent=self.state.csr[CSR.ERR] == 0)
        ledger.append(
            {
                "step": step + 1,
                "delta_mu_operational": 0,
                "delta_mu_information": 0,
                "total_mu_operational": self.state.mu_operational,
                "total_mu_information": self.state.mu_information,
                "total_mu": self.state.mu,
                "reason": "final",
            }
        )
        (outdir / "trace.log").write_text("\n".join(trace_lines), encoding='utf-8')
        (outdir / "mu_ledger.json").write_text(json.dumps(ledger), encoding='utf-8')
        summary = {
            "mu_operational": self.state.mu_operational,
            "mu_information": self.state.mu_information,
            "mu_total": self.state.mu,
            "cert": self.state.csr[CSR.CERT_ADDR]
        }
        (outdir / "summary.json").write_text(json.dumps(summary), encoding='utf-8')


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
