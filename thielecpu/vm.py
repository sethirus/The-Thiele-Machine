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

try:
    from .assemble import Instruction, parse
    from .logic import lassert, ljoin
    from .mdl import mdlacc
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
    from thielecpu.mdl import mdlacc
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

def placeholder(domain: Optional[List[str]] = None) -> SymbolicVariable:
    """Create a symbolic variable placeholder for logical deduction."""
    global _symbolic_var_counter
    if domain is None:
        # Default domain: lowercase letters and digits
        domain = list(string.ascii_lowercase + string.digits)

    var_name = f"var_{_symbolic_var_counter}"
    _symbolic_var_counter += 1

    return SymbolicVariable(var_name, domain)


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
            }

    def execute_python(self, code_or_path: str) -> Any:
        """Execute Python code or file in a sandboxed environment."""
        try:
            # Check if it's a file path
            if code_or_path.endswith('.py') or ('\n' not in code_or_path.strip() and Path(code_or_path).exists()):
                try:
                    # Try to read as file
                    code = Path(code_or_path).read_text()
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
            return None, f"Error: {str(e)}"

    def execute_symbolic_python(self, code: str, source_info: str) -> Any:
        """Execute Python code with symbolic variables using logical deduction."""
        import itertools
        import ast

        # 1. Parse the code and find symbolic assignments
        try:
            tree = ast.parse(code)
        except SyntaxError as e:
            return None, f"Syntax Error: {e}"

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
                                    # The value of the keyword argument is another AST node.
                                    # We need to evaluate it. The original code used ast.literal_eval,
                                    # which is too restrictive for calls like `list("abc")`.
                                    domain_val = None
                                    if (isinstance(kw.value, ast.Call) and
                                        isinstance(kw.value.func, ast.Name) and
                                        kw.value.func.id == 'list' and
                                        len(kw.value.args) == 1):

                                        arg_node = kw.value.args[0]
                                        str_val = None

                                        # Python 3.8+ uses ast.Constant for strings
                                        if isinstance(arg_node, ast.Constant) and isinstance(arg_node.value, str):
                                            str_val = arg_node.value
                                        # Python < 3.8 uses ast.Str, which we check for safely
                                        elif hasattr(ast, 'Str') and isinstance(arg_node, ast.Str):
                                            str_val = arg_node.s

                                        if str_val is not None:
                                            domain_val = list(str_val)

                                    if domain_val is None:
                                        # Fallback to literal_eval for simple lists like `['a', 'b', 'c']`
                                        try:
                                            domain_val = ast.literal_eval(kw.value)
                                        except Exception:
                                            pass  # Stick with default if eval fails

                                    if isinstance(domain_val, list):
                                        domain = domain_val
                        symbolic_assignments[var_name] = domain
                self.generic_visit(node)

        PlaceholderVisitor().visit(tree)

        if not symbolic_assignments:
            # No symbolic variables found, execute normally
            return self.execute_python(code)

        var_names = list(symbolic_assignments.keys())
        domains = [symbolic_assignments[name] for name in var_names]
        
        print(f"Found {len(var_names)} symbolic variables: {var_names}")

        total_combinations = 1
        for domain in domains:
            total_combinations *= len(domain)
        print(f"Searching through {total_combinations} combinations...")

        # Use an AST transformer to remove the symbolic assignments.
        # This is more robust than string manipulation.
        class SymbolicAssignmentRemover(ast.NodeTransformer):
            def visit_Assign(self, node):
                # Check if this is a symbolic assignment
                if (isinstance(node.value, ast.Call) and
                    isinstance(node.value.func, ast.Name) and
                    node.value.func.id == 'placeholder'):
                    # Remove this node by returning None
                    return None
                return node

        remover = SymbolicAssignmentRemover()
        new_tree = remover.visit(tree)
        ast.fix_missing_locations(new_tree)
        
        # Convert the modified AST back to code
        # Note: ast.unparse requires Python 3.9+. For broader compatibility,
        # a backport like `astunparse` would be needed if targeting older versions.
        # For this project, we assume Python 3.9+.
        code_to_run = ast.unparse(new_tree)

        # 2. Try each combination
        for combination in itertools.product(*domains):
            assignment = dict(zip(var_names, combination))
            print(f"Trying assignment: {assignment}")

            # 3. Create execution environment with solved values
            solved_globals = self.python_globals.copy()
            solved_globals.update(assignment)

            # 4. Try to execute with this assignment
            old_stdout = sys.stdout
            sys.stdout = captured_output = StringIO()
            
            success = False
            err = None
            output = ""

            try:
                exec(code_to_run, solved_globals)
                success = True
            except AssertionError as e:
                err = f"Assertion failed: {e}"
            except Exception as e:
                import traceback
                err = f"Other error: {e}\n{traceback.format_exc()}"
            
            output = captured_output.getvalue()
            sys.stdout = old_stdout # Restore stdout

            if success:
                print(f"✓ Found satisfying assignment: {assignment}")
                return None, f"Symbolic execution successful!\nAssignment: {assignment}\nOutput:\n{output}"
            else:
                # This will now print to the console for each failed attempt.
                print(f"x Failed assignment: {assignment} -> {err}")
        
        return None, "No satisfying assignment found for symbolic variables"

    def run(self, program: List[Instruction], outdir: Path) -> None:
        outdir.mkdir(parents=True, exist_ok=True)
        trace_lines: List[str] = []
        ledger: List[LedgerEntry] = []
        cert_dir = outdir / "certs"
        modules: Dict[str, int] = {}  # For tracking named modules
        current_module = self.state.pnew({1})
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
                trace_lines.append(f"{step}: PSPLIT {module_id} -> {m1}, {m2}")
            elif op == "PMERGE":
                # PMERGE m1 m2 - merge two modules
                parts = arg.split()
                m1 = ModuleId(int(parts[0]))
                m2 = ModuleId(int(parts[1]))
                merged = self.state.pmerge(m1, m2)
                trace_lines.append(f"{step}: PMERGE {m1}, {m2} -> {merged}")
                current_module = merged
            elif op == "LASSERT":
                formula = Path(arg).read_text()
                digest = lassert(self.state, current_module, formula, cert_dir)
                trace_lines.append(f"{step}: LASSERT {arg} -> {digest}")
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
                mu = mdlacc(self.state, module_id, consistent=consistent)
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
                if result is not None:
                    trace_lines.append(f"{step}: PYEXEC result: {result}")
                    # Store result in python globals for later use
                    self.python_globals['_last_result'] = result
                # Show what was executed (truncated for readability)
                if len(python_code) > 50:
                    trace_lines.append(f"{step}: PYEXEC {python_code[:47]}...")
                else:
                    trace_lines.append(f"{step}: PYEXEC {python_code}")
            else:
                raise ValueError(f"unknown opcode {op}")
        mdlacc(self.state, current_module, consistent=self.state.csr[CSR.ERR] == 0)
        ledger.append(
            {
                "step": step + 1,
                "delta_mu": 0,
                "total_mu": self.state.mu,
                "reason": "final",
            }
        )
        (outdir / "trace.log").write_text("\n".join(trace_lines))
        (outdir / "mu_ledger.json").write_text(json.dumps(ledger))
        summary = {"mu": self.state.mu, "cert": self.state.csr[CSR.CERT_ADDR]}
        (outdir / "summary.json").write_text(json.dumps(summary))


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
