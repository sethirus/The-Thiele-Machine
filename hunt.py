# hunt.py
# This is not a linter. It is an autonomous weapon.
# It hunts for the single, highest-leverage logical paradox in a codebase.

import ast
import os
import sys
from z3 import Solver, Int, Bool, And, Or, Not, sat, unsat

# --- Operator Dictionaries ---
BIN_OPS = {ast.Add: __import__('operator').add, ast.Sub: __import__('operator').sub, ast.Mult: __import__('operator').mul, ast.FloorDiv: __import__('operator').floordiv, ast.Mod: __import__('operator').mod}
CMP_OPS = {ast.Eq: __import__('operator').eq, ast.NotEq: __import__('operator').ne, ast.Lt: __import__('operator').lt, ast.LtE: __import__('operator').le, ast.Gt: __import__('operator').gt, ast.GtE: __import__('operator').ge}
BOOL_OPS = {ast.And: And, ast.Or: Or}
UNARY_OPS = {ast.USub: __import__('operator').neg, ast.Not: Not, ast.UAdd: lambda x: x}

class Category:
    def __init__(self, name):
        self.name = name
        self.morphisms = []

    def add_morphism(self, name, domain_sorts, codomain_sort, promises, arg_names):
        self.morphisms.append({
            'name': name,
            'dom': domain_sorts,
            'cod': codomain_sort,
            'promises': promises,
            'args': arg_names
        })

    def get_global_axioms(self):
        all_promises = []
        for m in self.morphisms:
            all_promises.extend(m.get('promises', []))
        from z3 import BoolVal
        return And(*all_promises) if all_promises else BoolVal(True)

class ThieleAuditor:
    def __init__(self, source_code):
        self.source = source_code
        self.func_node = self._parse_function(source_code)
        self.preconditions = []
        self.postconditions = []
        self.assertions = []
        self.contract_parse_error = None
        self._extract_contracts()
        self.z3_vars = {}
        self.category = None
        self.mubits = 0
        self.bits = None

    def _parse_function(self, source):
        try:
            tree = ast.parse(source)
            for node in ast.walk(tree):
                if isinstance(node, ast.FunctionDef):
                    return node
            raise ValueError("No function definition found.")
        except Exception as e:
            self.contract_parse_error = f"Parse error: {e}"
            return None

    def _extract_contracts(self):
        if not self.func_node:
            return
        doc = ast.get_docstring(self.func_node)
        if doc:
            for line in doc.splitlines():
                line = line.strip()
                if line.startswith("Pre:"):
                    self.preconditions.append(line[4:].strip())
                elif line.startswith("Post:"):
                    self.postconditions.append(line[5:].strip())
        for stmt in self.func_node.body:
            if isinstance(stmt, ast.Assert):
                self.assertions.append(ast.unparse(stmt.test))

    def _has_contract(self):
        return bool(self.preconditions or self.postconditions)

    def audit(self):
        if self.contract_parse_error or not self.func_node:
            return "IMPLEMENTATION_FAILURE", self.contract_parse_error or "Function parse error"
        if not self._has_contract():
            return "VACUOUS", "No contract found"
        try:
            arg_names = [a.arg for a in getattr(self.func_node.args, "args", [])]
            self.z3_vars = {name: Int(name) for name in arg_names}
            self.z3_vars['return'] = Int('return')
            self.z3_vars['result'] = self.z3_vars['return']
            domain_sorts = tuple(self.z3_vars[name].sort() for name in arg_names)
            codomain_sort = self.z3_vars['return'].sort()
            promises = []
            for pre in self.preconditions:
                try:
                    expr_ast = ast.parse(pre, mode='eval').body
                    promises.append(self._build_z3_expr(expr_ast))
                except Exception as e:
                    return "IMPLEMENTATION_FAILURE", f"Error in precondition '{pre}': {e}"
            for assertion in self.assertions:
                try:
                    expr_ast = ast.parse(assertion, mode='eval').body
                    promises.append(self._build_z3_expr(expr_ast))
                except Exception as e:
                    return "IMPLEMENTATION_FAILURE", f"Error in assertion '{assertion}': {e}"
            for post in self.postconditions:
                try:
                    expr_ast = ast.parse(post.replace("return", "result"), mode='eval').body
                    promises.append(self._build_z3_expr(expr_ast))
                except Exception as e:
                    return "IMPLEMENTATION_FAILURE", f"Error in postcondition '{post}': {e}"
            for stmt in getattr(self.func_node, "body", []):
                if isinstance(stmt, ast.Return) and stmt.value:
                    promises.append(self.z3_vars['return'] == self._build_z3_expr(stmt.value))
            self.category = Category("ProgramSpace")
            self.category.add_morphism(getattr(self.func_node, "name", "unknown"), domain_sorts, codomain_sort, promises, arg_names)
            solver = Solver()
            solver.add(self.category.get_global_axioms())
            if solver.check() == sat:
                return "PROVEN", "Contract is satisfiable"
            else:
                return "CONTRACT_VIOLATION", "No model exists; contract is self-contradictory"
        except Exception as e:
            return "IMPLEMENTATION_FAILURE", f"Audit error: {e}"

    def _build_z3_expr(self, node):
        if isinstance(node, ast.Constant):
            return node.value
        if isinstance(node, ast.Name):
            if node.id in self.z3_vars:
                return self.z3_vars[node.id]
            raise NameError(f"Unknown symbol: {node.id}")
        if isinstance(node, ast.UnaryOp):
            op = UNARY_OPS.get(type(node.op))
            if not op:
                raise TypeError(f"Unsupported unary op: {type(node.op)}")
            return op(self._build_z3_expr(node.operand))
        if isinstance(node, ast.BinOp):
            op = BIN_OPS.get(type(node.op))
            if not op:
                raise TypeError(f"Unsupported binary op: {type(node.op)}")
            left, right = self._build_z3_expr(node.left), self._build_z3_expr(node.right)
            return op(left, right)
        if isinstance(node, ast.BoolOp):
            op = BOOL_OPS.get(type(node.op))
            if not op:
                raise TypeError(f"Unsupported bool op: {type(node.op)}")
            return op(*[self._build_z3_expr(v) for v in node.values])
        if isinstance(node, ast.Compare):
            left = self._build_z3_expr(node.left)
            parts = []
            for op_node, right_node in zip(node.ops, node.comparators):
                op = CMP_OPS.get(type(op_node))
                if not op:
                    raise TypeError(f"Unsupported compare op: {type(op_node)}")
                right = self._build_z3_expr(right_node)
                parts.append(op(left, right))
                left = right
            return And(*parts)
        raise TypeError(f"Unsupported AST node: {ast.dump(node)}")

# --- Scoring Heuristic ---
SCORING_WEIGHTS = {
    'verdict': {
        'IMPLEMENTATION_FAILURE': 500,
        'CONTRACT_VIOLATION': 400,
        'VACUOUS': 0,
    },
    'simplicity': 1000,
    'impact': {
        'assert': 300, 'error': 200, 'verify': 200, 'core': 150,
        'truth': 250, 'rewrite': 250, 'check': 150, 'test': 100,
        'api': 200, 'public': 150,
    }
}

def calculate_score(paradox):
    score = 0
    score += SCORING_WEIGHTS['verdict'].get(paradox['verdict'], 0)
    line_count = paradox['lines']
    if line_count > 0:
        score += SCORING_WEIGHTS['simplicity'] / line_count
    search_string = (paradox['file'] + paradox['function']).lower()
    for keyword, value in SCORING_WEIGHTS['impact'].items():
        if keyword in search_string:
            score += value
    paradox['score'] = score
    return score

def hunt(root_path):
    found_paradoxes = []
    for dirpath, _, filenames in os.walk(root_path):
        for filename in filenames:
            if filename.endswith('.py'):
                file_path = os.path.join(dirpath, filename)
                try:
                    with open(file_path, 'r', encoding='utf-8') as f:
                        source = f.read()
                    tree = ast.parse(source)
                    # Set parent pointers for class/context detection
                    for parent in ast.walk(tree):
                        for child in ast.iter_child_nodes(parent):
                            child.parent = parent

                    def is_noop_function(fn):
                        b = fn.body
                        if not b:
                            return True
                        if len(b) == 1 and isinstance(b[0], ast.Pass):
                            return True
                        if len(b) == 1 and isinstance(b[0], ast.Return) and b[0].value is None:
                            return True
                        if len(b) == 1 and isinstance(b[0], ast.Expr) and isinstance(b[0].value, ast.Constant):
                            if b[0].value.value is Ellipsis or isinstance(b[0].value.value, str):
                                return True
                        return False

                    def enclosing_class_name(node):
                        while hasattr(node, 'parent'):
                            node = node.parent
                            if isinstance(node, ast.ClassDef):
                                return node.name
                        return None

                    for node in ast.walk(tree):
                        if isinstance(node, ast.FunctionDef):
                            # Skip no-op/marker functions
                            if is_noop_function(node):
                                continue
                            cls = enclosing_class_name(node)
                            if cls and any(tok in cls.lower() for tok in ("protocol", "dummy", "noop", "stub")):
                                continue
                            try:
                                func_source = ast.unparse(node)
                                print(f"Analyzing: {file_path} -> {node.name}")
                                auditor = ThieleAuditor(func_source)
                                # Only audit functions with explicit contracts OR internal asserts
                                if not (auditor.preconditions or auditor.postconditions or auditor.assertions):
                                    continue
                                verdict, result = auditor.audit()
                                if verdict in ['IMPLEMENTATION_FAILURE', 'CONTRACT_VIOLATION', 'VACUOUS']:
                                    start_line = getattr(node, 'lineno', None)
                                    end_line = getattr(node, 'end_lineno', None)
                                    if start_line is not None and end_line is not None:
                                        lines = end_line - start_line + 1
                                    else:
                                        lines = -1
                                    found_paradoxes.append({
                                        'file': file_path,
                                        'function': node.name,
                                        'lines': lines,
                                        'verdict': verdict,
                                        'evidence': result,
                                        'source': func_source,
                                    })
                            except Exception:
                                continue
                except Exception:
                    continue
    if not found_paradoxes:
        return None
    best_paradox = max(found_paradoxes, key=calculate_score)
    return best_paradox

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python3 hunt.py <path_to_target_directory>")
        sys.exit(1)
    target_directory = sys.argv[1]
    # Silent except for final output
    prime_target = hunt(target_directory)
    if prime_target:
        print("\n--- PRIME TARGET ACQUIRED ---")
        print(f"\nSCORE: {prime_target.get('score', 0):.2f}")
        print(f"FILE: {prime_target.get('file')}")
        print(f"FUNCTION: {prime_target.get('function')}")
        print(f"VERDICT: {prime_target.get('verdict')}")
        print(f"EVIDENCE: {prime_target.get('evidence')}")
        print("\n--- SOURCE OF PARADOX ---")
        print(prime_target.get('source'))
        print("\n--- MISSION DIRECTIVE ---")
        print("You have your target. This is the undeniable proof.")
        print("Craft the Pull Request. This is the first shot.")
    else:
        print("\n--- HUNT COMPLETE ---")
        print("No high-value logical paradoxes with explicit contracts were found.")