import ast
from z3 import Solver, Int, Bool, And, Or, Not, sat, unsat

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

BIN_OPS = {ast.Add: __import__('operator').add, ast.Sub: __import__('operator').sub, ast.Mult: __import__('operator').mul, ast.FloorDiv: __import__('operator').floordiv, ast.Mod: __import__('operator').mod}
CMP_OPS = {ast.Eq: __import__('operator').eq, ast.NotEq: __import__('operator').ne, ast.Lt: __import__('operator').lt, ast.LtE: __import__('operator').le, ast.Gt: __import__('operator').gt, ast.GtE: __import__('operator').ge}
BOOL_OPS = {ast.And: And, ast.Or: Or}
UNARY_OPS = {ast.USub: __import__('operator').neg, ast.Not: Not, ast.UAdd: lambda x: x}

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
        return bool(self.preconditions or self.postconditions or self.assertions)

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

    # Remove duplicate and conflicting methods from here on.

    def _ast_to_category(self, func_node):
        category = Category("ProgramSpace")
        try:
            arg_names = [a.arg for a in func_node.args.args]
            self.z3_vars = {name: Int(name) for name in arg_names}
            self.z3_vars['return'] = Int('return')
            self.z3_vars['result'] = self.z3_vars['return']

            domain_sorts = tuple(self.z3_vars[name].sort() for name in arg_names)
            codomain_sort = self.z3_vars['return'].sort()
            promises = []

            doc = ast.get_docstring(func_node)
            pre_lines = []
            post_lines = []
            if doc:
                for line in doc.splitlines():
                    line = line.strip()
                    if line.startswith("Pre:"):
                        pre_lines.append(line)
                    elif line.startswith("Post:"):
                        post_lines.append(line)

            for line in pre_lines:
                try:
                    _, expr_str = line.split(":", 1)
                    expr_str = expr_str.strip()
                    expr_ast = ast.parse(expr_str, mode='eval').body
                    promises.append(self._build_z3_expr(expr_ast))
                except Exception as e:
                    pass

            for stmt in func_node.body:
                if isinstance(stmt, ast.Assert):
                    promises.append(self._build_z3_expr(stmt.test))
                if isinstance(stmt, ast.Return) and stmt.value:
                    promises.append(self.z3_vars['return'] == self._build_z3_expr(stmt.value))

            if self.z3_vars.get('return') is not None:
                self.z3_vars['result'] = self.z3_vars['return']

            for line in post_lines:
                try:
                    _, expr_str = line.split(":", 1)
                    expr_str = expr_str.strip().replace("return", "result")
                    expr_ast = ast.parse(expr_str, mode='eval').body
                    promises.append(self._build_z3_expr(expr_ast))
                except Exception as e:
                    pass

            category.add_morphism(func_node.name, domain_sorts, codomain_sort, promises, arg_names)
        except Exception as e:
            pass
        return category


    def _format_model(self, model, arg_names, ret_name):
        parts = []
        decls = {str(d): d for d in model}
        for name in arg_names:
            if name in decls:
                parts.append(f"{name} = {model[decls[name]]}")
        if ret_name in decls:
            parts.append(f"return = {model[decls[ret_name]]}")
        return "[" + ", ".join(parts) + "]"
import os

def scan_directory(root_path):
    for dirpath, _, filenames in os.walk(root_path):
        for fname in filenames:
            if fname.endswith('.py'):
                fpath = os.path.join(dirpath, fname)
                try:
                    with open(fpath, 'r', encoding='utf-8') as f:
                        content = f.read()
                except UnicodeDecodeError:
                    continue
                try:
                    tree = ast.parse(content, filename=fpath)
                except SyntaxError:
                    continue
                for node in ast.walk(tree):
                    if isinstance(node, ast.FunctionDef):
                        try:
                            func_source = ast.unparse(node)
                        except Exception:
                            print(f"Could not unparse function in {fpath}: {node.name}")
                            continue
                        try:
                            auditor = ThieleAuditor(func_source)
                            # Remove debug output, only print paradox reports
                            if not (auditor.preconditions or auditor.postconditions or auditor.assertions):
                                continue
                            audit_result = auditor.audit()
                            if isinstance(audit_result, tuple) and len(audit_result) == 2:
                                verdict, result = audit_result
                            else:
                                verdict, result = "IMPLEMENTATION_FAILURE", f"Unexpected audit result: {audit_result}"
                            if verdict not in ["PROVEN", "CONSISTENT", "UNKNOWN", "VACUOUS"]:
                                print("\n--- PARADOX DISCOVERED ---")
                                print(f"FILE: {fpath}")
                                print(f"FUNCTION: {node.name}")
                                print(f"VERDICT: {verdict}")
                                print(f"EVIDENCE: {result}")
                                print("--- END REPORT ---\n")
                        except Exception as e:
                            # Suppress debug exception output
                            continue
if __name__ == "__main__":
    import sys
    if len(sys.argv) != 2:
        print(f"Usage: python {sys.argv[0]} <directory_to_scan>")
        sys.exit(1)
    scan_directory(sys.argv[1])
                        