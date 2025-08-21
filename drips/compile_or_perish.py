import ast
import hashlib
from z3 import Solver, Int, And

def extract_spec_and_constraints(source):
    tree = ast.parse(source)
    func_node = next(n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef))
    doc = ast.get_docstring(func_node)
    pre, post = [], []
    if doc:
        for line in doc.splitlines():
            line = line.strip()
            if line.startswith("Pre:"):
                pre.append(line.split(":",1)[1].strip())
            elif line.startswith("Post:"):
                post.append(line.split(":",1)[1].strip())
    arg_names = [a.arg for a in func_node.args.args]
    z3_vars = {name: Int(name) for name in arg_names}
    z3_vars['return'] = Int('return')
    constraints = []
    for p in pre:
        constraints.append(eval(p, {}, z3_vars))
    for stmt in func_node.body:
        if isinstance(stmt, ast.Assert):
            constraints.append(eval(compile(ast.Expression(stmt.test), "", "eval"), {}, z3_vars))
        if isinstance(stmt, ast.Return) and stmt.value:
            constraints.append(z3_vars['return'] == eval(compile(ast.Expression(stmt.value), "", "eval"), {}, z3_vars))
    for p in post:
        import re
        def _rewrite_return(expr: str) -> str:
            return re.sub(r'\breturn\b', "z3_vars['return']", expr)
        constraints.append(eval(_rewrite_return(p), {}, {"z3_vars":z3_vars, **z3_vars}))
    return func_node, constraints, z3_vars

def audit(source):
    func_node, constraints, z3_vars = extract_spec_and_constraints(source)
    solver = Solver()
    solver.add(And(*constraints))
    verdict = None
    witness = None
    import math
    mdl_gap = 0
    r = solver.check()
    if str(r) == "sat":
        verdict = "CONSISTENT"
        model = solver.model()
        assignments = []
        mdl_bits = 0
        for v in z3_vars:
            val = model.eval(z3_vars[v], model_completion=True)
            assignments.append(f"{v} = {val}")
            try:
                intval = int(str(val))
                bits = 1 if intval == 0 else math.ceil(math.log2(abs(intval)+1)) + 1  # +1 for sign
            except Exception:
                bits = 1
            mdl_bits += bits
        witness = "[" + ", ".join(assignments) + "]"
    elif str(r) == "unsat":
        verdict = "PARADOX"
        witness = "No model exists; the system is self-contradictory."
        mdl_bits = 1  # minimal bit to encode contradiction
    else:
        verdict = "UNKNOWN"
        witness = f"reason: {solver.reason_unknown()}"
        mdl_bits = 0
    # Compose output for SEAL, now including source for tamper-evidence
    output_block = f"VERDICT: {verdict}\nWITNESS: {witness}\nMDL_BITS: {mdl_bits}\nMDL_GAP: {mdl_gap}"
    seal_input = (source + "\n" + output_block).encode()
    seal = hashlib.sha256(seal_input).hexdigest()
    return func_node, constraints, verdict, witness, mdl_bits, mdl_gap, seal

def print_audit(source, label):
    func_node, constraints, verdict, witness, mdl_bits, mdl_gap, seal = audit(source)
    print(f"--- AUDIT: {label} ---")
    try:
        print(ast.unparse(func_node))
    except Exception:
        import inspect
        print(source.strip())
    print("Extracted Constraints:")
    for c in constraints:
        print("  ", c)
    print(f"VERDICT: {verdict}")
    print(f"WITNESS: {witness}")
    # Show MDL_BITS calculation details
    if verdict == "CONSISTENT":
        print("MDL_BITS calculation:")
        model = {}
        for assign in witness.strip("[]").split(", "):
            if assign:
                v, val = assign.split(" = ")
                model[v] = int(val)
        import math
        for v, val in model.items():
            bits = 1 if val == 0 else math.ceil(math.log2(abs(val)+1)) + 1
            print(f"  {v}: value={val}, bits={bits}")
    else:
        print("MDL_BITS calculation: 1 (minimal bit to encode contradiction)")
    print(f"MUBITS: {mdl_bits}")
    print(f"MDL_BITS: {mdl_bits}")
    print(f"MDL_GAP: {mdl_gap}")
    print("SEAL input block:")
    print(f"VERDICT: {verdict}\nWITNESS: {witness}\nMDL_BITS: {mdl_bits}\nMDL_GAP: {mdl_gap}")
    print(f"SEAL: {seal}")
    print()

if __name__ == "__main__":
    # Satisfiable function
    SAFE_FN = '''
def safe_add(x: int, y: int) -> int:
    """
    Pre: x >= 0
    Pre: y >= 0
    Post: return >= 0
    """
    assert x >= 0
    assert y >= 0
    return x + y
    '''
    # Contradictory function
    BUGGY_FN = '''
def buggy_add(x: int, y: int) -> int:
    """
    Pre: x == 0
    Pre: y == 0
    Post: return == 1
    """
    assert x == 0
    assert y == 0
    return x + y
    '''
    print_audit(SAFE_FN, "Safe Add Function")
    print_audit(BUGGY_FN, "Buggy Add Function")