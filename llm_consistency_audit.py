# Drip #3: AI / LLM Safety & Eval — Consistency Audit
# Self-contained, requires only z3-solver

from z3 import Solver, String, StringVal, Bool, Or, Not, Implies, sat, unsat
import hashlib

# Policy Axioms
# 1. Never lie
# 2. Never cause harm by stating a hurtful truth

# Scenario: In this context, telling the truth is hurtful (causes harm), but lying is, by definition, a lie.
context = String('context')  # e.g., "Should I tell Alice the painful truth?"
output = String('output')    # "truth" or "lie"

# Boolean variables for Z3
is_truth = Bool('is_truth')
is_lie = Bool('is_lie')
is_hurtful = Bool('is_hurtful')

# Encode scenario: Only two outputs possible, and truth is hurtful
s = Solver()
s.add(Or(output == StringVal("truth"), output == StringVal("lie")))
s.add(is_truth == (output == StringVal("truth")))
s.add(is_lie == (output == StringVal("lie")))
s.add(is_hurtful == (output == StringVal("truth")))  # Truth is hurtful in this context

# Axiom 1: Never lie
s.add(Not(is_lie))

# Axiom 2: Never cause harm by stating a hurtful truth
s.add(Implies(is_truth, Not(is_hurtful)))

# Try to find a consistent output
verdict = s.check()
witness = s.model() if verdict == sat else None

# Prepare output
# Minimal, undeniable output in the style of the first two drips

if verdict == sat and witness is not None:
    print("VERDICT: CONSISTENT")
    w = []
    for d in witness.decls():
        w.append(f"{d.name()} = {witness[d]}")
    print(f"WITNESS: [{', '.join(w)}]")
else:
    print("VERDICT: PARADOX")
    print("WITNESS: No model exists; the system is self-contradictory.")

# MUBITS: number of axioms checked (2)
print("MUBITS: 2")

# SEAL: Hash of source + output
def get_output():
    import io, sys
    buf = io.StringIO()
    sys_stdout = sys.stdout
    sys.stdout = buf
    res2 = s.check()
    if res2 == sat:
        model = s.model()
        print("VERDICT: CONSISTENT")
        print("WITNESS: [" + ", ".join(f"{d.name()} = {model[d]}" for d in model.decls()) + "]")
    elif res2 == unsat:
        print("VERDICT: PARADOX")
        print("WITNESS: No model exists; the system is self-contradictory.")
    else:
        print("VERDICT: UNKNOWN")
        print(f"WITNESS: reason={s.reason_unknown()}")
    print(f"MUBITS: {len(s.assertions())}")
    sys.stdout = sys_stdout
    return buf.getvalue().encode()

try:
    with open(__file__, "rb") as f:
        source_bytes = f.read()
except Exception:
    source_bytes = b""

output_bytes = get_output()
seal = hashlib.sha256(source_bytes + output_bytes).hexdigest()
print(f"SEAL: {seal}")