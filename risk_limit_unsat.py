# Drip #9: Risk & Finance (VaR/limits) — Risk Limit Unsatisfiability
# Self-contained, requires only z3-solver

from z3 import Solver, Int, And, Or, sat, unsat
import hashlib

# Model: Two assets, portfolio loss limit, tail event (perfect correlation)
A_loss = Int('A_loss')
B_loss = Int('B_loss')
limit = 100  # Maximum allowed portfolio loss

s = Solver()
# Normal regime: assets are uncorrelated (not modeled here, only tail event)
# Tail event: both assets lose together (perfect correlation)
s.add(A_loss == B_loss)
# Both losses are non-negative
s.add(A_loss >= 0)
s.add(B_loss >= 0)
# Portfolio loss is sum of both
portfolio_loss = A_loss + B_loss
# Loss limit promise
s.add(portfolio_loss <= limit)
# Tail event: each asset can lose up to 100
s.add(A_loss <= 100)
s.add(B_loss <= 100)
# Tail event: both assets lose maximum
s.add(A_loss == 100)
s.add(B_loss == 100)

verdict = None
witness = None
mubits = len(s.assertions())

res = s.check()
if res == sat:
    verdict = "CONSISTENT"
    m = s.model()
    witness = f"[A_loss = {m[A_loss]}, B_loss = {m[B_loss]}]"
else:
    verdict = "PARADOX"
    witness = "No allocation possible: loss limit is breached in tail event."

print(f"VERDICT: {verdict}")
print(f"WITNESS: {witness}")
print(f"MUBITS: {mubits}")

# SEAL: hash of source + output
def get_source():
    try:
        with open(__file__, "rb") as f:
            return f.read()
    except Exception:
        return b""

def get_output():
    import io, sys
    buf = io.StringIO()
    sys_stdout = sys.stdout
    sys.stdout = buf
    print(f"VERDICT: {verdict}")
    print(f"WITNESS: {witness}")
    print(f"MUBITS: {mubits}")
    sys.stdout = sys_stdout
    return buf.getvalue().encode()

source_bytes = get_source()
output_bytes = get_output()
seal = hashlib.sha256(source_bytes + output_bytes).hexdigest()
print(f"SEAL: {seal}")