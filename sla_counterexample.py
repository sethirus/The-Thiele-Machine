# Drip #7: Cloud SLAs / Multi-tenancy — SLA Paradox Demonstration
# Self-contained, requires only z3-solver

from z3 import Solver, Int, And, Or, sat, unsat
import hashlib

# Model: Two tenants, shared resource (CPU, 100%)
A_min = 10  # Tenant A guaranteed minimum (%)
B_min = 10  # Tenant B guaranteed minimum (%)
A_burst = 95  # Tenant A burst capacity (%)
B_burst = 95  # Tenant B burst capacity (%)
TOTAL = 100  # Total available resource

# Variables: actual allocation to each tenant
a = Int('a')
b = Int('b')

# SLA promises:
# 1. Each tenant gets at least their minimum
# 2. Each tenant can burst up to their burst cap
# 3. Both can burst simultaneously (worst-case)

s = Solver()
s.add(a >= A_min)
s.add(b >= B_min)
s.add(a <= A_burst)
s.add(b <= B_burst)
s.add(a + b <= TOTAL)
# Both tenants attempt to burst at the same time
s.add(a == A_burst)
s.add(b == B_burst)

verdict = None
witness = None
mubits = len(s.assertions())

res = s.check()
if res == sat:
    verdict = "CONSISTENT"
    m = s.model()
    witness = f"[a = {m[a]}, b = {m[b]}]"
else:
    verdict = "PARADOX"
    witness = "No allocation possible: SLA promises are mutually exclusive."

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