# Drip #8: Zero-Trust / Security Policy — Policy Consistency Probe
# Self-contained, requires only z3-solver

from z3 import Solver, String, Bool, And, Or, Not, sat, unsat
import hashlib

# Variables
user_role = String('user_role')
data_sensitivity = String('data_sensitivity')
allow = Bool('allow')
deny = Bool('deny')

# Policy rules:
# 1. Allow if user_role == 'admin'
# 2. Deny if data_sensitivity == 'top_secret'

s = Solver()
s.add(Or(user_role == "admin", user_role == "user"))
s.add(Or(data_sensitivity == "top_secret", data_sensitivity == "public"))

# Rule 1
s.add(allow == (user_role == "admin"))
# Rule 2
s.add(deny == (data_sensitivity == "top_secret"))

# Scenario: admin requests top_secret data
s.add(user_role == "admin")
s.add(data_sensitivity == "top_secret")

# Contradiction: can both allow and deny be true?
s.add(allow)
s.add(deny)

verdict = None
witness = None
mubits = len(s.assertions())

res = s.check()
if res == sat:
    verdict = "PARADOX"
    m = s.model()
    witness = f"[user_role = {m[user_role]}, data_sensitivity = {m[data_sensitivity]}, allow = {m[allow]}, deny = {m[deny]}]"
else:
    verdict = "CONSISTENT"
    witness = "No model exists; policy is consistent in this scenario."

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