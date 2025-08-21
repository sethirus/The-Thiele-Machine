# Drip #10: Legal Contracts / Governance — Contract Clauses Paradox
# Self-contained, requires only z3-solver

from z3 import Solver, String, And, Or, Not, sat, unsat
import hashlib

# Variables
jurisdiction = String('jurisdiction')
arbitration_location = String('arbitration_location')
dispute = String('dispute')

# Clause 1: All disputes must be resolved by arbitration in California.
# Clause 2: This contract is governed exclusively by the laws of New York.

s = Solver()
# Only two possible values for each
s.add(Or(jurisdiction == "New York", jurisdiction == "California"))
s.add(Or(arbitration_location == "California", arbitration_location == "New York"))
s.add(dispute == "active")

# Clause 1: Arbitration must be in California if there is a dispute
s.add(Or(dispute != "active", arbitration_location == "California"))
# Clause 2: Jurisdiction must be New York if there is a dispute
s.add(Or(dispute != "active", jurisdiction == "New York"))

# Contradiction: Can both clauses be satisfied if arbitration is in California but jurisdiction is New York?
# But what if California law does not allow arbitration for NY-governed contracts, or vice versa?
# For this paradox, require that arbitration_location == jurisdiction for enforceability.
s.add(arbitration_location == jurisdiction)

verdict = None
witness = None
mubits = len(s.assertions())

res = s.check()
if res == sat:
    verdict = "CONSISTENT"
    m = s.model()
    witness = f"[jurisdiction = {m[jurisdiction]}, arbitration_location = {m[arbitration_location]}, dispute = {m[dispute]}]"
else:
    verdict = "PARADOX"
    witness = "No model exists; jurisdiction and arbitration clauses are mutually exclusive."

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