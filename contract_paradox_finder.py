from z3 import Solver, BitVec, BitVecVal, BV2Int, UGT, UGE, sat, unsat

UINT_BITS = 8
TOTAL = 1

# BV (implementation state)
total_supply_bv     = BitVec('total_supply_bv', UINT_BITS)
sender_balance_bv   = BitVec('sender_balance_bv', UINT_BITS)
receiver_balance_bv = BitVec('receiver_balance_bv', UINT_BITS)
amount_bv           = BitVec('amount_bv', UINT_BITS)

# Integer (spec view of the same state)
total_supply = BV2Int(total_supply_bv)
sender_i     = BV2Int(sender_balance_bv)
receiver_i   = BV2Int(receiver_balance_bv)
amount_i     = BV2Int(amount_bv)

def transfer(sender_bv, receiver_bv, amount_bv):
    # implementation arithmetic in uint8 (wraps)
    return (sender_bv - amount_bv, receiver_bv + amount_bv)

s = Solver()

# Spec promises (in ℤ): total supply is constant and equals sum of balances
s.add(total_supply_bv == BitVecVal(TOTAL, UINT_BITS))
s.add(total_supply == sender_i + receiver_i)

# Pre-conditions (unsigned)
s.add(UGT(amount_bv, BitVecVal(0, UINT_BITS)))
# s.add(UGE(sender_balance_bv, amount_bv))  # Allow underflow to expose bug

# Execute transfer in implementation space
new_sender_bv, new_receiver_bv = transfer(sender_balance_bv, receiver_balance_bv, amount_bv)
new_sender_i   = BV2Int(new_sender_bv)
new_receiver_i = BV2Int(new_receiver_bv)

# Postcondition we expect by spec (in ℤ): conservation should still hold
# Ask for a COUNTEREXAMPLE: after impl step, spec conservation fails
s.add(total_supply != new_sender_i + new_receiver_i)

res = s.check()
if res == sat:
    m = s.model()
    decls = sorted(m.decls(), key=lambda d: d.name())
    w = ", ".join(f"{d.name()} = {m[d]}" for d in decls)
    print("VERDICT: PARADOX")
    print(f"WITNESS: [{w}]")
elif res == unsat:
    print("VERDICT: CONSISTENT")
    print("WITNESS: No model exists; the system is consistent.")
else:
    print("VERDICT: UNKNOWN")
    print(f"WITNESS: reason={s.reason_unknown()}")

print(f"MUBITS: {len(s.assertions())}")

import hashlib
import io
import sys

def get_output():
    buf = io.StringIO()
    sys_stdout = sys.stdout
    sys.stdout = buf
    res2 = s.check()
    if res2 == sat:
        m2 = s.model()
        decls2 = sorted(m2.decls(), key=lambda d: d.name())
        w2 = ", ".join(f"{d.name()} = {m2[d]}" for d in decls2)
        print("VERDICT: PARADOX")
        print(f"WITNESS: [{w2}]")
    elif res2 == unsat:
        print("VERDICT: CONSISTENT")
        print("WITNESS: No model exists; the system is consistent.")
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