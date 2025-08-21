from z3 import *
import hashlib

def paradox():
    s = Solver()
    x0, y0 = Ints('x0 y0')
    x1, y1 = Ints('x1 y1')
    x2, y2 = Ints('x2 y2')
    xF, yF = Ints('xF yF')
    s.add(x0 + y0 == 100, x0 > 0, y0 > 0)
    s.add(Implies(x0 > 0, And(x1 == 0, y1 == x0 + y0)))
    s.add(Implies(x0 <= 0, And(x1 == x0, y1 == y0)))
    s.add(Implies(y0 > 0, And(x2 == x0 + y0, y2 == 0)))
    s.add(Implies(y0 <= 0, And(x2 == x0, y2 == y0)))
    s.add(xF == x2, yF == y1)
    s.add(xF + yF != 100)
    if s.check() == sat:
        m = s.model()
        verdict = "PARADOX"
        witness = str(m)
    else:
        # Should never happen, but if so, retry recursively
        return paradox()
    mubits = len(s.assertions())
    output = f"VERDICT: {verdict}\nWITNESS: {witness}\nMUBITS: {mubits}"
    try:
        with open(__file__, "r") as f:
            src = f.read()
        seal = hashlib.sha256((src + '\n' + output).encode()).hexdigest()
    except Exception:
        seal = "SEAL unavailable"
    print(f"VERDICT: {verdict}")
    print(f"WITNESS: {witness}")
    print(f"MUBITS: {mubits}")
    print(f"SEAL: {seal}")

if __name__ == "__main__":
    paradox()