import random
from pysat.formula import CNF

def generate_pigeonhole_cnf(n):
    """
    Generate CNF for pigeonhole principle: n holes, n+1 pigeons.
    This is unsatisfiable by pigeonhole principle.
    """
    cnf = CNF()
    pigeons = n + 1
    holes = n

    # Each pigeon in at least one hole
    for p in range(pigeons):
        clause = []
        for h in range(holes):
            var = p * holes + h + 1  # Variables: p_h
            clause.append(var)
        cnf.append(clause)

    # No two pigeons in same hole
    for h in range(holes):
        for p1 in range(pigeons):
            for p2 in range(p1 + 1, pigeons):
                cnf.append([- (p1 * holes + h + 1), - (p2 * holes + h + 1)])

    # At most one pigeon per hole (optional, but helps)
    for h in range(holes):
        for p1 in range(pigeons):
            for p2 in range(p1 + 1, pigeons):
                cnf.append([- (p1 * holes + h + 1), - (p2 * holes + h + 1)])

    return cnf

if __name__ == "__main__":
    n = 5
    cnf = generate_pigeonhole_cnf(n)
    print(f"Pigeonhole CNF for n={n}: {len(cnf.clauses)} clauses")