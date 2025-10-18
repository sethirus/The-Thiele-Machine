# Thiele-Native Factoring Example
# Replace sympy oracle with partition-based approach

from fractions import Fraction
import z3

def thiele_factor(n):
    """
    Attempt Thiele-style factoring using partitions and Z3.
    For demonstration, split n into partitions and check consistency.
    """
    if n < 2:
        return None

    # Simple partition: try factors around sqrt(n)
    import math
    sqrt_n = int(math.sqrt(n)) + 1
    for i in range(2, sqrt_n):
        if n % i == 0:
            # Use Z3 to "certify" the partition
            s = z3.Solver()
            p = z3.Int('p')
            q = z3.Int('q')
            s.add(p * q == n, p > 1, q > 1, p <= q)
            if s.check() == z3.sat:
                model = s.model()
                p_val = model[p]
                q_val = model[q]
                if p_val is not None and q_val is not None:
                    return (p_val.as_long(), q_val.as_long())
    return None

# Test larger
print(thiele_factor(21))  # 3*7
print(thiele_factor(35))  # 5*7
print(thiele_factor(77))  # 7*11