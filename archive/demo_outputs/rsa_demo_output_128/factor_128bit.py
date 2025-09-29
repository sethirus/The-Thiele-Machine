
from thielecpu.factoring import recover_factors_partitioned
p, q = recover_factors_partitioned(326442297374080535972784962453066345011)
print(f"Found factors: p={p}, q={q}")
assert p * q == 326442297374080535972784962453066345011
print("Factorization verified")
