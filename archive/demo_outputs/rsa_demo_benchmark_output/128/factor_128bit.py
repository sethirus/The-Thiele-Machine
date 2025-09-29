
from thielecpu.factoring import recover_factors_partitioned
p, q = recover_factors_partitioned(202611590541171704913272606411235233791)
print(f"Found factors: p={p}, q={q}")
assert p * q == 202611590541171704913272606411235233791
print("Factorization verified")
