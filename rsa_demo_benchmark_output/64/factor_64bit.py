
from thielecpu.factoring import recover_factors_partitioned
p, q = recover_factors_partitioned(5756591084852148031)
print(f"Found factors: p={p}, q={q}")
assert p * q == 5756591084852148031
print("Factorization verified")
