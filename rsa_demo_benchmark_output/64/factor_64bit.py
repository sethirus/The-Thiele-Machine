
from thielecpu.factoring import recover_factors_partitioned
p, q = recover_factors_partitioned(6893895591596109377)
print(f"Found factors: p={p}, q={q}")
assert p * q == 6893895591596109377
print("Factorization verified")
