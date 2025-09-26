
from thielecpu.factoring import recover_factors_partitioned
p, q = recover_factors_partitioned(223450998221882392322455807218345037669)
print(f"Found factors: p={p}, q={q}")
assert p * q == 223450998221882392322455807218345037669
print("Factorization verified")
