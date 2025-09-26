
from thielecpu.factoring import recover_factors_partitioned
p, q = recover_factors_partitioned(8776682443826269559)
print(f"Found factors: p={p}, q={q}")
assert p * q == 8776682443826269559
print("Factorization verified")
