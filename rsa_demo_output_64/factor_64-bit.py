
from thielecpu.factoring import recover_factors_partitioned
p, q = recover_factors_partitioned(1000000028000000147)
print(f"Found factors: p={p}, q={q}")
assert p * q == 1000000028000000147
print("Factorization verified")
