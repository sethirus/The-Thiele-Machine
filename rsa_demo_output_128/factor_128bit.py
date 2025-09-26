
from thielecpu.factoring import recover_factors_partitioned
p, q = recover_factors_partitioned(248865267039480732872314991237239783439)
print(f"Found factors: p={p}, q={q}")
assert p * q == 248865267039480732872314991237239783439
print("Factorization verified")
