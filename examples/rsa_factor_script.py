from thielecpu.factoring import recover_factors_partitioned

n = 1000000007 * 1000000021  # 64-bit example
p, q = recover_factors_partitioned(n)
print(f"Factored {n} = {p} * {q}")
assert p * q == n
print("Factorization verified")