# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

from thielecpu.factoring import recover_factors_partitioned

n = 1000000007 * 1000000021  # 64-bit example
p, q = recover_factors_partitioned(n)
print(f"Factored {n} = {p} * {q}")
assert p * q == n
print("Factorization verified")