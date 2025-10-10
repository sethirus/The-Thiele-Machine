# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.


from thielecpu.factoring import recover_factors_partitioned
p, q = recover_factors_partitioned(202611590541171704913272606411235233791)
print(f"Found factors: p={p}, q={q}")
assert p * q == 202611590541171704913272606411235233791
print("Factorization verified")
