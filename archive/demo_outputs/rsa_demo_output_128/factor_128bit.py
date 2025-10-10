# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.


from thielecpu.factoring import recover_factors_partitioned
p, q = recover_factors_partitioned(326442297374080535972784962453066345011)
print(f"Found factors: p={p}, q={q}")
assert p * q == 326442297374080535972784962453066345011
print("Factorization verified")
