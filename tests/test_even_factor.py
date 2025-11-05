# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from thielecpu.factoring import recover_factors_partitioned

# Test even semiprime: 15 * 2 = 30
n_even = 30
p, q = recover_factors_partitioned(n_even)
print(f"For n={n_even}, factors: p={p}, q={q}")
print(f"Verification: {p * q == n_even}")

# Another test: 21 * 2 = 42
n_even2 = 42
p2, q2 = recover_factors_partitioned(n_even2)
print(f"For n={n_even2}, factors: p={p2}, q={q2}")
print(f"Verification: {p2 * q2 == n_even2}")