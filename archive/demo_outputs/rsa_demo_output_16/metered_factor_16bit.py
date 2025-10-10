# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.


import math
n = 54707
max_trial = int(math.sqrt(n)) + 1
for i in range(2, max_trial):
    if n % i == 0:
        p, q = i, n // i
        break
else:
    raise ValueError('No factors found')
print(f'Found factors: p={p}, q={q}')
# Set result for VM to detect
__result__ = (p, q)
