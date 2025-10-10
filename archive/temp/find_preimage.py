# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import hashlib
import itertools

chars = 'abcdefghijklmnopqrstuvwxyz0123456789'
for combo in itertools.product(chars, repeat=4):
    secret = ''.join(combo)
    h = hashlib.sha256(secret.encode('utf-8')).hexdigest()
    if h.startswith('00'):
        print(f"Found: {secret} -> {h}")
        break