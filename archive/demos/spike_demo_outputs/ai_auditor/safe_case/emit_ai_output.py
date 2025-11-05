# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import json
data = {"id": "kitten_01", "is_kitten": 0.98, "is_dangerous": 0.01}
print(json.dumps(data, indent=2, sort_keys=True))
