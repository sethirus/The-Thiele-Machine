# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env bash
set -euo pipefail
echo "Checking all Coq proofs via make..."
(cd coq/ && /usr/bin/coq_makefile -f _CoqProject -o Makefile && make)
