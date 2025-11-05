# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/bin/sh
set -e
python - <<'PY'
from pathlib import Path
from thielecpu.assemble import parse
from thielecpu.state import State
from thielecpu.vm import VM

prog_path = Path("examples/demo.thl")
with prog_path.open() as fh:
    program = parse(fh, prog_path.parent)

vm = VM(State())
vm.run(program, Path("out/demo"))
PY
