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
