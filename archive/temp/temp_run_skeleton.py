# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

from thielecpu.assemble import parse
from thielecpu.vm import VM
from thielecpu.state import State
from pathlib import Path

with open('examples/run_skeleton_key.thm', 'r') as f:
    lines = f.readlines()
program = parse(lines, Path('examples'))
vm = VM(State())
vm.run(program, Path('examples/skeleton_output'))

# Print the trace to terminal
trace_file = Path('examples/skeleton_output/trace.log')
if trace_file.exists():
    print("VM Execution Trace:")
    print(trace_file.read_text())
else:
    print("Trace file not found.")