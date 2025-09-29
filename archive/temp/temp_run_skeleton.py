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