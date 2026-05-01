# hello_world.asm — Simplest Thiele Machine program
#
# Creates a partition, loads two values, adds them, stores the result, halts.
# The Thiele Machine requires a partition before memory operations.
# Expected: r1=42, r2=58, r3=100, r5=0, mem[0]=100, halted=1, err=0

# Partition setup (portable: works on both OCaml runner and RTL cosim)
INIT_PT 0 128                 # RTL: set ptTable[0] = 128 (mem region size)
INIT_ACTIVE_MODULE 0          # RTL: set active_module = 0
PNEW {0,128} 1               # Coq/OCaml: create partition covering mem[0..127]
LOAD_IMM r1 42 1              # r1 = 42
LOAD_IMM r2 58 1              # r2 = 58
ADD r3 r1 r2 1                # r3 = 100
LOAD_IMM r5 0 0              # r5 = address 0
STORE r5 r3 1                # mem[r5] = r3 = 100
HALT 0
