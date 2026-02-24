# conditional.asm
# JNEZ (jump-if-not-zero) branching demo.
# Counts down from 10 to 0, accumulating the sum 10+9+...+1 in r2.
# Expected: r2 = 55 at HALT.

LOAD_IMM r1 10 1    # counter = 10
LOAD_IMM r2 0 1     # accumulator = 0
LOAD_IMM r3 1 0     # step = 1

LOOP:
ADD r2 r2 r1 1      # acc += counter
SUB r1 r1 r3 1      # counter -= 1
JNEZ r1 LOOP 1      # while counter != 0 → LOOP
HALT 0
