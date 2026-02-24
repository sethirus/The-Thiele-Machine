# mdl_acc.asm
# Demonstrates MDLACC (Minimum Description Length Accumulator).
# MDLACC op_a op_b cost
#   → Accumulates description-length evidence for op_a against oracle op_b.
#   → Each call charges cost against μ.
# This demo runs MDLACC five times with increasing costs, then halts.
# Useful for verifying that μ strictly decreases with each call.

LOAD_IMM r1 5 1     # loop counter
LOAD_IMM r2 1 0     # decrement step

LOOP:
MDLACC 0 1 1        # MDL accumulate (cost=1)
SUB r1 r1 r2 1      # counter -= 1
JNEZ r1 LOOP 1      # repeat until counter == 0

# Five MDLACC calls total; each consumed 1 unit of μ.
HALT 0
