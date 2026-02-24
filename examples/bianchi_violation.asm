# bianchi_violation.asm
# Triggers Bianchi conservation violation by REVEAL-ing more than mu.
# The hardware halts automatically when tensor_sum > mu.
# After violation: halted=1, error_code=1.

# Start with mu = 5 from these instructions
LOAD_IMM r0 1 1     # mu += 1
LOAD_IMM r1 2 1     # mu += 1
LOAD_IMM r2 3 1     # mu += 1
LOAD_IMM r3 4 1     # mu += 1
LOAD_IMM r4 5 1     # mu += 1
# mu = 5

# REVEAL tensor[0] += 200 -- MUCH more than mu=5 -- triggers violation
REVEAL 0 0 200      # tensor[0] += 200; Bianchi check fires
# Hardware halts here, following instruction never executes
LOAD_IMM r0 99 0    # unreachable
HALT 0
