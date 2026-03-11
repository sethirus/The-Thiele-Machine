# mu_demo.asm
# Demonstrates that mu monotonically increases.
# Every instruction has a cost >= 0, so mu never decreases.
# mu increases by cost each instruction.

LOAD_IMM r0 0 1     # cost=1: mu += 1
LOAD_IMM r1 0 2     # cost=2: mu += 2
LOAD_IMM r2 0 3     # cost=3: mu += 3
ADD r3 r0 r1 5      # cost=5: mu += 5
ADD r4 r2 r3 10     # cost=10: mu += 10
# mu is now at least 1+2+3+5+10 = 21
# Zero-cost instructions also permitted
LOAD_IMM r5 255 0   # cost=0: mu unchanged
HALT 0
