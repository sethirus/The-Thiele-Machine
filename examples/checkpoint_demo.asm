# checkpoint_demo.asm
# Demonstrates CHECKPOINT in the current VM instruction set.
# The numeric checkpoint label is metadata for this run, and the instruction still charges its encoded cost.

LOAD_IMM r1 42 1
CHECKPOINT 0 1
ADD r2 r1 r1 1
CHECKPOINT 1 2
HALT 0
