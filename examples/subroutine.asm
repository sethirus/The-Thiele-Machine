# subroutine.asm
# Demonstrates CALL/RET via a simple multiply-by-2 subroutine.
# r1 = input value, r2 = result (= 2 * r1).
# SP (r31) starts at 255 (initial stack pointer).

LOAD_IMM sp 255 1   # SP = 255 (stack pointer)
LOAD_IMM r1 7 1     # r1 = 7 (argument)
CALL DOUBLE 1       # call DOUBLE; return addr saved at mem[SP]
# r2 now holds 2*7 = 14
HALT 0

DOUBLE:
ADD r2 r1 r1 1       # r2 = r1 + r1 = 2*r1
RET 1               # return to caller
