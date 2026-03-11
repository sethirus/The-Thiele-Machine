# fibonacci.asm
# Compute the first 8 Fibonacci numbers and store them in memory[0..7].
# LOAD/STORE take literal addresses (not registers), so addresses are inlined.
# F: 0, 1, 1, 2, 3, 5, 8, 13
# r1 = F(n-2), r2 = F(n-1), r3 = F(n)

LOAD_IMM r1 0 1     # F(0) = 0
LOAD_IMM r2 1 1     # F(1) = 1

STORE 0 r1 1        # mem[0] = 0
STORE 1 r2 1        # mem[1] = 1

ADD r3 r1 r2 1      # F(2) = 0+1 = 1
STORE 2 r3 1
XFER r1 r2 1        # r1 = 1
XFER r2 r3 1        # r2 = 1

ADD r3 r1 r2 1      # F(3) = 1+1 = 2
STORE 3 r3 1
XFER r1 r2 1        # r1 = 1
XFER r2 r3 1        # r2 = 2

ADD r3 r1 r2 1      # F(4) = 1+2 = 3
STORE 4 r3 1
XFER r1 r2 1        # r1 = 2
XFER r2 r3 1        # r2 = 3

ADD r3 r1 r2 1      # F(5) = 2+3 = 5
STORE 5 r3 1
XFER r1 r2 1        # r1 = 3
XFER r2 r3 1        # r2 = 5

ADD r3 r1 r2 1      # F(6) = 3+5 = 8
STORE 6 r3 1
XFER r1 r2 1        # r1 = 5
XFER r2 r3 1        # r2 = 8

ADD r3 r1 r2 1      # F(7) = 5+8 = 13
STORE 7 r3 1

HALT 0
