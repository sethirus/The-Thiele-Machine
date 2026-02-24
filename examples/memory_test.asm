# memory_test.asm
# Exercises STORE and LOAD with literal addresses.
# Writes distinct values to several memory locations, then reads them back.
# Verifies correctness by XOR-folding reads: any mismatch would leave r9 != 0.
#
# LOAD  reg  addr_literal cost
# STORE addr_literal reg cost

LOAD_IMM r1 0xAA 1  # pattern A = 0xAA
LOAD_IMM r2 0x55 1  # pattern B = 0x55
LOAD_IMM r3 0xFF 1  # pattern C = 0xFF

# Write to addresses 0, 1, 2, 10, 255
STORE 0 r1 1        # mem[0]   = 0xAA
STORE 1 r2 1        # mem[1]   = 0x55
STORE 2 r3 1        # mem[2]   = 0xFF
STORE 10 r1 1       # mem[10]  = 0xAA
STORE 255 r2 1      # mem[255] = 0x55

# Read back
LOAD r4 0 1         # r4 = mem[0]   = 0xAA
LOAD r5 1 1         # r5 = mem[1]   = 0x55
LOAD r6 2 1         # r6 = mem[2]   = 0xFF
LOAD r7 10 1        # r7 = mem[10]  = 0xAA
LOAD r8 255 1       # r8 = mem[255] = 0x55

# XOR-fold reads back against written values; r9 should stay 0
XOR_LOAD r9 0 1     # r9 ^= mem[0]
XOR_LOAD r9 1 1     # r9 ^= mem[1]
XOR_LOAD r9 2 1     # r9 ^= mem[2]

HALT 0
