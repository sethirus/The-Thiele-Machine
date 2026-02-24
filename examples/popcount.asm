# popcount.asm
# Computes Hamming weight (popcount) of several values using XOR_RANK.
# Results stored in registers:
#   XOR_RANK r_dst r_src cost → r_dst = popcount(r_src)
# Test values and expected popcounts:
#   0x00 = 0   → 0 bits
#   0xFF = 255 → 8 bits
#   0x0F = 15  → 4 bits
#   0xAA = 170 → 4 bits (0b10101010)
#   0x01 = 1   → 1 bit

LOAD_IMM r0 0x00 1
LOAD_IMM r1 0xFF 1
LOAD_IMM r2 0x0F 1
LOAD_IMM r3 0xAA 1
LOAD_IMM r4 0x01 1

XOR_RANK r10 r0 1   # r10 = popcount(0x00) = 0
XOR_RANK r11 r1 1   # r11 = popcount(0xFF) = 8
XOR_RANK r12 r2 1   # r12 = popcount(0x0F) = 4
XOR_RANK r13 r3 1   # r13 = popcount(0xAA) = 4
XOR_RANK r14 r4 1   # r14 = popcount(0x01) = 1

HALT 0
