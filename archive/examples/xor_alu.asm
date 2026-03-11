# xor_alu.asm
# Exercises all four XOR-family instructions.
# XOR_LOAD  r_dst  addr_literal  cost  → r_dst ^= mem[addr]
# XOR_ADD   r_dst  r_src         cost  → r_dst ^= r_src
# XOR_SWAP  r_a    r_b           cost  → swap r_a and r_b
# XOR_RANK  r_dst  r_src         cost  → r_dst = popcount(r_src)
# Note: STORE addr_literal reg cost  (address comes first as a literal)

LOAD_IMM r1 0xAA 1  # r1 = 0b10101010 = 170
LOAD_IMM r2 0x55 1  # r2 = 0b01010101 = 85
LOAD_IMM r3 0xFF 1  # r3 = 0xFF = 255

# Store 0xFF at literal address 0
STORE 0 r3 1        # mem[0] = 255

# XOR_LOAD: r5 starts 0, XORs with mem[0]=255 → r5 = 255
LOAD_IMM r5 0 1
XOR_LOAD r5 0 1     # r5 = 0 XOR mem[0] = 0 XOR 255 = 255

# XOR_ADD: r6 = 0 XOR r2 (85) → r6 = 85
LOAD_IMM r6 0 1
XOR_ADD r6 r2 1     # r6 = 0 XOR 85 = 85

# XOR_SWAP r1 and r2 (170 ↔ 85)
XOR_SWAP r1 r2 1    # r1 = 85, r2 = 170

# XOR_RANK: popcount of r1 (now 85 = 0b01010101) = 4
XOR_RANK r8 r1 1    # r8 = popcount(85) = 4

HALT 0
