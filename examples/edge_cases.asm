# edge_cases.asm
# Tests boundary register numbers and maximum cost field (255).
# r0  = zero register (alias 'zero') — writes ignored, reads 0
# r31 = stack pointer alias (r31)
# cost = 255 — maximum cost value per instruction
# STORE addr_literal reg cost   (literal address, NOT register)
# LOAD  reg addr_literal cost

LOAD_IMM r0 255 1       # write to r0 (zero reg) – value discarded
LOAD_IMM r31 0 255      # write r31 with max cost
LOAD_IMM r1 255 255     # r1 = 255 with max cost
ADD r2 r1 r1 255        # r2 = r1 + r1 with max cost (wraps in 8-bit range)

# Address boundary: store/load at literal address 255 (max 8-bit addr)
STORE 255 r1 255        # mem[255] = 255 with max cost
LOAD r4 255 255         # r4 = mem[255] = 255 with max cost

# Max-cost PNEW and CHSH_TRIAL
PNEW 0 0 255
CHSH_TRIAL 0 0 255

HALT 0
