# edge_cases.asm
# Tests boundary register numbers and maximum cost field (255).
# r0  = zero register (alias 'zero') — writes ignored, reads 0
# r15 = stack pointer alias (sp)
# cost = 255 — maximum cost value per instruction
# STORE addr_literal reg cost   (literal address, NOT register)
# LOAD  reg addr_literal cost

LOAD_IMM r0 255 1       # write to r0 (zero reg) – value discarded
LOAD_IMM r15 0 255      # write r15 (SP) with max cost
LOAD_IMM r1 255 255     # r1 = 255 with max cost
ADD r2 r1 r1 255        # r2 = r1 + r1 with max cost (wraps in 8-bit range)

# Address boundary: store/load at literal address 127 (max 7-bit addr, MEM_SIZE=128)
STORE 127 r1 255        # mem[127] = 255 with max cost
LOAD r4 127 255         # r4 = mem[127] = 255 with max cost

# Max-cost PNEW and CHSH_TRIAL
PNEW 0 0 255
CHSH_TRIAL 0 0 255

HALT 0
