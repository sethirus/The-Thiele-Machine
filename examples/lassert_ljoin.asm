# lassert_ljoin.asm
# Demonstrates the current canonical LASSERT form followed by LJOIN.
# The formula is the one-variable SAT witness used by the VM's on-chip checker.
# The first witness satisfies x₁, and the second witness falsifies x₁.

LOAD_IMM r1 0 0
LOAD_IMM r2 1 0

# Formula header and one literal for x₁.
INIT_MEM 16 2
INIT_MEM 17 1
INIT_MEM 18 1
INIT_MEM 19 1
INIT_MEM 20 0

# Satisfying witness and countermodel.
INIT_MEM 81 1
INIT_MEM 82 0
LOAD_IMM r13 16 0
LOAD_IMM r14 80 0
LASSERT r13 r14 1 2 2

# Join contexts. LJOIN charges its encoded cost plus one.
LJOIN 0 0 1         # costs 2
LJOIN 0 1 1         # costs 2
LJOIN 1 0 1         # costs 2

# LASSERT charges flen*8 + cost + 1 = 2*8 + 2 + 1 = 19. Total: 19 + 3*2 = 25.
HALT 0
