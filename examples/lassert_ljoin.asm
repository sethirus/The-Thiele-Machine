# lassert_ljoin.asm
# Demonstrates LASSERT and LJOIN (logic assertion and join instructions).
# LASSERT op_a op_b cost → Assert a logical proposition (no-op in reference VM, charges cost).
# LJOIN   op_a op_b cost → Join two logical contexts (no-op in reference VM, charges cost).
#
# The Coq theorem lassert_ljoin_abstraction_sound proves these are identity
# transformations at the abstraction boundary—observable only via μ decrease.

LOAD_IMM r1 0 0
LOAD_IMM r2 1 0

# Assert that condition (0,0) holds.
LASSERT 0 0 2       # costs 2
# Assert that condition (0,1) holds.
LASSERT 0 1 2       # costs 2

# Join contexts.
LJOIN 0 0 1         # costs 1
LJOIN 0 1 1         # costs 1
LJOIN 1 0 1         # costs 1

# Total μ consumed: 2+2+1+1+1 = 7
HALT 0
