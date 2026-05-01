# tensor_metric.asm — set up diagonal metric for Einstein equation
#
# Sets up an isotropic diagonal metric g_{mu,nu} = 5 * delta_{mu,nu}
# on module 1. This is the simplest non-trivial metric configuration.
# NOTE: OCaml runner starts pg_next_id=1, so first PNEW creates module 1.
# Expected: r1 = 5 (g_00), r2 = 5 (g_11), r3 = 5 (g_22), r4 = 5 (g_33)
#           r5 = 0 (off-diagonal g_01 should be 0)

FUEL 100

INIT_PT 0 128
INIT_ACTIVE_MODULE 0

PNEW {0,128} 1               # creates module 1

# Set diagonal metric entries
TENSOR_SET 1 0 0 5 1          # g_00 = 5
TENSOR_SET 1 1 1 5 1          # g_11 = 5
TENSOR_SET 1 2 2 5 1          # g_22 = 5
TENSOR_SET 1 3 3 5 1          # g_33 = 5
# Off-diagonal entries default to 0 -> isotropic diagonal metric

# Read back to verify
TENSOR_GET r1 1 0 0 1          # r1 = g_00 = 5
TENSOR_GET r2 1 1 1 1          # r2 = g_11 = 5
TENSOR_GET r3 1 2 2 1          # r3 = g_22 = 5
TENSOR_GET r4 1 3 3 1          # r4 = g_33 = 5
TENSOR_GET r5 1 0 1 1          # r5 = g_01 = 0 (off-diagonal)

HALT 0
