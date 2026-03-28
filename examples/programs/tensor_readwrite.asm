# tensor_readwrite.asm — basic per-module tensor read/write
#
# Tests TENSOR_SET and TENSOR_GET on a single module.
# NOTE: OCaml runner starts pg_next_id=1, so first PNEW creates module ID 1.
# Expected: r1 = 42, r2 = 99

FUEL 100

INIT_PT 0 256
INIT_ACTIVE_MODULE 0

PNEW {0,256} 1               # creates module 1

TENSOR_SET 1 0 0 42 1        # Set module 1 tensor[0][0] = 42, cost 1
TENSOR_GET r1 1 0 0 1         # Read module 1 tensor[0][0] into r1, cost 1
# r1 should be 42

TENSOR_SET 1 1 2 99 1        # Set module 1 tensor[1][2] = 99, cost 1
TENSOR_GET r2 1 1 2 1         # Read module 1 tensor[1][2] into r2, cost 1
# r2 should be 99

HALT 0
