# tensor_multimodule.asm — per-module tensor isolation
#
# Tests that tensor data is isolated per-module:
# Module 1 gets tensor[0][0] = 10
# Module 2 gets tensor[0][0] = 20
# Reading back both should return separate values.
# NOTE: OCaml runner starts pg_next_id=1, so PNEWs create modules 1 and 2.
# Expected: r1 = 10, r2 = 20

FUEL 100

INIT_PT 0 64
INIT_PT 1 64
INIT_ACTIVE_MODULE 0

PNEW {0,64} 1                # creates module 1 (covers mem[0..63])
PNEW {64,128} 1              # creates module 2 (covers mem[64..127])

TENSOR_SET 1 0 0 10 1        # Module 1: tensor[0][0] = 10
TENSOR_SET 2 0 0 20 1        # Module 2: tensor[0][0] = 20

TENSOR_GET r1 1 0 0 1         # Read module 1: should be 10
TENSOR_GET r2 2 0 0 1         # Read module 2: should be 20

HALT 0
