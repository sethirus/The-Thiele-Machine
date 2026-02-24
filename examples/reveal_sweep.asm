# reveal_sweep.asm
# REVEALs all 16 mu_tensor entries (indices 0-15) with cost=1 each.
# After this program: each tensor[i] += 1, mu >= 16.

REVEAL 0  0 1       # tensor[0] += 1
REVEAL 1  0 1       # tensor[1] += 1
REVEAL 2  0 1       # tensor[2] += 1
REVEAL 3  0 1       # tensor[3] += 1
REVEAL 4  0 1       # tensor[4] += 1
REVEAL 5  0 1       # tensor[5] += 1
REVEAL 6  0 1       # tensor[6] += 1
REVEAL 7  0 1       # tensor[7] += 1
REVEAL 8  0 1       # tensor[8] += 1
REVEAL 9  0 1       # tensor[9] += 1
REVEAL 10 0 1       # tensor[10] += 1
REVEAL 11 0 1       # tensor[11] += 1
REVEAL 12 0 1       # tensor[12] += 1
REVEAL 13 0 1       # tensor[13] += 1
REVEAL 14 0 1       # tensor[14] += 1
REVEAL 15 0 1       # tensor[15] += 1
HALT 0
