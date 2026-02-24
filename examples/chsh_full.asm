# chsh_full.asm
# Complete CHSH inequality test.
# Runs all 4 (x,a) measurement-setting combinations.
# RTL semantics: op_a = x ∈ {0,1}, op_b = a ∈ {0,1}, cost ≥ 1.
# Any op_a or op_b > 1 is invalid and sets the error flag.

CHSH_TRIAL 0 0 1    # x=0, a=0 — quantum measurement settings
CHSH_TRIAL 0 1 1    # x=0, a=1
CHSH_TRIAL 1 0 1    # x=1, a=0
CHSH_TRIAL 1 1 1    # x=1, a=1

# 4 trials × cost=1 each → mu increases by 4
HALT 0
