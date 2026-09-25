# chsh_full.asm
# This runs four CHSH trial inputs through the current textual VM format.
# The instruction fields are x, y, a, b, and cost.
# The example checks that each binary setting is accepted and charged.

CHSH_TRIAL 0 0 0 0 1    # x=0, y=0, a=0, b=0
CHSH_TRIAL 0 1 0 0 1    # x=0, y=1, a=0, b=0
CHSH_TRIAL 1 0 0 0 1    # x=1, y=0, a=0, b=0
CHSH_TRIAL 1 1 0 0 1    # x=1, y=1, a=0, b=0

# 4 trials × cost=1 each → mu increases by 4
HALT 0
