# oracle_demo.asm
# Demonstrates ORACLE_HALTS instruction.
# ORACLE_HALTS op_a op_b cost
#   → If oracle says the machine would diverge, it halts early (conservative).
#   → Acts as a no-op at the VM level if the oracle returns False.
# In the reference VM every ORACLE_HALTS returns False (no halt) and simply
# charges cost against μ.  This demo shows normal execution continues past it.

LOAD_IMM r1 42 1        # r1 = 42
ORACLE_HALTS 0 0 1      # oracle check (no-op in reference VM, costs 1)
ORACLE_HALTS 1 1 2      # second check with higher cost
ADD r2 r1 r1 1          # r2 = 84 (executes because oracle did NOT halt)
ORACLE_HALTS 0 1 3      # third check
HALT 0
