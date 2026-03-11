# stress_test.asm
# Long-running stress test: counts down from 200 in an inner loop 10 times.
# Total inner iterations: 200 * 10 = 2000.
# Verifies that the VM sustains execution across thousands of steps.

LOAD_IMM r1 10 1    # outer counter (10 outer iterations)
LOAD_IMM r5 1 0     # step = 1

OUTER:
LOAD_IMM r2 200 1   # inner counter = 200

INNER:
SUB r2 r2 r5 1      # inner--
JNEZ r2 INNER 1     # while inner != 0

SUB r1 r1 r5 1      # outer--
JNEZ r1 OUTER 1     # while outer != 0

HALT 0
