# benchmark.asm
# Performance benchmark: measures instruction throughput via a tight countdown loop.
# Loop body: SUB + JNEZ = 2 instructions per iteration × N iterations.
# Set N = 100 → 200 dispatch cycles.  Useful for timing comparisons.
#
# Expected outcome: r1 = 0 at HALT.

LOAD_IMM r1 100 1   # N = 100 iterations
LOAD_IMM r2 1 0     # step = 1

BENCH_LOOP:
SUB r1 r1 r2 1      # r1--
JNEZ r1 BENCH_LOOP 1

HALT 0
