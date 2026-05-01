# fibonacci.asm — Compute Fibonacci numbers
#
# Computes fib(N) where N is loaded as immediate.
# Result in r3. Uses loop with counter.
#
# Expected: r3 = fib(10) = 55, r5 = 0, mem[0] = 55

FUEL 500

# Partition setup (portable: works on both OCaml runner and RTL cosim)
INIT_PT 0 128                 # RTL: set ptTable[0] = 128 (mem region size)
INIT_ACTIVE_MODULE 0          # RTL: set active_module = 0
PNEW {0,128} 1               # Coq/OCaml: create partition covering mem[0..127]
LOAD_IMM r1 10 1              # N = 10 iterations
LOAD_IMM r2 0 1           # a = fib(0) = 0
LOAD_IMM r3 1 1           # b = fib(1) = 1
LOAD_IMM r6 1 1           # constant 1 (for decrementing)

LOOP:
    JNEZ r1 BODY 0        # if counter > 0, continue
    JUMP DONE 0           # else done

BODY:
    ADD r4 r2 r3 1        # r4 = a + b
    XFER r2 r3 0          # a = old b
    XFER r3 r4 0          # b = a + b
    SUB r1 r1 r6 1        # counter--
    JUMP LOOP 0

DONE:
    XFER r3 r2 0          # result = a (fib(N))
    LOAD_IMM r5 0 0      # r5 = address 0
    STORE r5 r3 1        # mem[r5] = result
    HALT 0
