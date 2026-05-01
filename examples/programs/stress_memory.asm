# stress_memory.asm — Stress test: arithmetic loop + memory roundtrip
#
# Runs a tight loop 200 times doing arithmetic and XOR operations,
# then stores results and verifies memory roundtrip.
#
# Expected: r2 = 0 (loop exhausted), r10 = r1 (mem roundtrip), halted=1, err=0

FUEL 10000

# Partition setup (portable: works on both OCaml runner and RTL cosim)
INIT_PT 0 128                 # RTL: set ptTable[0] = 128 (mem region size)
INIT_ACTIVE_MODULE 0          # RTL: set active_module = 0
PNEW {0,128} 1               # Coq/OCaml: create partition covering mem[0..127]

# Setup
LOAD_IMM r1 0 1              # accumulator
LOAD_IMM r2 200 1            # loop count
LOAD_IMM r3 1 1              # increment
LOAD_IMM r4 7 1              # XOR value

STRESS_LOOP:
    ADD r1 r1 r3 1            # acc += 1
    XOR_LOAD r1 0 1           # XOR load acc
    XOR_ADD r4 0 1            # XOR add
    SUB r2 r2 r3 1            # count--
    JNEZ r2 STRESS_LOOP 0     # loop if count > 0

# Store results to memory
LOAD_IMM r12 0 0              # r12 = address 0
LOAD_IMM r13 1 0              # r13 = address 1
STORE r12 r1 1                # mem[r12] = r1 (accumulator)
STORE r13 r2 1                # mem[r13] = 0 (loop counter exhausted)

# Verify memory roundtrip
LOAD r10 r12 1                # r10 = mem[r12] should equal r1
LOAD r14 r13 1                # r14 = mem[r13] should equal 0

HALT 0
