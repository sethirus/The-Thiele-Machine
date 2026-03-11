# prime_sieve_demo.asm — Sieve of Eratosthenes + ALU verification suite
#
# PHASE 1 — Sieve of Eratosthenes (primes up to 20)
#   mem[0..19]  : is_prime flags (0=composite, 1=prime)
#   mem[20..27] : found primes packed into memory
#   r7          : prime count (expected: 8)
#
# PHASE 2 — Checksum + bit-ops verification
#   r25         : XOR checksum of all found primes (expected: 7)
#   r26         : popcount of checksum           (expected: 3)
#   r27         : AND of 42 & 58 = 40
#   r28         : OR  of 42 | 58 = 58
#   r29         : MUL of 7 * 11  = 77
#   r30         : LUI 0xAB       = 43776  (0xAB << 8)
#
# Sign-bit comparison trick: SUB A B; SHR result 31 → 1 if A < B (unsigned)
# Register map:
#   r1  = outer-loop i         r5  = constant 1
#   r2  = inner-loop j         r6  = scratch / sign-bit result
#   r3  = N = 20               r7  = prime count
#   r4  = sqrt_N = 5           r8  = temp value from memory
#   r9  = 31 (shift const)     r10 = output pointer (starts at 20)
#   r11 = inner limit N        r12 = phase-2 scratch
#   r20 = address register     r21 = address register 2

FUEL 3000

# ── Partition / state setup ─────────────────────────────────────────────────
INIT_PT 0 256
INIT_ACTIVE_MODULE 0
PNEW {0,256} 1

# ── Prime sieve array: mem[0]=0, mem[1]=0, mem[2..19]=1 ────────────────────
INIT_MEM 0  0
INIT_MEM 1  0
INIT_MEM 2  1
INIT_MEM 3  1
INIT_MEM 4  1
INIT_MEM 5  1
INIT_MEM 6  1
INIT_MEM 7  1
INIT_MEM 8  1
INIT_MEM 9  1
INIT_MEM 10 1
INIT_MEM 11 1
INIT_MEM 12 1
INIT_MEM 13 1
INIT_MEM 14 1
INIT_MEM 15 1
INIT_MEM 16 1
INIT_MEM 17 1
INIT_MEM 18 1
INIT_MEM 19 1

# ── Phase-1 constants ───────────────────────────────────────────────────────
LOAD_IMM r3  20 1           # N = 20
LOAD_IMM r4  5  1           # sqrt_N exclusive bound (outer i < 5)
LOAD_IMM r5  1  0           # constant 1
LOAD_IMM r7  0  0           # prime count = 0
LOAD_IMM r9  31 0           # shift amount for sign-bit comparison
LOAD_IMM r10 20 0           # output pointer = mem[20]

# ── PHASE 1: Outer sieve loop — mark composites ─────────────────────────────
LOAD_IMM r1 2 1             # i = 2

OUTER:
    # if i >= sqrt_N (5), stop sieving
    SUB  r6 r1 r4 0         # r6 = i - 5  (wraps if i < 5)
    SHR  r6 r6 r9 0         # r6 = sign bit: 1 iff i < 5
    JNEZ r6 CHECK_PRIME 0
    JUMP COLLECT 0

CHECK_PRIME:
    XFER r20 r1 0           # r20 = i (memory address)
    LOAD r8  r20 1          # r8  = is_prime[i]
    JNEZ r8  DO_INNER 0     # if prime, mark multiples
    JUMP OUTER_NEXT 0       # composite: skip inner

DO_INNER:
    MUL r2 r1 r1 1          # j = i * i  (start of inner loop)

INNER:
    # if j >= N, stop inner loop
    SUB  r6 r2 r3 0         # r6 = j - N  (wraps if j < N)
    SHR  r6 r6 r9 0         # r6 = sign bit: 1 iff j < N
    JNEZ r6 MARK 0
    JUMP OUTER_NEXT 0

MARK:
    XFER  r20 r2 0          # r20 = j
    LOAD_IMM r6 0 0         # value = 0
    STORE r20 r6 1          # is_prime[j] = 0
    ADD   r2  r2 r1 1       # j += i
    JUMP INNER 0

OUTER_NEXT:
    ADD  r1 r1 r5 1         # i++
    JUMP OUTER 0

# ── PHASE 1: Collect primes into mem[20..27] ────────────────────────────────
COLLECT:
    CHECKPOINT 0 0 1        # phase boundary marker
    LOAD_IMM r1 2 1         # scan from i = 2

COLLECT_LOOP:
    # if i >= N, done collecting
    SUB  r6 r1 r3 0
    SHR  r6 r6 r9 0         # 1 iff i < N
    JNEZ r6 CHECK_COLLECT 0
    JUMP PHASE2 0

CHECK_COLLECT:
    XFER r20 r1 0
    LOAD r8  r20 1          # r8 = is_prime[i]
    JNEZ r8  STORE_PRIME 0
    JUMP COLLECT_NEXT 0

STORE_PRIME:
    XFER  r20 r10 0         # address = output pointer
    STORE r20 r1  1         # mem[output_ptr] = prime value
    ADD   r7  r7  r5 1      # prime count++
    ADD   r10 r10 r5 0      # output pointer++

COLLECT_NEXT:
    ADD  r1 r1 r5 0         # i++
    JUMP COLLECT_LOOP 0

# ── PHASE 2: Checksum + ALU demos ────────────────────────────────────────────
PHASE2:
    CHECKPOINT 0 1 1        # phase 2 begins

    # -- XOR checksum of all 8 primes (mem[20..27]) --------------------------
    # Load each prime and XOR into r25 using XOR_ADD (register-mode)
    LOAD_IMM r25 0 1        # r25 = 0 (accumulator)
    LOAD_IMM r20 20 0       # address = 20
    LOAD r12 r20 1          # r12 = mem[20] = 2
    XOR_ADD r25 r12 1       # r25 ^= r12

    LOAD_IMM r20 21 0
    LOAD r12 r20 1          # r12 = mem[21] = 3
    XOR_ADD r25 r12 1       # r25 ^= 3   → r25 = 1

    LOAD_IMM r20 22 0
    LOAD r12 r20 1          # r12 = mem[22] = 5
    XOR_ADD r25 r12 1       # r25 ^= 5   → r25 = 4

    LOAD_IMM r20 23 0
    LOAD r12 r20 1          # r12 = mem[23] = 7
    XOR_ADD r25 r12 1       # r25 ^= 7   → r25 = 3

    LOAD_IMM r20 24 0
    LOAD r12 r20 1          # r12 = mem[24] = 11
    XOR_ADD r25 r12 1       # r25 ^= 11  → r25 = 8

    LOAD_IMM r20 25 0
    LOAD r12 r20 1          # r12 = mem[25] = 13
    XOR_ADD r25 r12 1       # r25 ^= 13  → r25 = 5

    LOAD_IMM r20 26 0
    LOAD r12 r20 1          # r12 = mem[26] = 17
    XOR_ADD r25 r12 1       # r25 ^= 17  → r25 = 20

    LOAD_IMM r20 27 0
    LOAD r12 r20 1          # r12 = mem[27] = 19
    XOR_ADD r25 r12 1       # r25 ^= 19  → r25 = 7  ← expected

    # -- Popcount of XOR checksum (expected: popcount(7) = 3) ---------------
    XOR_RANK r26 r25 1      # r26 = popcount(r25) = popcount(7=0b111) = 3

    # -- XOR swap demo -------------------------------------------------------
    LOAD_IMM r13 0xAA 1     # r13 = 0xAA = 170
    LOAD_IMM r14 0x55 1     # r14 = 0x55 = 85
    XOR_SWAP r13 r14 1      # swap r13 ↔ r14 via XOR trick
    # after: r13 = 0x55, r14 = 0xAA

    # -- AND / OR / SHL / SHR demos ------------------------------------------
    LOAD_IMM r11 42 1       # r11 = 42  = 0b00101010
    LOAD_IMM r12 58 1       # r12 = 58  = 0b00111010
    AND r27 r11 r12 1       # r27 = 42 & 58 = 40 = 0b00101000
    OR  r28 r11 r12 1       # r28 = 42 | 58 = 58

    LOAD_IMM r13 2 0        # shift amount = 2
    LOAD_IMM r14 7 0        # r14 = 7 = 0b111
    SHL r12 r14 r13 1       # r12 = 7 << 2 = 28
    SHR r11 r12 r13 1       # r11 = 28 >> 2 = 7  (round-trip)

    # -- MUL demo ------------------------------------------------------------
    LOAD_IMM r13 7  1       # r13 = 7
    LOAD_IMM r14 11 1       # r14 = 11
    MUL r29 r13 r14 1       # r29 = 7 * 11 = 77

    # -- LUI demo (load upper immediate) ------------------------------------
    LUI r30 0xAB 1          # r30 = 0xAB << 8 = 43776

    # -- Subroutine: compute 2^8 = 256 via repeated doubling ----------------
    LOAD_IMM r13 1 1        # r13 = 1 (initial value)
    LOAD_IMM r14 8 1        # r14 = 8 (count)
    CALL DBL_LOOP 1

AFTER_DBL:
    # r13 = 256, r14 = 0 on return

    HALT 0

# ── Subroutine: double r13 r14 times, decrement r14 ────────────────────────
DBL_LOOP:
    JNEZ r14 DO_DBL 0
    RET 1
DO_DBL:
    ADD  r13 r13 r13 1      # r13 *= 2
    SUB  r14 r14 r5  1      # r14--
    JUMP DBL_LOOP 0
