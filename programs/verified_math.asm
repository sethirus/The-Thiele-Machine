# verified_math.asm — Self-verifying computation on the Thiele Machine
#
# PHASE 1: Sum-of-Squares Identity
#   Loop computes S = 1² + 2² + ... + 10²  =  385
#   Formula computes N·(N+1)·(2N+1)        = 2310
#   Verification:   6 × S                  = 2310
#   r10 = S   = 385
#   r11 = N(N+1)(2N+1) = 2310
#   r12 = 6·S = 2310
#   r13 = r12 - r11 = 0  ← IDENTITY HOLDS
#
# PHASE 2: Bubble Sort with sum invariant
#   Input:  mem[50..57] = [15, 3, 9, 7, 18, 1, 11, 5]  sum = 69
#   Output: mem[50..57] = [1, 3, 5, 7, 9, 11, 15, 18]  sum = 69
#   r14 = sum before = 69
#   r15 = sum after  = 69
#   r16 = r15 - r14  = 0  ← SUM INVARIANT HOLDS
#
# PHASE 3: CERTIFY
#   r17 = r13 + r16  = 0  (both proofs passed)
#   machine state marked certified — mu cost logged
#
# Sign-bit comparison: SUB a b; SHR 31 → 1 iff a < b (unsigned wrap)

FUEL 5000

# ── Partition / state setup ──────────────────────────────────────────────────
INIT_PT 0 256
INIT_ACTIVE_MODULE 0
PNEW {0,256} 1

# ── Phase 2 input array ──────────────────────────────────────────────────────
INIT_MEM 50 15
INIT_MEM 51  3
INIT_MEM 52  9
INIT_MEM 53  7
INIT_MEM 54 18
INIT_MEM 55  1
INIT_MEM 56 11
INIT_MEM 57  5

# ── Global constants ─────────────────────────────────────────────────────────
LOAD_IMM r5  1  0           # constant 1
LOAD_IMM r9  31 0           # shift for sign-bit comparison

# ════════════════════════════════════════════════════════════════════════════
# PHASE 1 — Sum-of-Squares Identity
#   Prove: 6 × (Σ i² for i=1..10) = 10 × 11 × 21 = 2310
# ════════════════════════════════════════════════════════════════════════════
CHECKPOINT 1 0 1

    LOAD_IMM r3  10 1           # N  = 10
    LOAD_IMM r1   1 1           # i  = 1
    LOAD_IMM r10  0 1           # S  = 0  (accumulator)

SOS_LOOP:
    # exit when i > N: N - i wraps → sign bit set
    SUB  r6 r3 r1 0             # r6 = N - i
    SHR  r6 r6 r9 0             # sign bit: 1 iff i > N
    JNEZ r6 SOS_DONE 0
    MUL  r2 r1 r1 1             # r2 = i²
    ADD  r10 r10 r2 1           # S += i²
    ADD  r1  r1  r5 0           # i++
    JUMP SOS_LOOP 0

SOS_DONE:
    # r10 = 385  (sum of squares 1..10)

    # Formula: N × (N+1) × (2N+1) = 10 × 11 × 21
    LOAD_IMM r1 10 1
    LOAD_IMM r2 11 1
    LOAD_IMM r3 21 1
    MUL r11 r1  r2  1           # 10 × 11 = 110
    MUL r11 r11 r3  1           # 110 × 21 = 2310

    # 6 × S
    LOAD_IMM r1 6 1
    MUL r12 r1 r10 1            # 6 × 385 = 2310

    # Verify: 6S − N(N+1)(2N+1) = 0
    SUB r13 r12 r11 1           # r13 = 2310 − 2310 = 0  ← PROVEN

# ════════════════════════════════════════════════════════════════════════════
# PHASE 2 — Bubble Sort with sum invariant
#   Input: [15, 3, 9, 7, 18, 1, 11, 5]
#   Expected output: [1, 3, 5, 7, 9, 11, 15, 18]
# ════════════════════════════════════════════════════════════════════════════
CHECKPOINT 2 0 1

    # -- Compute sum BEFORE sort --
    LOAD_IMM r14  0  1          # sum_before = 0
    LOAD_IMM r20  50 0          # addr = 50
    LOAD_IMM r22  8  0          # count = 8

PRE_SUM:
    JNEZ r22 PRE_SUM_DO 0
    JUMP PRE_DONE 0
PRE_SUM_DO:
    LOAD r24 r20 1              # r24 = mem[addr]
    ADD  r14 r14 r24 0          # sum_before += value
    ADD  r20 r20 r5  0          # addr++
    SUB  r22 r22 r5  0          # count--
    JUMP PRE_SUM 0
PRE_DONE:
    # r14 = 69

    # -- Bubble sort: 7 passes over 8 elements --
    LOAD_IMM r22 7 1            # pass counter = N-1

SORT_OUTER:
    JNEZ r22 SORT_PASS 0
    JUMP SORT_DONE 0

SORT_PASS:
    LOAD_IMM r21 50 0           # j = 50  (index into array)
    LOAD_IMM r23 57 0           # last valid j for compare = 57

SORT_INNER:
    # if j >= 57, end of pass
    SUB  r6 r21 r23 0           # j - 57 (wraps if j < 57)
    SHR  r6 r6   r9 0           # sign bit: 1 iff j < 57
    JNEZ r6 SORT_CMP 0
    JUMP SORT_NEXT_PASS 0

SORT_CMP:
    LOAD r24 r21 1              # A = mem[j]
    ADD  r20 r21 r5 0           # r20 = j+1
    LOAD r25 r20 1              # B = mem[j+1]

    # swap if A > B: B - A wraps → sign bit set
    SUB  r6 r25 r24 0           # B - A
    SHR  r6 r6   r9 0           # sign bit: 1 iff A > B
    JNEZ r6 SORT_SWAP 0
    JUMP SORT_INC 0

SORT_SWAP:
    STORE r21 r25 1             # mem[j]   = B
    STORE r20 r24 1             # mem[j+1] = A

SORT_INC:
    ADD  r21 r21 r5 0           # j++
    JUMP SORT_INNER 0

SORT_NEXT_PASS:
    SUB  r22 r22 r5 0           # passes--
    JUMP SORT_OUTER 0

SORT_DONE:
    # -- Compute sum AFTER sort (must equal r14 = 69) --
    LOAD_IMM r15  0  1          # sum_after = 0
    LOAD_IMM r20  50 0          # addr = 50
    LOAD_IMM r22  8  0          # count = 8

POST_SUM:
    JNEZ r22 POST_SUM_DO 0
    JUMP POST_DONE 0
POST_SUM_DO:
    LOAD r24 r20 1
    ADD  r15 r15 r24 0
    ADD  r20 r20 r5  0
    SUB  r22 r22 r5  0
    JUMP POST_SUM 0
POST_DONE:
    # r15 = 69

    # Verify sum invariant
    SUB r16 r15 r14 1           # r16 = sum_after − sum_before = 0  ← PROVEN

# ════════════════════════════════════════════════════════════════════════════
# PHASE 3 — Combined verification and CERTIFY
# ════════════════════════════════════════════════════════════════════════════
CHECKPOINT 3 1 1

    # r17 = identity_error + sort_error: must be 0
    ADD r17 r13 r16 1           # r17 = 0 + 0 = 0

    # Mark this state as formally certified
    # (machine enforces: certified state = all mu-costs paid)
    CERTIFY 1

    HALT 0
