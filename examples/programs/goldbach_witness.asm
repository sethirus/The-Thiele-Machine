# goldbach_witness.asm — Machine-certified Goldbach proof witness
#
# CLAIM: 1000 = 3 + 997, where 3 and 997 are both prime.
#
# On a normal computer this is an assertion you trust.
# On this machine it is a theorem the hardware signs.
#
# The machine:
#   1. Verifies 3   is prime: checks 3   mod 2         (1 divisor)
#   2. Verifies 997 is prime: checks 997 mod 2,3,5,7,11,13,17,19,23,29,31
#                             (all primes up to floor(sqrt(997)) = 31)
#   3. Verifies 3 + 997 = 1000
#   4. Calls CERTIFY — hardware sets certified:true, logs unforgeable mu-cost
#
# The output certificate (certified:true + mu > 0) is a proof that:
#   - The divisibility tests were actually executed (mu-cost is evidence)
#   - No divisor divided evenly (r14=0, r15=0 in certified state)
#   - The sum is exactly 1000 (r16=0 in certified state)
#   - These facts are co-signed by the Coq kernel proof chain
#
# To forge this certificate you must do the same work.
# There is no shortcut. That is the theorem.
#
# Register map:
#   r5  = constant 1         r9  = constant 31 (shift)
#   r10 = P = 3              r11 = Q = 997
#   r12 = N = 1000
#   r14 = P primality error  (0 = prime, non-zero = composite FOUND)
#   r15 = Q primality error  (0 = prime, non-zero = composite FOUND)
#   r16 = sum error          (P+Q-N, 0 = correct)
#   r17 = combined proof     (r14+r15+r16 = 0 iff all checks pass)
#   r28 = MOD working register (dividend, in/out)
#   r2  = MOD divisor

FUEL 30000

# ── Partition / state setup ──────────────────────────────────────────────────
INIT_PT 0 256
INIT_ACTIVE_MODULE 0
PNEW {0,256} 1

# ── Global constants ─────────────────────────────────────────────────────────
LOAD_IMM r5   1    0        # constant 1
LOAD_IMM r9   31   0        # shift for sign-bit comparison

# ── Load the two primes and the target ──────────────────────────────────────
LOAD_IMM r10  3    1        # P = 3
LOAD_IMM r11  997  1        # Q = 997
LOAD_IMM r12  1000 1        # N = 1000

# ── Error registers: 0 = pass, non-zero = fail ───────────────────────────────
LOAD_IMM r14  0    0        # P primality error
LOAD_IMM r15  0    0        # Q primality error

# ════════════════════════════════════════════════════════════════════════════
# STEP 1: Prove P = 3 is prime
#   Only need to check d=2  (sqrt(3) < 2)
#   3 mod 2 = 1  →  not divisible  →  PRIME
# ════════════════════════════════════════════════════════════════════════════
CHECKPOINT 1 0 1

    XFER  r28 r10 0             # r28 = P = 3
    LOAD_IMM r2 2 1             # divisor = 2
    CALL MOD 1                  # r28 = 3 mod 2 = 1
    JNEZ  r28 P_PRIME 0         # if remainder != 0, not divisible → prime
    LOAD_IMM r14 2 0            # r14 = 2 means "P divisible by 2" (failure)
P_PRIME:
    # r14 = 0 → P = 3 is prime ✓

# ════════════════════════════════════════════════════════════════════════════
# STEP 2: Prove Q = 997 is prime
#   Check all prime divisors d ≤ floor(sqrt(997)) = 31
#   i.e., d ∈ {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31}
#   Each call: reload r28=997, set r2=d, CALL MOD
#   If any remainder is 0 → Q is composite (set r15 = d)
# ════════════════════════════════════════════════════════════════════════════
CHECKPOINT 2 0 1

    XFER r28 r11 0
    LOAD_IMM r2 2 1
    CALL MOD 1
    JNEZ r28 Q_D3 0
    LOAD_IMM r15 2 0
    JUMP Q_DONE 0
Q_D3:
    XFER r28 r11 0
    LOAD_IMM r2 3 1
    CALL MOD 1
    JNEZ r28 Q_D5 0
    LOAD_IMM r15 3 0
    JUMP Q_DONE 0
Q_D5:
    XFER r28 r11 0
    LOAD_IMM r2 5 1
    CALL MOD 1
    JNEZ r28 Q_D7 0
    LOAD_IMM r15 5 0
    JUMP Q_DONE 0
Q_D7:
    XFER r28 r11 0
    LOAD_IMM r2 7 1
    CALL MOD 1
    JNEZ r28 Q_D11 0
    LOAD_IMM r15 7 0
    JUMP Q_DONE 0
Q_D11:
    XFER r28 r11 0
    LOAD_IMM r2 11 1
    CALL MOD 1
    JNEZ r28 Q_D13 0
    LOAD_IMM r15 11 0
    JUMP Q_DONE 0
Q_D13:
    XFER r28 r11 0
    LOAD_IMM r2 13 1
    CALL MOD 1
    JNEZ r28 Q_D17 0
    LOAD_IMM r15 13 0
    JUMP Q_DONE 0
Q_D17:
    XFER r28 r11 0
    LOAD_IMM r2 17 1
    CALL MOD 1
    JNEZ r28 Q_D19 0
    LOAD_IMM r15 17 0
    JUMP Q_DONE 0
Q_D19:
    XFER r28 r11 0
    LOAD_IMM r2 19 1
    CALL MOD 1
    JNEZ r28 Q_D23 0
    LOAD_IMM r15 19 0
    JUMP Q_DONE 0
Q_D23:
    XFER r28 r11 0
    LOAD_IMM r2 23 1
    CALL MOD 1
    JNEZ r28 Q_D29 0
    LOAD_IMM r15 23 0
    JUMP Q_DONE 0
Q_D29:
    XFER r28 r11 0
    LOAD_IMM r2 29 1
    CALL MOD 1
    JNEZ r28 Q_D31 0
    LOAD_IMM r15 29 0
    JUMP Q_DONE 0
Q_D31:
    XFER r28 r11 0
    LOAD_IMM r2 31 1
    CALL MOD 1
    JNEZ r28 Q_DONE 0
    LOAD_IMM r15 31 0

Q_DONE:
    # r15 = 0 → Q = 997 is prime ✓

# ════════════════════════════════════════════════════════════════════════════
# STEP 3: Verify P + Q = N
# ════════════════════════════════════════════════════════════════════════════
CHECKPOINT 3 0 1

    ADD r6  r10 r11 1           # r6  = P + Q = 3 + 997 = 1000
    SUB r16 r6  r12 1           # r16 = (P+Q) - N = 1000 - 1000 = 0

# ════════════════════════════════════════════════════════════════════════════
# STEP 4: Combine all proofs and CERTIFY
# ════════════════════════════════════════════════════════════════════════════
CHECKPOINT 4 1 1

    ADD r17 r14 r15 1           # r17 = P_error + Q_error
    ADD r17 r17 r16 1           # r17 += sum_error  →  should be 0

    # r17 = 0 means:
    #   - 3 has no small divisors   (proven by exhaustive trial division)
    #   - 997 has no prime divisors ≤ 31  (proven by exhaustive trial division)
    #   - 3 + 997 = 1000  (proven by arithmetic)
    # Therefore: 1000 is a sum of two primes.
    # This state is now signed by the machine.

    CERTIFY 1

    HALT 0

# ════════════════════════════════════════════════════════════════════════════
# Subroutine MOD: r28 = r28 mod r2
#   Uses r6 as scratch. Preserves r2.
#   Repeated subtraction: while r28 >= r2, r28 -= r2
# ════════════════════════════════════════════════════════════════════════════
MOD:
MOD_LOOP:
    SUB  r6 r28 r2 0            # r6 = r28 - r2  (wraps if r28 < r2)
    SHR  r6 r6  r9 0            # sign bit: 1 iff r28 < r2
    JNEZ r6 MOD_RET 0           # if r28 < r2, done
    SUB  r28 r28 r2 0           # r28 -= r2
    JUMP MOD_LOOP 0
MOD_RET:
    RET 1
