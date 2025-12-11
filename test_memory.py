#!/usr/bin/env python3

# Simulate the Coq list operations for the tape_window_ok proof

TAPE_START_ADDR = 1000
RULES_START_ADDR = 100

def pad_to(k, l):
    """Pad list l to length k with zeros if shorter, else return l (assuming len(l) <= k)"""
    if len(l) < k:
        return l + [0] * (k - len(l))
    else:
        return l  # but in proof, len(l) <= k

def firstn(n, l):
    return l[:n]

def skipn(n, l):
    return l[n:]

def app(l1, l2):
    return l1 + l2

# Simulate the setup
# Assume some lengths
len_program = 50  # assume <= 100
len_rrules = 200  # assume <= 900
len_mem0_rrules = len_program + len_rrules  # assume <= 1000

program = [1] * len_program  # dummy
rrules = [2] * len_rrules  # dummy
tape = [3] * 100  # dummy tape

mem0 = pad_to(RULES_START_ADDR, program)
print(f"len(mem0) = {len(mem0)}")

mem0_rrules = app(mem0, rrules)
print(f"len(mem0_rrules) = {len(mem0_rrules)}")

pref = pad_to(TAPE_START_ADDR, mem0_rrules)
print(f"len(pref) = {len(pref)}")

mem = app(pref, tape)
print(f"len(mem) = {len(mem)}")

# Now, tape_window_ok: firstn(len(tape), skipn(TAPE_START_ADDR, mem)) == tape
skipped = skipn(TAPE_START_ADDR, mem)
print(f"len(skipped) = {len(skipped)}")
window = firstn(len(tape), skipped)
print(f"window == tape: {window == tape}")

# The lemma: firstn(len(tape), skipn(TAPE_START_ADDR, app(pref, tape))) == tape
# Since mem = app(pref, tape), skipn(TAPE_START_ADDR, mem) = tape
# firstn(len(tape), tape) = tape

print("Test passed" if window == tape else "Test failed")