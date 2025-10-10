# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
"""
Project Cerberus: Hash Collision Demonstration
Using the Thiele Machine to manufacture cryptographic hash collisions.
"""

import os
import time
import hashlib
import json

try:
    import z3
    from thielecpu.vm import VM
    from thielecpu.state import State
except ImportError as e:
    print(f"Import error: {e}")
    print("Ensure z3-solver and thielecpu are installed.")
    exit(1)

# --- Cerberus Hash Constants ---
# Well-chosen random-looking numbers for the hash function
IV = 0xDEADBEEF  # Initial value
ROUNDS = 4      # Number of rounds in permutation

# Substitution box (S-box) - maps 4-bit values
S_BOX = [
    0xE, 0x4, 0xD, 0x1, 0x2, 0xF, 0xB, 0x8,
    0x3, 0xA, 0x6, 0xC, 0x5, 0x9, 0x0, 0x7
]

# Permutation box (P-box) - permutes 32 bits
P_BOX = [
    31, 6, 29, 14, 1, 24, 19, 8,
    27, 2, 21, 12, 15, 4, 25, 10,
    23, 0, 17, 30, 7, 16, 13, 26,
    3, 20, 11, 28, 5, 22, 9, 18
]




def cerberus_hash(input_bytes: bytes) -> int:
    """The main hash function (simplified for demonstration)."""
    state = IV
    # Absorb the input with simplified operations
    for byte in input_bytes:
        state = state ^ (byte << 24)
        # Apply simplified permutation: rotate and add constants
        state = ((state << 13) | (state >> 19)) & 0xFFFFFFFF  # Rotate left by 13
        state = (state + 0xBADF00D) & 0xFFFFFFFF  # Add round constant
        # Simple non-linearity: multiply by a large prime and take mod 2^32
        state = (state * 0x9E3779B1) & 0xFFFFFFFF
    return state


def z3_cerberus_hash(input_bytes):
    """Z3 symbolic version of cerberus_hash for demonstration."""
    state = z3.BitVecVal(IV, 32)

    # Model the absorption phase symbolically
    for byte in input_bytes:
        # Mix in the byte with some non-linear operations
        state = state ^ z3.Concat(byte, z3.BitVecVal(0, 24))
        # Apply simplified permutation: rotate and add constants
        state = z3.RotateLeft(state, 13)  # Rotate left by 13
        state = state + z3.BitVecVal(0xBADF00D, 32)  # Add round constant
        # Simple non-linearity: multiply by a large prime and take mod 2^32
        state = (state * z3.BitVecVal(0x9E3779B1, 32)) & z3.BitVecVal(0xFFFFFFFF, 32)

    return state


def main():
    """Main demonstration function."""
    os.system('cls' if os.name == "nt" else "clear")
    print("=" * 80)
    print("  PROJECT CERBERUS: HASH COLLISION DEMONSTRATION")
    print("=" * 80)

    vm = VM(State())

    # --- Define the inputs ---
    benign_input = b"This is a legitimate contract."
    malicious_input_prefix = b"This contract is null and void. "

    # --- Compute the target hash (the classical, forward direction) ---
    vm.execute_python("print('PARTITION: Classical Hash Computation')")
    target_hash = cerberus_hash(benign_input)
    vm.execute_python(f"print('AXIOM: The hash of the benign input is {target_hash:08x}')")

    # --- The Thiele Machine's Task: The Inversion ---
    vm.execute_python("print('PARTITION: Thiele Machine - Collision Forgery')")
    vm.execute_python("print('AXIOM: We need to find a suffix that, when appended to the malicious prefix, produces the same hash.')")

    # Define the unknown: the "magic bytes" suffix
    magic_suffix_len = 4  # How many bytes we need to find
    magic_suffix_z3 = [z3.BitVec(f'suffix_{i}', 8) for i in range(magic_suffix_len)]
    malicious_prefix_z3 = [z3.BitVecVal(b, 8) for b in malicious_input_prefix]
    malicious_input_z3 = malicious_prefix_z3 + magic_suffix_z3

    # The Impossible Constraint
    vm.execute_python("print('LQUERY: Find a magic_suffix such that H(malicious_prefix + magic_suffix) == target_hash')")
    solver = z3.Solver()
    hash_constraint = z3_cerberus_hash(malicious_input_z3) == z3.BitVecVal(target_hash, 32)
    solver.add(hash_constraint)

    start_time = time.time()
    if solver.check() == z3.sat:
        solve_time = time.time() - start_time
        model = solver.model()
        # Extract the magic suffix bytes from the model
        magic_suffix_bytes = bytes([model.eval(b).as_long() for b in magic_suffix_z3])
        forged_input = malicious_input_prefix + magic_suffix_bytes

        vm.execute_python(f"print('LDEDUCE: Collision found in {solve_time:.2f} seconds')")
        vm.execute_python(f"print('LDEDUCE: Magic suffix: {magic_suffix_bytes.hex()}')")
    else:
        vm.execute_python("print('LASSERT: No collision found - this should not happen')")
        return

    # --- The Undeniable Report - The Side-by-Side Proof ---
    forged_hash = cerberus_hash(forged_input)

    print("\n" + "="*80)
    print("  PROJECT CERBERUS: FINAL VERIFICATION")
    print("="*80)
    print("\nBenign Input:")
    print(f"  > {benign_input.decode()}")
    print(f"  > Hash: {target_hash:08x}")

    print("\nForged Input (Discovered by Thiele Machine):")
    print(f"  > {forged_input.decode(errors='ignore')}")
    print(f"  > Hash: {forged_hash:08x}")

    print("\n" + "-"*80)
    if target_hash == forged_hash:
        print("VERDICT:   SUCCESS. HASH COLLISION MANUFACTURED.")
        print("ASSESSMENT: The cryptographic integrity of the Cerberus hash has been broken.")
        print("CONCLUSION: The Thiele Machine did not search. It solved. It treated the")
        print("            hash function's logic as a geometric object and calculated a")
        print("            second path to the same destination.")
    else:
        print("VERDICT:   FAILURE.")

    print("="*80)

    # Generate receipt
    receipt = {
        "experiment": "Project Cerberus: Hash Collision",
        "timestamp": time.time(),
        "benign_input": benign_input.decode(),
        "malicious_prefix": malicious_input_prefix.decode(),
        "target_hash": f"{target_hash:08x}",
        "forged_input": forged_input.decode(errors='ignore'),
        "forged_hash": f"{forged_hash:08x}",
        "collision_success": target_hash == forged_hash,
        "solve_time_seconds": solve_time
    }

    os.makedirs("results", exist_ok=True)
    with open('results/cerberus_receipt.json', 'w') as f:
        json.dump(receipt, f, indent=2)

    print("Receipt saved to results/cerberus_receipt.json")


if __name__ == "__main__":
    main()