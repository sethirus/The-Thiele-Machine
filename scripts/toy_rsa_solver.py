# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Toy RSA helper for education and testing only.

This module provides a trivial factorization-based RSA key recovery routine
limited to very small moduli. It MUST NOT be used on real RSA keys.

Safety policy:
- The function aborts if the modulus bit-length exceeds 32 bits.
- This file is for educational, testing, and CI purposes only.
"""

from math import isqrt


def recover_factors_trial_division(n: int):
    """Recover prime factors p, q of n using trial division.

    This is intentionally extremely slow for large n and enforces a strict
    size limit to prevent misuse.
    """
    if n.bit_length() > 32:
        raise ValueError("Modulus too large for toy solver; operation prohibited.")

    # Simple trial division search
    limit = isqrt(n) + 1
    for p_candidate in range(2, limit):
        if n % p_candidate == 0:
            q_candidate = n // p_candidate
            return int(p_candidate), int(q_candidate)
    raise ValueError("No small factors found; input may not be a product of two small primes.")


if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser(description='Toy RSA factorization (educational only)')
    parser.add_argument('--n', type=int, required=True, help='RSA modulus n (must be <= 32-bit)')
    args = parser.parse_args()

    try:
        p, q = recover_factors_trial_division(args.n)
        print(f'Found factors: p={p}, q={q}')
    except ValueError as e:
        print(f'Error: {e}')
