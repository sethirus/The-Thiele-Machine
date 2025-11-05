# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import pytest

from thielecpu.factoring import recover_factors_partitioned


def test_recover_small_rsa():
    """Test partitioned factoring for small RSA modulus (fast trial division)."""
    p = 10007
    q = 10009
    n = p * q
    found_p, found_q = recover_factors_partitioned(n)
    assert set((found_p, found_q)) == set((p, q))
    assert found_p * found_q == n


def test_recover_small_rsa_order_independent():
    """Test that order of p and q doesn't matter."""
    p = 10007
    q = 10009
    n = p * q
    found_p, found_q = recover_factors_partitioned(n)
    assert min(found_p, found_q) == min(p, q)
    assert max(found_p, found_q) == max(p, q)


def test_recover_64bit_rsa():
    """Test partitioned factoring for 64-bit RSA modulus using Pollard's rho."""
    p = 1000000007
    q = 1000000021
    n = p * q
    found_p, found_q = recover_factors_partitioned(n)
    assert set((found_p, found_q)) == set((p, q))
    assert found_p * found_q == n