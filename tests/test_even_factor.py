# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from thielecpu.factoring import recover_factors_partitioned


def test_even_semiprime_30():
    """Test factoring of even semiprime 15 * 2 = 30."""
    n_even = 30
    p, q = recover_factors_partitioned(n_even)

    assert p * q == n_even, f"Factors {p} * {q} should equal {n_even}"
    assert {p, q} == {15, 2} or {p, q} == {2, 15}, f"Factors should be 15 and 2, got {p} and {q}"


def test_even_semiprime_42():
    """Test factoring of even semiprime 21 * 2 = 42."""
    n_even2 = 42
    p2, q2 = recover_factors_partitioned(n_even2)

    assert p2 * q2 == n_even2, f"Factors {p2} * {q2} should equal {n_even2}"
    assert {p2, q2} == {21, 2} or {p2, q2} == {2, 21}, f"Factors should be 21 and 2, got {p2} and {q2}"