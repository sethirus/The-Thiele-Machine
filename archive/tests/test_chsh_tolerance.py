"""Exercise tolerance CHECK through the actual machine and version rules."""
from fractions import Fraction
from itertools import product

import pytest

from thiele_small.chsh import PCHSH, chain, tally_code, tally_of, tolerance_check, tolerance_host

NOISY = (86, 14, 85, 15, 86, 14, 14, 86)


def test_noisy_tally_certifies_only_with_tolerance_and_pays_three():
    code = tally_code(NOISY)
    assert tally_of(code) == NOISY
    exact, relaxed = tolerance_host(), tolerance_host(1, 10)
    rejected = exact.run_prog(100, chain(), exact.start({0: code}))
    accepted = relaxed.run_prog(100, chain(), relaxed.start({0: code}))
    assert rejected.err and not rejected.cert and rejected.mu == 1
    assert accepted.cert and not accepted.err and accepted.mu == 3


@pytest.mark.parametrize("p,q", [(-1, 10), (0, 0), (1, -1)])
def test_invalid_tolerance_traps_before_commit(p, q):
    host = tolerance_host(p, q)
    result = host.run_prog(20, chain(), host.start({0: tally_code(NOISY)}))
    assert result.err and not result.cert


def test_empty_tally_cannot_certify_even_with_large_tolerance():
    host = tolerance_host(100, 1)
    result = host.run_prog(20, chain(), host.start())
    assert result.err and not result.cert


def test_modifying_checked_register_invalidates_commitment():
    host = tolerance_host(1, 10)
    program = [("CHECK", PCHSH, 0), ("INC", 0), ("COMMIT", PCHSH, 0), ("CERTIFY",)]
    result = host.run_prog(20, program, host.start({0: tally_code(NOISY)}))
    assert result.err and not result.cert
    assert result.ver(0) == 1


def test_commit_cannot_skip_check():
    host = tolerance_host(1, 10)
    result = host.run_prog(20, chain()[1:], host.start({0: tally_code(NOISY)}))
    assert result.err and not result.cert


def test_integer_test_matches_independent_rational_matrix_condition():
    for counts in product(range(3), repeat=8):
        totals = [counts[i] + counts[i + 1] for i in range(0, 8, 2)]
        for p, q in ((0, 1), (1, 10), (1, 1)):
            if not all(totals):
                expected = False
            else:
                e00, e01, e10, e11 = [Fraction(counts[i] - counts[i + 1], totals[i // 2])
                                         for i in range(0, 8, 2)]
                r = (1 + Fraction(p, q)) ** 2
                a, b = r - e00**2 - e10**2, r - e01**2 - e11**2
                expected = a >= 0 and b >= 0 and (e00 * e01 + e10 * e11)**2 <= a * b
            assert tolerance_check(counts, p, q) == expected
