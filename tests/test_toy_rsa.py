from scripts.toy_rsa_solver import recover_factors_trial_division


def test_recover_small_rsa():
    p = 61
    q = 53
    n = p * q
    found_p, found_q = recover_factors_trial_division(n)
    assert set((found_p, found_q)) == set((p, q))


def test_recover_large_rsa_rejected():
    # Construct a large number > 32 bits and ensure it is rejected
    n = (1 << 40) + 12345
    try:
        recover_factors_trial_division(n)
        assert False, "Expected ValueError for large modulus"
    except ValueError:
        pass
