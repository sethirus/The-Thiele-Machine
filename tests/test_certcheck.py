from thielecpu.certcheck import check_lrat, check_model


def test_check_model_satisfies_cnf():
    cnf = "p cnf 2 2\n1 -2 0\n2 0\n"
    assignment = "1 2"
    assert check_model(cnf, assignment)


def test_check_model_rejects_incomplete_assignment():
    cnf = "p cnf 1 1\n1 0\n"
    assignment = ""
    assert not check_model(cnf, assignment)


def test_check_lrat_unsat_empty_clause():
    cnf = "p cnf 1 2\n1 0\n-1 0\n"
    proof = "3 0 1 2 0\n"
    assert check_lrat(cnf, proof)


def test_check_lrat_rejects_bad_proof():
    cnf = "p cnf 1 1\n1 0\n"
    proof = "3 -1 0 0\n"
    assert not check_lrat(cnf, proof)
