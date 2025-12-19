from scripts.time_dilation_experiment import run_experiment


def test_compute_rate_slows_as_comm_increases():
    data = run_experiment(write=False)
    scenarios = data["scenarios"]

    rates = [s["compute_rate"] for s in scenarios]
    assert rates == sorted(rates, reverse=True), "Compute rate should monotonically decrease with more communication"

    totals_match = all(s["mu_total"] == s["comm_mu"] + s["compute_mu"] for s in scenarios)
    assert totals_match, "μ totals must equal comm + compute spending"

    # The heaviest communication workload should spend nearly all μ on communication.
    heavy = scenarios[-1]
    assert heavy["comm_mu"] > heavy["compute_mu"], "Communication should dominate μ spending under heavy comm load"
