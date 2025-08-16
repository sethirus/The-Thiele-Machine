# test_tseitin.py
import sys
import traceback

from attempt import generate_tseitin_expander, run_blind_budgeted, solve_sighted_xor, RUN_SEED

def test_tseitin_instance(n=10, seed=0, conf_budget=100_000, prop_budget=5_000_000):
    print(f"Testing Tseitin instance: n={n}, seed={seed}")
    instance = generate_tseitin_expander(n, seed=seed, global_seed=RUN_SEED)
    blind = run_blind_budgeted(instance["cnf_clauses"], conf_budget, prop_budget)
    sighted = solve_sighted_xor(instance["xor_rows"])
    print("Blind solver:", blind)
    print("Sighted solver:", sighted)
    assert blind["status"] in ("unsat", "censored"), f"Blind solver failed: {blind}"
    assert sighted["result"] == "unsat", f"Sighted solver failed: {sighted}"

if __name__ == "__main__":
    try:
        test_tseitin_instance(n=10, seed=0)
        test_tseitin_instance(n=12, seed=1)
        print("All Tseitin tests passed.")
    except Exception as e:
        print("Tseitin test failed!")
        traceback.print_exc()
        sys.exit(1)