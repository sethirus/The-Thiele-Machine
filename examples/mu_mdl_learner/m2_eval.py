"""Brute-force learner vs random baseline."""
from __future__ import annotations

from examples.mu_mdl_learner.eval import (
    evaluate_brute_force,
    evaluate_random_baseline,
    format_table,
)
from examples.mu_mdl_learner.streams import make_dataset


N = 12
PERIODS = [2, 3, 4, 5, 6, 7, 8]
MAX_K = max(PERIODS)
SAMPLES_PER_PERIOD = 5
RANDOM_SAMPLES = 30


def main() -> int:
    print(f"M2 evaluation  (N={N}, periods={PERIODS}, "
          f"samples_per_period={SAMPLES_PER_PERIOD}, random_samples={RANDOM_SAMPLES})")
    dataset = make_dataset(
        n=N,
        periods=PERIODS,
        samples_per_period=SAMPLES_PER_PERIOD,
        random_samples=RANDOM_SAMPLES,
        seed=7,
        max_search_k=MAX_K,
    )
    print(f"Total streams: {len(dataset)}\n")

    print("== brute-force learner ==")
    bf_rows, bf_stats = evaluate_brute_force(dataset, max_k=MAX_K)
    print(format_table(bf_stats))

    bf_total_mu = sum(r.mu_paid for r in bf_rows)
    bf_total_correct = sum(1 for r in bf_rows if r.correct)
    print(f"\noverall  acc={bf_total_correct}/{len(bf_rows)} "
          f"({bf_total_correct / len(bf_rows):.2%})  "
          f"total_mu={bf_total_mu}  "
          f"mean_mu/stream={bf_total_mu / len(bf_rows):.1f}")

    print("\n== random-guess baseline ==")
    rg_rows, rg_stats = evaluate_random_baseline(dataset, max_k=MAX_K, seed=42)
    print(format_table(rg_stats))
    rg_correct = sum(1 for r in rg_rows if r.correct)
    print(f"\noverall  acc={rg_correct}/{len(rg_rows)} "
          f"({rg_correct / len(rg_rows):.2%})  total_mu=0 (no probing)")

    print()
    if bf_total_correct < int(0.95 * len(bf_rows)):
        print("M2 FAILED: brute-force accuracy below 95%. Investigate before M3.")
        return 1
    if bf_total_correct <= rg_correct:
        print("M2 FAILED: brute-force does not beat random.")
        return 1
    margin = bf_total_correct - rg_correct
    print(f"M2 OK: brute-force beat random by {margin} streams "
          f"({(bf_total_correct - rg_correct) / len(bf_rows):+.1%}). "
          "µ scales with probing depth.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
