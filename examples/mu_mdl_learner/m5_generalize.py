"""Held-out generalization: train compositional on one set, eval on a disjoint set."""
from __future__ import annotations

from typing import List

from examples.mu_mdl_learner.brute_force import brute_force_period
from examples.mu_mdl_learner.compositional import CompositionalLearner
from examples.mu_mdl_learner.streams import LabeledStream, make_dataset


N = 12
MIN_K = 2
PERIODS = [2, 3, 4, 5, 6, 7, 8]
MAX_K = max(PERIODS)


def _sequence(seed: int, samples_per_period: int, random_samples: int) -> List[LabeledStream]:
    return make_dataset(
        n=N,
        periods=PERIODS,
        samples_per_period=samples_per_period,
        random_samples=random_samples,
        seed=seed,
        max_search_k=MAX_K,
    )


def main() -> int:
    train = _sequence(seed=21, samples_per_period=4, random_samples=20)
    test = _sequence(seed=22, samples_per_period=4, random_samples=20)

    print(f"M5 generalization  (N={N}, periods={PERIODS})")
    print(f"  train stream count: {len(train)}")
    print(f"  test  stream count: {len(test)}")
    print()

    # Train the compositional learner: run it through the train set so its
    # history reflects the period distribution. We discard the µ paid during
    # training when we report test µ — training cost is a separate budget.
    learner = CompositionalLearner(min_k=MIN_K, max_k=MAX_K)
    train_correct = 0
    train_mu = 0
    train_probes = 0
    for s in train:
        r = learner.predict(s.bits)
        train_correct += int(r.predicted_period == s.period)
        train_mu += r.total_mu
        train_probes += r.num_probes
    print(f"  training pass: acc={train_correct}/{len(train)} "
          f"({train_correct / len(train):.2%}) µ={train_mu} probes={train_probes}")
    print(f"  learner history after training (most-recent first): {learner.history}")

    # Now evaluate on the held-out test set. Compositional learner keeps its
    # accumulated history (we don't reset). Compare against brute-force run
    # fresh on the same test set.
    print()
    print("== test pass ==")
    cp_correct = 0
    cp_mu = 0
    cp_probes = 0
    for s in test:
        r = learner.predict(s.bits)
        cp_correct += int(r.predicted_period == s.period)
        cp_mu += r.total_mu
        cp_probes += r.num_probes

    bf_correct = 0
    bf_mu = 0
    bf_probes = 0
    for s in test:
        r = brute_force_period(s.bits, max_k=MAX_K, min_k=MIN_K)
        bf_correct += int(r.predicted_period == s.period)
        bf_mu += r.total_mu
        bf_probes += r.num_probes

    print(f"  compositional: acc={cp_correct}/{len(test)} ({cp_correct/len(test):.2%}) "
          f"µ={cp_mu} probes={cp_probes}")
    print(f"  brute-force:   acc={bf_correct}/{len(test)} ({bf_correct/len(test):.2%}) "
          f"µ={bf_mu} probes={bf_probes}")

    if bf_mu == 0:
        return 1
    savings_pct = (bf_mu - cp_mu) / bf_mu * 100
    print()
    if cp_correct < len(test):
        print(f"M5 NOTE: compositional accuracy below 100% on held-out "
              f"({cp_correct}/{len(test)}). Investigate before relying on this.")
    if cp_mu < bf_mu:
        print(f"M5 OK: compositional saved {bf_mu - cp_mu} µ "
              f"({savings_pct:.1f}%) on held-out streams it didn't see in training.")
    else:
        print(f"M5 NEGATIVE RESULT: compositional did not save µ on held-out "
              f"(used {cp_mu - bf_mu} more). The bias did not transfer.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
