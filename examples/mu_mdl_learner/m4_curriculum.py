"""Compositional vs brute-force on curriculum (grouped) and shuffled stream orders."""
from __future__ import annotations

import random
from dataclasses import dataclass
from typing import List, Tuple

from examples.mu_mdl_learner.brute_force import brute_force_period
from examples.mu_mdl_learner.compositional import CompositionalLearner
from examples.mu_mdl_learner.streams import LabeledStream, make_dataset


N = 12
MIN_K = 2
PERIODS_FOR_CURRICULUM = [2, 4, 6, 8]   # spaced so multiples-of-2 chain shows
MAX_K = max(PERIODS_FOR_CURRICULUM)
SAMPLES_PER_PERIOD = 5
SEED = 11


@dataclass
class Tally:
    streams_seen: int = 0
    correct: int = 0
    total_mu: int = 0
    total_probes: int = 0


def _build_curriculum_dataset() -> List[LabeledStream]:
    """Periods grouped: all period-2 first, then period-4, etc."""
    return make_dataset(
        n=N,
        periods=PERIODS_FOR_CURRICULUM,
        samples_per_period=SAMPLES_PER_PERIOD,
        random_samples=0,
        seed=SEED,
        max_search_k=MAX_K,
    )


def _shuffle(dataset: List[LabeledStream], seed: int) -> List[LabeledStream]:
    rng = random.Random(seed)
    out = list(dataset)
    rng.shuffle(out)
    return out


def _run_brute_force(dataset: List[LabeledStream]) -> Tally:
    tally = Tally()
    for labeled in dataset:
        result = brute_force_period(labeled.bits, max_k=MAX_K, min_k=MIN_K)
        tally.streams_seen += 1
        if result.predicted_period == labeled.period:
            tally.correct += 1
        tally.total_mu += result.total_mu
        tally.total_probes += result.num_probes
    return tally


def _run_compositional(dataset: List[LabeledStream]) -> Tally:
    learner = CompositionalLearner(min_k=MIN_K, max_k=MAX_K)
    tally = Tally()
    for labeled in dataset:
        result = learner.predict(labeled.bits)
        tally.streams_seen += 1
        if result.predicted_period == labeled.period:
            tally.correct += 1
        tally.total_mu += result.total_mu
        tally.total_probes += result.num_probes
    return tally


def _print_tally(name: str, t: Tally) -> None:
    print(f"  {name:>15}: streams={t.streams_seen}  correct={t.correct}/{t.streams_seen}  "
          f"total_mu={t.total_mu}  total_probes={t.total_probes}")


def main() -> int:
    curriculum = _build_curriculum_dataset()
    shuffled = _shuffle(curriculum, seed=SEED * 13 + 1)

    print(f"M4 curriculum benchmark  (N={N}, periods={PERIODS_FOR_CURRICULUM}, "
          f"{SAMPLES_PER_PERIOD} samples/period, total streams={len(curriculum)})")
    print()
    print("=== curriculum order (periods grouped) ===")
    bf_curr = _run_brute_force(curriculum)
    cp_curr = _run_compositional(curriculum)
    _print_tally("brute-force", bf_curr)
    _print_tally("compositional", cp_curr)
    curr_savings = bf_curr.total_mu - cp_curr.total_mu
    curr_savings_pct = (curr_savings / bf_curr.total_mu) * 100 if bf_curr.total_mu else 0
    print(f"  compositional savings: {curr_savings} µ ({curr_savings_pct:.1f}% of brute-force total)")
    print()
    print("=== shuffled order (no curriculum) ===")
    bf_shuf = _run_brute_force(shuffled)
    cp_shuf = _run_compositional(shuffled)
    _print_tally("brute-force", bf_shuf)
    _print_tally("compositional", cp_shuf)
    shuf_savings = bf_shuf.total_mu - cp_shuf.total_mu
    shuf_savings_pct = (shuf_savings / bf_shuf.total_mu) * 100 if bf_shuf.total_mu else 0
    print(f"  compositional savings: {shuf_savings} µ ({shuf_savings_pct:.1f}% of brute-force total)")
    print()

    # Acceptance check (from the brief).
    ok = True
    if cp_curr.total_mu >= bf_curr.total_mu:
        print("M4 FAILED on curriculum: compositional did not save µ.")
        ok = False
    elif curr_savings_pct < 5:
        print(f"M4 WARNING on curriculum: savings only {curr_savings_pct:.1f}%. "
              "Brief asked for 'a measurable margin' — this is technically a win "
              "but small.")
    # Shuffled: we expect a near-tie. Allow either direction within a few µ.
    rel_diff = abs(cp_shuf.total_mu - bf_shuf.total_mu) / max(1, bf_shuf.total_mu)
    if rel_diff > 0.1:
        print(f"M4 WARNING on shuffled: compositional and brute-force differ by "
              f"{rel_diff:.1%}. Brief expected a tie.")
    if ok:
        print(f"M4 OK: compositional saved {curr_savings} µ ({curr_savings_pct:.1f}%) on the curriculum, "
              f"differs by {rel_diff:.1%} on shuffled.")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
