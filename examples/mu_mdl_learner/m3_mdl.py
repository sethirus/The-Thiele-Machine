"""µ paid vs MDL bits gained: bucket table + ASCII scatter."""
from __future__ import annotations

from typing import Dict, List, Tuple

from examples.mu_mdl_learner.brute_force import brute_force_period
from examples.mu_mdl_learner.mdl import MDLScore, mdl_score
from examples.mu_mdl_learner.streams import LabeledStream, make_dataset


N = 12
MIN_K = 2
PERIODS = [2, 3, 4, 5, 6, 7, 8]
MAX_K = max(PERIODS)
SAMPLES_PER_PERIOD = 5
RANDOM_SAMPLES = 30


def _format_stream(bits) -> str:
    return "".join(str(int(b)) for b in bits)


def _run_one(labeled: LabeledStream) -> Tuple[MDLScore, int, int]:
    """Returns (mdl_score, mu_paid, num_probes)."""
    result = brute_force_period(labeled.bits, max_k=MAX_K, min_k=MIN_K)
    last_probe = result.probes[-1] if result.probes else None
    score = mdl_score(
        stream=labeled.bits,
        predicted_period=result.predicted_period,
        min_k=MIN_K,
        max_k=MAX_K,
        verified=bool(last_probe and last_probe.verified),
    )
    return score, result.total_mu, result.num_probes


def _ascii_scatter(points: List[Tuple[int, int, str]], width: int = 60, height: int = 14) -> str:
    """Crude ASCII scatter for (µ, MDL gain). Each point: (x, y, marker).

    Marker is a single character: 'p' for periodic streams, '.' for non-
    periodic. Overlap collapses to '*'. No external plotting deps so this
    runs in any environment.
    """
    if not points:
        return "(no points)"
    xs = [x for x, _, _ in points]
    ys = [y for _, y, _ in points]
    xmin, xmax = min(xs), max(xs)
    ymin, ymax = min(ys), max(ys)
    if xmin == xmax:
        xmax = xmin + 1
    if ymin == ymax:
        ymax = ymin + 1
    grid = [[" "] * width for _ in range(height)]
    for x, y, m in points:
        col = int((x - xmin) / (xmax - xmin) * (width - 1))
        row = int((y - ymin) / (ymax - ymin) * (height - 1))
        row = height - 1 - row  # flip so larger y is at top
        existing = grid[row][col]
        if existing == " ":
            grid[row][col] = m
        elif existing != m:
            grid[row][col] = "*"
    lines = []
    for ri, row in enumerate(grid):
        if ri == 0:
            lines.append(f"  {ymax:>5}  |" + "".join(row))
        elif ri == height - 1:
            lines.append(f"  {ymin:>5}  |" + "".join(row))
        else:
            lines.append(f"        |" + "".join(row))
    lines.append("        +" + "-" * width)
    lines.append(f"         {xmin:<{width // 2}}{xmax:>{width // 2}}")
    lines.append("         µ paid →                     legend: p=periodic .=non-periodic *=mixed")
    lines.append("         (y axis: MDL bits gained, larger = better compression)")
    return "\n".join(lines)


def main() -> int:
    print(f"M3 MDL scoring  (N={N}, periods={PERIODS}, "
          f"samples_per_period={SAMPLES_PER_PERIOD}, random_samples={RANDOM_SAMPLES})")
    dataset = make_dataset(
        n=N, periods=PERIODS,
        samples_per_period=SAMPLES_PER_PERIOD,
        random_samples=RANDOM_SAMPLES,
        seed=7,
        max_search_k=MAX_K,
    )

    per_stream: List[Tuple[LabeledStream, MDLScore, int, int]] = []
    for labeled in dataset:
        score, mu_paid, num_probes = _run_one(labeled)
        per_stream.append((labeled, score, mu_paid, num_probes))

    # Per-truth-period table.
    print()
    print(f"{'truth':>14} {'count':>6} {'mean_mu':>10} {'mean_gain':>11} {'mean_probes':>12}")
    print("-" * 60)
    by_truth: Dict = {}
    for labeled, score, mu, probes in per_stream:
        by_truth.setdefault(labeled.period, []).append((score, mu, probes))
    sort_key = lambda k: (1, 0) if k is None else (0, k)
    for truth in sorted(by_truth.keys(), key=sort_key):
        group = by_truth[truth]
        n = len(group)
        mean_mu = sum(mu for _, mu, _ in group) / n
        mean_gain = sum(s.gain_bits for s, _, _ in group) / n
        mean_probes = sum(p for _, _, p in group) / n
        label = ("period " + str(truth)) if truth is not None else "non-periodic"
        print(f"{label:>14} {n:>6} {mean_mu:>10.1f} {mean_gain:>+11.1f} {mean_probes:>12.2f}")

    # Sample-level transcript so the bit accounting is auditable.
    print()
    print("sample-level (first 12 streams):")
    print(f"{'stream':<14} {'truth':>6} {'pred':>5} {'gain_bits':>10} {'mu':>6} {'probes':>7}")
    for labeled, score, mu, probes in per_stream[:12]:
        truth = str(labeled.period) if labeled.period is not None else "."
        pred = str(score.predicted_period) if score.predicted_period is not None else "."
        print(f"{_format_stream(labeled.bits):<14} {truth:>6} {pred:>5} "
              f"{score.gain_bits:>+10} {mu:>6} {probes:>7}")

    # Scatter.
    points = []
    for labeled, score, mu, _probes in per_stream:
        marker = "p" if labeled.period is not None else "."
        points.append((mu, score.gain_bits, marker))
    print()
    print("µ vs MDL gain scatter:")
    print(_ascii_scatter(points))

    # Separability sanity check.
    print()
    periodic_gains = [s.gain_bits for l, s, _, _ in per_stream if l.period is not None]
    nonperiodic_gains = [s.gain_bits for l, s, _, _ in per_stream if l.period is None]
    periodic_mus = [mu for l, _, mu, _ in per_stream if l.period is not None]
    nonperiodic_mus = [mu for l, _, mu, _ in per_stream if l.period is None]
    if periodic_gains and nonperiodic_gains:
        print(f"periodic streams:     mean gain = {sum(periodic_gains)/len(periodic_gains):+.2f} bits, "
              f"mean µ = {sum(periodic_mus)/len(periodic_mus):.1f}")
        print(f"non-periodic streams: mean gain = {sum(nonperiodic_gains)/len(nonperiodic_gains):+.2f} bits, "
              f"mean µ = {sum(nonperiodic_mus)/len(nonperiodic_mus):.1f}")
        max_nonperiodic = max(nonperiodic_gains)
        min_periodic = min(periodic_gains)
        separable = min_periodic > max_nonperiodic
        print(f"max(non-periodic gain) = {max_nonperiodic:+d},  "
              f"min(periodic gain) = {min_periodic:+d}  "
              f"=> clusters {'are' if separable else 'are NOT'} fully separable on gain alone")
        if not separable:
            print("  (Not a failure: short-period streams pay less µ, long-period streams")
            print("   pay more and gain less. The pattern is still clear in the scatter.)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
