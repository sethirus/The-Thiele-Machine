"""Utilities for probing the falsifiable predictions shipped with the repo.

The Thiele Machine now exposes two quantitative statements that external
auditors can try to break:

* **Landauer work inequality.**  Every canonical question that shrinks an
  effective search space must pay at least ``8|canon(q)| + log₂(N/M)`` μ-bits of
  effort, which for physical processes translates into a Landauer-style lower
  bound on expended work.
* **Sighted vs. blind scaling gap.**  Solvers that know the true composition
  should keep μ-cost nearly constant as problem depth grows, while blind solvers
  pay super-polynomially.

This module pulls metrics out of the archived experiment proofpacks so we can
check those falsifiable forms against the public data.  It intentionally avoids
any heavy computation – only ledger parsing – so that unit tests and auditors
can run it without reproducing the experiments from scratch.
"""

from __future__ import annotations

from dataclasses import dataclass
import argparse
import json
import math
from pathlib import Path
import statistics
from typing import Dict, Iterable, Iterator, List, Mapping, Sequence, Tuple


SUMMARY_START_MARKER = "<!-- FALSIFIABILITY_SUMMARY_START -->"
SUMMARY_END_MARKER = "<!-- FALSIFIABILITY_SUMMARY_END -->"


# ---------------------------------------------------------------------------
# Dataclasses capturing the statistics we care about.


@dataclass(slots=True)
class LandauerTrial:
    """Summary of a single Landauer trial."""

    run_dir: Path
    seed: int
    temperature: float
    trial_id: int
    protocol: str
    mu_sum: float
    work_bits: float

    @property
    def margin(self) -> float:
        """Return ``work_bits - mu_sum`` (positive = comfortable margin)."""

        return self.work_bits - self.mu_sum


@dataclass(slots=True)
class LandauerStats:
    """Aggregated Landauer falsifiability metrics."""

    epsilon: float
    trials: List[LandauerTrial]

    @property
    def run_count(self) -> int:
        return len({trial.run_dir for trial in self.trials})

    @property
    def trial_count(self) -> int:
        return len(self.trials)

    @property
    def min_margin(self) -> float:
        if not self.trials:
            return math.inf
        return min(trial.margin for trial in self.trials)

    @property
    def worst_violation(self) -> float:
        """Return the maximum deficit after granting the ε slack."""

        if not self.trials:
            return 0.0
        return max(trial.mu_sum - trial.work_bits - self.epsilon for trial in self.trials)


@dataclass(slots=True)
class RuntimeProfile:
    """Runtime distribution for a specific protocol."""

    final_runtimes: List[float]
    module_means: Mapping[int, float]

    @property
    def mean_final_runtime(self) -> float:
        return statistics.mean(self.final_runtimes)

    @property
    def max_final_runtime(self) -> float:
        return max(self.final_runtimes)

    @property
    def min_final_runtime(self) -> float:
        return min(self.final_runtimes)


@dataclass(slots=True)
class TurbulenceStats:
    """Runtime scaling metrics for the turbulence proofpack ledgers."""

    profiles: Mapping[str, RuntimeProfile]

    def ratio(self, numerator: str, denominator: str) -> float:
        num = self.profiles[numerator].mean_final_runtime
        den = self.profiles[denominator].mean_final_runtime
        return num / den if den else math.inf

    def module_ratios(self, numerator: str, denominator: str) -> Dict[int, float]:
        ratios: Dict[int, float] = {}
        num_profile = self.profiles[numerator]
        den_profile = self.profiles[denominator]
        for module_id, num_mean in num_profile.module_means.items():
            den_mean = den_profile.module_means.get(module_id, 0.0)
            ratios[module_id] = num_mean / den_mean if den_mean else math.inf
        return ratios


@dataclass(slots=True)
class CrossDomainStats:
    """Sighted vs. blind runtime comparison for the cross-domain run."""

    sighted_runtime: RuntimeProfile
    blind_runtime: RuntimeProfile

    @property
    def final_runtime_ratio(self) -> float:
        den = self.sighted_runtime.mean_final_runtime
        return self.blind_runtime.mean_final_runtime / den if den else math.inf


# ---------------------------------------------------------------------------
# Landauer analysis helpers.


def _iter_landauer_ledgers(root: Path) -> Iterator[Path]:
    for path in root.glob("**/landauer_steps.jsonl"):
        if "proofpack" not in path.parts:
            continue
        yield path


def _collect_landauer_trials(ledger_path: Path) -> Iterable[LandauerTrial]:
    metadata_path = ledger_path.with_name("landauer_metadata.json")
    if not metadata_path.exists():
        raise FileNotFoundError(f"Missing metadata for ledger {ledger_path}")
    metadata = json.loads(metadata_path.read_text())
    k_b = float(metadata.get("k_B", 1.0))
    ln2 = float(metadata.get("ln2", math.log(2.0)))

    aggregates: Dict[Tuple[int, float, int, str], Dict[str, float]] = {}
    with ledger_path.open("r", encoding="utf-8") as handle:
        for line in handle:
            payload = json.loads(line)
            key = (
                int(payload["seed"]),
                float(payload["T"]),
                int(payload["trial_id"]),
                str(payload.get("protocol", metadata.get("protocol", "unknown"))),
            )
            state = aggregates.setdefault(
                key,
                {
                    "mu_sum": 0.0,
                    "work": 0.0,
                },
            )
            state["mu_sum"] += float(payload.get("mu_answer", 0.0))
            state["work"] = float(payload.get("cumulative_work", state["work"]))

    for (seed, temperature, trial_id, protocol), state in aggregates.items():
        kTln2 = k_b * temperature * ln2
        work_bits = state["work"] / kTln2 if kTln2 else math.inf
        yield LandauerTrial(
            run_dir=ledger_path.parent,
            seed=seed,
            temperature=temperature,
            trial_id=trial_id,
            protocol=protocol,
            mu_sum=state["mu_sum"],
            work_bits=work_bits,
        )


def analyze_landauer(root: Path, epsilon: float = 0.05) -> LandauerStats:
    """Aggregate Landauer work margins across archived runs."""

    trials: List[LandauerTrial] = []
    for ledger_path in _iter_landauer_ledgers(root):
        trials.extend(_collect_landauer_trials(ledger_path))
    return LandauerStats(epsilon=epsilon, trials=trials)


# ---------------------------------------------------------------------------
# Turbulence ledger helpers.


def _iter_turbulence_ledger_dirs(root: Path) -> Iterator[Path]:
    for ledger in root.glob("**/turbulence/**/ledgers/sighted.jsonl"):
        if "proofpack" not in ledger.parts:
            continue
        yield ledger.parent


def _load_runtime_profile(ledger_path: Path) -> RuntimeProfile:
    final_by_point: Dict[Tuple[object, object, object], List[Tuple[int, float]]] = {}
    module_aggs: Dict[int, List[float]] = {}
    with ledger_path.open("r", encoding="utf-8") as handle:
        for line in handle:
            payload = json.loads(line)
            key = (
                payload.get("dataset"),
                payload.get("point_index"),
                payload.get("time_index"),
            )
            module_id = int(payload["module_id"])
            final_by_point.setdefault(key, []).append((module_id, float(payload["runtime_cumulative"])))
            module_aggs.setdefault(module_id, []).append(float(payload["runtime_increment"]))

    final_runtimes = []
    for modules in final_by_point.values():
        modules.sort(key=lambda item: item[0])
        final_runtimes.append(modules[-1][1])

    module_means = {module: statistics.mean(values) for module, values in module_aggs.items()}
    return RuntimeProfile(final_runtimes=final_runtimes, module_means=module_means)


def analyze_turbulence(root: Path) -> TurbulenceStats | None:
    """Summarise blind vs sighted runtime growth from turbulence ledgers."""

    # Each ledger directory should contain blind/sighted/destroyed jsonl files.
    for ledger_dir in _iter_turbulence_ledger_dirs(root):
        profiles = {}
        for protocol in ("sighted", "blind", "destroyed"):
            ledger_path = ledger_dir / f"{protocol}.jsonl"
            if not ledger_path.exists():
                break
            profiles[protocol] = _load_runtime_profile(ledger_path)
        else:
            return TurbulenceStats(profiles=profiles)
    return None


# ---------------------------------------------------------------------------
# Cross-domain comparison (shallow depth but still informative).


def _load_cross_domain_profile(path: Path) -> RuntimeProfile:
    final_by_trial: Dict[Tuple[int, int, str], List[Tuple[int, float]]] = {}
    module_aggs: Dict[int, List[float]] = {}
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            payload = json.loads(line)
            key = (
                int(payload["seed"]),
                int(payload["trial_id"]),
                str(payload.get("domain", "")),
            )
            module_index = int(payload["module_index"])
            final_by_trial.setdefault(key, []).append((module_index, float(payload["runtime_cumulative"])))
            module_aggs.setdefault(module_index, []).append(float(payload["runtime_increment"]))

    finals = []
    for modules in final_by_trial.values():
        modules.sort(key=lambda item: item[0])
        finals.append(modules[-1][1])

    module_means = {module: statistics.mean(values) for module, values in module_aggs.items()}
    return RuntimeProfile(final_runtimes=finals, module_means=module_means)


def analyze_cross_domain(root: Path) -> CrossDomainStats | None:
    sighted_path = None
    blind_path = None
    for candidate in root.glob("**/cross_domain/sighted/cross_domain_steps.jsonl"):
        if "proofpack" in candidate.parts:
            sighted_path = candidate
            break
    for candidate in root.glob("**/cross_domain/blind/cross_domain_steps.jsonl"):
        if "proofpack" in candidate.parts:
            blind_path = candidate
            break
    if not (sighted_path and blind_path):
        return None
    return CrossDomainStats(
        sighted_runtime=_load_cross_domain_profile(sighted_path),
        blind_runtime=_load_cross_domain_profile(blind_path),
    )


# ---------------------------------------------------------------------------
# Human-readable report plumbing.


def _format_landauer(stats: LandauerStats) -> str:
    if not stats.trials:
        return "Landauer: no trials discovered"
    lines = [
        "Landauer work inequality:",
        f"  runs analysed: {stats.run_count}",
        f"  trials analysed: {stats.trial_count}",
        f"  min(W/kTln2 − Σμ): {stats.min_margin:.6f}",
        f"  worst deficit beyond ε={stats.epsilon:.3f}: {max(stats.worst_violation, 0.0):.6f}",
    ]
    return "\n".join(lines)


def _format_turbulence(stats: TurbulenceStats | None) -> str:
    if stats is None:
        return "Turbulence: no ledgers discovered"
    ratio = stats.ratio("blind", "sighted")
    lines = [
        "Turbulence runtime scaling:",
        f"  mean final runtime ratio (blind/sighted): {ratio:.3f}",
    ]
    for module_id, module_ratio in sorted(stats.module_ratios("blind", "sighted").items()):
        lines.append(f"  module {module_id} runtime ratio (blind/sighted): {module_ratio:.3f}")
    return "\n".join(lines)


def _format_cross_domain(stats: CrossDomainStats | None) -> str:
    if stats is None:
        return "Cross-domain runtime comparison: no ledgers discovered"
    ratio = stats.final_runtime_ratio
    lines = [
        "Cross-domain runtime comparison:",
        f"  mean final runtime ratio (blind/sighted): {ratio:.3f}",
    ]
    return "\n".join(lines)


def render_markdown_summary(
    landauer_stats: LandauerStats,
    turbulence_stats: TurbulenceStats | None,
    cross_domain_stats: CrossDomainStats | None,
) -> str:
    """Render a deterministic Markdown table summarising falsifiability probes."""

    def _fmt(value: float | None) -> str:
        if value is None or math.isnan(value):
            return "n/a"
        return f"{value:.3f}"

    rows = [
        "| Probe | Metric | Value |",
        "| --- | --- | --- |",
        f"| Landauer | runs analysed | {landauer_stats.run_count} |",
        f"| Landauer | trials analysed | {landauer_stats.trial_count} |",
        f"| Landauer | min(W/kTln2 − Σμ) | {_fmt(landauer_stats.min_margin)} |",
        f"| Landauer | worst deficit beyond ε={landauer_stats.epsilon:.3f} | {_fmt(max(landauer_stats.worst_violation, 0.0))} |",
    ]

    if turbulence_stats is not None:
        rows.append(
            f"| Turbulence | mean final runtime ratio (blind/sighted) | {_fmt(turbulence_stats.ratio('blind', 'sighted'))} |"
        )
        for module_id, module_ratio in sorted(turbulence_stats.module_ratios("blind", "sighted").items()):
            rows.append(
                f"| Turbulence | module {module_id} runtime ratio (blind/sighted) | {_fmt(module_ratio)} |"
            )
    else:
        rows.append("| Turbulence | ledgers detected | 0 |")

    if cross_domain_stats is not None:
        rows.append(
            f"| Cross-domain | mean final runtime ratio (blind/sighted) | {_fmt(cross_domain_stats.final_runtime_ratio)} |"
        )
    else:
        rows.append("| Cross-domain | ledgers detected | 0 |")

    return "\n".join(rows)


def update_readme_summary(readme_path: Path, summary: str) -> None:
    """Replace the falsifiability summary block inside ``readme_path``."""

    text = readme_path.read_text(encoding="utf-8")
    if SUMMARY_START_MARKER not in text or SUMMARY_END_MARKER not in text:
        raise ValueError(
            f"README at {readme_path} is missing falsifiability markers {SUMMARY_START_MARKER} / {SUMMARY_END_MARKER}"
        )

    before, _, remainder = text.partition(SUMMARY_START_MARKER)
    _, _, after = remainder.partition(SUMMARY_END_MARKER)
    replacement = (
        f"{SUMMARY_START_MARKER}\n"
        f"{summary}\n"
        f"{SUMMARY_END_MARKER}"
    )
    updated = before + replacement + after
    readme_path.write_text(updated, encoding="utf-8")


def run_analysis(
    root: Path,
    epsilon: float,
) -> tuple[str, LandauerStats, TurbulenceStats | None, CrossDomainStats | None]:
    landauer_stats = analyze_landauer(root, epsilon=epsilon)
    turbulence_stats = analyze_turbulence(root)
    cross_domain_stats = analyze_cross_domain(root)

    sections = [
        _format_landauer(landauer_stats),
        _format_turbulence(turbulence_stats),
        _format_cross_domain(cross_domain_stats),
    ]
    return "\n\n".join(sections), landauer_stats, turbulence_stats, cross_domain_stats


def _parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Probe falsifiable predictions using archived ledgers")
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("artifacts/experiments"),
        help="Root directory containing experiment proofpacks",
    )
    parser.add_argument(
        "--epsilon",
        type=float,
        default=0.05,
        help="Tolerance used for the Landauer work inequality",
    )
    parser.add_argument(
        "--write-markdown",
        type=Path,
        help="Optional path to write the Markdown summary table",
    )
    parser.add_argument(
        "--update-readme",
        type=Path,
        help="Path to a README whose falsifiability summary should be updated",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(argv)
    report, landauer_stats, turbulence_stats, cross_domain_stats = run_analysis(args.root, epsilon=args.epsilon)
    print(report)
    if args.write_markdown or args.update_readme:
        summary = render_markdown_summary(landauer_stats, turbulence_stats, cross_domain_stats)
        if args.write_markdown:
            args.write_markdown.write_text(summary + "\n", encoding="utf-8")
        if args.update_readme:
            update_readme_summary(args.update_readme, summary)
    # Treat any positive violation beyond epsilon as a failing exit status.
    if landauer_stats.worst_violation > 0.0:
        return 1
    return 0


if __name__ == "__main__":  # pragma: no cover - exercised via CLI
    raise SystemExit(main())
