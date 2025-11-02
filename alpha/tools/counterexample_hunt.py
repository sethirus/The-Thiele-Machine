"""Automated counterexample hunts for the falsifiability dashboard.

This helper orchestrates targeted Landauer and cross-domain experiments that
stress the current falsifiable predictions.  The script intentionally favours
lightweight configurations so that auditors can regenerate the artefacts during
CI yet still gather meaningful evidence.

Running the module as a CLI will materialise proofpack-ready artefacts under
``artifacts/experiments/counterexample-hunts/proofpack`` and emit a short JSON
summary to stdout.  The summary is also persisted alongside the artefacts for
future inspection.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
import csv
import json
import argparse
from pathlib import Path
from typing import Mapping, Sequence

from experiments import ledger_io
from experiments.run_cross_domain import CrossDomainConfig, run_cross_domain
from experiments.run_landauer import LandauerConfig, TrialSummary, run_landauer
from tools import falsifiability_analysis

DEFAULT_OUTPUT = Path("artifacts/experiments/counterexample-hunts")


@dataclass(slots=True)
class LandauerHuntResult:
    """Aggregated diagnostics for the Landauer counterexample search."""

    min_margin_bits: float
    max_mu_bits: float
    min_work_bits: float
    trials_analyzed: int


@dataclass(slots=True)
class CrossDomainHuntResult:
    """Diagnostics for the deep compositional cross-domain sweep."""

    mean_blind_runtime: float
    mean_sighted_runtime: float
    final_runtime_ratio: float
    domains: Sequence[str]
    modules: int
    domain_runtime_ratios: Mapping[str, float]


@dataclass(slots=True)
class HuntSummary:
    landauer: LandauerHuntResult
    cross_domain: CrossDomainHuntResult

    def to_json(self) -> str:
        return json.dumps(
            {
                "landauer": asdict(self.landauer),
                "cross_domain": asdict(self.cross_domain),
            },
            indent=2,
            sort_keys=True,
        )


def _landauer_output_root(base: Path) -> Path:
    return base / "proofpack" / "landauer" / "min_work"


def _cross_domain_output_root(base: Path) -> Path:
    return base / "proofpack" / "cross_domain"


def _ensure_clean_dir(path: Path) -> None:
    path.mkdir(parents=True, exist_ok=True)


def _write_summary_csv(path: Path, summaries: Sequence[Mapping[str, str]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(summaries[0].keys()) if summaries else [])
        if summaries:
            writer.writeheader()
            writer.writerows(summaries)


def _write_metadata(path: Path, metadata: Mapping[str, object], digest: str) -> None:
    payload = dict(metadata)
    payload["ledger_digest_sha256"] = digest
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")


def _domain_runtime_ratios(base: Path) -> dict[str, float]:
    sighted_rows: dict[tuple[str, int], float] = {}
    blind_rows: dict[tuple[str, int], float] = {}

    with (base / "sighted" / "cross_domain_summary.csv").open(encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            sighted_rows[(row["domain"], int(row["trial_id"]))] = float(row["runtime_total"])

    with (base / "blind" / "cross_domain_summary.csv").open(encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            blind_rows[(row["domain"], int(row["trial_id"]))] = float(row["runtime_total"])

    ratios: dict[str, list[float]] = {}
    for key, blind_total in blind_rows.items():
        sighted_total = sighted_rows.get(key)
        if sighted_total is None:
            continue
        domain = key[0]
        ratios.setdefault(domain, []).append(blind_total / sighted_total if sighted_total else float("inf"))

    return {domain: sum(values) / len(values) for domain, values in ratios.items() if values}


def run_landauer_hunt(output_root: Path) -> LandauerHuntResult:
    base = _landauer_output_root(output_root)
    summaries: list[TrialSummary] = []
    for protocol in ("sighted", "blind"):
        result_dir = base / protocol
        _ensure_clean_dir(result_dir)
        config = LandauerConfig(
            output_dir=result_dir,
            seeds=[0, 1],
            temps=[0.35, 0.5],
            trials_per_condition=12,
            protocol=protocol,
            steps=36,
            coupling=0.7,
            bias_final=0.15,
        )
        run_result = run_landauer(config)
        ledger_path = result_dir / "landauer_steps.jsonl"
        summary_path = result_dir / "landauer_summary.csv"
        metadata_path = result_dir / "landauer_metadata.json"

        ledger_io.dump_ledger(run_result.ledger_rows, ledger_path)
        digest = ledger_io.ledger_digest(ledger_io.load_ledger(ledger_path))
        rows = [summary.as_row() for summary in run_result.summaries]
        _write_summary_csv(summary_path, rows)
        _write_metadata(metadata_path, run_result.metadata, digest)

        summaries.extend(run_result.summaries)

    min_margin = float("inf")
    max_mu = 0.0
    min_work_bits = float("inf")
    for summary in summaries:
        work_bits = summary.work_over_kTln2
        margin = work_bits - summary.sum_mu_bits
        min_margin = min(min_margin, margin)
        max_mu = max(max_mu, summary.sum_mu_bits)
        min_work_bits = min(min_work_bits, work_bits)

    return LandauerHuntResult(
        min_margin_bits=min_margin,
        max_mu_bits=max_mu,
        min_work_bits=min_work_bits,
        trials_analyzed=len(summaries),
    )


def run_cross_domain_hunt(output_root: Path) -> CrossDomainHuntResult:
    base = _cross_domain_output_root(output_root)
    protocols = ("sighted", "blind", "destroyed")
    for protocol in protocols:
        result_dir = base / protocol
        _ensure_clean_dir(result_dir)
        config = CrossDomainConfig(
            output_dir=result_dir,
            seeds=[0, 1],
            trials_per_condition=4,
            modules=14,
            protocol=protocol,
            domains=("compression", "ldpc", "sql"),
            mu_base=0.24,
            mu_jitter=0.03,
            runtime_base=1.0,
            runtime_scale=0.9,
        )
        run_result = run_cross_domain(config)
        ledger_path = result_dir / "cross_domain_steps.jsonl"
        summary_path = result_dir / "cross_domain_summary.csv"
        metadata_path = result_dir / "cross_domain_metadata.json"

        ledger_io.dump_ledger(run_result.ledger_rows, ledger_path)
        digest = ledger_io.ledger_digest(ledger_io.load_ledger(ledger_path))
        _write_summary_csv(summary_path, [summary.as_row() for summary in run_result.summaries])
        _write_metadata(metadata_path, run_result.metadata, digest)

    stats = falsifiability_analysis.analyze_cross_domain(output_root)
    if stats is None:
        raise RuntimeError("Cross-domain hunt failed to produce analyzable ledgers")
    sighted = stats.sighted_runtime
    blind = stats.blind_runtime
    ratios = _domain_runtime_ratios(base)
    return CrossDomainHuntResult(
        mean_blind_runtime=blind.mean_final_runtime,
        mean_sighted_runtime=sighted.mean_final_runtime,
        final_runtime_ratio=stats.final_runtime_ratio,
        domains=("compression", "ldpc", "sql"),
        modules=14,
        domain_runtime_ratios=ratios,
    )


def execute_hunts(output_root: Path | None = None) -> HuntSummary:
    base = output_root or DEFAULT_OUTPUT
    landauer = run_landauer_hunt(base)
    cross_domain = run_cross_domain_hunt(base)
    summary = HuntSummary(landauer=landauer, cross_domain=cross_domain)
    summary_path = base / "analysis" / "summary.json"
    summary_path.parent.mkdir(parents=True, exist_ok=True)
    summary_path.write_text(summary.to_json() + "\n", encoding="utf-8")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description="Run targeted counterexample hunts")
    parser.add_argument(
        "--output-root",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Directory in which proofpack artefacts should be written",
    )
    args = parser.parse_args()
    summary = execute_hunts(output_root=args.output_root)
    print(summary.to_json())


if __name__ == "__main__":
    main()
