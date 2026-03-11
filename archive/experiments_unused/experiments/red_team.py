"""Deterministic adversarial perturbations for the red-team battery."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Dict, Iterable, List, MutableMapping, Tuple

from experiments import ledger_io
from experiments.run_cross_domain import (
    _summaries_from_rows as cross_domain_summaries,
    _write_summary as write_cross_domain_summary,
)
from experiments.run_entropy import (
    _summaries_from_rows as entropy_summaries,
    _write_series_csv as write_entropy_series,
    _write_summary_csv as write_entropy_summary,
)
from experiments.run_cwd import (
    _summaries_from_ledger as cwd_summaries_from_ledger,
    _write_summary as write_cwd_summary,
)


def _load_metadata(path: Path) -> Dict[str, object]:
    if path.exists():
        with path.open("r", encoding="utf-8") as handle:
            return json.load(handle)
    return {}


def _write_metadata(path: Path, metadata: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        json.dump(metadata, handle, indent=2, sort_keys=True)
        handle.write("\n")


def _canonical_rows(entries: Iterable[ledger_io.LedgerEntry]) -> List[MutableMapping[str, object]]:
    return [dict(entry.payload) for entry in entries]


def structure_ablation(source: Path, destination: Path) -> Path:
    """Ablate structural cues in a cross-domain run so sighted flatness fails."""

    source = Path(source)
    destination = Path(destination)
    destination.mkdir(parents=True, exist_ok=True)

    ledger_path = source / "cross_domain_steps.jsonl"
    entries = ledger_io.load_ledger(ledger_path)
    mutated_rows: List[MutableMapping[str, object]] = []
    mu_state: Dict[Tuple[int, str, int], float] = {}
    runtime_state: Dict[Tuple[int, str, int], float] = {}

    for entry in entries:
        row = dict(entry.payload)
        key = (int(row["seed"]), str(row["domain"]), int(row["trial_id"]))
        mu_increment = float(row.get("mu_answer", 0.0))
        mu_total = mu_state.get(key, 0.0) + mu_increment
        mu_state[key] = mu_total
        runtime_increment = abs(mu_total) * 4.0 + (int(row.get("module_index", 0)) + 1) * 0.25
        runtime_total = runtime_state.get(key, 0.0) + runtime_increment
        runtime_state[key] = runtime_total
        row["mu_cumulative"] = mu_total
        row["runtime_increment"] = runtime_increment
        row["runtime_cumulative"] = runtime_total
        row["structure_integrity"] = 0.2
        mutated_rows.append(row)

    mutated_ledger = destination / "cross_domain_steps.jsonl"
    ledger_io.dump_ledger(mutated_rows, mutated_ledger)

    canonical_entries = ledger_io.load_ledger(mutated_ledger)
    summaries = cross_domain_summaries(_canonical_rows(canonical_entries))
    summary_path = destination / "cross_domain_summary.csv"
    write_cross_domain_summary(summary_path, summaries)

    metadata_path = destination / "cross_domain_metadata.json"
    metadata = _load_metadata(source / "cross_domain_metadata.json")
    metadata.update(
        {
            "ledger_digest_sha256": ledger_io.ledger_digest(canonical_entries),
            "red_team_attack": "structure_ablation",
        }
    )
    _write_metadata(metadata_path, metadata)
    return destination


def scramble_entropy(source: Path, destination: Path) -> Path:
    """Scramble mid-run entropy signals to break the correlation checks."""

    source = Path(source)
    destination = Path(destination)
    destination.mkdir(parents=True, exist_ok=True)

    ledger_path = source / "entropy_steps.jsonl"
    entries = ledger_io.load_ledger(ledger_path)
    grouped: Dict[Tuple[int, float, int, str], List[MutableMapping[str, object]]] = {}
    for entry in entries:
        row = dict(entry.payload)
        key = (
            int(row["seed"]),
            float(row["T"]),
            int(row["trial_id"]),
            str(row.get("protocol", "unknown")),
        )
        grouped.setdefault(key, []).append(row)

    scrambled_rows: List[MutableMapping[str, object]] = []
    for key, rows in grouped.items():
        pivot = max(1, len(rows) // 2)
        mu_flip = -1.0
        entropy_scale = 0.5
        for index, row in enumerate(rows):
            mu_value = float(row.get("mu_answer", 0.0))
            entropy_value = float(row.get("entropy_delta", 0.0))
            if index >= pivot:
                mu_value = mu_flip * abs(mu_value)
                entropy_value = -abs(entropy_value) - 0.75 * abs(mu_value)
            else:
                entropy_value *= entropy_scale
            row["mu_answer"] = mu_value
            row["entropy_delta"] = entropy_value
            scrambled_rows.append(row)

    mutated_ledger = destination / "entropy_steps.jsonl"
    ledger_io.dump_ledger(scrambled_rows, mutated_ledger)

    canonical_entries = ledger_io.load_ledger(mutated_ledger)
    summary_objs, series_rows = entropy_summaries(_canonical_rows(canonical_entries))
    summary_path = destination / "entropy_summary.csv"
    series_path = destination / "entropy_series.csv"
    write_entropy_summary(summary_path, summary_objs)
    write_entropy_series(series_path, series_rows)

    metadata_path = destination / "entropy_metadata.json"
    metadata = _load_metadata(source / "entropy_metadata.json")
    metadata.update(
        {
            "ledger_digest_sha256": ledger_io.ledger_digest(canonical_entries),
            "red_team_attack": "coarse_grain_scramble",
        }
    )
    _write_metadata(metadata_path, metadata)
    return destination


def worst_order_schedule(source: Path, destination: Path) -> Path:
    """Degrade blind CWD runs so the penalty inequality no longer holds."""

    source = Path(source)
    destination = Path(destination)
    destination.mkdir(parents=True, exist_ok=True)

    ledger_path = source / "cwd_steps.jsonl"
    entries = ledger_io.load_ledger(ledger_path)
    work_state: Dict[Tuple[int, float, int], float] = {}

    mutated_rows: List[MutableMapping[str, object]] = []
    for entry in entries:
        row = dict(entry.payload)
        key = (
            int(row["seed"]),
            float(row["T"]),
            int(row["trial_id"]),
        )
        mu_increment = float(row.get("mu_answer", 0.0))
        reduced_work = abs(mu_increment) * 0.01
        cumulative = work_state.get(key, 0.0) + reduced_work
        work_state[key] = cumulative
        row["work"] = reduced_work
        row["base_work"] = reduced_work
        row["cumulative_work"] = cumulative
        row["penalty_bits"] = 0.0
        row["policy_success"] = 0
        mutated_rows.append(row)

    mutated_ledger = destination / "cwd_steps.jsonl"
    ledger_io.dump_ledger(mutated_rows, mutated_ledger)

    canonical_entries = ledger_io.load_ledger(mutated_ledger)
    summaries = cwd_summaries_from_ledger(canonical_entries)
    summary_path = destination / "cwd_summary.csv"
    write_cwd_summary(summary_path, summaries)

    metadata_path = destination / "cwd_metadata.json"
    metadata = _load_metadata(source / "cwd_metadata.json")
    metadata.update(
        {
            "ledger_digest_sha256": ledger_io.ledger_digest(canonical_entries),
            "red_team_attack": "worst_order_schedule",
        }
    )
    _write_metadata(metadata_path, metadata)
    return destination


__all__ = [
    "scramble_entropy",
    "structure_ablation",
    "worst_order_schedule",
]

