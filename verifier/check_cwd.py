"""Auditor checks for the compositional work decomposition (CWD) builder."""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, MutableMapping, Optional, Sequence, Tuple

from experiments import ledger_io

K_BOLTZMANN = 1.0
LN2 = math.log(2.0)


TrialKey = Tuple[int, float, int, str]


def _load_summary(summary_path: Path) -> Dict[TrialKey, Mapping[str, str]]:
    if not summary_path.exists():
        raise FileNotFoundError(f"Missing CWD summary CSV: {summary_path}")
    with summary_path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        rows = list(reader)
    if not rows:
        raise ValueError(f"CWD summary CSV is empty: {summary_path}")
    summary: Dict[TrialKey, Mapping[str, str]] = {}
    for row in rows:
        key = (
            int(row["seed"]),
            float(row["T"]),
            int(row["trial_id"]),
            str(row["protocol"]),
        )
        summary[key] = row
    return summary


def _mutual_information_bits(joint_counts: Mapping[int, Mapping[int, int]], total_steps: int) -> float:
    if total_steps == 0:
        return 0.0
    action_totals: Dict[int, int] = {}
    module_totals: Dict[int, int] = {}
    for module, counts in joint_counts.items():
        module_totals[module] = sum(counts.values())
        for action, count in counts.items():
            action_totals[action] = action_totals.get(action, 0) + count
    mi = 0.0
    total = float(total_steps)
    for module, counts in joint_counts.items():
        module_total = module_totals.get(module, 0)
        if module_total == 0:
            continue
        p_module = module_total / total
        for action, count in counts.items():
            if count == 0:
                continue
            p_action = action_totals.get(action, 0) / total
            p_joint = count / total
            if p_action <= 0 or p_module <= 0:
                continue
            ratio = p_joint / (p_module * p_action)
            if ratio <= 0.0:
                continue
            mi += p_joint * math.log2(ratio)
    return mi


def _aggregates_from_ledger(entries: Iterable[ledger_io.LedgerEntry]) -> Dict[TrialKey, MutableMapping[str, float]]:
    aggregates: Dict[TrialKey, MutableMapping[str, float]] = {}
    for entry in entries:
        payload = entry.payload
        key: TrialKey = (
            int(payload["seed"]),
            float(payload["T"]),
            int(payload["trial_id"]),
            str(payload["protocol"]),
        )
        state = aggregates.setdefault(
            key,
            {
                "modules": set(),
                "steps_per_module": {},
                "mu_total": 0.0,
                "work_total": 0.0,
                "penalty_bits": 0.0,
                "success_count": 0.0,
                "joint": {},
                "row_count": 0,
            },
        )
        module = int(payload["module"])
        policy_action = int(payload["policy_action"])
        state["modules"].add(module)
        steps_map = state["steps_per_module"]
        steps_map[module] = steps_map.get(module, 0) + 1
        state["mu_total"] += float(payload.get("mu_answer", 0.0))
        state["work_total"] += float(payload.get("work", 0.0))
        state["penalty_bits"] += float(payload.get("penalty_bits", 0.0))
        state["success_count"] += int(payload.get("policy_success", 0))
        joint = state["joint"].setdefault(module, {})
        joint[policy_action] = joint.get(policy_action, 0) + 1
        state["row_count"] += 1
    if not aggregates:
        raise ValueError("No ledger rows found for CWD run")
    return aggregates


def _verify_metadata(metadata_path: Path, ledger_entries: Sequence[ledger_io.LedgerEntry]) -> bool:
    if not metadata_path.exists():
        raise FileNotFoundError(f"Missing CWD metadata JSON: {metadata_path}")
    with metadata_path.open("r", encoding="utf-8") as handle:
        metadata = json.load(handle)
    expected = metadata.get("ledger_digest_sha256")
    actual = ledger_io.ledger_digest(ledger_entries)
    return expected == actual


def _load_run(run_dir: Optional[Path]) -> Tuple[Optional[Dict[TrialKey, Mapping[str, str]]], Optional[Dict[TrialKey, MutableMapping[str, float]]], Optional[List[ledger_io.LedgerEntry]], bool]:
    if run_dir is None:
        return None, None, None, False
    run_dir = Path(run_dir)
    ledger_path = run_dir / "cwd_steps.jsonl"
    summary_path = run_dir / "cwd_summary.csv"
    metadata_path = run_dir / "cwd_metadata.json"
    if not ledger_path.exists():
        raise FileNotFoundError(f"Missing CWD ledger: {ledger_path}")
    ledger_entries = list(ledger_io.load_ledger(ledger_path))
    summary_rows = _load_summary(summary_path)
    aggregates = _aggregates_from_ledger(ledger_entries)
    metadata_ok = _verify_metadata(metadata_path, ledger_entries)
    return summary_rows, aggregates, ledger_entries, metadata_ok


def verify_cwd(
    sighted_dir: Path,
    blind_dir: Path,
    destroyed_dir: Path | None = None,
    epsilon: float = 0.05,
    eta: float = 0.05,
    out_path: Path | None = None,
) -> Tuple[Path, Mapping[str, object]]:
    """Validate compositional work decomposition outputs across protocols."""

    sighted_summary, sighted_aggregates, sighted_ledger, sighted_metadata_ok = _load_run(Path(sighted_dir))
    blind_summary, blind_aggregates, blind_ledger, blind_metadata_ok = _load_run(Path(blind_dir))
    destroyed_summary: Optional[Dict[TrialKey, Mapping[str, str]]] = None
    destroyed_aggregates: Optional[Dict[TrialKey, MutableMapping[str, float]]] = None
    destroyed_metadata_ok = True
    if destroyed_dir is not None:
        destroyed_summary, destroyed_aggregates, _, destroyed_metadata_ok = _load_run(Path(destroyed_dir))

    trials: List[Dict[str, object]] = []
    penalty_checks: List[Dict[str, object]] = []

    status = sighted_metadata_ok and blind_metadata_ok and destroyed_metadata_ok

    for key, summary in sighted_summary.items():
        aggregate = sighted_aggregates.get(key) if sighted_aggregates else None
        if aggregate is None:
            status = False
            trials.append(
                {
                    "key": {
                        "seed": key[0],
                        "T": key[1],
                        "trial_id": key[2],
                        "protocol": key[3],
                    },
                    "error": "missing_sighted_ledger_rows",
                }
            )
            continue

        mu_summary = float(summary["mu_total_bits"])
        work_summary = float(summary["work"])
        work_bits_summary = float(summary["work_over_kTln2"])
        penalty_summary = float(summary["penalty_bits_total"])
        mi_summary = float(summary["mutual_information_bits"])
        success_summary = float(summary["success_rate"])

        mu_ledger = float(aggregate["mu_total"])
        work_ledger = float(aggregate["work_total"])
        penalty_ledger = float(aggregate["penalty_bits"])
        success_rate = (
            float(aggregate["success_count"]) / aggregate["row_count"]
            if aggregate["row_count"]
            else 0.0
        )
        mi_ledger = _mutual_information_bits(aggregate["joint"], int(aggregate["row_count"]))

        temperature = key[1]
        kTln2 = K_BOLTZMANN * temperature * LN2
        work_bits_ledger = work_ledger / kTln2 if kTln2 else float("inf")
        diff_bits = abs(work_bits_ledger - mu_ledger)
        within_tolerance = diff_bits <= epsilon

        trial_result = {
            "key": {
                "seed": key[0],
                "T": temperature,
                "trial_id": key[2],
                "protocol": key[3],
            },
            "mu_summary": mu_summary,
            "mu_ledger": mu_ledger,
            "work_bits_summary": work_bits_summary,
            "work_bits_ledger": work_bits_ledger,
            "penalty_bits_summary": penalty_summary,
            "penalty_bits_ledger": penalty_ledger,
            "mutual_information_summary": mi_summary,
            "mutual_information_ledger": mi_ledger,
            "success_rate_summary": success_summary,
            "success_rate_ledger": success_rate,
            "within_tolerance": within_tolerance,
            "summary_matches_ledger": all(
                abs(a - b) <= 5e-6 * max(1.0, abs(b))
                for a, b in [
                    (mu_summary, mu_ledger),
                    (work_summary, work_ledger),
                    (penalty_summary, penalty_ledger),
                    (mi_summary, mi_ledger),
                    (success_summary, success_rate),
                ]
            ),
        }
        trials.append(trial_result)
        if not (trial_result["within_tolerance"] and trial_result["summary_matches_ledger"]):
            status = False

    def _base_key_map(summary: Dict[TrialKey, Mapping[str, str]]) -> Dict[Tuple[int, float, int], TrialKey]:
        return {(k[0], k[1], k[2]): k for k in summary.keys()}

    sighted_base = _base_key_map(sighted_summary)
    blind_base = _base_key_map(blind_summary)

    shared_bases = set(sighted_base.keys()) & set(blind_base.keys())
    for base_key in sorted(shared_bases):
        sighted_key = sighted_base[base_key]
        blind_key = blind_base[base_key]
        sighted = sighted_summary[sighted_key]
        blind = blind_summary[blind_key]
        temperature = base_key[1]
        kTln2 = K_BOLTZMANN * temperature * LN2

        sighted_work = float(sighted["work"])
        blind_work = float(blind["work"])
        diff_bits = (blind_work - sighted_work) / kTln2 if kTln2 else float("inf")

        sighted_mi = float(sighted["mutual_information_bits"])
        blind_penalty = float(blind["penalty_bits_total"])

        aggregate_blind = blind_aggregates.get(blind_key) if blind_aggregates else None
        penalty_match = True
        if aggregate_blind is not None:
            penalty_match = math.isclose(
                blind_penalty,
                float(aggregate_blind["penalty_bits"]),
                rel_tol=5e-6,
                abs_tol=5e-6,
            )
        else:
            penalty_match = False

        penalty_result = {
            "key": {
                "seed": base_key[0],
                "T": temperature,
                "trial_id": base_key[2],
            },
            "diff_bits": diff_bits,
            "mutual_information_bits": sighted_mi,
            "penalty_bits_blind": blind_penalty,
            "penalty_matches_ledger": penalty_match,
            "penalty_bound_holds": diff_bits + eta >= sighted_mi,
        }
        penalty_checks.append(penalty_result)
        if not (penalty_result["penalty_bound_holds"] and penalty_result["penalty_matches_ledger"]):
            status = False

    if destroyed_summary and destroyed_aggregates:
        # Ensure destroyed runs reflect degraded routing (success rate well below 1.0).
        for key, summary in destroyed_summary.items():
            aggregate = destroyed_aggregates.get(key)
            if aggregate is None:
                status = False
                continue
            success_rate = (
                float(aggregate["success_count"]) / aggregate["row_count"]
                if aggregate["row_count"]
                else 0.0
            )
            if success_rate > 0.75:
                status = False
                penalty_checks.append(
                    {
                        "key": {
                            "seed": key[0],
                            "T": key[1],
                            "trial_id": key[2],
                        },
                        "error": "destroyed_success_rate_too_high",
                        "success_rate": success_rate,
                    }
                )

    result: Dict[str, object] = {
        "status": status,
        "epsilon": epsilon,
        "eta": eta,
        "metadata_digest_matches": {
            "sighted": sighted_metadata_ok,
            "blind": blind_metadata_ok,
            "destroyed": destroyed_metadata_ok,
        },
        "sighted_trials": trials,
        "penalty_checks": penalty_checks,
    }

    out_path = out_path or Path("verifier/cwd_verifier.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2, sort_keys=True)
        handle.write("\n")
    return out_path, result


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Verify CWD outputs across protocols")
    parser.add_argument("--sighted", type=Path, required=True, help="Directory for sighted protocol outputs")
    parser.add_argument("--blind", type=Path, required=True, help="Directory for blind protocol outputs")
    parser.add_argument("--destroyed", type=Path, default=None, help="Optional directory for destroyed protocol outputs")
    parser.add_argument("--epsilon", type=float, default=0.05, help="Tolerance for sighted work equality")
    parser.add_argument("--eta", type=float, default=0.05, help="Margin for the penalty inequality")
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("verifier/cwd_verifier.json"),
        help="Path to write verifier JSON",
    )
    return parser


def main(argv: Iterable[str] | None = None) -> None:  # pragma: no cover - CLI wrapper
    parser = _build_parser()
    args = parser.parse_args(argv)
    out_path, _ = verify_cwd(
        sighted_dir=args.sighted,
        blind_dir=args.blind,
        destroyed_dir=args.destroyed,
        epsilon=args.epsilon,
        eta=args.eta,
        out_path=args.out,
    )
    print(f"Wrote verifier JSON: {out_path}")


if __name__ == "__main__":  # pragma: no cover - script entry point
    main()

