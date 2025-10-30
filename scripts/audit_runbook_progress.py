from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Mapping, MutableMapping, Sequence

from experiments.data_sources.download import verify_manifest

SOURCES: tuple[str, ...] = ("osf", "figshare", "dryad", "zenodo")
REQUIRED_LEDGER_PROTOCOLS: tuple[str, ...] = ("sighted", "blind", "destroyed")


def _load_json(path: Path) -> tuple[Mapping[str, object] | None, str | None]:
    try:
        return json.loads(path.read_text(encoding="utf-8")), None
    except FileNotFoundError:
        return None, None
    except json.JSONDecodeError as exc:  # pragma: no cover - defensive guard
        return None, f"Invalid JSON ({exc})"


def _candidate_projects(candidates: Sequence[Mapping[str, object]] | None) -> set[str]:
    projects: set[str] = set()
    if not isinstance(candidates, Sequence):
        return projects
    for candidate in candidates:
        if not isinstance(candidate, Mapping):
            continue
        identifier = candidate.get("node_id") or candidate.get("id")
        if isinstance(identifier, str) and identifier.strip():
            projects.add(identifier.strip())
    return projects


def _audit_candidates(source: str, path: Path) -> MutableMapping[str, object]:
    payload, error = _load_json(path)
    report: MutableMapping[str, object] = {
        "status": "missing",
        "count": 0,
        "issues": [],
    }
    if error:
        report.update({"status": "error", "issues": [error]})
        return report
    if payload is None:
        report["issues"].append(f"Discover {source.upper()} candidates")
        return report

    candidates = payload.get("candidates") if isinstance(payload, Mapping) else None
    if not isinstance(candidates, Sequence):
        report.update({"status": "error", "issues": ["Candidates payload is missing"]})
        return report

    count = sum(1 for candidate in candidates if isinstance(candidate, Mapping))
    report["count"] = count
    if source == "osf":
        projects = _candidate_projects(candidates)
        report["distinct_projects"] = len(projects)
        if count >= 10 and len(projects) >= 3:
            report["status"] = "ok"
        else:
            report["status"] = "insufficient"
            report["issues"].append("Collect >=10 OSF candidates across >=3 projects")
    else:
        if count:
            report["status"] = "ok"
        else:
            report["status"] = "insufficient"
            report["issues"].append(f"Collect candidate datasets for {source.upper()}")
    return report


def _audit_selected(source: str, path: Path) -> MutableMapping[str, object]:
    payload, error = _load_json(path)
    report: MutableMapping[str, object] = {
        "status": "missing",
        "selected": 0,
        "issues": [],
    }
    if error:
        report.update({"status": "error", "issues": [error]})
        return report
    if payload is None:
        report["issues"].append(f"Extract anchors for {source.upper()} candidates")
        return report

    selected = payload.get("selected") if isinstance(payload, Mapping) else None
    if not isinstance(selected, Sequence):
        report.update({"status": "error", "issues": ["Selected payload is missing"]})
        return report

    complete = 0
    issues: list[str] = []
    for entry in selected:
        if not isinstance(entry, Mapping):
            continue
        anchors = entry.get("anchors")
        dataset_label = entry.get("candidate", {}).get("title") if isinstance(entry.get("candidate"), Mapping) else None
        anchor_missing = []
        if not isinstance(anchors, Mapping):
            anchor_missing.append("anchors")
        else:
            for key in ("T_K", "pixel_scale_um_per_px", "frame_interval_s"):
                value = anchors.get(key)
                if value in (None, ""):
                    anchor_missing.append(key)
        if anchor_missing:
            label = dataset_label or entry.get("candidate", {}).get("id")
            issues.append(f"Incomplete anchors ({', '.join(anchor_missing)}) for {label or source}")
        else:
            complete += 1
    report["selected"] = complete
    if issues:
        report.update({"status": "incomplete", "issues": issues})
    elif complete:
        report["status"] = "ok"
    else:
        report.update({"status": "insufficient", "issues": [f"No anchored {source.upper()} datasets selected"]})
    return report


def _audit_mirrors(source: str, root: Path) -> MutableMapping[str, object]:
    base = root / source
    report: MutableMapping[str, object] = {
        "status": "missing",
        "datasets": [],
        "issues": [],
    }
    if not base.exists():
        report["issues"].append(f"Mirror anchored {source.upper()} datasets with manifests")
        return report

    dataset_reports: list[MutableMapping[str, object]] = []
    ok_count = 0
    for dataset_dir in sorted(base.iterdir()):
        if not dataset_dir.is_dir():
            continue
        dataset_status = "ok"
        dataset_issues: list[str] = []
        manifest_path = dataset_dir / "MANIFEST.json"
        if not manifest_path.exists():
            dataset_status = "incomplete"
            dataset_issues.append("Missing MANIFEST.json")
        else:
            try:
                verify_manifest(manifest_path)
            except Exception as exc:  # pragma: no cover - defensive guard
                dataset_status = "incomplete"
                dataset_issues.append(f"Manifest verification failed: {exc}")
        for rel in ("candidate.json", "anchors.json"):
            if not (dataset_dir / rel).exists():
                dataset_status = "incomplete"
                dataset_issues.append(f"Missing {rel}")
        if not (dataset_dir / "raw").exists():
            dataset_status = "incomplete"
            dataset_issues.append("Missing raw/ directory")
        dataset_reports.append(
            {
                "dataset": dataset_dir.name,
                "status": dataset_status,
                "issues": dataset_issues,
            }
        )
        if dataset_status == "ok":
            ok_count += 1
    report["datasets"] = dataset_reports
    if not dataset_reports:
        report.update({"status": "insufficient", "issues": [f"No mirrored {source.upper()} datasets found"]})
    elif ok_count == len(dataset_reports):
        report["status"] = "ok"
    else:
        report["status"] = "incomplete"
        for dataset in dataset_reports:
            if dataset["status"] != "ok":
                report["issues"].append(
                    f"Fix mirrored dataset {source.upper()}:{dataset['dataset']} ({'; '.join(dataset['issues'])})"
                )
    return report


def _audit_proofpacks(source: str, proofpack_dir: Path | None) -> MutableMapping[str, object]:
    report: MutableMapping[str, object] = {
        "status": "missing",
        "datasets": [],
        "issues": [],
        "verifier_flag": False,
    }
    if proofpack_dir is None:
        report["issues"].append(f"Run proofpack pipeline for {source.upper()} datasets")
        return report
    base = proofpack_dir / "public_data" / source
    if not base.exists():
        report["issues"].append(f"Run proofpack pipeline for {source.upper()} datasets")
        return report

    dataset_reports: list[MutableMapping[str, object]] = []
    ok_count = 0
    for dataset_dir in sorted(base.iterdir()):
        if not dataset_dir.is_dir():
            continue
        dataset_status = "ok"
        dataset_issues: list[str] = []
        for rel in ("protocol.json", "summary.json", "public_spt_metadata.json", "oos_metrics.json"):
            if not (dataset_dir / rel).exists():
                dataset_status = "incomplete"
                dataset_issues.append(f"Missing {rel}")
        ledgers_dir = dataset_dir / "ledgers"
        for protocol in REQUIRED_LEDGER_PROTOCOLS:
            ledger_path = ledgers_dir / f"{protocol}.jsonl"
            if not ledger_path.exists():
                dataset_status = "incomplete"
                dataset_issues.append(f"Missing ledger {ledger_path.relative_to(dataset_dir)}")
        verifier_path = dataset_dir / "verifier" / "public_spt.json"
        if not verifier_path.exists():
            dataset_status = "incomplete"
            dataset_issues.append("Missing verifier/public_spt.json")
        else:
            try:
                verifier_payload = json.loads(verifier_path.read_text(encoding="utf-8"))
                if not bool(verifier_payload.get("status")):
                    dataset_status = "incomplete"
                    dataset_issues.append("Verifier reported failure")
            except json.JSONDecodeError as exc:
                dataset_status = "incomplete"
                dataset_issues.append(f"Invalid verifier JSON: {exc}")
        dataset_reports.append(
            {
                "dataset": dataset_dir.name,
                "status": dataset_status,
                "issues": dataset_issues,
            }
        )
        if dataset_status == "ok":
            ok_count += 1
    report["datasets"] = dataset_reports

    verdict_path = proofpack_dir / "verifier" / "THIELE_OK"
    if verdict_path.exists():
        report["verifier_flag"] = True
    else:
        report["issues"].append("Unified verifier THIELE_OK flag missing")

    if not dataset_reports:
        report["status"] = "insufficient"
        report["issues"].append(f"No proofpack datasets for {source.upper()}")
    elif ok_count == len(dataset_reports) and report["verifier_flag"]:
        report["status"] = "ok"
    else:
        report["status"] = "incomplete"
        for dataset in dataset_reports:
            if dataset["status"] != "ok":
                report["issues"].append(
                    f"Complete proofpack artefacts for {source.upper()}:{dataset['dataset']} ({'; '.join(dataset['issues'])})"
                )
    return report


def audit_runbook(
    *,
    sources: Sequence[str] = SOURCES,
    candidates_root: Path,
    selected_root: Path,
    mirror_root: Path,
    proofpack_dir: Path | None,
) -> MutableMapping[str, object]:
    summary: MutableMapping[str, object] = {
        "complete": True,
        "sources": {},
    }
    for source in sources:
        source_summary: MutableMapping[str, object] = {}
        candidates_report = _audit_candidates(source, candidates_root / f"{source}_candidates.json")
        selected_report = _audit_selected(source, selected_root / f"{source}_selected.json")
        mirrors_report = _audit_mirrors(source, mirror_root)
        proofpack_report = _audit_proofpacks(source, proofpack_dir)

        source_summary["candidates"] = candidates_report
        source_summary["selected"] = selected_report
        source_summary["mirrors"] = mirrors_report
        source_summary["proofpack"] = proofpack_report

        outstanding: list[str] = []
        for report in (candidates_report, selected_report, mirrors_report, proofpack_report):
            outstanding.extend(report.get("issues", []))
        source_summary["outstanding"] = outstanding

        source_ok = all(report["status"] == "ok" for report in (candidates_report, selected_report, mirrors_report, proofpack_report))
        source_summary["status"] = "ok" if source_ok else "incomplete"
        summary["complete"] = summary["complete"] and source_ok

        summary["sources"][source] = source_summary

    return summary


def _parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sources", nargs="*", choices=SOURCES, default=list(SOURCES))
    parser.add_argument("--candidates-root", type=Path, default=Path("."))
    parser.add_argument("--selected-root", type=Path, default=Path("."))
    parser.add_argument("--mirror-root", type=Path, default=Path("public_data"))
    parser.add_argument("--proofpack-dir", type=Path)
    parser.add_argument("--output", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(argv)
    proofpack_dir = args.proofpack_dir.resolve() if args.proofpack_dir else None
    summary = audit_runbook(
        sources=args.sources,
        candidates_root=args.candidates_root.resolve(),
        selected_root=args.selected_root.resolve(),
        mirror_root=args.mirror_root.resolve(),
        proofpack_dir=proofpack_dir,
    )
    document = json.dumps(summary, indent=2, sort_keys=True)
    if args.output:
        args.output.write_text(document + "\n", encoding="utf-8")
    print(document)
    return 0


if __name__ == "__main__":  # pragma: no cover - CLI entrypoint
    raise SystemExit(main())
