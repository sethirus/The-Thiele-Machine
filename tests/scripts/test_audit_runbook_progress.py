from __future__ import annotations

import hashlib
import json
from pathlib import Path

from scripts.audit_runbook_progress import audit_runbook


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _create_manifest(dataset_dir: Path) -> None:
    raw_dir = dataset_dir / "raw"
    raw_dir.mkdir(parents=True, exist_ok=True)
    file_path = raw_dir / "tracks.csv"
    file_path.write_text("time,x,y\n0,0,0\n", encoding="utf-8")
    data = file_path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    manifest = {
        "source": "osf",
        "dataset_id": "test",  # identifier not relevant for audit
        "title": "Dataset 0",
        "generated_at": "2025-01-01T00:00:00Z",
        "file_count": 1,
        "files": [
            {
                "path": "raw/tracks.csv",
                "sha256": digest,
                "size": len(data),
            }
        ],
    }
    _write_json(dataset_dir / "MANIFEST.json", manifest)


def test_audit_runbook_complete(tmp_path: Path) -> None:
    candidates_root = tmp_path / "candidates"
    selected_root = tmp_path / "selected"
    mirror_root = tmp_path / "mirrors"
    proofpack_dir = tmp_path / "proofpack"

    candidates = [
        {"node_id": f"node-{index % 3}", "title": f"Dataset {index}", "files": []}
        for index in range(10)
    ]
    _write_json(candidates_root / "osf_candidates.json", {"candidates": candidates})

    selected = [
        {
            "candidate": {"title": "Dataset 0"},
            "anchors": {
                "T_K": 298.15,
                "pixel_scale_um_per_px": 0.12,
                "frame_interval_s": 0.01,
            },
        }
    ]
    _write_json(selected_root / "osf_selected.json", {"selected": selected})

    dataset_dir = mirror_root / "osf" / "dataset-0"
    dataset_dir.mkdir(parents=True, exist_ok=True)
    _write_json(dataset_dir / "candidate.json", {"title": "Dataset 0"})
    _write_json(
        dataset_dir / "anchors.json",
        {
            "T_K": 298.15,
            "pixel_scale_um_per_px": 0.12,
            "frame_interval_s": 0.01,
        },
    )
    _create_manifest(dataset_dir)

    proofpack_dataset_dir = proofpack_dir / "public_data" / "osf" / "dataset-0"
    (proofpack_dataset_dir / "ledgers").mkdir(parents=True, exist_ok=True)
    for protocol in ("sighted", "blind", "destroyed"):
        (proofpack_dataset_dir / "ledgers" / f"{protocol}.jsonl").write_text("{}\n", encoding="utf-8")
    _write_json(proofpack_dataset_dir / "protocol.json", {"anchors": {}, "thresholds": {}})
    _write_json(
        proofpack_dataset_dir / "summary.json",
        {
            "dataset": "Dataset 0",
            "protocol": "sighted",
            "spearman_rho": 0.95,
            "spearman_pvalue": 1e-7,
        },
    )
    _write_json(
        proofpack_dataset_dir / "public_spt_metadata.json",
        {
            "dataset": "Dataset 0",
            "source": "osf",
        },
    )
    _write_json(
        proofpack_dataset_dir / "oos_metrics.json",
        {
            "oos_median_abs_pct_error": 0.05,
        },
    )
    verifier_dir = proofpack_dataset_dir / "verifier"
    verifier_dir.mkdir(parents=True, exist_ok=True)
    _write_json(verifier_dir / "public_spt.json", {"status": True})

    proofpack_verifier = proofpack_dir / "verifier"
    proofpack_verifier.mkdir(parents=True, exist_ok=True)
    (proofpack_verifier / "THIELE_OK").write_text("THIELE_OK\n", encoding="utf-8")

    summary = audit_runbook(
        sources=("osf",),
        candidates_root=candidates_root,
        selected_root=selected_root,
        mirror_root=mirror_root,
        proofpack_dir=proofpack_dir,
    )

    assert summary["complete"] is True
    osf_summary = summary["sources"]["osf"]
    assert osf_summary["status"] == "ok"
    assert osf_summary["outstanding"] == []
    assert osf_summary["proofpack"]["verifier_flag"] is True


def test_audit_runbook_reports_gaps(tmp_path: Path) -> None:
    mirror_root = tmp_path / "mirrors"
    summary = audit_runbook(
        sources=("osf",),
        candidates_root=tmp_path,
        selected_root=tmp_path,
        mirror_root=mirror_root,
        proofpack_dir=None,
    )

    assert summary["complete"] is False
    osf_summary = summary["sources"]["osf"]
    assert osf_summary["candidates"]["status"] == "missing"
    assert any("Discover OSF candidates" in issue for issue in osf_summary["outstanding"])
    assert any("Run proofpack pipeline" in issue for issue in osf_summary["outstanding"])
