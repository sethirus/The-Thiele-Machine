from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
GENERATOR = REPO_ROOT / "scripts" / "generate_rtl_pipeline_manifest.py"
MANIFEST = REPO_ROOT / "artifacts" / "rtl_pipeline_manifest.json"


def test_rtl_pipeline_manifest_generator_exists() -> None:
    assert GENERATOR.exists(), f"Missing generator script: {GENERATOR}"


def test_rtl_pipeline_manifest_matches_committed(tmp_path: Path) -> None:
    fresh = tmp_path / "rtl_pipeline_manifest.json"
    result = subprocess.run(
        [sys.executable, str(GENERATOR), "--out", str(fresh)],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=60,
    )
    assert result.returncode == 0, result.stderr or result.stdout
    assert MANIFEST.exists(), f"Missing committed manifest: {MANIFEST}"
    assert MANIFEST.read_text(encoding="utf-8") == fresh.read_text(encoding="utf-8")


def test_rtl_pipeline_manifest_invariants() -> None:
    payload = json.loads(MANIFEST.read_text(encoding="utf-8"))

    assert payload["manifest_kind"] == "canonical_rtl_pipeline_provenance"
    assert payload["source_of_truth"]["coq_canonical_module"].endswith(":canonical_cpu_module")
    assert payload["source_of_truth"]["coq_generator_theorem"].endswith(":canonical_cpu_module_from_source")
    assert payload["source_of_truth"]["printer_entrypoint"].endswith(":targetB")

    invariants = payload["invariants"]
    failed = [name for name, ok in invariants.items() if not ok]
    assert not failed, "RTL pipeline manifest contains failed invariants:\n" + "\n".join(failed)
    assert invariants["tracked_rtl_matches_generated_synth_verilog"]
    assert invariants["main_ml_drives_pp_through_targetB"]
    assert invariants["canonical_cpu_module_generated_in_coq"]
    assert payload["boundary_statement"]["trusted_boundary"] == (
        "coq/kernel/VerilogRTLCorrespondence.v:bsc_kami_compilation_trusted"
    )


def test_rtl_pipeline_manifest_hashes_are_fresh() -> None:
    payload = json.loads(MANIFEST.read_text(encoding="utf-8"))
    for record in payload["files"]:
        path = REPO_ROOT / record["path"]
        assert path.exists(), f"Manifest file missing: {record['path']}"
        assert path.stat().st_size == record["size_bytes"], f"Stale size for {record['path']}"

        import hashlib

        current = hashlib.sha256(path.read_bytes()).hexdigest()
        assert current == record["sha256"], f"Stale hash for {record['path']}"
