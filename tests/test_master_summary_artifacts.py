from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
MASTER_SUMMARY = REPO_ROOT / "coq" / "kernel" / "MasterSummary.v"
ARTIFACT_DIR = REPO_ROOT / "artifacts" / "final_claim_audit"
GENERATOR = REPO_ROOT / "scripts" / "generate_master_summary_artifacts.py"

OBLIGATION_RE = re.compile(r'obligation_name := "([^"]+)"')
EXPECTED_FILES = {
    "cross_layer_equivalence_scope.json",
    "dependency_manifest_certificate.json",
    "master_summary_open_obligations.json",
    "physics_research_boundaries.json",
    "proof_spine_reduction_status.json",
    "raychaudhuri_einstein_closure.json",
    "repository_non_circularity_scope.json",
    "semantic_partition_inventory.json",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_master_summary_obligations() -> list[str]:
    text = MASTER_SUMMARY.read_text(encoding="utf-8")
    obligations = OBLIGATION_RE.findall(text)
    assert len(obligations) == 7, f"Expected 7 obligations in {MASTER_SUMMARY}, found {len(obligations)}"
    return obligations


def test_generator_exists() -> None:
    assert GENERATOR.exists(), f"Missing generator script: {GENERATOR}"


def test_expected_artifacts_exist() -> None:
    missing = sorted(name for name in EXPECTED_FILES if not (ARTIFACT_DIR / name).exists())
    assert not missing, "Missing MasterSummary artifacts:\n" + "\n".join(f"  {name}" for name in missing)


def test_generated_artifacts_match_committed(tmp_path: Path) -> None:
    result = subprocess.run(
        [sys.executable, str(GENERATOR), "--out-dir", str(tmp_path)],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=60,
    )
    assert result.returncode == 0, result.stderr or result.stdout

    generated = {path.name for path in tmp_path.glob("*.json")}
    assert generated == EXPECTED_FILES, (
        "Generated artifact set drifted.\n"
        f"Generated: {sorted(generated)}\n"
        f"Expected: {sorted(EXPECTED_FILES)}"
    )

    mismatches: list[str] = []
    for name in sorted(EXPECTED_FILES):
        committed = ARTIFACT_DIR / name
        fresh = tmp_path / name
        if committed.read_text(encoding="utf-8") != fresh.read_text(encoding="utf-8"):
            mismatches.append(name)
    assert not mismatches, "Committed MasterSummary artifacts are stale:\n" + "\n".join(f"  {name}" for name in mismatches)


def test_obligation_inventory_matches_master_summary() -> None:
    master_summary_obligations = _load_master_summary_obligations()
    payload = json.loads((ARTIFACT_DIR / "master_summary_open_obligations.json").read_text(encoding="utf-8"))

    assert payload["source_file"] == "coq/kernel/MasterSummary.v"
    assert payload["source_sha256"] == _sha256(MASTER_SUMMARY)

    artifact_obligations = [entry["name"] for entry in payload["obligations"]]
    assert artifact_obligations == master_summary_obligations

    for entry in payload["obligations"]:
        assert entry["status"] == "open-but-ci-backed"
        artifact_path = REPO_ROOT / entry["artifact"]
        assert artifact_path.exists(), f"Referenced artifact missing: {entry['artifact']}"
        for rel_path in entry["backing_files"]:
            assert (REPO_ROOT / rel_path).exists(), f"Referenced backing file missing: {rel_path}"


def test_cross_layer_scope_is_observable_only() -> None:
    payload = json.loads((ARTIFACT_DIR / "cross_layer_equivalence_scope.json").read_text(encoding="utf-8"))
    assert payload["equivalence_mode"] == "observable_only"
    assert payload["full_state_identity_status"] == "not claimed"
    assert payload["observable_fields"] == ["vm_pc", "vm_mu"]


def test_dependency_manifest_hashes_are_fresh() -> None:
    payload = json.loads((ARTIFACT_DIR / "dependency_manifest_certificate.json").read_text(encoding="utf-8"))
    assert payload["certificate_status"] == "current-surfaces-pinned"
    for record in payload["inputs"]:
        path = REPO_ROOT / record["path"]
        assert path.exists(), f"Dependency manifest input missing: {record['path']}"
        assert record["sha256"] == _sha256(path), f"Stale hash for {record['path']}"