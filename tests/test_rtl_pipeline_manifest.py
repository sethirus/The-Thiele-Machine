from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
GENERATOR = REPO_ROOT / "scripts" / "generate_rtl_pipeline_manifest.py"
MANIFEST = REPO_ROOT / "artifacts" / "rtl_pipeline_manifest.json"

# In CI we keep the strict check so a forgotten manifest refresh fails the build.
# Locally we auto-regenerate so `pytest` doesn't bounce on routine source edits;
# `git diff` still shows the change, so the developer can stage it and commit.
IN_CI = bool(os.environ.get("CI") or os.environ.get("GITHUB_ACTIONS"))


@pytest.fixture(scope="module", autouse=True)
def _refresh_manifest_locally() -> None:
    """Regenerate the manifest in place when running locally; no-op in CI."""
    if IN_CI:
        return
    if not GENERATOR.exists():
        return
    subprocess.run(
        [sys.executable, str(GENERATOR), "--out", str(MANIFEST)],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=60,
        check=False,
    )


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
    if MANIFEST.read_text(encoding="utf-8") != fresh.read_text(encoding="utf-8"):
        raise AssertionError(
            "Committed RTL pipeline manifest is stale (a tracked source has been edited "
            "without regenerating the manifest).\n\n"
            "Locally this should not happen: the test fixture auto-regenerates.\n"
            "If you see this in CI, fix locally with:\n"
            "    make refresh-manifests\n"
            "or directly:\n"
            "    python3 scripts/generate_rtl_pipeline_manifest.py "
            "--out artifacts/rtl_pipeline_manifest.json\n\n"
            "Then `git add artifacts/rtl_pipeline_manifest.json` and re-commit.\n"
            "To prevent this in the future, install the pre-commit hook once:\n"
            "    make install-hooks\n"
        )


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
    fix_hint = (
        "\n\nFix: `make refresh-manifests` "
        "(or install the pre-commit hook with `make install-hooks` "
        "to prevent this in future commits)."
    )
    for record in payload["files"]:
        path = REPO_ROOT / record["path"]
        assert path.exists(), f"Manifest file missing: {record['path']}{fix_hint}"
        assert path.stat().st_size == record["size_bytes"], (
            f"Stale size for {record['path']}{fix_hint}"
        )

        import hashlib

        current = hashlib.sha256(path.read_bytes()).hexdigest()
        assert current == record["sha256"], f"Stale hash for {record['path']}{fix_hint}"
