"""Checks for the project-local RTL text-transform audit manifest."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "audit_rtl_text_transforms.py"
MANIFEST = ROOT / "artifacts" / "rtl_text_transform_audit.json"

# Strict in CI so a forgotten refresh fails the build; auto-regenerating
# locally so routine source edits don't bounce the suite. Same split as
# tests/test_rtl_pipeline_manifest.py.
IN_CI = bool(os.environ.get("CI") or os.environ.get("GITHUB_ACTIONS"))


@pytest.fixture(scope="module", autouse=True)
def _refresh_manifest_locally() -> None:
    """Regenerate the manifest in place when running locally; no-op in CI."""
    if IN_CI or not SCRIPT.exists():
        return
    subprocess.run(
        [sys.executable, str(SCRIPT), "--out", str(MANIFEST)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=60,
        check=False,
    )


def _load_manifest() -> dict:
    return json.loads(MANIFEST.read_text(encoding="utf-8"))


def test_transform_audit_script_exists() -> None:
    assert SCRIPT.exists()


def test_transform_audit_manifest_is_fresh(tmp_path: Path) -> None:
    """Regenerate the audit manifest into a temp dir and assert the committed
    copy matches it byte for byte.

    This gate must be able to fail. An earlier version copied the fresh file
    over the committed one and emitted a warning instead of asserting, which
    meant a corrupt or hand-edited committed manifest was silently repaired
    by the very test that was supposed to detect it. Locally the fixture
    below regenerates in place first, so routine source edits don't bounce
    the suite; in CI nothing is regenerated and drift is a hard failure.
    """
    out = tmp_path / "rtl_text_transform_audit.json"
    subprocess.run(
        [sys.executable, str(SCRIPT), "--out", str(out)],
        cwd=ROOT,
        check=True,
    )
    fresh_text = out.read_text(encoding="utf-8")
    assert MANIFEST.exists(), f"Missing committed manifest: {MANIFEST}"
    assert fresh_text == MANIFEST.read_text(encoding="utf-8"), (
        "Committed RTL text-transform audit manifest is stale or has been "
        "modified by hand (a tracked source changed without regenerating it, "
        "or the committed JSON does not match generator output).\n\n"
        "Regenerate with:\n"
        f"    python scripts/audit_rtl_text_transforms.py --out {MANIFEST.relative_to(ROOT)}\n"
        "then commit the refreshed file."
    )


def test_transform_audit_core_invariants_hold() -> None:
    data = _load_manifest()
    assert data["manifest_kind"] == "rtl_text_transform_audit"
    failed = [name for name, value in data["invariants"].items() if not value]
    assert not failed, f"failing transform-audit invariants: {failed}"


def test_bsv_transform_scope_is_storage_only_regfile_rewrite() -> None:
    data = _load_manifest()
    # MEM_SIZE=128 → MemAddrSz=7 (silicon-side bound).
    # imem and mem are the only large vectors (>=256 entries) that get the
    # explicit RegFile rewrite treatment via the BSV transform script.
    # lassert_cbuf/lassert_fbuf at 64 entries (addr_width=6) are below the
    # large-vector threshold so they appear in regfile_targets but not in
    # large_vector_sources.
    expected_sources = {
        "imem": (128, 7, "Bit#(128)"),
        "mem": (128, 7, "Bit#(32)"),
    }
    sources = {
        item["name"]: (item["elements"], item["address_bits"], item["element_type"])
        for item in data["bsv_transform"]["large_vector_sources"]
    }
    assert sources == expected_sources

    expected_targets = {
        "imem": (7, "Bit#(128)"),
        "mem": (7, "Bit#(32)"),
        "lassert_cbuf": (6, "Bit#(32)"),
        "lassert_fbuf": (6, "Bit#(32)"),
    }
    targets = {
        item["name"]: (item["address_bits"], item["element_type"])
        for item in data["bsv_transform"]["regfile_targets"]
    }
    assert targets == expected_targets
    assert data["bsv_transform"]["sub_reads"] > 0
    assert data["bsv_transform"]["upd_writes"] > 0


def test_verilog_transform_scope_is_current_storage_shape() -> None:
    data = _load_manifest()
    raw_counts = data["verilog_transform"]["raw_flat_storage_counts"]
    assert raw_counts["mu_tensor_512"] == 1
    assert raw_counts["imem_8192"] == 0
    assert raw_counts["mem_scalar_regs"] == 0
    assert raw_counts["rf_scalar_regs"] == 0
    assert raw_counts["pt_scalar_regs"] == 0

    rewrites = data["verilog_transform"]["storage_rewrites"]
    assert rewrites["mt_arr_refs"] > 0
    assert rewrites["imem_arr_refs"] == 0
    assert rewrites["dm_refs"] == 0
    assert rewrites["rf_refs"] == 0
    assert rewrites["pt_tbl_refs"] == 0
