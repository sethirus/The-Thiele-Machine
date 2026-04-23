"""Checks for the project-local RTL text-transform audit manifest."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "audit_rtl_text_transforms.py"
MANIFEST = ROOT / "artifacts" / "rtl_text_transform_audit.json"


def _load_manifest() -> dict:
    return json.loads(MANIFEST.read_text(encoding="utf-8"))


def test_transform_audit_script_exists() -> None:
    assert SCRIPT.exists()


def test_transform_audit_manifest_is_fresh(tmp_path: Path) -> None:
    out = tmp_path / "rtl_text_transform_audit.json"
    subprocess.run(
        [sys.executable, str(SCRIPT), "--out", str(out)],
        cwd=ROOT,
        check=True,
    )
    assert json.loads(out.read_text(encoding="utf-8")) == _load_manifest()


def test_transform_audit_core_invariants_hold() -> None:
    data = _load_manifest()
    assert data["manifest_kind"] == "rtl_text_transform_audit"
    failed = [name for name, value in data["invariants"].items() if not value]
    assert not failed, f"failing transform-audit invariants: {failed}"


def test_bsv_transform_scope_is_storage_only_regfile_rewrite() -> None:
    data = _load_manifest()
    expected_sources = {
        "imem": (65536, 16, "Bit#(128)"),
        "lassert_cbuf": (512, 9, "Bit#(32)"),
        "lassert_fbuf": (256, 8, "Bit#(32)"),
        "mem": (65536, 16, "Bit#(32)"),
    }
    sources = {
        item["name"]: (item["elements"], item["address_bits"], item["element_type"])
        for item in data["bsv_transform"]["large_vector_sources"]
    }
    assert sources == expected_sources

    targets = {
        item["name"]: (item["address_bits"], item["element_type"])
        for item in data["bsv_transform"]["regfile_targets"]
    }
    assert targets == {
        name: (address_bits, element_type)
        for name, (_elements, address_bits, element_type) in expected_sources.items()
    }
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
