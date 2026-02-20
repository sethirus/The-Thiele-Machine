import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]

# Check if extraction runner is available
_EXTRACTED_RUNNER = REPO_ROOT / "thielecpu" / "generated" / "generated_core.py"
_HAS_EXTRACTION = _EXTRACTED_RUNNER.exists()


def _has_iverilog() -> bool:
    """Check if iverilog is available in PATH."""
    return shutil.which("iverilog") is not None


# Skip all tests in this module if extraction is not available
pytestmark = [
    pytest.mark.skipif(
        not _HAS_EXTRACTION,
        reason="Coq extraction not built. Run: scripts/forge_artifact.sh"
    ),
    pytest.mark.skipif(
        not _has_iverilog(),
        reason="iverilog not installed"
    ),
]

def _run_bundle(
    env: dict,
    out_path: Path,
    expect_ok: bool,
    *,
    scenario: str | None = None,
) -> subprocess.CompletedProcess[str]:
    full_env = os.environ.copy()
    full_env.update(env)
    existing_pythonpath = full_env.get("PYTHONPATH", "")
    full_env["PYTHONPATH"] = (
        f"{REPO_ROOT}{os.pathsep}{existing_pythonpath}"
        if existing_pythonpath
        else str(REPO_ROOT)
    )
    full_env.setdefault("OCAMLRUNPARAM", "l=64M")

    cmd = [sys.executable, "scripts/equivalence_bundle.py", "--out", str(out_path)]
    if scenario is not None:
        cmd.extend(["--scenario", scenario])

    result = subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        env=full_env,
        text=True,
        capture_output=True,
    )

    if expect_ok:
        assert result.returncode == 0, result.stdout + result.stderr
    else:
        assert result.returncode != 0, "expected equivalence bundle run to fail"
    return result


def test_equivalence_bundle_requires_opt_in_for_mu_normalization(tmp_path: Path) -> None:
    out_path = tmp_path / "equivalence_bundle.json"
    result = _run_bundle({"FORCE_ZERO_MU_EXTRACTED": "1"}, out_path, expect_ok=False)
    assert "ALLOW_MU_NORMALIZE=1" in result.stdout + result.stderr


def test_equivalence_bundle_evidence_strict_blocks_normalization(tmp_path: Path) -> None:
    out_path = tmp_path / "equivalence_bundle.json"
    result = _run_bundle(
        {
            "ALLOW_MU_NORMALIZE": "1",
            "EVIDENCE_STRICT": "1",
            "FORCE_ZERO_MU_EXTRACTED": "1",
        },
        out_path,
        expect_ok=False,
    )
    assert "EVIDENCE_STRICT forbids" in result.stdout + result.stderr


def test_equivalence_bundle_marks_normalized_mu_outputs(tmp_path: Path) -> None:
    out_path = tmp_path / "equivalence_bundle.json"
    _run_bundle(
        {
            "ALLOW_MU_NORMALIZE": "1",
            "FORCE_ZERO_MU_EXTRACTED": "1",
            "FORCE_ZERO_MU_RTL": "1",
        },
        out_path,
        expect_ok=True,
    )

    bundle = json.loads(out_path.read_text())

    assert bundle["python"]["mu_normalized"] is False
    assert bundle["extracted"]["mu_normalized"] is True
    assert bundle["extracted"]["mu_normalize_reason"] == "extracted_missing_mu"
    assert bundle["extracted"]["mu_raw"] in {None, 0}
    assert bundle["rtl"]["mu_normalized"] is True
    assert bundle["rtl"]["mu_normalize_reason"] == "rtl_missing_mu"
    assert bundle["rtl"]["mu_raw"] in {None, 0}
    assert bundle["python"]["mu"] == bundle["extracted"]["mu"] == bundle["rtl"]["mu"]
    assert bundle["evidence_strict"] is False
    assert bundle["allow_mu_normalize"] is True


def test_equivalence_bundle_passes_in_evidence_mode_when_mu_is_present(tmp_path: Path) -> None:
    out_path = tmp_path / "equivalence_bundle.json"
    _run_bundle(
        {
            "EVIDENCE_STRICT": "1",
        },
        out_path,
        expect_ok=True,
    )

    bundle = json.loads(out_path.read_text())
    assert bundle["evidence_strict"] is True
    assert bundle["python"]["mu_normalized"] is False
    assert bundle["extracted"]["mu_normalized"] is False
    assert bundle["rtl"]["mu_normalized"] is False
    assert bundle["python"]["mu"] == bundle["extracted"]["mu"] == bundle["rtl"]["mu"]


def test_equivalence_bundle_multiop_compute_passes_in_evidence_mode(tmp_path: Path) -> None:
    out_path = tmp_path / "equivalence_bundle.json"
    _run_bundle(
        {
            "EVIDENCE_STRICT": "1",
        },
        out_path,
        expect_ok=True,
        scenario="multiop_compute",
    )

    bundle = json.loads(out_path.read_text())
    assert bundle["program"]["scenario"] == "multiop_compute"
    assert bundle["evidence_strict"] is True
    assert bundle["aligned"] is True
    assert len(bundle["program"]["text"]) > 2


def test_equivalence_bundle_psplit_odd_kills_parent_and_matches_partitions(tmp_path: Path) -> None:
    out_path = tmp_path / "equivalence_bundle.json"
    _run_bundle(
        {
            "EVIDENCE_STRICT": "1",
        },
        out_path,
        expect_ok=True,
        scenario="psplit_odd",
    )

    bundle = json.loads(out_path.read_text())
    assert bundle["program"]["scenario"] == "psplit_odd"
    assert bundle["evidence_strict"] is True
    assert bundle["aligned"] is True
    assert bundle["partition"]["aligned"] is True
    assert bundle["partition"]["zombie_parent_present"] is False


def test_equivalence_bundle_magic_ops_are_priced_identically(tmp_path: Path) -> None:
    out_path = tmp_path / "equivalence_bundle.json"
    _run_bundle(
        {
            "EVIDENCE_STRICT": "1",
        },
        out_path,
        expect_ok=True,
        scenario="magic_ops",
    )

    bundle = json.loads(out_path.read_text())
    assert bundle["program"]["scenario"] == "magic_ops"
    assert bundle["evidence_strict"] is True
    assert bundle["aligned"] is True


def test_magic_ops_alignment_regression(tmp_path: Path) -> None:
    """Regression test: magic_ops must remain aligned across layers."""
    out_path = tmp_path / "equivalence_bundle.json"
    _run_bundle({}, out_path, expect_ok=True, scenario="magic_ops")
    bundle = json.loads(out_path.read_text())
    assert bundle["program"]["scenario"] == "magic_ops"
    assert bundle["aligned"] is True
    # Ensure μ totals match exactly across Python, Extracted, and RTL
    assert bundle["python"]["mu"] == bundle["extracted"]["mu"] == bundle["rtl"]["mu"]


def test_equivalence_bundle_mdlacc_pdiscover_pricing_parity(tmp_path: Path) -> None:
    """Ensure MDLACC and PDISCOVER μ deltas are priced and reflected identically across layers.

    - MDLACC must charge the expected Q16.16 execution cost (1 << 16 for the test module).
    - The PDISCOVER info_gain in the program text must appear in the remaining μ after MDLACC
      and be observable in the ledger's final entry.
    - Exact ledger `reason` strings for MDLACC and the terminal receipt are asserted.
    - Python, extracted, and RTL totals must remain aligned.
    """
    out_path = tmp_path / "equivalence_bundle.json"
    _run_bundle({"EVIDENCE_STRICT": "1"}, out_path, expect_ok=True, scenario="magic_ops")

    bundle = json.loads(out_path.read_text())
    assert bundle["program"]["scenario"] == "magic_ops"
    assert bundle["aligned"] is True

    # MDLACC ledger entry must exist and charge Q16.16 (1 << 16)
    mdl_entry = next((e for e in bundle["python"]["mu_ledger"] if e.get("reason", "").startswith("mdlacc")), None)
    assert mdl_entry is not None
    # exact reason string (regression guard)
    assert mdl_entry["reason"] == "mdlacc_explicit_module1"
    assert mdl_entry["delta_mu_execution"] == (1 << 16)

    # Locate the terminal / final ledger entry and assert its reason string
    final_entry = next((e for e in bundle["python"]["mu_ledger"] if e.get("reason") == "final"), None)
    assert final_entry is not None
    assert final_entry["reason"] == "final"
    assert final_entry["total_mu"] == bundle["python"]["mu"]

    # PDISCOVER's info_gain (from program text) should account for the remaining μ
    # after MDLACC — this delta is observed between the MDLACC entry and the final entry.
    pdiscover_instr = next((t for t in bundle["program"]["text"] if t[0] == "PDISCOVER"), None)
    assert pdiscover_instr is not None
    expected_info_gain = int(pdiscover_instr[1].split()[-1])

    # Confirm the final ledger reflects the PDISCOVER contribution
    exec_delta_after_mdl = final_entry["total_mu_execution"] - mdl_entry["total_mu_execution"]
    assert exec_delta_after_mdl == expected_info_gain

    # Cross-layer parity: totals must match exactly
    assert bundle["python"]["mu"] == bundle["extracted"]["mu"] == bundle["rtl"]["mu"]


def test_equivalence_bundle_oracle_halts_special_handling(tmp_path: Path) -> None:
    """ORACLE_HALTS charges an extremely large μ — exercise special handling.

    - Skip invoking the extracted runner (SKIP_EXTRACTED_RUNNER=1) because the
      extracted binary cannot safely handle the oracle's μ magnitude in tests.
    - Allow μ-normalization so the placeholder extracted output falls back to
      the Python total.
    - Verify Python and RTL both see the oracle charge (1_000_000) and that
      extracted is normalized to Python's total.
    """
    out_path = tmp_path / "equivalence_bundle.json"

    env = {
        "ALLOW_MU_NORMALIZE": "1",
        "SKIP_EXTRACTED_RUNNER": "1",
    }
    _run_bundle(env, out_path, expect_ok=True, scenario="oracle_halts")

    bundle = json.loads(out_path.read_text())
    assert bundle["program"]["scenario"] == "oracle_halts"

    # Python layer must include the oracle execution charge (1_000_000)
    assert bundle["python"]["summary"]["mu_execution"] >= 1000000
    assert bundle["python"]["summary"]["mu_operational"] == 1000000.0

    # RTL should observe the same total (Python + RTL parity)
    assert bundle["python"]["mu"] == bundle["rtl"]["mu"]

    # Extracted was skipped and must be normalized to Python's μ
    assert bundle["extracted"]["mu_normalized"] is True
    assert bundle["allow_mu_normalize"] is True
