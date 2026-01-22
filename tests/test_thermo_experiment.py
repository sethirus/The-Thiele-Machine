import json
import os
import shutil
import subprocess
from pathlib import Path
import sys

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPT = REPO_ROOT / "scripts" / "thermo_experiment.py"

# Check for Coq extraction
_EXTRACTED_RUNNER = REPO_ROOT / "build" / "extracted_vm_runner"
_HAS_EXTRACTION = _EXTRACTED_RUNNER.exists()
_HAS_IVERILOG = shutil.which("iverilog") is not None


@pytest.mark.skipif(not _HAS_EXTRACTION or not _HAS_IVERILOG, 
                    reason="Requires Coq extraction and iverilog")
@pytest.mark.timeout(120)
def test_thermo_experiment_outputs(tmp_path):
    out_path = tmp_path / "thermo_experiment.json"
    env = os.environ.copy()
    env["ALLOW_MU_NORMALIZE"] = "1"
    env.setdefault("PYTHONPATH", str(REPO_ROOT))

    subprocess.run([sys.executable, str(SCRIPT), "--out", str(out_path)], check=True, env=env)

    assert out_path.exists(), "thermo_experiment.json missing"
    payload = json.loads(out_path.read_text())

    assert payload.get("runs"), "no runs recorded"
    names = {run["name"] for run in payload["runs"]}
    assert {"singleton_from_2", "singleton_from_4", "singleton_from_16", "singleton_from_64"}.issubset(names)

    for run in payload["runs"]:
        mu = float(run["python"]["mu"])
        lower = float(run["log2_ratio"])
        assert mu >= lower
        # Aligned state/μ when normalization is enabled.
        assert run["aligned"] is True
        # Explicitly surface normalization flags
        assert "mu_normalized" in run["extracted"]
        assert "mu_normalized" in run["rtl"]
        assert "mu_over_log2_ratio" in run
        assert run["evidence_strict"] is False
    assert payload["mu_slack_bits"]["max"] >= payload["mu_slack_bits"]["min"]
    assert payload["allow_mu_normalize"] is True
    assert payload["evidence_strict"] is False


@pytest.mark.timeout(120)
def test_thermo_experiment_blocks_normalization_in_evidence_mode(tmp_path):
    out_path = tmp_path / "thermo_experiment.json"
    env = os.environ.copy()
    env["ALLOW_MU_NORMALIZE"] = "1"
    env["EVIDENCE_STRICT"] = "1"
    env.setdefault("PYTHONPATH", str(REPO_ROOT))
    env["FORCE_ZERO_MU_EXTRACTED"] = "1"

    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--out", str(out_path)],
        env=env,
        capture_output=True,
        text=True,
    )
    assert result.returncode != 0
    assert "EVIDENCE_STRICT forbids" in result.stdout + result.stderr


@pytest.mark.skipif(not _HAS_EXTRACTION or not _HAS_IVERILOG, 
                    reason="Requires Coq extraction and iverilog")
@pytest.mark.timeout(120)
def test_thermo_experiment_passes_in_evidence_mode_when_mu_is_present(tmp_path):
    out_path = tmp_path / "thermo_experiment.json"
    env = os.environ.copy()
    env["EVIDENCE_STRICT"] = "1"
    env.setdefault("PYTHONPATH", str(REPO_ROOT))

    subprocess.run([sys.executable, str(SCRIPT), "--out", str(out_path)], check=True, env=env)

    payload = json.loads(out_path.read_text())
    assert payload["evidence_strict"] is True
    for run in payload["runs"]:
        assert run["extracted"]["mu_normalized"] is False
        assert run["rtl"]["mu_normalized"] is False
        assert run["aligned"] is True
