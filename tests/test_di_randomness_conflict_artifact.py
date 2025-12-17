from __future__ import annotations

import json
from pathlib import Path


def test_di_randomness_conflict_artifact_shows_gap(tmp_path: Path):
    # Use the canonical example transcript already in the repo.
    repo_root = Path(__file__).resolve().parents[1]
    receipts = repo_root / "examples" / "tsirelson_step_receipts.json"
    assert receipts.exists(), "missing examples/tsirelson_step_receipts.json"

    out = tmp_path / "conflict.json"

    # Run the generator script (real execution).
    import subprocess
    import sys

    proc = subprocess.run(
        [sys.executable, "scripts/di_randomness_conflict_chart.py", "--receipts", str(receipts), "--out", str(out)],
        cwd=repo_root,
        check=True,
        capture_output=True,
        text=True,
    )
    assert out.exists(), proc.stdout + proc.stderr

    payload = json.loads(out.read_text(encoding="utf-8"))
    std = float(payload["bounds"]["standard_di"]["hmin_lower_bound_bits"])
    th = float(payload["bounds"]["thiele_certified"]["hmin_lower_bound_bits"])

    observed = payload["observed"]
    assert isinstance(observed["cert_setter_steps"], int)
    assert isinstance(observed["mu_acc_delta"], int)
    assert isinstance(observed["mu_delta_total"], float)
    assert observed["cert_setter_steps"] >= 0

    env = payload["bounds"]["thiele_cert_step_envelope"]
    assert "f_count" in env
    assert "count_le_f_count" in env
    assert "cert_setter_positive_cost_assumption_holds" in env

    if env["cert_setter_positive_cost_assumption_holds"]:
        assert bool(env["count_le_f_count"]) == (observed["cert_setter_steps"] <= int(env["f_count"]))
    else:
        assert env["count_le_f_count"] is None

    # This example is designed to have nontrivial CHSH-derived Hmin, but no
    # structure-addition/certification in receipts, so Thiele-certified is 0.
    assert std >= 0.0
    assert th == 0.0
    assert std >= th
