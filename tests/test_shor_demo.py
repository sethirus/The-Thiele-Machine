from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

import pytest


@pytest.fixture(scope="module")
def shor_demo_module():
    script_path = Path(__file__).resolve().parents[1] / "scripts" / "shor_on_thiele_demo.py"
    spec = importlib.util.spec_from_file_location("shor_demo", script_path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_shor_demo_produces_receipts(tmp_path: Path, shor_demo_module):
    output_dir = tmp_path / "shor"
    analysis = shor_demo_module.run_demo(21, 2, output_dir)

    assert analysis["number"] == 21
    assert analysis["classical_work"] >= 2
    assert analysis["thiele_work"] == 0
    assert analysis["reasoning_mu_cost"] > 0

    summary_path = output_dir / "act_ii" / "summary.json"
    reasoning_path = output_dir / "act_ii" / "reasoning_summary.json"
    assert summary_path.exists()
    assert reasoning_path.exists()

    payload = json.loads(reasoning_path.read_text())
    assert payload["period"] == 6
    assert payload["claims"]
