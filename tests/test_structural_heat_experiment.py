import json
import os
import subprocess
from pathlib import Path
import sys

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPT = REPO_ROOT / "scripts" / "structural_heat_experiment.py"


def _run_script(out_path: Path, env_overrides=None):
    env = os.environ.copy()
    if env_overrides:
        env.update(env_overrides)
    env.setdefault("PYTHONPATH", str(REPO_ROOT))
    subprocess.run([sys.executable, str(SCRIPT), "--out", str(out_path)], check=True, env=env)


@pytest.mark.timeout(90)
def test_structural_heat_outputs(tmp_path: Path):
    out_path = tmp_path / "structural_heat_experiment.json"
    _run_script(out_path)
    assert out_path.exists(), "structural_heat_experiment.json missing"
    payload = json.loads(out_path.read_text())
    runs = {run["name"]: run for run in payload["runs"]}
    assert "erase_random_noise" in runs and "erase_structured_sorted" in runs

    random_mu = runs["erase_random_noise"]["mu_total"]
    structured_mu = runs["erase_structured_sorted"]["mu_total"]

    assert structured_mu > random_mu
    assert runs["erase_structured_sorted"]["landauer_min_joules"] > runs["erase_random_noise"][
        "landauer_min_joules"
    ]


@pytest.mark.timeout(90)
def test_structural_heat_scaling_with_temperature(tmp_path: Path):
    out_path = tmp_path / "structural_heat_experiment.json"
    _run_script(out_path, {"THERMO_TEMPERATURE_K": "150"})
    payload_low = json.loads(out_path.read_text())
    low_runs = {run["name"]: run for run in payload_low["runs"]}

    _run_script(out_path, {"THERMO_TEMPERATURE_K": "600"})
    payload_high = json.loads(out_path.read_text())
    high_runs = {run["name"]: run for run in payload_high["runs"]}

    assert high_runs["erase_structured_sorted"]["landauer_min_joules"] > low_runs["erase_structured_sorted"][
        "landauer_min_joules"
    ]
