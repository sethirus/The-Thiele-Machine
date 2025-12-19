import json
import shutil
from pathlib import Path

import pytest

from scripts.halting_trap import LoopConfig, run_budgeted_loop
from scripts.generate_waveform import generate_waveform
from scripts.plot_time_dilation_curve import plot_time_dilation
from scripts.time_dilation_experiment import run_experiment


def test_time_dilation_curve(tmp_path: Path):
    data = run_experiment(write=False)
    input_json = tmp_path / "time_dilation_experiment.json"
    input_json.write_text(json.dumps(data, indent=2), encoding="utf-8")
    output = tmp_path / "curve.png"
    plot_time_dilation(input_path=input_json, output_path=output)
    assert output.exists()


def test_halting_trap_budget():
    result = run_budgeted_loop(LoopConfig(budget_mu=1000, step_cost=1, max_steps=2000), write=False)
    assert result.status == "mu_overflow"
    assert result.mu_spent >= result.budget_mu
    assert result.steps_executed == result.mu_spent


@pytest.mark.skipif(shutil.which("iverilog") is None, reason="iverilog not installed")
def test_waveform_generation(tmp_path: Path):
    vcd_path = generate_waveform(output_dir=tmp_path)
    assert vcd_path.exists()
    # VCD should not be empty
    assert vcd_path.stat().st_size > 0
