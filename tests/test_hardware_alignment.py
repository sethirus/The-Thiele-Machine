# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""Check that RTL simulation traces agree with decoded instruction metrics."""

from __future__ import annotations

import shutil
import subprocess

import pytest

from tools.verify_end_to_end import (
    HARDWARE_DIR,
    LOG_PATH,
    TB_PATH,
    metrics_from_instructions,
    parse_instructions,
    summary_from_log,
    verify_final_state,
    verify_metrics,
)


@pytest.mark.integration
def test_rtl_trace_matches_decoded_metrics():
    if shutil.which("iverilog") is None or shutil.which("vvp") is None:
        pytest.skip("iverilog/vvp not available in PATH")

    compile_cmd = [
        "iverilog",
        "-g2012",
        "-o",
        "thiele_cpu_tb",
        "thiele_cpu.v",
        "thiele_cpu_tb.v",
        "mu_alu.v",
        "mu_core.v",
    ]
    subprocess.run(compile_cmd, cwd=HARDWARE_DIR, check=True, capture_output=True)

    run = subprocess.run(
        ["vvp", "thiele_cpu_tb"], cwd=HARDWARE_DIR, check=True, capture_output=True, text=True
    )

    # Persist the log so summary_from_log can parse it.
    LOG_PATH.write_text(run.stdout)

    instrs = parse_instructions(TB_PATH)
    expected = metrics_from_instructions(instrs)
    summary = summary_from_log(LOG_PATH)

    verify_metrics(expected, summary.metrics)
    verify_final_state(instrs, summary)
