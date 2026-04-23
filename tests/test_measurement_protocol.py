#!/usr/bin/env python3
"""Executable measurement protocol for the REVEAL lane.

This file turns the measurement-problem lane in the closure guide into one
concrete falsifiable protocol: REVEAL must charge the exact successor-law
cost predicted by the active theory surfaces.

If either backend violates these equalities, the local measurement story in
the repository is false for that trace.
"""

from __future__ import annotations

import shutil

import pytest

from thielecpu.vm import VMState, vm_run


def _run_py(instructions, fuel=500):
    state = VMState.default()
    return vm_run(state, instructions, max_steps=fuel)


def _predicted_reveal_delta(bits: int, cost: int) -> int:
    return bits + cost + 1


def _run_rtl(program):
    from thielecpu.hardware.cosim import run_verilog

    result = run_verilog(program, timeout=30)
    assert result is not None, "run_verilog returned None despite iverilog being present"
    return result


IVERILOG = shutil.which("iverilog")
pytestmark = [pytest.mark.measurement]


class TestRevealMeasurementProtocol:
    def test_python_reveal_matches_quantitative_prediction(self):
        bits = 4
        cost = 5

        state = _run_py(
            [
                {"op": "reveal", "module": 0, "bits": bits, "cert": "proof", "cost": cost},
                {"op": "halt", "cost": 0},
            ]
        )

        assert state.vm_mu == _predicted_reveal_delta(bits, cost)

    def test_python_sequential_reveal_costs_add_exactly(self):
        first_bits = 1
        first_cost = 0
        second_bits = 3
        second_cost = 2

        state = _run_py(
            [
                {"op": "reveal", "module": 0, "bits": first_bits, "cert": "left", "cost": first_cost},
                {"op": "reveal", "module": 1, "bits": second_bits, "cert": "right", "cost": second_cost},
                {"op": "halt", "cost": 0},
            ]
        )

        expected_mu = _predicted_reveal_delta(first_bits, first_cost) + _predicted_reveal_delta(second_bits, second_cost)
        assert state.vm_mu == expected_mu

    @pytest.mark.integration
    @pytest.mark.strict_rtl
    @pytest.mark.skipif(IVERILOG is None, reason="iverilog not installed")
    def test_rtl_reveal_matches_quantitative_prediction(self):
        bits = 5
        cost = 0

        state = _run_rtl(
            [
                "INIT_LOGIC_ACC -889263410",
                f"REVEAL 0 {bits} {cost}",
                "HALT 0",
            ]
        )

        assert state["status"] == 2
        assert state["mu"] == _predicted_reveal_delta(bits, cost)
        assert state["mu_tensor_0"] == bits

    @pytest.mark.integration
    @pytest.mark.strict_rtl
    @pytest.mark.skipif(IVERILOG is None, reason="iverilog not installed")
    def test_rtl_sequential_reveal_costs_add_exactly(self):
        first_bits = 2
        second_bits = 7

        state = _run_rtl(
            [
                "INIT_LOGIC_ACC -889263410",
                f"REVEAL 0 {first_bits} 0",
                f"REVEAL 1 {second_bits} 0",
                "HALT 0",
            ]
        )

        expected_mu = _predicted_reveal_delta(first_bits, 0) + _predicted_reveal_delta(second_bits, 0)
        tensor_total = sum(state[f"mu_tensor_{index}"] for index in range(4))
        assert state["status"] == 2
        assert state["mu"] == expected_mu
        assert tensor_total == first_bits + second_bits