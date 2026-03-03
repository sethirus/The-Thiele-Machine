"""Canonical accelerator-path tests via active Kami CPU cosimulation.

These tests validate partition, receipt-visible, and arithmetic-adjacent behavior
through thielecpu/hardware/cosim.py and current RTL only.
"""

from __future__ import annotations

from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent


def _run_cosim(program: str):
    from thielecpu.hardware.cosim import run_verilog

    result = run_verilog(program, timeout=30)
    if result is None:
        pytest.skip("RTL simulator unavailable")
    return result


class TestPartitionPath:
    def test_pnew_updates_partition_ops_and_mu(self):
        state = _run_cosim("PNEW {0,1,2} 3\nHALT")
        assert state.get("partition_ops", 0) >= 1
        assert state["mu"] >= 3

    def test_pmerge_sequence_runs(self):
        state = _run_cosim("PNEW {0,1} 2\nPNEW {2,3} 2\nPMERGE 0 1 5\nHALT")
        assert state.get("partition_ops", 0) >= 3
        assert state["mu"] >= 9


class TestReceiptVisiblePath:
    def test_emit_increases_mu(self):
        baseline = _run_cosim("HALT")
        emitted = _run_cosim("EMIT 0 0 6\nHALT")
        assert emitted["mu"] >= baseline["mu"] + 6

    def test_reveal_after_logic_init_runs(self):
        state = _run_cosim("INIT_LOGIC_ACC -889263410\nREVEAL 0 0 4\nHALT")
        assert state["mu"] >= 4


class TestArithmeticAdjacentPath:
    def test_xor_load_and_add_pipeline(self):
        state = _run_cosim("XOR_LOAD 0 0 0\nXOR_LOAD 1 1 0\nXOR_ADD 0 1 0\nHALT")
        assert isinstance(state["regs"], list)
        assert len(state["regs"]) >= 2

    def test_xor_swap_pipeline(self):
        state = _run_cosim("XOR_LOAD 0 0 0\nXOR_LOAD 1 1 0\nXOR_SWAP 0 1 0\nHALT")
        assert isinstance(state["regs"][0], int)
        assert isinstance(state["regs"][1], int)


class TestCanonicalFiles:
    def test_canonical_rtl_present(self):
        assert (REPO_ROOT / "thielecpu/hardware/rtl/thiele_cpu_kami.v").exists()

    def test_canonical_tb_present(self):
        assert (REPO_ROOT / "thielecpu/hardware/testbench/thiele_cpu_kami_tb.v").exists()
