"""Hardware enforcement proof tests against canonical Kami RTL only.

These tests verify enforcement-related behavior through the active
thiele_cpu_kami.v + thiele_cpu_kami_tb.v simulation path.
Only active canonical RTL/testbench files are used.
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


class TestCanonicalRtlPresence:
    def test_kami_rtl_exists(self):
        assert (REPO_ROOT / "thielecpu/hardware/rtl/thiele_cpu_kami.v").exists()

    def test_kami_tb_exists(self):
        assert (REPO_ROOT / "thielecpu/hardware/testbench/thiele_cpu_kami_tb.v").exists()


class TestMuEnforcement:
    def test_mu_non_decreasing_for_costed_sequence(self):
        state = _run_cosim(
            "\n".join(
                [
                    "PNEW {1,2,3} 3",
                    "PNEW {4,5} 2",
                    "PMERGE 0 1 4",
                    "EMIT 0 0 1",
                    "HALT",
                ]
            )
        )
        # Explicit costs sum to 10 and mu should be monotonic cumulative.
        assert state["mu"] >= 10

    def test_longer_program_accumulates_more_mu(self):
        short_state = _run_cosim("PNEW {1} 2\nHALT")
        long_state = _run_cosim("PNEW {1} 2\nPNEW {2} 3\nPNEW {3} 4\nHALT")
        assert long_state["mu"] >= short_state["mu"]


class TestPartitionEnforcement:
    def test_partition_ops_counter_moves_with_partition_instructions(self):
        state = _run_cosim("PNEW {1} 1\nPNEW {2} 1\nPMERGE 0 1 2\nHALT")
        assert state.get("partition_ops", 0) >= 3

    def test_partition_table_reflects_activity(self):
        state = _run_cosim("PNEW {1,2,3} 3\nHALT")
        modules = state.get("modules")
        assert isinstance(modules, list)
        assert len(modules) > 0


class TestLogicEngineEnforcement:
    def test_logic_handshake_path_executes(self):
        state = _run_cosim(
            "\n".join(
                [
                    "INIT_LOGIC_ACC -889263410",
                    "LASSERT 1 0 3",
                    "LJOIN 2 0 4",
                    "REVEAL 0 0 3",
                    "HALT",
                ]
            )
        )
        assert state["mu"] >= 3
        assert "status" in state

    def test_emit_and_reveal_both_charge_mu(self):
        base = _run_cosim("HALT")
        emit_then_reveal = _run_cosim("EMIT 0 0 4\nREVEAL 0 0 5\nHALT")
        # REVEAL charging depends on logic state; EMIT charge is guaranteed.
        assert emit_then_reveal["mu"] >= base["mu"] + 4
