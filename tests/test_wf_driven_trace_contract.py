#!/usr/bin/env python3
"""Representative executable witnesses for the WF-driven RTL contract.

These tests do not try to re-prove the Coq theorems in Python. They provide
one focused executable surface for the stronger Item 3 theorem lane added in:

- GraphReconstructionBridge.v: driven_step_wf, driven_trace_commutes
- VerilogSemantics.v: coq_kami_model_satisfies_rtl_step_correct_wf,
  coq_kami_model_trace_correct_wf
- ShadowDeviceTrace.v: rtl_shadow_trace_compat_wf
- ThieleCanonicality.v: thiele_trace_compat_wf_driven

The repository already has broad opcode smoke, fuzz, and cross-layer tests.
What was missing was one named strict-RTL gate that bundles representative
valid traces for the conditional opcode families behind WFDrivenPrecondition.
If one of these traces regresses, the strengthened theorem surface has lost
its nearest executable witness on the generated RTL path.
"""

from __future__ import annotations

import shutil

import pytest

from thielecpu.hardware.cosim import run_verilog


IVERILOG = shutil.which("iverilog")
pytestmark = [
    pytest.mark.integration,
    pytest.mark.strict_rtl,
    pytest.mark.skipif(IVERILOG is None, reason="iverilog not installed"),
]


def _run(program: list[str]) -> dict[str, object]:
    result = run_verilog(program, timeout=30)
    assert result is not None, "run_verilog returned None despite strict RTL gating"
    return result


def _rtl_lassert_sat_program(cost: int) -> list[str]:
    return [
        "INIT_MEM 16 2",
        "INIT_MEM 17 1",
        "INIT_MEM 18 1",
        "INIT_MEM 19 1",
        "INIT_MEM 20 0",
        "INIT_MEM 97 1",
        "INIT_MEM 98 0",
        "LOAD_IMM 28 16 0",
        "LOAD_IMM 29 96 0",
        f"LASSERT 28 29 1 2 {cost}",
    ]


class TestWFDrivenTraceContract:
    def test_partition_family_trace_executes_cleanly(self) -> None:
        state = _run([
            "PNEW {0,256} 3",
            "PSPLIT 0 {0,128} {128,256} 2",
            "HALT 0",
        ])

        assert not state["err"], f"unexpected partition-trace error: {state}"
        assert state["status"] == 2
        assert state["mu"] == 5
        assert state["partition_ops"] >= 2

    def test_call_ret_family_trace_executes_cleanly(self) -> None:
        state = _run([
            "INIT_PT 0 128",
            "INIT_ACTIVE_MODULE 0",
            "CALL 3 1",
            "LOAD_IMM 2 55 1",
            "HALT 0",
            "LOAD_IMM 1 44 1",
            "RET 1",
        ])

        assert not state["err"], f"unexpected call/ret trace error: {state}"
        assert state["status"] == 2
        assert state["regs"][1] == 44
        assert state["regs"][2] == 55
        assert state["mu"] == 4

    def test_logic_family_trace_executes_cleanly(self) -> None:
        lassert_state = _run([
            "INIT_LOGIC_ACC 0xCAFEEACE",
            "PNEW {0,256} 1",
            *_rtl_lassert_sat_program(1),
            "HALT 0",
        ])

        chsh_state = _run([
            "INIT_LOGIC_ACC 0xCAFEEACE",
            "PNEW {0,256} 1",
            "CHSH_TRIAL 0 1 0 0 2",
            "HALT 0",
        ])

        assert not lassert_state["err"], f"unexpected LASSERT witness error: {lassert_state}"
        assert lassert_state["status"] == 2
        assert lassert_state.get("error_code", 0) == 0
        assert lassert_state["mu"] >= 19

        assert not chsh_state["err"], f"unexpected CHSH witness error: {chsh_state}"
        assert chsh_state["status"] == 2
        assert chsh_state.get("error_code", 0) == 0
        assert chsh_state["mu"] == 3

    def test_tensor_family_trace_executes_cleanly(self) -> None:
        state = _run([
            "LOAD_IMM 2 42 50",
            "TENSOR_SET 3 2 50",
            "TENSOR_GET 3 0 1",
            "HALT 0",
        ])

        assert not state["err"], f"unexpected tensor-family trace error: {state}"
        assert state["status"] == 2
        assert state["regs"][3] == 42
        assert state["mu"] == 101

    def test_morph_family_trace_executes_cleanly(self) -> None:
        state = _run([
            "PNEW {1} 1",
            "PNEW {2} 1",
            "PNEW {3} 1",
            "MORPH_EXT 10 1 2 0 1",
            "MORPH_EXT 11 2 3 0 1",
            "COMPOSE_EXT 12 1 2 1",
            "MORPH_GET_EXT 13 3 0 0",
            "MORPH_GET_EXT 14 3 1 0",
            "HALT 0",
        ])

        assert not state["err"], f"unexpected morph-family trace error: {state}"
        assert state["status"] == 2
        assert state["regs"][12] == 3
        assert state["regs"][13] == 1
        assert state["regs"][14] == 3