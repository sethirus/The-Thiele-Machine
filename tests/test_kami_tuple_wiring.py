from __future__ import annotations

from pathlib import Path


RTL = Path(__file__).resolve().parents[1] / "thielecpu" / "hardware" / "rtl" / "thiele_cpu_kami.v"


def _rtl_text() -> str:
    if not RTL.exists():
        raise AssertionError(f"Kami RTL not found: {RTL}")
    return RTL.read_text(encoding="utf-8")


def test_kami_tuple_observation_ports_present() -> None:
    txt = _rtl_text()
    expected = [
        "getPC",
        "getMu",
        "getErr",
        "getHalted",
        "getErrorCode",
        "getMuTensor0",
        "getMuTensor1",
        "getMuTensor2",
        "getMuTensor3",
        "getBianchiAlarm",
        "getPtNextId",
        "getPtSize",
    ]
    for signal in expected:
        assert signal in txt, f"Missing tuple-observation signal: {signal}"


def test_logic_onchip_fsm_signals_present() -> None:
    txt = _rtl_text()
    # On-chip LASSERT FSM signals (replaced the old external coprocessor interface).
    expected = [
        "lassert_phase",
        "lassert_fbase",
        "lassert_cbuf",
        "lassert_fbuf",
    ]
    for signal in expected:
        assert signal in txt, f"Missing on-chip LASSERT FSM signal: {signal}"


def test_logic_related_opcodes_defined_in_coq_and_present_in_rtl_paths() -> None:
    coq_types = (Path(__file__).resolve().parents[1] / "coq" / "kami_hw" / "ThieleTypes.v").read_text(encoding="utf-8")
    assert "OP_LASSERT" in coq_types
    assert "OP_LJOIN" in coq_types
    # OP_ORACLE_HALTS was removed (0x10 reserved); legacy cost constant remains
    assert "ORACLE_HALTS_HW_COST" in coq_types

    txt = _rtl_text()
    # LASSERT appears as explicit opcode literal in the extracted RTL.
    # LJOIN may be optimized into shared/default datapaths in generated output.
    # ORACLE_HALTS (0x10) removed from RTL — no longer checked here.
    assert "8'h03" in txt
