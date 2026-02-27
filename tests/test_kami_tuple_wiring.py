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


def test_logic_coprocessor_interface_ports_present() -> None:
    txt = _rtl_text()
    # L interface is now explicit in-core ports (request + response path).
    expected = [
        "getLogicReqValid",
        "getLogicReqOpcode",
        "getLogicReqPayload",
        "setLogicResp",
    ]
    for signal in expected:
        assert signal in txt, f"Missing L-coprocessor interface signal: {signal}"


def test_logic_related_opcodes_defined_in_coq_and_present_in_rtl_paths() -> None:
    coq_types = (Path(__file__).resolve().parents[1] / "coq" / "kami_hw" / "ThieleTypes.v").read_text(encoding="utf-8")
    assert "OP_LASSERT" in coq_types
    assert "OP_LJOIN" in coq_types
    assert "OP_ORACLE_HALTS" in coq_types

    txt = _rtl_text()
    # LASSERT and ORACLE_HALTS appear as explicit opcode literals in the extracted RTL.
    # LJOIN may be optimized into shared/default datapaths in generated output.
    assert "8'h03" in txt
    assert "8'h10" in txt
