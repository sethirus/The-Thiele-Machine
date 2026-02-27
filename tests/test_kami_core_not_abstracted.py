from __future__ import annotations

from pathlib import Path


CORE = Path(__file__).resolve().parents[1] / "coq" / "kami_hw" / "ThieleCPUCore.v"
TYPES = Path(__file__).resolve().parents[1] / "coq" / "kami_hw" / "ThieleTypes.v"


def test_core_has_in_core_logic_engine_state_and_paths() -> None:
    txt = CORE.read_text(encoding="utf-8")
    assert 'Register "logic_acc"' in txt
    assert 'LET logic_issue <-' in txt
    assert 'Register "logic_req_valid"' in txt
    assert 'Register "logic_resp_valid"' in txt
    assert 'OP_LASSERT' in txt and 'OP_LJOIN' in txt and 'OP_ORACLE_HALTS' in txt
    assert 'LET new_logic_acc : Bit WordSz <-' in txt
    assert 'Write "logic_acc"      <- #new_logic_acc;' in txt


def test_logic_error_code_constant_is_declared() -> None:
    txt = TYPES.read_text(encoding="utf-8")
    assert 'Definition ERR_LOGIC_VAL' in txt
    assert '0xC43471A1' in txt
