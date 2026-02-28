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
    assert 'Definition ERR_PARTITION_VAL' in txt
    assert '0xBADF001D' in txt


def test_logic_gate_not_stubbed_and_high_value_ops_are_gated() -> None:
    txt = CORE.read_text(encoding="utf-8")
    assert 'LET high_value_locked <- $$false;' not in txt
    assert 'LET is_high_value_op <-' in txt
    assert '(#opcode == $$(OP_REVEAL))' in txt
    assert '(#opcode == $$(OP_PDISCOVER))' in txt
    assert 'LET high_value_locked <- #is_high_value_op && !#logic_key_ok;' in txt


def test_stack_operations_are_partition_bounded() -> None:
    txt = CORE.read_text(encoding="utf-8")
    assert 'LET call_in_bounds <- check_bounds #sp_addr #active_region_size;' in txt
    assert 'LET ret_in_bounds <- check_bounds #sp_dec_addr #active_region_size;' in txt
    assert 'LET call_locality_bad <- #is_call_op && !#call_in_bounds;' in txt
    assert 'LET ret_locality_bad <- #is_ret_op && !#ret_in_bounds;' in txt


def test_partition_table_wraparound_is_explicitly_guarded() -> None:
    txt = CORE.read_text(encoding="utf-8")
    assert 'LET ptable_room_one <- #pt_next_id_v < $64;' in txt
    assert 'LET ptable_room_two <- (#pt_next_id_v + $1) < $64;' in txt
    assert 'LET ptable_overflow_violation <- #pnew_overflow || #psplit_overflow || #pmerge_overflow;' in txt
    assert 'ERR_PARTITION_VAL' in txt


def test_no_free_insight_gate_is_wired_in_core() -> None:
    txt = CORE.read_text(encoding="utf-8")
    assert 'LET nfi_violation <- #is_info_gain_op && (#cost32 < #op_b_32);' in txt
    assert '!#nfi_violation' in txt
    assert 'then $$(ERR_LOGIC_VAL)' in txt
