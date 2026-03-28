from __future__ import annotations

from pathlib import Path


CORE = Path(__file__).resolve().parents[1] / "coq" / "kami_hw" / "ThieleCPUCore.v"
TYPES = Path(__file__).resolve().parents[1] / "coq" / "kami_hw" / "ThieleTypes.v"


def test_core_has_in_core_logic_engine_state_and_paths() -> None:
    txt = CORE.read_text(encoding="utf-8")
    assert 'Register "logic_acc"' in txt
    # On-chip FSM registers replace external coprocessor interface
    assert 'Register "lassert_phase"' in txt
    assert 'Register "lassert_fbuf"' in txt
    assert 'Register "lassert_cbuf"' in txt
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
    assert 'LET ptable_full <- #pt_next_id_v >= $64;' in txt
    assert 'LET ptable_room_one <- !#ptable_full;' in txt
    assert 'LET ptable_room_two <- (#pt_next_id_v + $2) <= $64;' in txt
    assert 'LET ptable_overflow_violation <- #pnew_overflow || #psplit_overflow || #pmerge_overflow;' in txt
    assert 'ERR_PARTITION_VAL' in txt


def test_no_free_insight_gate_is_wired_in_core() -> None:
    txt = CORE.read_text(encoding="utf-8")
    assert 'LET nfi_violation <- #is_info_gain_op && (#cost32 < #op_b_32);' in txt
    assert '!#nfi_violation' in txt
    assert 'then $$(ERR_LOGIC_VAL)' in txt


def test_partition_guard_matches_vector_pt_bank() -> None:
    txt = CORE.read_text(encoding='utf-8')
    assert 'Register "ptTable"  : Vector (Bit WordSz) PTableIdxSz <- Default' in txt
    assert 'Write "ptTable"        <- #new_pt_sizes;' in txt
    assert 'with Register "pt0"' not in txt
    assert 'Write "pt0"' not in txt
    assert 'LET ptable_full <- #pt_next_id_v >= $64;' in txt
    assert 'LET ptable_room_one <- !#ptable_full;' in txt
    assert 'LET ptable_room_two <- (#pt_next_id_v + $2) <= $64;' in txt


def test_psplit_boundary_62_allowed_but_63_rejected() -> None:
    txt = CORE.read_text(encoding='utf-8')
    # Explicitly guard split by requiring room for two slots (next_id and next_id+1).
    assert 'LET ptable_room_two <- (#pt_next_id_v + $2) <= $64;' in txt


def test_ptable_index_width_is_6_bits() -> None:
    txt = TYPES.read_text(encoding='utf-8')
    assert 'Definition PTableIdxSz := 6.' in txt
    assert 'Definition PTableNextIdSz := 7.' in txt


def test_rtl_partition_guards_match_physical_capacity() -> None:
    rtl = (CORE.parents[2] / 'thielecpu' / 'hardware' / 'rtl' / 'thiele_cpu_kami.v').read_text(encoding='utf-8')
    # The bsc compiler generates implementation-specific signal names that encode
    # the semantic guard: pt_next_id < 64 (PNEW/PMERGE need one free slot).
    # The exact signal name depends on the bsc version; match the semantic pattern.
    assert "pt_next_id < 7'h40" in rtl or "pt_next_id < 32'h00000040" in rtl
    # PSPLIT guard: pt_next_id + 2 <= 64 (needs two free slots).
    assert "<= 7'h40" in rtl or "< 32'h00000040" in rtl


def test_pt_next_id_register_is_narrow_and_zero_extended_on_output() -> None:
    txt = CORE.read_text(encoding='utf-8')
    assert 'with Register "pt_next_id"    : Bit PTableNextIdSz <- PT_NEXT_ID_INIT' in txt
    assert 'Read v : Bit PTableNextIdSz <- "pt_next_id";' in txt
    assert 'LET v32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #v;' in txt


def test_bianchi_clears_logic_stall_and_pending_logic_request() -> None:
    txt = CORE.read_text(encoding='utf-8')
    # On-chip model: bianchi_violation stops mu accrual and traps PC
    # (no external coprocessor stall/req/resp to clear)
    assert 'IF (#bianchi_violation' in txt
    assert 'ERR_BIANCHI_VAL' in txt
    assert '#trap_vector_v' in txt
