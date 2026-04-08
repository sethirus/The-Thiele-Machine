from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_kami_full_state_bridge_theorems_are_present() -> None:
    text = (ROOT / "coq" / "kami_hw" / "FullStep.v").read_text(encoding="utf-8")

    assert "Definition kami_step_full" in text
    assert "Theorem kami_step_full_refines" in text
    assert "Fixpoint kami_run_full" in text
    assert "Theorem kami_run_full_refines" in text


def test_full_embed_step_theorems_are_present() -> None:
    text = (ROOT / "coq" / "kami_hw" / "FullEmbedStep.v").read_text(encoding="utf-8")

    expected = [
        "Definition with_graph",
        "Lemma full_abs_as_with_graph",
        "Lemma kami_step_preserves_full_graph",
        "Lemma vm_apply_with_graph_commute",
        "Theorem full_embed_step_compute",
        "Theorem full_embed_step",
        "Theorem full_embed_step_trace",
        "Theorem full_embed_step_general",
    ]
    for needle in expected:
        assert needle in text, f"Missing FullEmbedStep theorem: {needle}"


def test_kami_snapshot_has_rich_state_payload() -> None:
    text = (ROOT / "coq" / "kami_hw" / "Abstraction.v").read_text(encoding="utf-8")

    assert "Record RichSnapshotState" in text
    assert "Record FormulaDescriptorEntry" in text
    assert "Record CertificationDescriptorEntry" in text
    assert "Record DescriptorMetadataEntry" in text
    assert "Record LassertShadowState" in text
    assert "snap_rich_state" in text
    assert "Definition snap_full_graph" in text
    assert "snapshot_morphisms_of_rich_state" in text


def test_kami_core_declares_bounded_rich_state_tables() -> None:
    text = (ROOT / "coq" / "kami_hw" / "ThieleCPUCore.v").read_text(encoding="utf-8")

    expected = [
        'Register "morph_src_table"',
        'Register "morph_dst_table"',
        'Register "morph_coupling_desc_table"',
        'Register "morph_valid_table"',
        'Register "morph_identity_table"',
        'Register "morph_next_id"',
        'Register "coupling_desc_base_table"',
        'Register "coupling_desc_count_table"',
        'Register "coupling_desc_valid_table"',
        'Register "coupling_desc_next_id"',
        'Register "coupling_pair_src_table"',
        'Register "coupling_pair_dst_table"',
        'Register "coupling_pair_valid_table"',
        'Register "coupling_pair_next_id"',
        'Register "formula_desc_base_table"',
        'Register "formula_desc_count_table"',
        'Register "formula_desc_valid_table"',
        'Register "formula_desc_next_id"',
        'Register "cert_desc_base_table"',
        'Register "cert_desc_count_table"',
        'Register "cert_desc_valid_table"',
        'Register "cert_desc_next_id"',
        'Register "desc_meta_subtype_table"',
        'Register "desc_meta_kind_table"',
        'Register "desc_meta_inline_len_table"',
        'Register "desc_meta_aux_table"',
        'Register "desc_meta_valid_table"',
        'Register "desc_meta_next_id"',
        'Register "cert_addr"',
        'Method "getMorphNextId"',
        'Method "getMorphSrc"',
        'Method "getMorphDst"',
        'Method "getMorphCouplingDesc"',
        'Method "getCouplingDescBase"',
        'Method "getCouplingPairSrc"',
        'Method "getFormulaDescBase"',
        'Method "getFormulaDescNextId"',
        'Method "getCertDescBase"',
        'Method "getCertDescNextId"',
        'Method "getDescMetaSubtype"',
        'Method "getDescMetaNextId"',
        'Method "getCertAddr"',
        'Method "getLassertPhase"',
        'Method "getLassertFbufWord"',
        'Method "getLassertCbufWord"',
    ]
    for needle in expected:
        assert needle in text, f"Missing rich-state hardware declaration: {needle}"


def test_rich_state_error_codes_are_declared() -> None:
    text = (ROOT / "coq" / "kami_hw" / "ThieleTypes.v").read_text(encoding="utf-8")

    expected = [
        "ERR_ISA_VERSION",
        "ERR_FORMAT_INVALID",
        "ERR_DESC_RANGE",
        "ERR_INLINE_MALFORMED",
        "ERR_TABLE_OVERFLOW",
        "ERR_CERT_DESC_INVALID",
    ]
    for needle in expected:
        assert needle in text, f"Missing rich-state fault code: {needle}"


def test_kami_core_wires_rich_fault_decode_and_trap_path() -> None:
    text = (ROOT / "coq" / "kami_hw" / "ThieleCPUCore.v").read_text(encoding="utf-8")

    expected = [
        "LET isa_version : Bit 8 <-",
        "LET flags : Bit 16 <-",
        "LET desc_kind : Bit DescKindFieldSz <-",
        "LET inline_len : Bit InlineLenSz <-",
        "LET generic_desc_range_fault <-",
        "LET cert_desc_invalid <-",
        "LET rich_table_overflow <-",
        "LET rich_fault <-",
        "LET rich_fault_error_code : Bit WordSz <-",
        "then $$(ERR_ISA_VERSION)",
        "then $$(ERR_FORMAT_INVALID)",
        "then $$(ERR_DESC_RANGE)",
        "then $$(ERR_INLINE_MALFORMED)",
        "then $$(ERR_TABLE_OVERFLOW)",
        "then $$(ERR_CERT_DESC_INVALID)",
        'Write "lassert_phase"      <- IF (#is_lassert && #lassert_is_sat && !#rich_fault)',
    ]
    for needle in expected:
        assert needle in text, f"Missing rich-fault decoder hook: {needle}"
