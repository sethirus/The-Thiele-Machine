"""The real-system models contain the machinery their results talk about.

docs/RESULTS.md states each model's scope. These checks make sure the Coq
models are not prose: the RFC 9162 verifiers keep their iterative control
flow, the proof-carrying-code fragment keeps its consumer pipeline, the RAMs
keep indirect addressing and branching, and the TPM refutation keeps its
assumption report.
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
KERNEL = ROOT / "coq" / "kernel"


def read(relative: str) -> str:
    return (KERNEL / relative).read_text(encoding="utf-8")


def test_rfc9162_model_contains_the_iterative_verifiers():
    text = read("reductions/RFC9162MerkleTarget.v")
    for symbol in ("hash_leaf", "hash_node", "inclusion_fold", "verify_inclusion",
                   "consistency_fold", "verify_consistency"):
        assert symbol in text
    assert "Nat.odd fn" in text
    assert "Nat.div2" in text


def test_pcc_fragment_models_the_consumer_pipeline():
    text = read("reductions/NeculaPCCTarget.v")
    for token in ("policy_allows", "verification_condition", "PCCProof", "check_program"):
        assert token in text


def test_concrete_record_machines_define_their_steps():
    text = read("reductions/ConcreteRecordMachinesTarget.v")
    for token in ("tied_step", "untied_step", "junbounded_step", "jbounded_step"):
        assert token in text


def test_cook_reckhow_ram_has_indirect_access_and_branching():
    text = read("foundation/CrossBaseGranularityRAM.v")
    for token in ("RLoadInd", "RStoreInd", "RJumpPos"):
        assert token in text
    for name in ("ram_store_then_load", "ram_jump_pos_taken", "ram_halted_stutters",
                 "ram_base_has_initial", "record_axis_is_latch_on_ram_holds"):
        assert f"Theorem {name}" in text
        assert f"Print Assumptions {name}." in text


def test_l_adapter_agrees_with_the_reduction_relation():
    text = read("foundation/CrossBaseGranularityL.v")
    for name in ("l_step_fun_correct", "l_base_halted_iff_irreducible",
                 "l_base_run_is_star", "star_is_l_base_run",
                 "record_axis_is_latch_on_l_holds"):
        assert f"Theorem {name}" in text
        assert f"Print Assumptions {name}." in text


def test_tpm_refutation_reports_its_assumptions():
    text = read("reductions/TPMQuoteAuthenticity.v")
    assert "Print Assumptions tpm_interface_authenticity_refuted" in text


def test_five_narrow_consequences_are_theorems():
    text = read("reductions/RealSystemConsequences.v")
    for name in ("ct_local_view_insufficient", "tpm_selection_binding_is_necessary",
                 "weak_subjective_suffix_insufficient", "wal_ack_requires_durability",
                 "audit_local_snapshot_insufficient"):
        assert f"Theorem {name}" in text
