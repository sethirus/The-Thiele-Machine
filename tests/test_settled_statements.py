"""Each settled question has a Coq theorem with exactly the stated shape.

A proved result is a theorem whose statement is the named proposition; a
refuted one is a theorem whose statement is its negation. docs/RESULTS.md
describes these results; this file pins the exact statements so that a
renamed or weakened proposition fails here.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
KERNEL = ROOT / "coq" / "kernel"

SETTLED = {
    "foundation/StructuralRecordAxis.v": {
        "record_axis_is_latch_holds": "record_axis_is_latch",
        "record_pair_is_two_latches_holds": "record_pair_is_two_latches",
    },
    "foundation/GrowingRecord.v": {
        "growing_record_decomposes_holds": "growing_record_decomposes",
        "thresholds_determine_record_holds": "thresholds_determine_record",
        "record_price_iff_threshold_price_holds": "record_price_iff_threshold_price",
        "one_latch_refuted": "~ one_latch_suffices",
        "chain_needs_bits_holds": "chain_needs_bits",
    },
    "foundation/ProbabilisticRecord.v": {
        "deterministic_latch_handles_branching_refuted": "~ deterministic_latch_handles_branching",
        "schedule_determines_probabilities_refuted": "~ schedule_determines_probabilities",
        "probability_preserving_equivalence_reflexive_holds":
            "probability_preserving_equivalence_reflexive",
    },
    "foundation/CrossBaseGranularity.v": {
        "weak_base_equiv_refl_holds": "weak_base_equiv_refl",
        "weak_base_equiv_sym_holds": "weak_base_equiv_sym",
        "weak_base_equiv_trans_holds": "weak_base_equiv_trans",
        "weak_equiv_preserves_record_latch_holds": "weak_equiv_preserves_record_latch",
        "record_axis_is_latch_on_tm_holds": "record_axis_is_latch_on_tm",
    },
    "foundation/CrossBaseGranularityL.v": {
        "record_axis_is_latch_on_l_holds": "record_axis_is_latch_on l_base",
    },
    "foundation/CrossBaseGranularityRAM.v": {
        "record_axis_is_latch_on_ram_holds": "forall p, record_axis_is_latch_on (ram_base p)",
    },
    "nfi/PricingPhysicsAudit.v": {
        "no_forced_price_beyond_merges":
            "forall (S I : Type) (step : S -> I -> S) "
            "(instr_eq_dec : forall a b : I, {a = b} + {a <> b}), "
            "no_price_beyond_merges step instr_eq_dec",
        "permanent_write_has_logical_payment":
            "forall (S I : Type) (step : S -> I -> S) (cert : S -> bool), "
            "permanent_flip_logical_payment step cert",
        "mu_has_no_intrinsic_joule_value": "no_intrinsic_joule_scale",
        "calibrated_mu_landauer_energy": "forall k_B T : R, mu_landauer_calibration k_B T",
        "permanence_heat_floor_uses_landauer": "landauer_permanence_heat_floor",
    },
    "frontier/RecordProliferationSurvey.v": {
        "twelve_candidate_measurements_checked": "twelve_candidate_measurements",
        "swapped_event_is_pointer_checked": "swapped_event_is_pointer",
    },
    "frontier/EcosystemGame.v": {
        "toggle_game_refutes_strong_pointer_necessity": "~ strong_pointer_necessity",
    },
    "reductions/TPMQuoteAuthenticity.v": {
        "tpm_interface_authenticity_refuted": "interface_authenticity_refuted",
    },
}

CASES = [
    (relative, name, statement)
    for relative, theorems in SETTLED.items()
    for name, statement in theorems.items()
]


def statement(source: str, name: str) -> str:
    match = re.search(
        rf"^Theorem\s+{re.escape(name)}\s*:(.*?)\.\s*Proof\.",
        source,
        flags=re.MULTILINE | re.DOTALL,
    )
    assert match is not None, f"missing theorem: {name}"
    return " ".join(match.group(1).split())


@pytest.mark.parametrize(("relative", "name", "expected"), CASES,
                         ids=[name for _, name, _ in CASES])
def test_settled_theorem_has_the_stated_shape(relative: str, name: str, expected: str):
    source = (KERNEL / relative).read_text(encoding="utf-8")
    assert statement(source, name) == expected


@pytest.mark.parametrize("relative", sorted(SETTLED))
def test_settling_file_has_no_holes(relative: str):
    source = (KERNEL / relative).read_text(encoding="utf-8")
    assert not re.search(r"\bAdmitted\.|^\s*(Axiom|Parameter|Hypothesis)\s", source,
                         re.MULTILINE)


@pytest.mark.parametrize("relative", sorted(SETTLED))
def test_settling_file_is_built_with_the_project(relative: str):
    project = (ROOT / "coq" / "_CoqProject").read_text(encoding="utf-8").splitlines()
    assert f"kernel/{relative}" in project


def test_strong_pointer_necessity_keeps_its_premises():
    text = (KERNEL / "frontier/EcosystemGameTarget.v").read_text(encoding="utf-8")
    assert "Definition strong_pointer_necessity : Prop" in text
    for premise in ("observer_consensus g ->", "observer_authenticity g ->",
                    "coordinator_free_update g ->", "event_permanent g."):
        assert premise in text


def test_durable_boundary_and_calorimeter_theorems_exist():
    ecosystem = (KERNEL / "frontier/EcosystemGame.v").read_text(encoding="utf-8")
    assert "Theorem durable_consensus_implies_permanence" in ecosystem
    calorimeter = (KERNEL / "thermodynamic/CalorimeterProtocol.v").read_text(encoding="utf-8")
    for name in ("canonical_reset_satisfies_master_equation", "canonical_reset_heat_exact",
                 "selected_gap_gives_landauer_heat",
                 "canonical_reset_heat_below_landauer_at_small_gap",
                 "master_equation_does_not_fix_heat_scale"):
        assert f"Theorem {name}" in calorimeter
        assert f"Print Assumptions {name}." in calorimeter
