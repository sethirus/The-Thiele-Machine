"""Acceptance checks for the exact two-state calorimeter protocol."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PROOF = ROOT / "coq/kernel/thermodynamic/CalorimeterProtocol.v"


def test_calorimeter_closes_exact_and_boundary_theorems():
    text = PROOF.read_text()
    assert "Theorem canonical_reset_satisfies_master_equation" in text
    assert "Theorem canonical_reset_heat_exact" in text
    assert "Theorem selected_gap_gives_landauer_heat" in text
    assert "Theorem smaller_gap_refutes_unconditional_landauer_floor" in text


def test_calorimeter_does_not_claim_an_intrinsic_mu_scale():
    text = PROOF.read_text()
    assert "master_equation_does_not_fix_heat_scale" in text
    assert "Print Assumptions smaller_gap_refutes_unconditional_landauer_floor" in text
