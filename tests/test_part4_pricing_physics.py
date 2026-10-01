from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_part4_frozen_before_proof_artifacts():
    freeze = ROOT / "research/rounds/2026-10-01-part4-round1-freeze.md"
    text = freeze.read_text()
    assert "part4-pricing-physics-target.v.sha256" in text
    assert "Predicted outcome" in text
    assert "Success" in text and "Failure" in text


def test_part4_exact_formal_outcomes_exist():
    proof = (ROOT / "coq/kernel/nfi/PricingPhysicsAudit.v").read_text()
    for name in (
        "no_forced_price_beyond_merges",
        "permanent_write_has_logical_payment",
        "mu_has_no_intrinsic_joule_value",
        "calibrated_mu_landauer_energy",
        "permanence_heat_floor_uses_landauer",
    ):
        assert f"Theorem {name}" in proof


def test_part4_report_keeps_physics_claims_conditional():
    report = (ROOT / "research/rounds/2026-10-01-part4-round1-results.md").read_text()
    assert "4.1 | PROVED BUT KNOWN" in report
    assert "4.2 | PARTIAL" in report
    assert "4.3 | PARTIAL" in report
    assert "4.4 | PROVED BUT KNOWN" in report
    assert "does not identify one μ with a measured number of joules" in report
    assert "No device measurement was performed" in report
