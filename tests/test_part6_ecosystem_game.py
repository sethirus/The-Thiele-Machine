"""Acceptance checks for the ecosystem-game necessity test."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "coq/kernel/frontier/EcosystemGameTarget.v"
PROOF = ROOT / "coq/kernel/frontier/EcosystemGame.v"


def test_frozen_strong_statement_is_not_weakened():
    text = TARGET.read_text()
    assert "Definition strong_pointer_necessity : Prop" in text
    assert "observer_consensus g ->" in text
    assert "observer_authenticity g ->" in text
    assert "coordinator_free_update g ->" in text
    assert "event_permanent g." in text


def test_counterexample_and_durable_boundary_are_closed():
    text = PROOF.read_text()
    assert "Theorem toggle_game_refutes_strong_pointer_necessity" in text
    assert "Theorem durable_consensus_implies_permanence" in text
    assert "Print Assumptions toggle_game_refutes_strong_pointer_necessity" in text
    assert "Print Assumptions durable_consensus_implies_permanence" in text
