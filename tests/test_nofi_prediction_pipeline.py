"""Deliverable C2: falsifier harness for prediction-pipeline divergence.

We demonstrate an operational rule:
- A pipeline may *claim* improved predictive power (higher SCORE), but
- the verifier only accepts this claim if it is accompanied by:
  1) semantic structure-addition evidence (cert_addr empty->nonempty), and
  2) a paid μ-information cost.

This test is intentionally CHSH-free.
"""

from __future__ import annotations

from pathlib import Path

from verifier.prediction_pipeline import verify_prediction_pipeline


def test_prediction_pipeline_rejects_free_insight_improvement(tmp_path: Path) -> None:
    from thielecpu.state import State
    from thielecpu.vm import VM

    baseline = 0.90

    outdir = tmp_path / "nofi_prediction_forged"
    vm = VM(State())

    # Forged improvement: emit a higher score without any certificate-setting step.
    program = [
        ("PNEW", "{1}"),
        ("PYEXEC", "score = 0.99"),
        ("EMIT", "SCORE 0.99"),
        ("EMIT", "done"),
    ]

    vm.run(program, outdir)

    verdict = verify_prediction_pipeline(
        outdir,
        baseline_score=baseline,
        require_cert_for_improvement=True,
        require_mu_for_improvement=True,
        min_mu_information=1.0,
    )

    assert verdict.claimed_score == 0.99
    assert verdict.ok is False


def test_prediction_pipeline_accepts_certified_paid_improvement(tmp_path: Path) -> None:
    from thielecpu.state import State
    from thielecpu.vm import VM

    baseline = 0.90

    outdir = tmp_path / "nofi_prediction_certified"
    vm = VM(State())

    # Certified improvement: REVEAL charges μ-information and creates cert evidence.
    program = [
        ("PNEW", "{1}"),
        ("REVEAL", "1 64 cert_payload_for_score"),
        ("PYEXEC", "score = 0.99"),
        ("EMIT", "SCORE 0.99"),
        ("EMIT", "done"),
    ]

    vm.run(program, outdir)

    verdict = verify_prediction_pipeline(
        outdir,
        baseline_score=baseline,
        require_cert_for_improvement=True,
        require_mu_for_improvement=True,
        min_mu_information=1.0,
    )

    assert verdict.claimed_score == 0.99
    assert verdict.has_structure_addition is True
    assert verdict.mu_information_total >= 1.0
    assert verdict.ok is True
