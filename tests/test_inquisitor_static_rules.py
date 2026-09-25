"""Regression tests for source-level proof-audit rules."""
from __future__ import annotations

import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent


def _inquisitor_module():
    sys.path.insert(0, str(REPO_ROOT / "scripts"))
    try:
        import inquisitor  # type: ignore[import-not-found]
    finally:
        sys.path.pop(0)
    return inquisitor


def test_nested_true_conjunct_with_closing_delimiter_is_reported(tmp_path: Path) -> None:
    """The historical vacuity shape must not pass the static scanner."""
    source = tmp_path / "StressEnergyDynamics.v"
    source.write_text(
        """Theorem information_gravity_coupling : forall s m threshold,
  high_stress_energy_module s m threshold ->
  exists encoding_bound,
    (module_encoding_length s m >= encoding_bound)%nat /\\
    (forall (trace : list vm_instruction) (s' : VMState),
      (exists (mid : ModuleID), In (instr_pnew region encoding_bound) trace) ->
      True
    ).
Proof.
  intros s m threshold Hhigh.
  exists (module_encoding_length s m).
  split.
  - apply PeanoNat.Nat.le_refl.
  - intros trace s' Hpnew.
    trivial.
Qed.
""",
        encoding="utf-8",
    )

    inquisitor = _inquisitor_module()
    findings = inquisitor.scan_vacuous_conjunction(source)

    assert any(
        finding.rule_id == "VACUOUS_CONJUNCTION"
        and finding.line == 1
        for finding in findings
    ), [(finding.rule_id, finding.line, finding.snippet) for finding in findings]
