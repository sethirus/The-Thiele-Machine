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


def test_phantom_foundation_import_is_not_satisfied_by_binder_names(tmp_path: Path) -> None:
    """A file that imports EarnedCore and only uses binders named n, S or H must be
    reported; the declared-name sets hold real identifiers, not binder-like names."""
    inquisitor = _inquisitor_module()
    names = inquisitor._foundation_module_decls("EarnedCore")
    for binder in ("n", "S", "H", "a", "i", "_", "mu", "run", "err", "pc"):
        assert binder not in names, binder
    assert "run_prog" in names and "halted" in names

    source = tmp_path / "UsesOnlyBinders.v"
    source.write_text(
        "From Coq Require Import Arith.\n"
        "Require Minimal.EarnedCore.\n"
        "\n"
        "Theorem plus_zero_right : forall n : nat, n + 0 = n.\n"
        "Proof. intros n. rewrite Nat.add_0_r. reflexivity. Qed.\n",
        encoding="utf-8",
    )
    findings = inquisitor.scan_phantom_imports(source)
    assert [f.rule_id for f in findings] == ["PHANTOM_KERNEL_IMPORT"], findings


def test_foundation_import_that_uses_a_declared_name_is_accepted(tmp_path: Path) -> None:
    inquisitor = _inquisitor_module()
    source = tmp_path / "UsesRunProg.v"
    source.write_text(
        "Require Minimal.EarnedCore.\n"
        "Module E := Minimal.EarnedCore.\n"
        "\n"
        "Theorem halted_stays : forall P s, E.halted P (E.core_of s) -> True.\n"
        "Proof. intros. exact I. Qed.\n",
        encoding="utf-8",
    )
    assert inquisitor.scan_phantom_imports(source) == []


def test_kernel_file_importing_an_unknown_namespace_is_a_tier1_finding(tmp_path: Path) -> None:
    """Under coq/kernel/ only Coq, Kernel, Minimal, Undecidability and TestFixtures may be
    imported; any other namespace, in a From line or a qualified Require, is reported
    unless a SCOPE NOTE above it gives the reason."""
    inquisitor = _inquisitor_module()
    kernel = tmp_path / "coq" / "kernel"
    kernel.mkdir(parents=True)

    def scan(name: str, body: str):
        source = kernel / name
        source.write_text(body, encoding="utf-8")
        return [f.rule_id for f in inquisitor.scan_scope_drift(source)]

    allowed = (
        "From Coq Require Import List.\n"
        "From Kernel Require Import Foo.\n"
        "From Undecidability.MinskyMachines Require Import MM.\n"
        "Require Minimal.EarnedCore.\n"
        "Require Import Kernel.Bar Minimal.EarnedGeneric.\n"
    )
    assert scan("Allowed.v", allowed) == []
    assert scan("FromLine.v", "From Mystery Require Import Foo.\n") == ["SCOPE_DRIFT_TIER1"]
    assert scan("QualifiedLine.v", "Require Import Mystery.Foo.\n") == ["SCOPE_DRIFT_TIER1"]
    assert scan(
        "Noted.v",
        "(* SCOPE NOTE: cross-tier import for a pinned external library. *)\n"
        "From Mystery Require Import Foo.\n",
    ) == []
