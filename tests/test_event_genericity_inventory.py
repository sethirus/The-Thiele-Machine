"""Extraction tests for the frozen Item 1.1 occurrence inventory.

These tests pin the claim-surface grammar and resolution machinery. They do
not test the semantic event-genericity predictions or their Coq evidence.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MODULE_PATH = ROOT / "scripts" / "event_genericity_inventory.py"
SPEC = importlib.util.spec_from_file_location("event_genericity_inventory", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
inventory = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = inventory
SPEC.loader.exec_module(inventory)


def test_wrapped_latex_identifier_is_one_token(tmp_path: Path) -> None:
    source = tmp_path / "wrapped.tex"
    source.write_text(r"See \code{Kernel.\allowbreak{}Module.some\_theorem}." + "\n")
    rows = inventory.raw_occurrences(source, "wrapped.tex")
    assert [(row.syntax, row.token) for row in rows] == [
        ("latex_code", "Kernel.Module.some_theorem")
    ]


def test_claim_ledger_and_key_results_syntaxes_are_typed(tmp_path: Path) -> None:
    source = tmp_path / "claims.md"
    source.write_text(
        r"\textit{\small first\_theorem / second\_theorem}" + "\n"
        "Key results: third_theorem, fourth_theorem (+2 more)\n"
    )
    rows = inventory.raw_occurrences(source, "claims.md")
    assert {(row.syntax, row.token) for row in rows} == {
        ("latex_small", "first_theorem"),
        ("latex_small", "second_theorem"),
        ("key_results", "third_theorem"),
        ("key_results", "fourth_theorem"),
    }


def test_latex_theorem_label_is_seen(tmp_path: Path) -> None:
    source = tmp_path / "labels.tex"
    source.write_text(r"\begin{theorem}\label{thm:tensor_bifunctor}X\end{theorem}" + "\n")
    rows = inventory.raw_occurrences(source, "labels.tex")
    assert [(row.syntax, row.token) for row in rows] == [
        ("latex_theorem_label", "tensor_bifunctor")
    ]


def test_frozen_claim_surface_and_universe_are_exhaustive() -> None:
    typed, declarations, errors = inventory.type_occurrences(
        ROOT, inventory.DEFAULT_BINDINGS
    )
    assert errors == []
    proof_rows = [row for row in typed if row.occurrence_kind == "proof"]
    nonproof_rows = [row for row in typed if row.occurrence_kind == "nonproof"]
    universe = {row.identity for row in proof_rows}
    unaddressable = {
        identity
        for identity in universe
        if declarations[identity].addressability != "addressable"
    }
    assert len(inventory.discover_sources(ROOT)) == 39
    assert len(proof_rows) == 1143
    assert len(nonproof_rows) == 4066
    assert len(universe) == 472
    assert unaddressable == {
        "NoFI.MuChaitinTheory_Theorem.MuChaitinTheory.mu_info_nat_le_from_mu_budget",
        "NoFI.MuChaitinTheory_Theorem.MuChaitinTheory.proves_bits_bounded_by_description",
        "NoFI.MuChaitinTheory_Theorem.MuChaitinTheory.supra_cert_run_implies_paid_payload",
        "NoFI.NoFreeInsight_Theorem.NoFreeInsight.no_free_insight",
    }


def test_ambiguous_names_use_the_frozen_bindings() -> None:
    typed, _, errors = inventory.type_occurrences(ROOT, inventory.DEFAULT_BINDINGS)
    assert errors == []
    resolved = {
        (row.token, row.identity, row.resolution)
        for row in typed
        if row.token in {"tensor_bifunctor", "trace_run_mu_monotone"}
        and row.occurrence_kind == "proof"
    }
    assert resolved == {
        (
            "tensor_bifunctor",
            "Kernel.CategoryMonoidal.tensor_bifunctor",
            "explicit_binding",
        ),
        (
            "trace_run_mu_monotone",
            "NoFI.Instance_Kernel.KernelNoFI.trace_run_mu_monotone",
            "explicit_binding",
        ),
    }


def test_descriptive_theorem_labels_have_explicit_proof_support() -> None:
    typed, _, errors = inventory.type_occurrences(ROOT, inventory.DEFAULT_BINDINGS)
    assert errors == []
    all_channels = {
        (row.identity, row.resolution)
        for row in typed
        if row.syntax == "latex_theorem_label" and row.token == "allchannels"
    }
    assert all_channels == {
        (
            "Kernel.AbstractNoFI.no_free_certification_trace_mu",
            "label_aggregate",
        ),
        (
            "Kernel.WitnessInsightGeneral.no_free_certification_certified_trace_mu",
            "label_aggregate",
        ),
    }
    dimensional_gap = {
        (row.identity, row.resolution)
        for row in typed
        if row.syntax == "latex_theorem_label" and row.token == "dimensional_gap"
    }
    assert dimensional_gap == {
        (
            "Kernel.DimensionalGapTheorem.dimensional_gap_forces_constant",
            "label_proof",
        )
    }
