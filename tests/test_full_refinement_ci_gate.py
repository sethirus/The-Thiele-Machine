"""CI gate: full-refinement theorem presence and strength.

Phase 7 of FULL_REFINEMENT_GUIDE.md — ensures the stronger refinement
theorems cannot silently disappear or weaken without breaking CI.
"""
from __future__ import annotations

from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]


# ---------------------------------------------------------------------------
# Python bridge theorem guards
# ---------------------------------------------------------------------------

def test_python_full_state_bridge_theorems_exist() -> None:
    """Guard: PythonBisimulation.v must contain full-state step+run refinement."""
    text = (ROOT / "coq" / "kernel" / "PythonBisimulation.v").read_text(encoding="utf-8")
    required = [
        "Record PythonStateFull",
        "Definition python_full_abs",
        "Definition python_full_repr",
        "Theorem python_step_full_refines",
        "Theorem python_run_full_refines",
    ]
    for needle in required:
        assert needle in text, f"Missing Python full-state bridge: {needle}"


# ---------------------------------------------------------------------------
# Kami bridge theorem guards
# ---------------------------------------------------------------------------

def test_kami_full_state_bridge_theorems_exist() -> None:
    """Guard: FullStep.v must contain full-state step+run refinement."""
    text = (ROOT / "coq" / "kami_hw" / "FullStep.v").read_text(encoding="utf-8")
    required = [
        "Definition kami_step_full",
        "Theorem kami_step_full_refines",
        "Fixpoint kami_run_full",
        "Theorem kami_run_full_refines",
    ]
    for needle in required:
        assert needle in text, f"Missing Kami full-state bridge: {needle}"


def test_full_embed_step_main_theorem_exists() -> None:
    """Guard: FullEmbedStep.v must contain the 31-opcode full-state theorem."""
    text = (ROOT / "coq" / "kami_hw" / "FullEmbedStep.v").read_text(encoding="utf-8")
    required = [
        "Theorem full_embed_step_compute",
        "Theorem full_embed_step_trace",
        "Theorem full_embed_step_general",
    ]
    for needle in required:
        assert needle in text, f"Missing FullEmbedStep theorem: {needle}"


# ---------------------------------------------------------------------------
# Extraction targets canonical vm_apply
# ---------------------------------------------------------------------------

def test_extraction_targets_simulation_proof_vm_apply() -> None:
    """Guard: Extraction.v must extract from SimulationProof.vm_apply."""
    text = (ROOT / "coq" / "Extraction.v").read_text(encoding="utf-8")
    assert "SimulationProof.vm_apply" in text, \
        "Extraction.v does not reference SimulationProof.vm_apply"


# ---------------------------------------------------------------------------
# No Admitted in full-refinement proof files
# ---------------------------------------------------------------------------

FULL_REFINEMENT_FILES = [
    "coq/kernel/PythonBisimulation.v",
    "coq/kami_hw/FullAbstraction.v",
    "coq/kami_hw/FullStep.v",
    "coq/kami_hw/FullEmbedStep.v",
    "coq/kami_hw/RichStateCommutation.v",
]


@pytest.mark.parametrize("relpath", FULL_REFINEMENT_FILES)
def test_no_admitted_in_refinement_files(relpath: str) -> None:
    """Guard: full-refinement proof files must have zero Admitted."""
    path = ROOT / relpath
    if not path.exists():
        pytest.fail(f"Full-refinement file missing: {relpath}")
    text = path.read_text(encoding="utf-8")
    import re
    matches = re.findall(r"^\s*Admitted\.", text, re.MULTILINE)
    assert len(matches) == 0, f"{relpath} has {len(matches)} Admitted proof(s)"


# ---------------------------------------------------------------------------
# No "full bisimulation" language without backing theorems
# ---------------------------------------------------------------------------

def test_readme_does_not_overclaim_full_bisimulation() -> None:
    """Guard: README.md should not claim 'full bisimulation' without qualifier."""
    text = (ROOT / "README.md").read_text(encoding="utf-8").lower()
    if "full bisimulation" in text:
        # If the phrase appears, it must be accompanied by a reference to
        # the actual theorem or a qualifier about scope.
        assert "full_embed_step" in text or "documented" in text or "35" in text, \
            "README.md claims 'full bisimulation' without referencing the actual theorem scope"
