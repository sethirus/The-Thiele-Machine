"""Coverage-link tests for high-priority uncovered Coq bridge files."""

from pathlib import Path
import re


REPO_ROOT = Path(__file__).resolve().parents[1]


def _read(rel_path: str) -> str:
    return (REPO_ROOT / rel_path).read_text(encoding="utf-8")


def require_Extraction(text: str) -> bool:
    return "Require" in text and "Extraction" in text


def require_ExtrOcamlBasic(text: str) -> bool:
    return "ExtrOcamlBasic" in text


def require_VMState(text: str) -> bool:
    return "VMState" in text


def require_VMStep(text: str) -> bool:
    return "VMStep" in text


def require_SimulationProof(text: str) -> bool:
    return "SimulationProof" in text


def simulation_correctness_trials(text: str) -> bool:
    return bool(re.search(r"(?m)^\s*Theorem\s+simulation_correctness_trials\b", text))


def decodes_to_self(text: str) -> bool:
    return bool(re.search(r"(?m)^\s*Lemma\s+decodes_to_self\b", text))


def mu_ledger_bisim(text: str) -> bool:
    return bool(re.search(r"(?m)^\s*Definition\s+mu_ledger_bisim\b", text))


def empty_ledger_bisim(text: str) -> bool:
    return bool(re.search(r"(?m)^\s*Lemma\s+empty_ledger_bisim\b", text))


def is_chain_valid(text: str) -> bool:
    return bool(re.search(r"(?m)^\s*Definition\s+is_chain_valid\b", text))


def compute_hash_chain(text: str) -> bool:
    return bool(re.search(r"(?m)^\s*Fixpoint\s+compute_hash_chain\b", text))


def test_extraction_requires_present() -> None:
    extraction = _read("coq/Extraction.v")
    assert require_Extraction(extraction)
    assert require_ExtrOcamlBasic(extraction)
    assert require_VMState(extraction)
    assert require_VMStep(extraction)
    assert require_SimulationProof(extraction)


def test_kernel_contract_declarations_present() -> None:
    """Key kernel definitions exist (bridge/ and catnet/ were archived as disconnected)."""
    vmstep = _read("coq/kernel/VMStep.v")
    simproof = _read("coq/kernel/SimulationProof.v")
    assert require_VMStep(vmstep)
    assert "vm_is_a_correct_refinement_of_kernel" in simproof
