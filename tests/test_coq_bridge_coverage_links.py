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
    minimal = _read("coq/MinimalExtraction.v")
    assert require_Extraction(extraction)
    assert require_Extraction(minimal)
    assert require_ExtrOcamlBasic(extraction)
    assert require_ExtrOcamlBasic(minimal)
    assert require_VMState(extraction)
    assert require_VMState(minimal)
    assert require_VMStep(extraction)
    assert require_VMStep(minimal)
    assert require_SimulationProof(extraction)
    assert require_SimulationProof(minimal)


def test_bridge_contract_declarations_present() -> None:
    boxworld = _read("coq/bridge/BoxWorld_to_Kernel.v")
    causal = _read("coq/bridge/Causal_to_Kernel.v")
    entropy = _read("coq/bridge/Entropy_to_Kernel.v")
    finite_quantum = _read("coq/bridge/FiniteQuantum_to_Kernel.v")
    pymu = _read("coq/bridge/PythonMuLedgerBisimulation.v")
    randomness = _read("coq/bridge/Randomness_to_Kernel.v")
    tomography = _read("coq/bridge/Tomography_to_Kernel.v")
    catnet = _read("coq/catnet/coqproofs/CatNet.v")

    assert simulation_correctness_trials(boxworld)
    assert simulation_correctness_trials(finite_quantum)
    assert decodes_to_self(causal)
    assert decodes_to_self(entropy)
    assert decodes_to_self(tomography)
    assert mu_ledger_bisim(pymu)
    assert empty_ledger_bisim(pymu)
    assert "decode_is_filter_payloads" in randomness
    assert is_chain_valid(catnet)
    assert compute_hash_chain(catnet)
