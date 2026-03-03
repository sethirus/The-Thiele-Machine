from __future__ import annotations

import re
from collections import deque
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
COQ_ROOT = REPO_ROOT / "coq"
EXTRACTION_V = COQ_ROOT / "Extraction.v"

# Critical proof surfaces that must remain connected to kernel VM semantics.
CRITICAL_DIRS = (
    COQ_ROOT / "kernel",
    COQ_ROOT / "bridge",
    COQ_ROOT / "kami_hw",
)

# Semantic anchors for "Thiele machine" meaning in proofs.
ANCHOR_MODULES = {
    "VMState",
    "VMStep",
    "VMEncoding",
    "KernelTM",
    "SimulationProof",
    "MuCostModel",
    "MuLedgerConservation",
    "MuInitiality",
    "NoFreeInsight",
    "BridgeDefinitions",
    "PythonBisimulation",
    "HardwareBisimulation",
}

# Infrastructure files that define alternative formalizations, HW type constants,
# or Kami primitives — naturally disconnected from VM semantic anchors.
# Connectivity is enforced by the authoritative inquisitor (PROOF_CONNECTIVITY_GAP rule).
CONNECTIVITY_EXEMPT = {
    "CertCheck", "CrossLayerManifest", "Kernel", "PartitionSeparation",
    "ReceiptIntegrity", "Abstraction", "Blink", "Compatibility",
    "ThieleCPUCore", "ThieleTypes",
}

_FROM_IMPORT_RE = re.compile(r"From\s+([A-Za-z0-9_\.]+)\s+Require\s+Import\s+([^\.]+)\.")
_REQUIRE_IMPORT_RE = re.compile(r"Require\s+Import\s+([^\.]+)\.")


def _all_coq_files() -> list[Path]:
    out: list[Path] = []
    for d in CRITICAL_DIRS:
        if d.exists():
            out.extend(sorted(d.rglob("*.v")))
    return out


def _module_index(files: list[Path]) -> dict[str, list[Path]]:
    index: dict[str, list[Path]] = {}
    for p in files:
        index.setdefault(p.stem, []).append(p)
    return index


def _parse_import_module_names(text: str) -> set[str]:
    mods: set[str] = set()

    for m in _FROM_IMPORT_RE.finditer(text):
        imported = m.group(2)
        for tok in imported.split():
            tok = tok.strip()
            if tok:
                mods.add(tok)

    for m in _REQUIRE_IMPORT_RE.finditer(text):
        imported = m.group(1)
        for tok in imported.split():
            tok = tok.strip()
            if tok and tok != "From":
                mods.add(tok)

    return mods


def _build_import_graph(files: list[Path]) -> dict[Path, set[Path]]:
    graph: dict[Path, set[Path]] = {p: set() for p in files}
    mod_index = _module_index(files)

    for p in files:
        txt = p.read_text(encoding="utf-8")
        for mod in _parse_import_module_names(txt):
            for target in mod_index.get(mod, []):
                if target != p:
                    graph[p].add(target)
    return graph


def _anchor_files(files: list[Path]) -> set[Path]:
    return {p for p in files if p.stem in ANCHOR_MODULES}


def _reaches_any_anchor(start: Path, graph: dict[Path, set[Path]], anchors: set[Path]) -> bool:
    if start in anchors:
        return True
    seen: set[Path] = set()
    q = deque([start])
    while q:
        cur = q.popleft()
        if cur in seen:
            continue
        seen.add(cur)
        for nxt in graph.get(cur, set()):
            if nxt in anchors:
                return True
            if nxt not in seen:
                q.append(nxt)
    return False


def test_extraction_exports_core_vm_semantics() -> None:
    assert EXTRACTION_V.exists(), f"Missing extraction file: {EXTRACTION_V}"
    txt = EXTRACTION_V.read_text(encoding="utf-8")
    assert "SimulationProof.vm_apply" in txt
    assert "VMState.VMState" in txt
    assert "VMStep.vm_instruction" in txt
    assert "Extraction \"../build/thiele_core.ml\"" in txt


def test_critical_proof_files_connect_to_thiele_semantics() -> None:
    files = _all_coq_files()
    assert files, "No critical Coq proof files found"

    graph = _build_import_graph(files)
    anchors = _anchor_files(files)
    assert anchors, "No anchor modules found in critical proof surfaces"

    disconnected: list[str] = []
    for p in files:
        if p.stem in CONNECTIVITY_EXEMPT:
            continue
        if not _reaches_any_anchor(p, graph, anchors):
            disconnected.append(str(p.relative_to(REPO_ROOT)))

    assert not disconnected, (
        "Critical proof files disconnected from Thiele VM semantic anchors "
        "(VMState/VMStep/SimulationProof/MuLedgerConservation/NoFreeInsight):\n"
        + "\n".join(f"- {d}" for d in disconnected)
    )
