from __future__ import annotations

import re
from collections import deque
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
COQ_ROOT = REPO_ROOT / "coq"
COQ_PROJECT = COQ_ROOT / "_CoqProject"

# Proof surfaces that must remain connected to the foundation chain.
CRITICAL_DIRS = (
    COQ_ROOT / "kernel",
    REPO_ROOT / "minimal",
)

# The foundation chain: the abstract certification system and its universal
# floor, the record-carrying machine, the abstract substrate, the Turing
# kernel, and the small machine with the definition it meets.
ANCHOR_MODULES = {
    "UniversalCertificationCost",
    "StructuralCore",
    "Substrate",
    "KernelTM",
    "EarnedCore",
    "ThieleComplete",
}

# The anchors' own files and where they live.
ANCHOR_FILES = {
    "UniversalCertificationCost": "coq/kernel/nfi/UniversalCertificationCost.v",
    "StructuralCore": "coq/kernel/foundation/StructuralCore.v",
    "Substrate": "coq/kernel/foundation/Substrate.v",
    "KernelTM": "coq/kernel/foundation/KernelTM.v",
    "EarnedCore": "minimal/EarnedCore.v",
    "ThieleComplete": "minimal/ThieleComplete.v",
}

# Files that hold only base data types the anchors are built from.
# Kernel.v is the toy Turing machine's state and instruction types, which
# KernelTM runs; it has nothing to connect to below itself.
CONNECTIVITY_EXEMPT = {"Kernel"}

_FROM_IMPORT_RE = re.compile(r"From\s+([A-Za-z0-9_\.]+)\s+Require\s+Import\s+([^\.]+)\.")
_REQUIRE_IMPORT_RE = re.compile(r"Require\s+(?:Import\s+|Export\s+)?([^\.]+(?:\.[A-Za-z][^\.\s]*)*)\.")


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
        for tok in m.group(2).split():
            tok = tok.strip()
            if tok:
                # Handle dotted names like Kernel.StructuralCore → StructuralCore
                mods.add(tok.rsplit(".", 1)[-1])

    for m in _REQUIRE_IMPORT_RE.finditer(text):
        for tok in m.group(1).split():
            tok = tok.strip()
            if tok and tok not in ("From", "Import", "Export"):
                mods.add(tok.rsplit(".", 1)[-1])

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


def test_foundation_chain_is_built_with_the_project() -> None:
    """Every anchor file exists and is a canonical compile target."""
    project = COQ_PROJECT.read_text(encoding="utf-8").splitlines()
    for module, rel in ANCHOR_FILES.items():
        assert (REPO_ROOT / rel).is_file(), f"missing foundation file for {module}: {rel}"
        entry = rel[len("coq/"):] if rel.startswith("coq/") else "../" + rel
        assert entry in project, f"{rel} is not listed in coq/_CoqProject"


# A file may declare itself standalone in the source rather than in the
# list above. The marker is the same one the Inquisitor honours for
# PROOF_CONNECTIVITY_GAP, so the exemption lives next to the code it describes
# and cannot drift out of sync with a list kept here.
#
# The alternative is to import a foundation module and never use it, which
# satisfies a reachability check while telling the reader nothing. A scope
# marker states the truth next to the code it describes.
_CONNECTIVITY_WAIVER_RE = re.compile(
    r"(?:SCOPE NOTE.*proof[- ]?connect|"
    r"SCOPE NOTE.*(?:foundation connectivity|standalone proof scope)|"
    r"PROOF SCOPE:\s*standalone algebra)",
    re.IGNORECASE,
)


def _carries_connectivity_waiver(path: Path) -> bool:
    try:
        return bool(_CONNECTIVITY_WAIVER_RE.search(
            path.read_text(encoding="utf-8", errors="replace")))
    except OSError:
        return False


def test_critical_proof_files_connect_to_thiele_semantics() -> None:
    files = _all_coq_files()
    assert files, "No critical Coq proof files found"

    graph = _build_import_graph(files)
    anchors = _anchor_files(files)
    assert {p.stem for p in anchors} == ANCHOR_MODULES, (
        "Not every foundation module was found in the critical proof surfaces: "
        + ", ".join(sorted(ANCHOR_MODULES - {p.stem for p in anchors}))
    )

    disconnected: list[str] = []
    for p in files:
        if p.stem in CONNECTIVITY_EXEMPT:
            continue
        if _carries_connectivity_waiver(p):
            continue
        if not _reaches_any_anchor(p, graph, anchors):
            disconnected.append(str(p.relative_to(REPO_ROOT)))

    assert not disconnected, (
        "Proof files disconnected from the foundation chain "
        "(UniversalCertificationCost/StructuralCore/Substrate/KernelTM/EarnedCore/"
        "ThieleComplete) and carrying no SCOPE NOTE saying why:\n"
        + "\n".join(f"- {d}" for d in disconnected)
    )
