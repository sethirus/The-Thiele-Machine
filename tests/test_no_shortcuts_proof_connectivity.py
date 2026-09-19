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
    "GraphReconstructionBridge", "RichStateCommutation",
    "RTLGapRegistry",
    # Unification-probe math files: substrate-free real analysis, matrix
    # algebra, correlator algebra, and generic-cost-ledger theorems.
    # Connected to the VM via the aggregator files (UnificationProbeBridges,
    # UnificationProbePattern), not by direct imports of VMState/VMStep.
    "MeasurementExtraction",
    "HolevoGeneralD", "HolevoTwoQubit", "OperatorAlgebra",
    "TsirelsonFromIC", "TsirelsonFromMu",
    "AdditionalProbes", "BekensteinBound", "DimensionalGapTheorem",
    # The substrate-free half of the A2 substitution gate. Every theorem is
    # indicator-uniqueness over an abstract local-predicate pricing record and
    # imports no VM semantics on purpose: the floor follows from the cost
    # schedule alone. The VM teeth are in CommitmentCostDecomposition.v
    # (imports VMState/VMStep/SimulationProof), and A2Payoff.v is the
    # aggregator that combines the two. Carries the matching INQUISITOR NOTE.
    "CommitmentPredicateAdequacy",
    # Substrate.v is the abstract A2-respecting substrate typeclass that the
    # 51-opcode VM instantiates via VMSubstrateInstance.v. It is
    # foundation-tier (more foundational than VMState, which is one
    # realization of it), so it cannot connect "down" to VMState without
    # inverting the substrate-vs-scaffolding dependency direction. The
    # inquisitor exempts it for the same reason (scripts/inquisitor.py:119).
    "Substrate",
    # The Kami step-rule decomposition. These files state one substep of
    # `ThieleCPUCore.v`'s getRules FSM each (dispatch admission, normalization
    # scan, morph copy/join, boundary decode, CHSH/LASSERT phase arithmetic,
    # rich-fault word decode) and import that module directly. ThieleCPUCore is
    # itself exempt as a Kami primitive, so the decomposition inherits the same
    # status: it is hardware-substrate refinement, not VM semantics, and it
    # cannot reach VMState/VMStep without asserting the very bridge these
    # modules exist to break down. The authoritative inquisitor reports no
    # PROOF_CONNECTIVITY_GAP for them (0 HIGH, 0 MEDIUM).
    "ActionEvaluator", "ActionObservation", "BoundaryDecoded", "BoundaryRun",
    "ChshArith", "ChshStepFields", "CoreExecution", "CoreRules", "CoreTyping",
    "DecodedReadFree", "DispatchAddFamily", "DispatchContracts",
    "DispatchExecution", "DispatchFetch", "DispatchLets", "DispatchObservation",
    "DispatchReset", "HWBoundary", "HWBoundaryCompleteness", "HWBoundaryReads",
    "LassertSpec", "LassertStepFields", "LegacyWordDecode", "MorphCopy",
    "MorphJoin", "MorphLoading", "MorphRetirement", "MorphTensorGap",
    "NormalizationExclusivity", "NormalizationExecution", "NormalizationFrame",
    "NormalizationLoop", "NormalizationPrefix", "NormalizationRetirement",
    "NormalizationScanExecution", "NormalizationStart", "NormalizationSteps",
    "ReadFreeObservation", "RichFaultWords", "RichWordDecode", "RuleNext",
    "RuleStep", "StepEval", "StepFields", "StepFieldsMorph", "TensorDispatch",
    "MM2ComplementUndec",
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
                # Handle dotted names like Kernel.VMState → VMState
                mods.add(tok.rsplit(".", 1)[-1])

    for m in _REQUIRE_IMPORT_RE.finditer(text):
        imported = m.group(1)
        for tok in imported.split():
            tok = tok.strip()
            if tok and tok != "From":
                # Handle dotted names like Kernel.VMState → VMState
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


def test_extraction_exports_core_vm_semantics() -> None:
    assert EXTRACTION_V.exists(), f"Missing extraction file: {EXTRACTION_V}"
    txt = EXTRACTION_V.read_text(encoding="utf-8")
    # Extraction now targets canonical kernel/kami_hw modules directly
    # (no longer routes through the monolithic ThieleMachineComplete).
    assert "SimulationProof.vm_apply" in txt
    assert "VMState.VMState" in txt
    assert "VMStep.vm_instruction" in txt
    assert "Extraction \"../build/thiele_core.ml\"" in txt


# A file may declare itself substrate-free in the source rather than in the
# list above. The marker is the same one the Inquisitor honours for
# PROOF_CONNECTIVITY_GAP, so the exemption lives next to the code it describes
# and cannot drift out of sync with a list kept here.
#
# The alternative is what these files used to do: import VMState/VMStep and
# never use them, which satisfies a reachability check while telling the
# reader nothing. A waiver states the truth and gets counted in the WAIVERS
# census in INQUISITOR_REPORT.md.
_CONNECTIVITY_WAIVER_RE = re.compile(
    r"INQUISITOR NOTE.*proof[- ]?connect", re.IGNORECASE
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
    assert anchors, "No anchor modules found in critical proof surfaces"

    disconnected: list[str] = []
    for p in files:
        if p.stem in CONNECTIVITY_EXEMPT:
            continue
        if _carries_connectivity_waiver(p):
            continue
        if not _reaches_any_anchor(p, graph, anchors):
            disconnected.append(str(p.relative_to(REPO_ROOT)))

    assert not disconnected, (
        "Critical proof files disconnected from Thiele VM semantic anchors "
        "(VMState/VMStep/SimulationProof/MuLedgerConservation/NoFreeInsight):\n"
        + "\n".join(f"- {d}" for d in disconnected)
    )
