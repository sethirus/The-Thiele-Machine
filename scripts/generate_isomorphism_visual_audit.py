#!/usr/bin/env python3

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Set, Tuple


REPO_ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS_DIR = REPO_ROOT / "artifacts"
CHARTS_DIR = ARTIFACTS_DIR / "charts"

PROOF_DAG_PATH = ARTIFACTS_DIR / "proof_dependency_dag.json"
ISOMORPHISM_VALIDATION_PATH = ARTIFACTS_DIR / "isomorphism_validation.json"

LAYER_FILES: Dict[str, List[Path]] = {
    "coq": [
        REPO_ROOT / "coq/kernel/VMState.v",
        REPO_ROOT / "coq/kernel/VMStep.v",
        REPO_ROOT / "coq/kernel/ThreeLayerIsomorphism.v",
        REPO_ROOT / "coq/kernel/HardwareBisimulation.v",
        REPO_ROOT / "coq/bridge/PythonMuLedgerBisimulation.v",
        REPO_ROOT / "coq/kernel/ReceiptIntegrity.v",
    ],
    "python": [
        REPO_ROOT / "thielecpu/state.py",
        REPO_ROOT / "thielecpu/vm.py",
        REPO_ROOT / "thielecpu/hardware/cosim.py",
        REPO_ROOT / "scripts/verify_3layer.py",
    ],
    "rtl": [
        REPO_ROOT / "thielecpu/hardware/rtl/thiele_cpu_unified.v",
        REPO_ROOT / "thielecpu/hardware/testbench/thiele_cpu_tb.v",
    ],
    "tests": [
        REPO_ROOT / "tests/test_rtl_compute_isomorphism.py",
        REPO_ROOT / "tests/test_partition_isomorphism_minimal.py",
        REPO_ROOT / "tests/test_bisimulation_complete.py",
        REPO_ROOT / "tests/test_three_layer_isomorphism_fuzz.py",
        REPO_ROOT / "tests/test_receipt_chain.py",
    ],
}

SEMANTIC_KEYWORDS = [
    "isomorphism",
    "bisim",
    "lockstep",
    "mu",
    "partition",
    "opcode",
    "receipt",
    "bianchi",
    "vmstate",
    "vmstep",
    "fullwirespec",
    "tensor",
]

OUTSIDE_MARKERS = {
    "archive",
    "exploration",
    "exploratory",
    "unused",
    "disabled",
    "deprecated",
    "legacy",
    "patches",
    "old",
}


@dataclass(frozen=True)
class ElementSpec:
    key: str
    label: str
    checks: Dict[str, List[str]]


ELEMENTS: List[ElementSpec] = [
    ElementSpec(
        key="state_shape",
        label="State shape (graph/csr/regs/mem/pc/mu)",
        checks={
            "coq": [r"Record\s+VMState", r"vm_graph", r"vm_regs", r"vm_mem", r"vm_pc", r"vm_mu"],
            "python": [r"class\s+State", r"regions", r"csr", r"mu_ledger", r"program"],
            "rtl": [r"reg_file", r"data_mem", r"pc_reg", r"mu_accumulator", r"module_table"],
            "tests": [r"py_regs\s*==\s*coq_regs\s*==\s*rtl_regs"],
        },
    ),
    ElementSpec(
        key="opcode_alignment",
        label="Opcode alignment (ISA parity)",
        checks={
            "coq": [r"Inductive\s+vm_instruction", r"instruction_cost"],
            "python": [r"OPCODES", r"verify_opcode_alignment|generated_opcodes"],
            "rtl": [r"localparam\s+\[7:0\]\s+OPCODE_"],
            "tests": [r"opcode|OpcodeAlignment|test_opcode_values"],
        },
    ),
    ElementSpec(
        key="mu_accounting",
        label="μ accounting conservation",
        checks={
            "coq": [r"vm_mu", r"instruction_cost", r"mu_conservation|trace_mu_exact|vm_apply_mu"],
            "python": [r"mu_discovery", r"mu_execution", r"def\s+total", r"charge_execution|charge_discovery"],
            "rtl": [r"mu_accumulator", r"operand_cost", r"assign\s+mu\s*=\s*mu_accumulator"],
            "tests": [r"mu_matches|mu_cost|isomorphic"],
        },
    ),
    ElementSpec(
        key="mu_tensor_bianchi",
        label="μ-tensor + Bianchi enforcement",
        checks={
            "coq": [r"vm_mu_tensor|vm_mu_tensor_add_at|advance_state_reveal"],
            "python": [r"mu_tensor", r"BianchiViolationError", r"check_bianchi_consistency"],
            "rtl": [r"mu_tensor_reg", r"bianchi_alarm", r"tensor_total"],
            "tests": [r"test_bianchi_enforcement|REVEAL"],
        },
    ),
    ElementSpec(
        key="partition_semantics",
        label="Partition semantics (PNEW/PSPLIT/PMERGE)",
        checks={
            "coq": [r"graph_pnew|graph_psplit|graph_pmerge|PartitionGraph"],
            "python": [r"def\s+pnew", r"def\s+psplit", r"def\s+pmerge"],
            "rtl": [r"OPCODE_PNEW", r"OPCODE_PSPLIT", r"OPCODE_PMERGE", r"module_exists"],
            "tests": [r"partition_ops.*isomorphic|pmerge|psplit"],
        },
    ),
    ElementSpec(
        key="receipts_integrity",
        label="Receipt integrity binding",
        checks={
            "coq": [r"ReceiptIntegrity|receipt_mu_consistent"],
            "python": [r"receipt|verify_receipt|InstructionWitness|step_receipts"],
            "rtl": [r"receipt_integrity_checker|receipt_value|receipt_accepted"],
            "tests": [r"receipt"],
        },
    ),
    ElementSpec(
        key="cross_layer_bisim",
        label="Cross-layer bisimulation statements",
        checks={
            "coq": [r"three_layer_bisimulation|HardwareBisimulation|PythonBisimulation"],
            "python": [r"isomorphism|bisimulation|verify_3layer|verify_isomorphism|equivalence_bundle"],
            "rtl": [r"THREE-LAYER ISOMORPHISM|isomorphism"],
            "tests": [r"isomorphism|bisimulation|lockstep"],
        },
    ),
]


def _read_text(path: Path) -> str:
    if not path.exists():
        return ""
    return path.read_text(encoding="utf-8", errors="replace")


def _layer_blob(layer: str) -> str:
    return "\n".join(_read_text(p) for p in LAYER_FILES[layer])


def _contains_all(blob: str, patterns: List[str]) -> bool:
    return all(re.search(pat, blob, re.IGNORECASE | re.MULTILINE) for pat in patterns)


def _path_tokens(path: str) -> Set[str]:
    parts = re.split(r"[/_.\-]+", path.lower())
    return {p for p in parts if len(p) >= 3 and p not in {"test", "tests", "coq", "py", "rtl"}}


def _nearest_declared(path_str: str, declared: List[str], limit: int = 3) -> List[str]:
    source_tokens = _path_tokens(path_str)
    if not source_tokens:
        return declared[:limit]

    scored: List[Tuple[float, str]] = []
    for item in declared:
        item_tokens = _path_tokens(item)
        if not item_tokens:
            continue
        union = source_tokens | item_tokens
        if not union:
            continue
        score = len(source_tokens & item_tokens) / len(union)
        if score > 0:
            scored.append((score, item))

    scored.sort(key=lambda x: (-x[0], x[1]))
    if scored:
        return [p for _, p in scored[:limit]]
    return declared[:limit]


def _is_semantic_file(path: Path, text: str) -> bool:
    blob = f"{path.as_posix()}\n{text}".lower()
    return any(keyword in blob for keyword in SEMANTIC_KEYWORDS)


def _discover_layer_files(layer: str) -> List[Path]:
    if layer == "coq":
        roots = [REPO_ROOT / "coq"]
        suffix = ".v"
    elif layer == "python":
        roots = [REPO_ROOT / "thielecpu", REPO_ROOT / "scripts", REPO_ROOT / "tools", REPO_ROOT / "verifier"]
        suffix = ".py"
    elif layer == "rtl":
        roots = [REPO_ROOT / "thielecpu/hardware", REPO_ROOT / "fpga"]
        suffix = ".v"
    elif layer == "tests":
        roots = [REPO_ROOT / "tests"]
        suffix = ".py"
    else:
        return []

    out: List[Path] = []
    for root in roots:
        if not root.exists():
            continue
        for file_path in sorted(root.rglob(f"*{suffix}")):
            if "__pycache__" in file_path.parts:
                continue
            if layer == "tests" and not file_path.name.startswith("test_"):
                continue
            out.append(file_path)
    return out


def _collect_repo_surface_audit() -> Dict[str, object]:
    declared_by_layer = {
        layer: sorted([p.relative_to(REPO_ROOT).as_posix() for p in paths])
        for layer, paths in LAYER_FILES.items()
    }

    discovered_by_layer: Dict[str, List[str]] = {}
    semantic_unmapped_by_layer: Dict[str, List[Dict[str, object]]] = {}

    for layer in LAYER_FILES:
        discovered_paths = _discover_layer_files(layer)
        discovered_rel = [p.relative_to(REPO_ROOT).as_posix() for p in discovered_paths]
        discovered_by_layer[layer] = discovered_rel

        declared_set = set(declared_by_layer[layer])
        semantic_unmapped: List[Dict[str, object]] = []
        for file_path in discovered_paths:
            rel = file_path.relative_to(REPO_ROOT).as_posix()
            if rel in declared_set:
                continue
            text = _read_text(file_path)
            if not _is_semantic_file(file_path, text):
                continue
            semantic_unmapped.append(
                {
                    "path": rel,
                    "nearby_declared": _nearest_declared(rel, declared_by_layer[layer]),
                    "why": "Semantic content found outside declared audit file set.",
                }
            )

        semantic_unmapped_by_layer[layer] = semantic_unmapped

    coverage = {}
    for layer in LAYER_FILES:
        discovered = len(discovered_by_layer[layer])
        declared = len(declared_by_layer[layer])
        ratio = (declared / discovered) if discovered else 1.0
        coverage[layer] = {
            "declared": declared,
            "discovered": discovered,
            "declared_coverage_ratio": round(ratio, 4),
            "semantic_unmapped_count": len(semantic_unmapped_by_layer[layer]),
        }

    outside_main_body: List[Dict[str, object]] = []
    all_semantic_candidates: List[Path] = []
    for root in [REPO_ROOT / "archive", REPO_ROOT / "coq", REPO_ROOT / "scripts", REPO_ROOT / "tests"]:
        if not root.exists():
            continue
        for file_path in sorted(root.rglob("*")):
            if not file_path.is_file():
                continue
            if file_path.suffix not in {".v", ".py", ".v", ".sv", ".md"}:
                continue
            text = _read_text(file_path)
            if _is_semantic_file(file_path, text):
                all_semantic_candidates.append(file_path)

    for file_path in all_semantic_candidates:
        rel = file_path.relative_to(REPO_ROOT).as_posix()
        marker_hit = [part for part in file_path.parts if part.lower() in OUTSIDE_MARKERS]
        if not marker_hit:
            continue
        outside_main_body.append(
            {
                "path": rel,
                "markers": sorted(set(marker_hit)),
                "classification": "outside-main-body",
            }
        )

    duplicate_buckets: Dict[str, List[str]] = {}
    for file_path in all_semantic_candidates:
        rel = file_path.relative_to(REPO_ROOT).as_posix()
        stem = file_path.stem.lower()
        normalized = re.sub(r"(copy|backup|old|v\d+|_\d+|-\d+)$", "", stem)
        key = f"{file_path.suffix}:{normalized}"
        duplicate_buckets.setdefault(key, []).append(rel)

    iterated_groups = [
        {"key": key, "paths": sorted(paths)}
        for key, paths in duplicate_buckets.items()
        if len(paths) > 1
    ]
    iterated_groups.sort(key=lambda g: (-len(g["paths"]), g["key"]))

    superfluous_candidates: List[Dict[str, object]] = []
    for file_path in all_semantic_candidates:
        rel = file_path.relative_to(REPO_ROOT).as_posix()
        rel_low = rel.lower()
        if any(marker in rel_low for marker in ["unused", "disabled", "deprecated", "legacy", "archive/"]):
            superfluous_candidates.append(
                {
                    "path": rel,
                    "reason": "Path marker indicates likely stale/externalized component.",
                }
            )

    return {
        "declared_by_layer": declared_by_layer,
        "discovered_by_layer": discovered_by_layer,
        "coverage": coverage,
        "semantic_unmapped_by_layer": semantic_unmapped_by_layer,
        "outside_main_body": outside_main_body,
        "iterated_groups": iterated_groups[:80],
        "superfluous_candidates": superfluous_candidates[:120],
    }


def _collect_counts() -> Dict[str, int]:
    coq_files = list((REPO_ROOT / "coq").rglob("*.v"))
    theorem_like = 0
    admit_like = 0
    axiom_like = 0
    for file_path in coq_files:
        text = _read_text(file_path)
        theorem_like += len(re.findall(r"^\s*(Lemma|Theorem|Corollary|Proposition)\s+", text, re.MULTILINE))
        admit_like += len(re.findall(r"\bAdmitted\.|\badmit\.", text))
        axiom_like += len(re.findall(r"^\s*(Axiom|Hypothesis|Parameter)\s+", text, re.MULTILINE))

    iso_test_files = list((REPO_ROOT / "tests").rglob("test_*.py"))
    iso_related_tests = 0
    for file_path in iso_test_files:
        text = _read_text(file_path)
        if re.search(r"isomorphism|bisimulation|lockstep", text, re.IGNORECASE):
            iso_related_tests += 1

    return {
        "coq_file_count": len(coq_files),
        "theorem_like_count": theorem_like,
        "admit_count": admit_like,
        "axiom_decl_count": axiom_like,
        "isomorphism_related_test_files": iso_related_tests,
    }


def _load_json(path: Path) -> dict:
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}


def _fullwirespec_obligation() -> Dict[str, object]:
    """Detect whether concrete non-Coq FullWireSpec instances are proven in Coq."""
    path = REPO_ROOT / "coq/kernel/ThreeLayerIsomorphism.v"
    text = _read_text(path)
    defs = re.findall(r"^\s*Definition\s+([A-Za-z0-9_']+)_full_wire_spec\b", text, re.MULTILINE)
    unique_defs = sorted(set(defs))
    non_coq = [name for name in unique_defs if name.lower() != "coq"]
    return {
        "file": "coq/kernel/ThreeLayerIsomorphism.v",
        "declared_full_wire_specs": [f"{name}_full_wire_spec" for name in unique_defs],
        "non_coq_full_wire_specs": [f"{name}_full_wire_spec" for name in non_coq],
        "discharged_for_non_coq": len(non_coq) > 0,
        "note": (
            "ThreeLayer full-state theorem relies on fws_step_correct. "
            "If only coq_full_wire_spec is present, concrete implementation discharge remains via runtime verification, not in-file Coq instantiation."
        ),
    }


def _classify_gap_action(gap: Dict[str, object]) -> str:
    element = str(gap.get("element", "")).lower()
    label = str(gap.get("label", "")).lower()
    raw_missing_layers = gap.get("missing_layers", [])
    if not isinstance(raw_missing_layers, list):
        raw_missing_layers = []
    missing_layers = [str(layer).lower() for layer in raw_missing_layers]

    if "fullwirespec" in element or "theorem" in label or "coq" in " ".join(missing_layers):
        return "formalize"
    if "tests" in " ".join(missing_layers) or "runtime" in label or "lockstep" in label:
        return "reintegrate"
    if "rtl" in " ".join(missing_layers) or "python" in " ".join(missing_layers):
        return "reintegrate"
    return "move_or_archive"


def _build_connection_audit(
    matrix_rows: List[Dict[str, object]],
    gaps: List[Dict[str, object]],
    proof_dag: Dict[str, object],
    counts: Dict[str, int],
    fullwirespec: Dict[str, object],
    repo_surface: Dict[str, object],
) -> Dict[str, object]:
    aligned = [
        {
            "element": row["element"],
            "label": row["label"],
        }
        for row in matrix_rows
        if row["aligned_surface"]
    ]

    disconnected = [
        {
            "element": gap.get("element"),
            "label": gap.get("label"),
            "missing_layers": gap.get("missing_layers", []),
            "action": _classify_gap_action(gap),
            "next_action": gap.get("next_action"),
        }
        for gap in gaps
    ]

    dag_rank = proof_dag.get("rank", {}) if isinstance(proof_dag, dict) else {}
    isolated = dag_rank.get("isolated", []) if isinstance(dag_rank, dict) else []
    weak_components = dag_rank.get("weakComponents", {}).get("largest", []) if isinstance(dag_rank, dict) else []

    tiny_components = [
        comp for comp in weak_components if isinstance(comp, dict) and int(comp.get("size", 0)) <= 2
    ]

    weak_links = []
    if isolated:
        weak_links.append(
            {
                "kind": "proof-isolated-declarations",
                "count": len(isolated),
                "sample": isolated[:20],
                "recommendation": "Review declarations for dead-end proofs or unhooked lemmas; reintegrate or archive.",
                "action": "reintegrate",
            }
        )
    if tiny_components:
        weak_links.append(
            {
                "kind": "proof-tiny-components",
                "count": len(tiny_components),
                "sample": tiny_components[:10],
                "recommendation": "Small disconnected clusters may indicate proof islands; connect to main theorem spine or move to archive.",
                "action": "move_or_archive",
            }
        )
    if not fullwirespec.get("discharged_for_non_coq", False):
        weak_links.append(
            {
                "kind": "formal-obligation-open",
                "count": 1,
                "sample": ["fullwirespec_discharge"],
                "recommendation": "Discharge non-Coq FullWireSpec in Coq to remove runtime-only closure dependence.",
                "action": "formalize",
            }
        )

    file_presence = {
        layer: [
            {
                "path": p.relative_to(REPO_ROOT).as_posix(),
                "exists": p.exists(),
            }
            for p in paths
        ]
        for layer, paths in LAYER_FILES.items()
    }
    missing_files = [
        item["path"]
        for layer_items in file_presence.values()
        for item in layer_items
        if not item["exists"]
    ]

    if missing_files:
        disconnected.append(
            {
                "element": "layer_file_presence",
                "label": "Declared layer files missing on disk",
                "missing_layers": ["source-files"],
                "action": "reintegrate",
                "next_action": "Restore or update file list in visual audit script.",
                "files": missing_files,
            }
        )

    semantic_unmapped = repo_surface.get("semantic_unmapped_by_layer", {}) if isinstance(repo_surface, dict) else {}
    if isinstance(semantic_unmapped, dict):
        for layer, items in semantic_unmapped.items():
            if not isinstance(items, list) or not items:
                continue
            disconnected.append(
                {
                    "element": f"semantic_unmapped::{layer}",
                    "label": f"Semantic files in {layer} outside declared main audit body",
                    "missing_layers": [layer, "matrix-coverage"],
                    "action": "reintegrate",
                    "next_action": "Promote critical nearby files into declared layer set or explicitly archive them.",
                    "count": len(items),
                    "sample": items[:20],
                }
            )

    confidence = "high"
    if disconnected or weak_links:
        confidence = "medium"
    if len(disconnected) >= 3 or counts.get("admit_count", 0) > 0:
        confidence = "guarded"

    return {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "summary": {
            "connected_count": len(aligned),
            "disconnected_count": len(disconnected),
            "weak_link_count": len(weak_links),
            "confidence": confidence,
        },
        "connected": aligned,
        "disconnected": disconnected,
        "weak_links": weak_links,
        "proof_graph_signals": {
            "isolated_count": len(isolated),
            "tiny_component_count": len(tiny_components),
            "weak_component_count": int(dag_rank.get("weakComponents", {}).get("count", 0))
            if isinstance(dag_rank, dict)
            else 0,
        },
        "coverage_scope": repo_surface.get("coverage", {}) if isinstance(repo_surface, dict) else {},
        "outside_main_body": repo_surface.get("outside_main_body", []) if isinstance(repo_surface, dict) else [],
        "iterated_groups": repo_surface.get("iterated_groups", []) if isinstance(repo_surface, dict) else [],
        "superfluous_candidates": repo_surface.get("superfluous_candidates", [])
        if isinstance(repo_surface, dict)
        else [],
        "file_presence": file_presence,
        "operator_actions": {
            "formalize": "Convert runtime-backed claims into explicit Coq obligations and proofs.",
            "reintegrate": "Connect orphan implementations/tests back to theorem and lockstep surfaces.",
            "move_or_archive": "Move exploratory/dead-end proof islands to archive if no active dependency.",
            "delete_candidate": "Remove obsolete compatibility glue only when replacement is verified by tests.",
        },
    }


def build_artifacts() -> None:
    CHARTS_DIR.mkdir(parents=True, exist_ok=True)

    blobs = {layer: _layer_blob(layer) for layer in LAYER_FILES}
    matrix_rows = []
    gaps = []

    for elem in ELEMENTS:
        per_layer = {}
        missing_layers = []
        for layer, patterns in elem.checks.items():
            ok = _contains_all(blobs[layer], patterns)
            per_layer[layer] = ok
            if not ok:
                missing_layers.append(layer)

        aligned = len(missing_layers) == 0
        row = {
            "element": elem.key,
            "label": elem.label,
            "per_layer": per_layer,
            "aligned_surface": aligned,
        }
        matrix_rows.append(row)

        if not aligned:
            gaps.append({
                "element": elem.key,
                "label": elem.label,
                "missing_layers": missing_layers,
                "next_action": "Add or tighten implementation/tests in missing layers and re-run isomorphism gates.",
            })

    counts = _collect_counts()
    proof_dag = _load_json(PROOF_DAG_PATH)
    iso_validation = _load_json(ISOMORPHISM_VALIDATION_PATH)
    fullwirespec = _fullwirespec_obligation()
    repo_surface = _collect_repo_surface_audit()

    matrix_payload = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "layers": list(LAYER_FILES.keys()),
        "elements": matrix_rows,
        "summary": {
            "aligned_elements": sum(1 for r in matrix_rows if r["aligned_surface"]),
            "total_elements": len(matrix_rows),
        },
        "counts": counts,
        "proof_dag_meta": proof_dag.get("meta", {}),
        "isomorphism_validation": iso_validation,
        "formal_obligation": fullwirespec,
        "repo_surface_coverage": repo_surface,
    }

    if not fullwirespec["discharged_for_non_coq"]:
        gaps.append(
            {
                "element": "fullwirespec_discharge",
                "label": "Concrete FullWireSpec discharge beyond Coq self-spec",
                "missing_layers": ["coq(instantiation)"],
                "next_action": (
                    "Add machine-checked FullWireSpec instantiation/proof for concrete implementation model, "
                    "or keep runtime lockstep as evidence and track this as an explicit theorem gap."
                ),
            }
        )

    gap_payload = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "gaps": gaps,
        "notes": [
            "This is a surface-completeness audit using symbol presence + known validation artifacts.",
            "Mathematical equivalence still relies on proof checking + runtime lockstep gates.",
        ],
    }

    connection_audit = _build_connection_audit(matrix_rows, gaps, proof_dag, counts, fullwirespec, repo_surface)

    backlog = []
    if not fullwirespec["discharged_for_non_coq"]:
        backlog.append(
            {
                "id": "P0-fullwirespec-discharge",
                "priority": "P0",
                "title": "Discharge concrete FullWireSpec obligation in Coq",
                "why": "Moves concrete implementation equivalence from runtime evidence into explicit Coq instantiation theorem(s).",
                "inputs": [
                    "coq/kernel/ThreeLayerIsomorphism.v",
                    "artifacts/isomorphism_gap_report.json",
                ],
                "outputs": [
                    "Concrete *_full_wire_spec definition(s)",
                    "Proofs consuming fws_step_correct for non-Coq spec(s)",
                ],
                "validation": [
                    "coqchk on updated module set",
                    "make proof-undeniable",
                ],
            }
        )

    backlog.extend(
        [
            {
                "id": "P1-lockstep-expansion",
                "priority": "P1",
                "title": "Expand lockstep corpus and adversarial coverage",
                "why": "Increase confidence envelope beyond representative traces.",
                "inputs": [
                    "tests/test_rtl_compute_isomorphism.py",
                    "tests/test_three_layer_isomorphism_fuzz.py",
                    "scripts/measurement_and_fuzzing_suite.py",
                ],
                "outputs": [
                    "Additional isomorphic trace suites (edge/corner/fuzz)",
                    "Updated artifacts/isomorphism_validation.json",
                ],
                "validation": [
                    "make test-smoke-isomorphism",
                    "make isomorphism-bitlock",
                ],
            },
            {
                "id": "P1-receipt-endtoend",
                "priority": "P1",
                "title": "Receipt integrity end-to-end closure",
                "why": "Ensure signed receipt claims are mathematically and operationally bound across all layers.",
                "inputs": [
                    "coq/kernel/ReceiptIntegrity.v",
                    "scripts/verify_receipt.py",
                    "tests/test_receipt_chain.py",
                ],
                "outputs": [
                    "Cross-layer receipt conformance checklist",
                    "Regression tests for forged/invalid chains",
                ],
                "validation": [
                    "pytest -q tests/test_receipt_chain.py",
                    "make proof-undeniable",
                ],
            },
            {
                "id": "P2-backend-parity",
                "priority": "P2",
                "title": "Dual-simulator parity (iverilog/verilator)",
                "why": "Reduces simulator-specific blind spots in RTL evidence.",
                "inputs": [
                    "thielecpu/hardware/cosim.py",
                    "tests/test_emergent_geometry_proxies.py",
                ],
                "outputs": [
                    "Documented backend parity checks",
                    "Stable passing profile for both simulators",
                ],
                "validation": [
                    "make test-emergent-geometry",
                    "make test-emergent-geometry-verilator",
                ],
            },
        ]
    )

    (ARTIFACTS_DIR / "isomorphism_implementation_matrix.json").write_text(
        json.dumps(matrix_payload, indent=2), encoding="utf-8"
    )
    (ARTIFACTS_DIR / "isomorphism_gap_report.json").write_text(
        json.dumps(gap_payload, indent=2), encoding="utf-8"
    )
    (ARTIFACTS_DIR / "isomorphism_development_backlog.json").write_text(
        json.dumps(
            {
                "generated_at": datetime.now(timezone.utc).isoformat(),
                "backlog": backlog,
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    (ARTIFACTS_DIR / "isomorphism_connection_audit.json").write_text(
        json.dumps(connection_audit, indent=2), encoding="utf-8"
    )

    stack_chart = """flowchart LR
    A[Coq Kernel Proofs\nVMState/VMStep/ThreeLayerIsomorphism] --> B[Bridges\nPythonMuLedgerBisimulation\nHardwareBisimulation]
    B --> C[Python VM\nstate.py + vm.py]
    B --> D[RTL CPU\nthiele_cpu_unified.v]
    C --> E[Runtime Isomorphism Tests]
    D --> E
    E --> F[Lockstep Verdict\nmake isomorphism-bitlock]
    A --> G[Proof DAG\nartifacts/proof_dependency_dag.json]
    G --> H[Dependency Analysis\nroots / hubs / leaves]
"""

    modes_chart = """flowchart TD
    M1[Mode 1: Theorem dependency]\n    M2[Mode 2: Symbol parity matrix]\n    M3[Mode 3: Runtime lockstep tests]\n    M4[Mode 4: Independent coqchk]\n    M5[Mode 5: RTL simulation backends]

    M1 --> O[Completeness Signal]
    M2 --> O
    M3 --> O
    M4 --> O
    M5 --> O

    O --> P[Gap Report]\n    P --> Q[Development Priorities]
"""

    roadmap_chart = """flowchart TD
    R0[Current Baseline\nproof-undeniable + isomorphism-bitlock PASS]
    R1[P0: Coq FullWireSpec discharge\n(concrete non-Coq instantiation)]
    R2[P1: Lockstep corpus expansion\n(edge/corner/fuzz traces)]
    R3[P1: Receipt end-to-end closure\n(proof + runtime anti-forgery)]
    R4[P2: Dual-simulator parity\n(iverilog + verilator)]
    R5[Release Readiness\nmathematical + visual + runtime closure]

    R0 --> R1 --> R2 --> R5
    R1 --> R3 --> R5
    R2 --> R4 --> R5
"""

    (CHARTS_DIR / "isomorphism_stack.mmd").write_text(stack_chart, encoding="utf-8")
    (CHARTS_DIR / "analysis_modes.mmd").write_text(modes_chart, encoding="utf-8")
    (CHARTS_DIR / "isomorphism_finish_order.mmd").write_text(roadmap_chart, encoding="utf-8")

    connection_chart = """flowchart LR
    C0[Connected Elements] --> C1[Cross-layer alignment]
    D0[Disconnected Elements] --> D1[Missing layers / obligations]
    W0[Weak Links] --> W1[Isolated proofs / tiny components]

    C1 --> T[Connection Truth Report]
    D1 --> T
    W1 --> T
"""
    (CHARTS_DIR / "connection_truth_map.mmd").write_text(connection_chart, encoding="utf-8")

    aligned = matrix_payload["summary"]["aligned_elements"]
    total = matrix_payload["summary"]["total_elements"]

    visual_md = f"""# Isomorphism Visual + Programmatic Audit

Generated: {matrix_payload['generated_at']}

## Scope

- This report connects proof structure, implementation surfaces, and runtime verification artifacts.
- It is designed to answer: \"what does all-the-same mean\" and \"what is missing\".

## Chart A — Proof to Implementation Stack

```mermaid
{stack_chart}
```

## Chart B — Analysis Modes Composition

```mermaid
{modes_chart}
```

## Programmatic Artifacts

- `artifacts/isomorphism_implementation_matrix.json`
- `artifacts/isomorphism_gap_report.json`
- `artifacts/isomorphism_development_backlog.json`
- `artifacts/isomorphism_connection_audit.json`
- `artifacts/proof_dependency_dag.json`
- `artifacts/isomorphism_validation.json`
- `artifacts/charts/isomorphism_stack.mmd`
- `artifacts/charts/analysis_modes.mmd`
- `artifacts/charts/isomorphism_finish_order.mmd`
- `artifacts/charts/connection_truth_map.mmd`

## Chart C — Finish-Order Roadmap

```mermaid
{roadmap_chart}
```

## What \"All the Same\" Means (Operational Definition)

A change is \"all the same\" only if all of the following hold together:

1. **Semantic equivalence**: Coq step semantics and implementation steps preserve the same observables (μ, pc, state projections).
2. **Structural equivalence**: Partition graph/module behavior aligns (PNEW/PSPLIT/PMERGE invariants).
3. **Accounting equivalence**: μ-cost updates and μ-tensor/Bianchi invariants align across layers.
4. **Encoding equivalence**: Opcode/field encoding and decoding match.
5. **Behavioral equivalence**: Runtime lockstep tests pass on representative and adversarial traces.

## Surface Matrix Summary

- Aligned surfaces: **{aligned}/{total}**
- Coq files: **{counts['coq_file_count']}**
- Theorem-like declarations: **{counts['theorem_like_count']}**
- Explicit axioms/parameters/hypotheses: **{counts['axiom_decl_count']}**
- Admits: **{counts['admit_count']}**
- Isomorphism-related test files: **{counts['isomorphism_related_test_files']}**

## Repo Coverage Scope

- Layer coverage ratios come from discovered files vs declared matrix files.
- This report now explicitly identifies semantic files outside the declared main body and tags nearby anchors for reintegration.
- `repo_surface_coverage` is embedded in `artifacts/isomorphism_implementation_matrix.json`.

## Explicit Formal Obligation Status

- `fws_step_correct` discharge for non-Coq concrete specs: **{matrix_payload['formal_obligation']['discharged_for_non_coq']}**
- Declared `*_full_wire_spec` defs: **{', '.join(matrix_payload['formal_obligation']['declared_full_wire_specs']) or 'none'}**

## Gap Reading Guide

Use `artifacts/isomorphism_gap_report.json`:
- Each gap item names an element and missing layer(s).
- Missing layer means either implementation symbol absence or missing validation surface.
- Prioritize gaps that affect μ-accounting, partition semantics, and lockstep tests first.

## Connection Truth Guide

Use `artifacts/isomorphism_connection_audit.json`:
- `connected`: elements presently aligned across all declared layers.
- `disconnected`: concrete missing links with action tags (`formalize`/`reintegrate`/`move_or_archive`).
- `weak_links`: non-failing but unstable connections (isolated proofs, tiny proof islands, open formal obligations).
"""

    (ARTIFACTS_DIR / "ISOMORPHISM_VISUALS.md").write_text(visual_md, encoding="utf-8")

    raw_conn = connection_audit.get("summary", {})
    conn = raw_conn if isinstance(raw_conn, dict) else {}
    connection_md = f"""# Isomorphism Connection Audit

Generated: {connection_audit['generated_at']}

## Summary

- Connected elements: **{conn.get('connected_count', 0)}**
- Disconnected items: **{conn.get('disconnected_count', 0)}**
- Weak links: **{conn.get('weak_link_count', 0)}**
- Confidence: **{conn.get('confidence', 'unknown')}**

## Disconnected (Actionable)

"""

    disconnected_items = connection_audit.get("disconnected", [])
    if not isinstance(disconnected_items, list):
        disconnected_items = []

    if disconnected_items:
        for item in disconnected_items:
            connection_md += (
                f"- `{item.get('element')}` [{item.get('action')}]: "
                f"missing={item.get('missing_layers')} → {item.get('next_action')}\n"
            )
    else:
        connection_md += "- None currently detected.\n"

    connection_md += "\n## Weak Links\n\n"

    weak_link_items = connection_audit.get("weak_links", [])
    if not isinstance(weak_link_items, list):
        weak_link_items = []

    if weak_link_items:
        for item in weak_link_items:
            connection_md += (
                f"- `{item.get('kind')}` [{item.get('action')}]: "
                f"count={item.get('count')} → {item.get('recommendation')}\n"
            )
    else:
        connection_md += "- None currently detected.\n"

    coverage_scope = connection_audit.get("coverage_scope", {})
    if isinstance(coverage_scope, dict):
        connection_md += "\n## Coverage Scope\n\n"
        for layer, stats in coverage_scope.items():
            if not isinstance(stats, dict):
                continue
            connection_md += (
                f"- `{layer}`: declared={stats.get('declared', 0)}, discovered={stats.get('discovered', 0)}, "
                f"coverage={stats.get('declared_coverage_ratio', 0)}, semantic_unmapped={stats.get('semantic_unmapped_count', 0)}\n"
            )

    outside_main_body = connection_audit.get("outside_main_body", [])
    if isinstance(outside_main_body, list):
        connection_md += "\n## Outside Main Body\n\n"
        if outside_main_body:
            for item in outside_main_body[:30]:
                if not isinstance(item, dict):
                    continue
                connection_md += f"- `{item.get('path')}` markers={item.get('markers')}\n"
        else:
            connection_md += "- None currently detected.\n"

    iterated_groups = connection_audit.get("iterated_groups", [])
    if isinstance(iterated_groups, list):
        connection_md += "\n## Iterated/Similar Groups\n\n"
        if iterated_groups:
            for group in iterated_groups[:20]:
                if not isinstance(group, dict):
                    continue
                paths = group.get("paths", [])
                if not isinstance(paths, list):
                    paths = []
                connection_md += f"- `{group.get('key')}` count={len(paths)} sample={paths[:5]}\n"
        else:
            connection_md += "- None currently detected.\n"

    superfluous_candidates = connection_audit.get("superfluous_candidates", [])
    if isinstance(superfluous_candidates, list):
        connection_md += "\n## Stale/Superfluous Candidates\n\n"
        if superfluous_candidates:
            for item in superfluous_candidates[:30]:
                if not isinstance(item, dict):
                    continue
                connection_md += f"- `{item.get('path')}` → {item.get('reason')}\n"
        else:
            connection_md += "- None currently detected.\n"

    connection_md += "\n## Visualization\n\n```mermaid\n" + connection_chart + "```\n"

    (ARTIFACTS_DIR / "ISOMORPHISM_CONNECTION_AUDIT.md").write_text(connection_md, encoding="utf-8")

    roadmap_md = """# Isomorphism Finish-Order Roadmap

This roadmap translates current audit gaps into execution priority.

```mermaid
""" + roadmap_chart + """
```

## Priority Policy

- P0: theorem-surface obligations that block full mathematical closure
- P1: runtime confidence expansion and attack-surface closure
- P2: robustness and environment parity hardening

## Programmatic Backlog

See `artifacts/isomorphism_development_backlog.json` for machine-readable tasks.
"""
    (ARTIFACTS_DIR / "ISOMORPHISM_ROADMAP.md").write_text(roadmap_md, encoding="utf-8")

    print("Wrote artifacts/isomorphism_implementation_matrix.json")
    print("Wrote artifacts/isomorphism_gap_report.json")
    print("Wrote artifacts/isomorphism_development_backlog.json")
    print("Wrote artifacts/isomorphism_connection_audit.json")
    print("Wrote artifacts/ISOMORPHISM_VISUALS.md")
    print("Wrote artifacts/ISOMORPHISM_ROADMAP.md")
    print("Wrote artifacts/ISOMORPHISM_CONNECTION_AUDIT.md")
    print("Wrote artifacts/charts/isomorphism_stack.mmd")
    print("Wrote artifacts/charts/analysis_modes.mmd")
    print("Wrote artifacts/charts/isomorphism_finish_order.mmd")
    print("Wrote artifacts/charts/connection_truth_map.mmd")


if __name__ == "__main__":
    build_artifacts()
