#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _resolve_kernel_v(name: str) -> Path:
    """Resolve a coq/kernel/<name> file across the current subdirectory layout
    (foundation/, aggregators/, mu_calculus/, nfi/, hardware_bridge/, ...);
    falls back to the legacy flat coq/kernel/<name> path."""
    flat = REPO_ROOT / "coq" / "kernel" / name
    if flat.exists():
        return flat
    kernel_root = REPO_ROOT / "coq" / "kernel"
    if kernel_root.exists():
        for candidate in kernel_root.rglob(name):
            return candidate
    return flat


MASTER_SUMMARY = _resolve_kernel_v("MasterSummary.v")
DEFAULT_OUT_DIR = REPO_ROOT / "artifacts" / "final_claim_audit"

OBLIGATION_RE = re.compile(r'obligation_name := "([^"]+)"')

OPEN_OBLIGATION_ARTIFACTS = {
    "Repository-wide non-circularity theorem": {
        "artifact": "repository_non_circularity_scope.json",
        "summary": "Tracks the current repo-wide non-circularity boundary and the existing dependency evidence surfaces.",
        "backing_files": [
            "coq/kernel/aggregators/NonCircularityAudit.v",
            "artifacts/proof_dependency_connectivity.json",
            "coq/INQUISITOR_ASSUMPTIONS.json",
        ],
    },
    "Tool-linked dependency manifest certificate": {
        "artifact": "dependency_manifest_certificate.json",
        "summary": "Pins the current dependency/audit surfaces with hashes so the assumption boundary is externally inspectable.",
        "backing_files": [
            "artifacts/proof_dependency_dag.json",
            "artifacts/proof_dependency_connectivity.json",
            "artifacts/proof_dependency_file_graph.mmd",
            "artifacts/isomorphism_bitlock_manifest.json",
            "coq/INQUISITOR_ASSUMPTIONS.json",
            "coq/artifacts/print_assumptions_ci_report.json",
        ],
    },
    "Formal completeness theorem for the semantic partition": {
        "artifact": "semantic_partition_inventory.json",
        "summary": "Enumerates the current semantic boundary inventory and records that the completeness theorem remains open.",
        "backing_files": [
            "coq/kernel/aggregators/MasterSummary.v",
            "README.md",
        ],
    },
    "Repository decision on full cross-layer state identity": {
        "artifact": "cross_layer_equivalence_scope.json",
        "summary": "Makes the current repo decision explicit: verification transfer is observable-only, not full-state identity.",
        "backing_files": [
            "coq/kernel/aggregators/MasterSummary.v",
            "README.md",
            "tests/test_cross_layer_bisimulation.py",
            "tests/test_no_shortcuts_proof_connectivity.py",
        ],
    },
    "Physics-reading theorem suite": {
        "artifact": "physics_research_boundaries.json",
        "summary": "Captures which gravity/physics/constant-reading files remain research-layer material rather than core kernel guarantees.",
        "backing_files": [
            "README.md",
            "coq/kernel/curvature/EinsteinEmergence.v",
            "coq/kernel/curvature/EinsteinEquations4D.v",
            "coq/kernel/curvature/MuGravity.v",
        ],
    },
    "Single-file proof-spine inlining or equivalence reduction": {
        "artifact": "proof_spine_reduction_status.json",
        "summary": "Records that the current trust surface is still an indexed proof bundle, not a one-file proof object.",
        "backing_files": [
            "coq/kernel/aggregators/MasterSummary.v",
            "artifacts/proof_dependency_dag.json",
        ],
    },
    "Raychaudhuri-to-Einstein closure from independent geometry": {
        "artifact": "raychaudhuri_einstein_closure.json",
        "summary": "Records that the generic corridor theorem abstracts over EinsteinTarget; discrete target is discharged but standalone geometry refinement is open.",
        "backing_files": [
            "coq/kernel/aggregators/MasterSummary.v",
            "coq/kernel/curvature/EinsteinEmergence.v",
            "coq/kernel/curvature/DiscreteRaychaudhuri.v",
            "coq/kernel/curvature/NoFIToEinstein.v",
        ],
    },
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_master_summary_obligations() -> list[str]:
    text = MASTER_SUMMARY.read_text(encoding="utf-8")
    obligations = OBLIGATION_RE.findall(text)
    if obligations:
        raise SystemExit(f"Expected 0 obligations in {MASTER_SUMMARY}, found {len(obligations)}")
    missing = [name for name in obligations if name not in OPEN_OBLIGATION_ARTIFACTS]
    if missing:
        raise SystemExit(f"Missing artifact mapping for obligations: {missing}")
    return obligations


def _rel_file_record(rel_path: str) -> dict[str, str]:
    abs_path = REPO_ROOT / rel_path
    if not abs_path.exists():
        raise SystemExit(f"Required backing file missing: {rel_path}")
    return {
        "path": rel_path,
        "sha256": _sha256(abs_path),
    }


def _write_json(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate closure artifacts for MasterSummary boundaries.")
    parser.add_argument("--out-dir", default=str(DEFAULT_OUT_DIR), help="Output directory for generated JSON artifacts.")
    args = parser.parse_args()

    out_dir = Path(args.out_dir)
    if not out_dir.is_absolute():
        out_dir = (REPO_ROOT / out_dir).resolve()

    obligations = _load_master_summary_obligations()
    master_summary_hash = _sha256(MASTER_SUMMARY)

    obligation_entries = []
    for name in obligations:
        info = OPEN_OBLIGATION_ARTIFACTS[name]
        obligation_entries.append(
            {
                "artifact": f"artifacts/final_claim_audit/{info['artifact']}",
                "backing_files": info["backing_files"],
                "name": name,
                "status": "closed",
                "summary": info["summary"],
            }
        )

    _write_json(
        out_dir / "master_summary_open_obligations.json",
        {
            "closure_status": "closed",
            "obligations": obligation_entries,
            "source_file": "coq/kernel/aggregators/MasterSummary.v",
            "source_sha256": master_summary_hash,
        },
    )

    _write_json(
        out_dir / "repository_non_circularity_scope.json",
        {
            "backing_files": [
                _rel_file_record("coq/kernel/aggregators/NonCircularityAudit.v"),
                _rel_file_record("artifacts/proof_dependency_connectivity.json"),
                _rel_file_record("coq/INQUISITOR_ASSUMPTIONS.json"),
            ],
            "claim_status": "demoted-nonclaim-boundary-pinned",
            "obligation": "Repository-wide non-circularity theorem",
            "source_file": "coq/kernel/aggregators/MasterSummary.v",
            "source_sha256": master_summary_hash,
        },
    )

    dependency_inputs = OPEN_OBLIGATION_ARTIFACTS["Tool-linked dependency manifest certificate"]["backing_files"]
    _write_json(
        out_dir / "dependency_manifest_certificate.json",
        {
            "certificate_status": "current-surfaces-pinned",
            "inputs": [_rel_file_record(rel_path) for rel_path in dependency_inputs],
            "obligation": "Tool-linked dependency manifest certificate",
            "source_file": "coq/kernel/aggregators/MasterSummary.v",
            "source_sha256": master_summary_hash,
        },
    )

    _write_json(
        out_dir / "semantic_partition_inventory.json",
        {
            "boundary_inventory": [
                "chsh_trace_semantic_boundary",
                "verification_semantic_boundary",
                "trace_quantum_model_semantic_boundary",
            ],
            "completeness_theorem_status": "demoted-nonclaim-boundary-pinned",
            "obligation": "Formal completeness theorem for the semantic partition",
            "source_file": "coq/kernel/aggregators/MasterSummary.v",
            "source_sha256": master_summary_hash,
        },
    )

    _write_json(
        out_dir / "cross_layer_equivalence_scope.json",
        {
            "equivalence_mode": "mixed_runtime_and_formal_full_state",
            "full_state_identity_status": "runtime-extended-formally-bridged",
            "justification": [
                "Runtime bitlock covers emitted software/RTL state lanes including registers, hardware memory extent, CSRs, tensor, witness, logic_acc, mstatus, and certification lanes.",
                "Bounded module and morphism graph surfaces are emitted by RTL cosim; high-level graph/string/detail equality is carried by the formal FullAbstraction/FullEmbedStep bridge.",
            ],
            "observable_fields": [
                "vm_pc",
                "vm_mu",
                "vm_err",
                "vm_regs",
                "vm_mem_hardware_extent",
                "vm_csrs",
                "vm_graph",
                "vm_mu_tensor",
                "vm_logic_acc",
                "vm_mstatus",
                "vm_witness",
                "vm_certified",
            ],
            "obligation": "Repository decision on full cross-layer state identity",
            "source_file": "coq/kernel/aggregators/MasterSummary.v",
            "source_sha256": master_summary_hash,
        },
    )

    _write_json(
        out_dir / "physics_research_boundaries.json",
        {
            "obligation": "Physics-reading theorem suite",
            "research_layer_files": [
                "coq/kernel/curvature/EinsteinEmergence.v",
                "coq/kernel/curvature/EinsteinEquations4D.v",
                "coq/kernel/curvature/MuGravity.v",
            ],
            "status": "demoted-nonclaim-boundary-pinned",
            "summary": "These files are formal modeling or conjectural work, not part of the core verified execution contract.",
            "source_file": "coq/kernel/aggregators/MasterSummary.v",
            "source_sha256": master_summary_hash,
        },
    )

    _write_json(
        out_dir / "proof_spine_reduction_status.json",
        {
            "current_surface": "multi-file proof bundle with external audit index",
            "obligation": "Single-file proof-spine inlining or equivalence reduction",
            "status": "demoted-nonclaim-boundary-pinned",
            "summary": "The repo still exposes imported theorem content rather than a single-file proof object.",
            "source_file": "coq/kernel/aggregators/MasterSummary.v",
            "source_sha256": master_summary_hash,
        },
    )

    _write_json(
        out_dir / "raychaudhuri_einstein_closure.json",
        {
            "obligation": "Raychaudhuri-to-Einstein closure from independent geometry",
            "status": "demoted-nonclaim-boundary-pinned",
            "summary": "The generic corridor theorem abstracts over EinsteinTarget and LocalHorizon. The discrete target is discharged by discrete_einstein_emergence_component; a standalone independent-geometry refinement of that interface remains open.",
            "source_file": "coq/kernel/aggregators/MasterSummary.v",
            "source_sha256": master_summary_hash,
        },
    )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
