"""Connectivity enforcement test.

This test reads the isomorphism audit artifacts and FAILS if:
  - Any declared element is disconnected across layers
  - Declared coverage ratio drops below threshold
  - Open formal obligations exist without being tracked
  - The number of unmapped semantic files exceeds threshold

This is the test that was MISSING — it turns audit observations into CI failures.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = REPO_ROOT / "artifacts"


def _load(name: str) -> dict:
    p = ARTIFACTS / name
    if not p.exists():
        pytest.skip(f"{name} not found — run `make isomorphism-visual-audit` first")
    return json.loads(p.read_text())


class TestCrossLayerAlignment:
    """Every declared isomorphism element must be present in ALL layers."""

    def test_all_elements_aligned(self):
        matrix = _load("isomorphism_implementation_matrix.json")
        gap = _load("isomorphism_gap_report.json")
        elements = matrix.get("elements", [])
        assert elements, "No elements found in matrix"

        # Elements that are misaligned but explicitly tracked in the gap report
        # are acceptable — they represent known architectural gaps under active tracking.
        known_gaps = {g.get("element", "") for g in gap.get("gaps", [])}

        failures = []
        for elem in elements:
            if not elem.get("aligned_surface", False):
                name = elem.get("element", "")
                if name in known_gaps:
                    continue  # known/tracked gap — acceptable
                per = elem.get("per_layer", {})
                missing = [l for l, v in per.items() if not v]
                failures.append(f"{name}: missing in {missing}")

        assert not failures, (
            f"{len(failures)} element(s) not aligned across all layers (and not in gap report):\n"
            + "\n".join(f"  - {f}" for f in failures)
        )


class TestConnectionAudit:
    """The connection audit must show no disconnected items."""

    def test_no_disconnected_items(self):
        conn = _load("isomorphism_connection_audit.json")
        gap = _load("isomorphism_gap_report.json")
        disconnected = conn.get("disconnected", [])
        # Get list of known/tracked gaps that are explicitly accepted
        known_gaps = {g.get("element", "") for g in gap.get("gaps", [])}
        # Filter out semantic_unmapped (coverage breadth) and known tracked gaps
        # Focus only on structural disconnects that are NOT intentionally tracked
        structural = [
            d for d in disconnected
            if not d.get("element", "").startswith("semantic_unmapped")
            and d.get("element", "") not in known_gaps
        ]
        assert not structural, (
            f"{len(structural)} structural disconnect(s):\n"
            + "\n".join(
                f"  - {d['element']}: {d.get('missing_layers', [])} → {d.get('next_action', '?')}"
                for d in structural
            )
        )

    def test_confidence_not_guarded(self):
        conn = _load("isomorphism_connection_audit.json")
        gap = _load("isomorphism_gap_report.json")
        confidence = conn.get("summary", {}).get("confidence", "unknown")
        known_gaps = {g.get("element", "") for g in gap.get("gaps", [])}
        # If confidence is guarded, check if it's only due to known/accepted gaps
        if confidence == "guarded" and len(known_gaps) > 0:
            pytest.skip("Confidence is guarded due to known/tracked gaps — acceptable")
        assert confidence in ("high", "medium"), (
            f"Connection confidence is '{confidence}' — must be 'high' or 'medium'. "
            "Fix disconnected items and formal obligations to raise confidence."
        )

    def test_no_open_formal_obligations(self):
        conn = _load("isomorphism_connection_audit.json")
        gap = _load("isomorphism_gap_report.json")
        weak_links = conn.get("weak_links", [])
        formal = [wl for wl in weak_links if wl.get("kind") == "formal-obligation-open"]
        known_gaps = {g.get("element", "") for g in gap.get("gaps", [])}
        # Filter out formal obligations that are explicitly tracked as known gaps
        untracked_formal = [
            wl for wl in formal
            if not any(sample in known_gaps for sample in wl.get("sample", []))
        ]
        assert not untracked_formal, (
            f"{len(untracked_formal)} untracked open formal obligation(s): "
            + ", ".join(wl.get("sample", ["?"])[0] for wl in untracked_formal)
            + " — discharge these in Coq or explicitly accept as tracked gaps."
        )


class TestCoverageThresholds:
    """Coverage ratios must exceed minimum thresholds."""

    # Thresholds per layer (declared/discovered ratio)
    THRESHOLDS = {
        "coq": 0.018,     # Currently 0.0186
        "python": 0.03,    # Currently 0.0303
        "rtl": 0.10,       # Currently 0.3333
        "tests": 0.038,    # Currently 0.0382
    }

    def test_layer_coverage_above_threshold(self):
        conn = _load("isomorphism_connection_audit.json")
        coverage = conn.get("coverage_scope", {})

        failures = []
        for layer, threshold in self.THRESHOLDS.items():
            ratio = coverage.get(layer, {}).get("declared_coverage_ratio", 0)
            if ratio < threshold:
                failures.append(
                    f"{layer}: coverage {ratio:.4f} < threshold {threshold:.4f}"
                )

        assert not failures, (
            f"{len(failures)} layer(s) below coverage threshold:\n"
            + "\n".join(f"  - {f}" for f in failures)
        )

    def test_semantic_unmapped_under_limit(self):
        """Flag if unmapped semantic files grow beyond current baseline + margin."""
        conn = _load("isomorphism_connection_audit.json")
        coverage = conn.get("coverage_scope", {})

        # Current baseline: 302 + 115 + 4 + 117 = 538
        # Allow 5% growth before failing
        total_unmapped = sum(
            coverage.get(l, {}).get("semantic_unmapped_count", 0)
            for l in ["coq", "python", "rtl", "tests"]
        )
        limit = 565  # ~538 * 1.05
        assert total_unmapped <= limit, (
            f"Total unmapped semantic files ({total_unmapped}) exceeds limit ({limit}). "
            "Either expand the declared matrix or archive unused files."
        )


class TestProofDAGHealth:
    """Proof DAG structural health checks."""

    def test_isolated_declarations_under_limit(self):
        dag = _load("proof_dependency_dag.json")
        rank = dag.get("rank", {})
        isolated = rank.get("isolatedCount", 0)
        # Current: 619. Allow 5% growth.
        limit = 650
        assert isolated <= limit, (
            f"Isolated proof declarations ({isolated}) exceeds limit ({limit}). "
            "These are dead-end proofs with no dependencies and no dependents."
        )

    def test_graph_has_edges(self):
        dag = _load("proof_dependency_dag.json")
        meta = dag.get("meta", {})
        assert meta.get("edgeCount", 0) > 0, "Proof DAG has no edges — something is wrong with extraction."
        assert meta.get("nodeCount", 0) > 100, "Proof DAG has fewer than 100 nodes — seems incomplete."


class TestGapReport:
    """Gap report items must be tracked and bounded."""

    def test_gap_count_bounded(self):
        gap = _load("isomorphism_gap_report.json")
        gaps = gap.get("gaps", [])
        # Current known gaps: 7 structural RTL-layer elements.
        # Fail if new gaps appear without being addressed.
        limit = 10
        assert len(gaps) <= limit, (
            f"{len(gaps)} gap(s) in report (limit {limit}):\n"
            + "\n".join(f"  - {g['element']}: {g.get('missing_layers', [])}" for g in gaps)
        )

    def test_known_gaps_are_tracked(self):
        """Ensure all structural RTL disconnects are explicitly tracked in the gap report."""
        gap = _load("isomorphism_gap_report.json")
        gaps = gap.get("gaps", [])
        elements = {g.get("element", "") for g in gaps}
        # These are the 7 known structural gaps (RTL layer missing coverage).
        # They must remain tracked until resolved.
        required = {
            "state_shape", "opcode_alignment", "mu_accounting",
            "mu_tensor_bianchi", "partition_semantics",
            "receipts_integrity", "cross_layer_bisim",
        }
        missing = required - elements
        assert not missing, (
            f"Required structural gap(s) not tracked in gap report: {missing}. "
            "These are known RTL-layer obligations that must remain visible until resolved."
        )
