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
        elements = matrix.get("elements", [])
        assert elements, "No elements found in matrix"

        failures = []
        for elem in elements:
            if not elem.get("aligned_surface", False):
                per = elem.get("per_layer", {})
                missing = [l for l, v in per.items() if not v]
                failures.append(f"{elem['element']}: missing in {missing}")

        assert not failures, (
            f"{len(failures)} element(s) not aligned across all layers:\n"
            + "\n".join(f"  - {f}" for f in failures)
        )


class TestConnectionAudit:
    """The connection audit must show no disconnected items."""

    def test_no_disconnected_items(self):
        conn = _load("isomorphism_connection_audit.json")
        disconnected = conn.get("disconnected", [])
        # Filter out semantic_unmapped (coverage breadth) — focus on structural disconnects
        structural = [d for d in disconnected if not d.get("element", "").startswith("semantic_unmapped")]
        assert not structural, (
            f"{len(structural)} structural disconnect(s):\n"
            + "\n".join(
                f"  - {d['element']}: {d.get('missing_layers', [])} → {d.get('next_action', '?')}"
                for d in structural
            )
        )

    def test_confidence_not_guarded(self):
        conn = _load("isomorphism_connection_audit.json")
        confidence = conn.get("summary", {}).get("confidence", "unknown")
        assert confidence in ("high", "medium"), (
            f"Connection confidence is '{confidence}' — must be 'high' or 'medium'. "
            "Fix disconnected items and formal obligations to raise confidence."
        )

    def test_no_open_formal_obligations(self):
        conn = _load("isomorphism_connection_audit.json")
        weak_links = conn.get("weak_links", [])
        formal = [wl for wl in weak_links if wl.get("kind") == "formal-obligation-open"]
        assert not formal, (
            f"{len(formal)} open formal obligation(s): "
            + ", ".join(wl.get("sample", ["?"])[0] for wl in formal)
            + " — discharge these in Coq or explicitly accept as tracked gaps."
        )


class TestCoverageThresholds:
    """Coverage ratios must exceed minimum thresholds."""

    # Thresholds per layer (declared/discovered ratio)
    THRESHOLDS = {
        "coq": 0.02,      # Currently 0.0195 — barely passing
        "python": 0.03,    # Currently 0.0323
        "rtl": 0.10,       # Currently 0.1333
        "tests": 0.04,     # Currently 0.045
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

        # Current baseline: 261 + 107 + 13 + 98 = 479
        # Allow 10% growth before failing
        total_unmapped = sum(
            coverage.get(l, {}).get("semantic_unmapped_count", 0)
            for l in ["coq", "python", "rtl", "tests"]
        )
        limit = 530  # ~479 * 1.10
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
        # Currently 1 gap (FullWireSpec). Fail if new gaps appear without being addressed.
        limit = 2
        assert len(gaps) <= limit, (
            f"{len(gaps)} gap(s) in report (limit {limit}):\n"
            + "\n".join(f"  - {g['element']}: {g.get('missing_layers', [])}" for g in gaps)
        )

    def test_known_gaps_are_tracked(self):
        """Ensure the FullWireSpec gap is explicitly tracked."""
        gap = _load("isomorphism_gap_report.json")
        gaps = gap.get("gaps", [])
        elements = [g.get("element", "") for g in gaps]
        # This is the known open gap — it should be tracked
        assert "fullwirespec_discharge" in elements, (
            "FullWireSpec discharge gap is not tracked in gap report. "
            "This is a known obligation that must remain visible until resolved."
        )
