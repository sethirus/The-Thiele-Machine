#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Tuple


REPO_ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = REPO_ROOT / "artifacts"
CHARTS = ARTIFACTS / "charts"


@dataclass
class InquisitorSignals:
    high: int = 0
    medium: int = 0
    low: int = 0
    rules: Dict[str, int] = field(default_factory=dict)


def _load_json(path: Path) -> dict:
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}


def _parse_inquisitor(report_path: Path, output_path: Path) -> InquisitorSignals:
    sig = InquisitorSignals()

    report_text = report_path.read_text(encoding="utf-8", errors="replace") if report_path.exists() else ""
    output_text = output_path.read_text(encoding="utf-8", errors="replace") if output_path.exists() else ""

    m_high = re.search(r"-\s+HIGH:\s+(\d+)", report_text)
    m_med = re.search(r"-\s+MEDIUM:\s+(\d+)", report_text)
    m_low = re.search(r"-\s+LOW:\s+(\d+)", report_text)
    if m_high:
        sig.high = int(m_high.group(1))
    if m_med:
        sig.medium = int(m_med.group(1))
    if m_low:
        sig.low = int(m_low.group(1))

    def parse_findings_rules(text: str) -> None:
        if not text:
            return
        lines = text.splitlines()
        in_findings = False
        for line in lines:
            stripped = line.strip()
            if stripped.startswith("## Findings") or stripped.startswith("Findings"):
                in_findings = True
                continue
            if in_findings and stripped.startswith("## "):
                break
            if not in_findings:
                continue
            # Expected finding style:
            # - file.v:L423 RULE_ID ...
            # - [HIGH] RULE_ID: ...
            match = re.search(r"\b([A-Z][A-Z0-9_]{2,})\b", stripped)
            if not match:
                continue
            rule = match.group(1)
            if rule in {"HIGH", "MEDIUM", "LOW", "INQUISITOR", "FAIL", "FORBIDDEN", "NONE"}:
                continue
            sig.rules[rule] = sig.rules.get(rule, 0) + 1

    parse_findings_rules(report_text)
    parse_findings_rules(output_text)

    return sig


def _build_alignment_heatmap_data(matrix: dict) -> Tuple[List[str], List[str], List[List[float]]]:
    layers = matrix.get("layers", [])
    elements = [e.get("label", e.get("element", "unknown")) for e in matrix.get("elements", [])]
    values: List[List[float]] = []
    for elem in matrix.get("elements", []):
        per_layer = elem.get("per_layer", {})
        row = [1.0 if per_layer.get(layer, False) else 0.0 for layer in layers]
        values.append(row)
    return elements, layers, values


def _connection_pressure(connection_audit: dict) -> Dict[str, float]:
    summary = connection_audit.get("summary", {}) if isinstance(connection_audit, dict) else {}
    proof = connection_audit.get("proof_graph_signals", {}) if isinstance(connection_audit, dict) else {}

    disconnected = float(summary.get("disconnected_count", 0) or 0)
    weak_links = float(summary.get("weak_link_count", 0) or 0)
    connected = float(summary.get("connected_count", 0) or 0)
    isolated = float(proof.get("isolated_count", 0) or 0)
    coverage_scope = connection_audit.get("coverage_scope", {}) if isinstance(connection_audit, dict) else {}
    outside_main_body = connection_audit.get("outside_main_body", []) if isinstance(connection_audit, dict) else []
    superfluous_candidates = connection_audit.get("superfluous_candidates", []) if isinstance(connection_audit, dict) else []

    denom = max(1.0, connected + disconnected)
    disconnect_pressure = min(1.0, (disconnected + 0.5 * weak_links) / denom)
    proof_isolation = min(1.0, isolated / 100.0)

    semantic_unmapped_total = 0.0
    if isinstance(coverage_scope, dict):
        for _, layer_stats in coverage_scope.items():
            if not isinstance(layer_stats, dict):
                continue
            semantic_unmapped_total += float(layer_stats.get("semantic_unmapped_count", 0) or 0)

    semantic_sprawl = min(1.0, semantic_unmapped_total / 120.0)
    outside_pressure = min(1.0, (len(outside_main_body) if isinstance(outside_main_body, list) else 0) / 80.0)
    stale_pressure = min(1.0, (len(superfluous_candidates) if isinstance(superfluous_candidates, list) else 0) / 80.0)

    return {
        "disconnect_pressure": disconnect_pressure,
        "proof_isolation": proof_isolation,
        "semantic_sprawl": semantic_sprawl,
        "outside_pressure": outside_pressure,
        "stale_pressure": stale_pressure,
    }


def _risk_factors_for_backlog_item(item: dict, sig: InquisitorSignals, connection_audit: dict) -> List[float]:
    title = (item.get("title") or "").lower()
    identifier = (item.get("id") or "").lower()

    formal_risk = 1.0 if "fullwirespec" in identifier or "proof" in title else 0.5
    runtime_risk = 1.0 if "lockstep" in title or "coverage" in title else 0.6
    receipt_risk = 1.0 if "receipt" in title else 0.4
    backend_risk = 1.0 if "simulator" in title or "backend" in title else 0.4
    inquisitor_pressure = min(1.0, (sig.high * 2 + sig.medium + 0.5 * sig.low) / 10.0)
    connection = _connection_pressure(connection_audit)
    disconnect_pressure = connection["disconnect_pressure"]
    proof_isolation = connection["proof_isolation"]
    semantic_sprawl = connection.get("semantic_sprawl", 0.0)
    outside_pressure = connection.get("outside_pressure", 0.0)
    stale_pressure = connection.get("stale_pressure", 0.0)

    return [
        formal_risk,
        runtime_risk,
        receipt_risk,
        backend_risk,
        inquisitor_pressure,
        disconnect_pressure,
        proof_isolation,
        semantic_sprawl,
        outside_pressure,
        stale_pressure,
    ]


def _build_targeting(backlog_payload: dict, matrix_payload: dict, sig: InquisitorSignals, connection_audit: dict) -> dict:
    backlog = backlog_payload.get("backlog", [])
    factors = [
        "formal_gap",
        "runtime_coverage",
        "receipt_integrity",
        "backend_parity",
        "inquisitor_pressure",
        "disconnect_pressure",
        "proof_isolation",
        "semantic_sprawl",
        "outside_pressure",
        "stale_pressure",
    ]

    factor_weights = {
        "formal_gap": 0.24,
        "runtime_coverage": 0.20,
        "receipt_integrity": 0.16,
        "backend_parity": 0.12,
        "inquisitor_pressure": 0.08,
        "disconnect_pressure": 0.12,
        "proof_isolation": 0.08,
        "semantic_sprawl": 0.05,
        "outside_pressure": 0.04,
        "stale_pressure": 0.03,
    }

    rows = []
    for item in backlog:
        vals = _risk_factors_for_backlog_item(item, sig, connection_audit)
        weighted = (
            vals[0] * factor_weights["formal_gap"]
            + vals[1] * factor_weights["runtime_coverage"]
            + vals[2] * factor_weights["receipt_integrity"]
            + vals[3] * factor_weights["backend_parity"]
            + vals[4] * factor_weights["inquisitor_pressure"]
            + vals[5] * factor_weights["disconnect_pressure"]
            + vals[6] * factor_weights["proof_isolation"]
            + vals[7] * factor_weights["semantic_sprawl"]
            + vals[8] * factor_weights["outside_pressure"]
            + vals[9] * factor_weights["stale_pressure"]
        )
        rows.append(
            {
                "id": item.get("id"),
                "priority": item.get("priority"),
                "title": item.get("title"),
                "factors": {name: vals[i] for i, name in enumerate(factors)},
                "heuristic_score": round(weighted, 4),
                "validation": item.get("validation", []),
            }
        )

    rows.sort(key=lambda r: r["heuristic_score"], reverse=True)

    return {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "factor_weights": factor_weights,
        "connection_signals": _connection_pressure(connection_audit),
        "inquisitor": {
            "high": sig.high,
            "medium": sig.medium,
            "low": sig.low,
            "top_rules": sorted(sig.rules.items(), key=lambda kv: kv[1], reverse=True)[:20],
        },
        "alignment_summary": matrix_payload.get("summary", {}),
        "targets": rows,
    }


def _plot_heatmap(title: str, rows: List[str], cols: List[str], data: List[List[float]], out_path: Path, cmap: str = "viridis") -> None:
    import matplotlib.pyplot as plt
    import numpy as np

    arr = np.array(data, dtype=float) if data else np.zeros((1, 1))
    fig_w = max(8, len(cols) * 1.6)
    fig_h = max(5, len(rows) * 0.6)
    fig, ax = plt.subplots(figsize=(fig_w, fig_h))
    im = ax.imshow(arr, cmap=cmap, aspect="auto")

    ax.set_title(title)
    ax.set_xticks(range(len(cols)))
    ax.set_xticklabels(cols, rotation=30, ha="right")
    ax.set_yticks(range(len(rows)))
    ax.set_yticklabels(rows)

    for i in range(arr.shape[0]):
        for j in range(arr.shape[1]):
            val = arr[i, j]
            text = f"{val:.0f}" if val in (0.0, 1.0) else f"{val:.2f}"
            ax.text(j, i, text, ha="center", va="center", color="white" if val > 0.65 else "black", fontsize=8)

    fig.colorbar(im, ax=ax, fraction=0.046, pad=0.04)
    fig.tight_layout()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_path, dpi=170)
    plt.close(fig)


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate heatmaps + heuristic targeting from isomorphism/inquisitor artifacts")
    parser.add_argument("--matrix", default="artifacts/isomorphism_implementation_matrix.json")
    parser.add_argument("--gap", default="artifacts/isomorphism_gap_report.json")
    parser.add_argument("--backlog", default="artifacts/isomorphism_development_backlog.json")
    parser.add_argument("--connection-audit", default="artifacts/isomorphism_connection_audit.json")
    parser.add_argument("--inquisitor-report", default="INQUISITOR_REPORT.md")
    parser.add_argument("--inquisitor-output", default="inquisitor_output.txt")
    args = parser.parse_args()

    matrix_path = (REPO_ROOT / args.matrix).resolve()
    gap_path = (REPO_ROOT / args.gap).resolve()
    backlog_path = (REPO_ROOT / args.backlog).resolve()
    connection_audit_path = (REPO_ROOT / args.connection_audit).resolve()
    report_path = (REPO_ROOT / args.inquisitor_report).resolve()
    output_path = (REPO_ROOT / args.inquisitor_output).resolve()

    matrix = _load_json(matrix_path)
    gap = _load_json(gap_path)
    backlog = _load_json(backlog_path)
    connection_audit = _load_json(connection_audit_path)
    sig = _parse_inquisitor(report_path, output_path)

    elements, layers, align_data = _build_alignment_heatmap_data(matrix)

    targeting = _build_targeting(backlog, matrix, sig, connection_audit)

    # Heatmap 1: layer-element alignment
    _plot_heatmap(
        "Cross-Layer Alignment Heatmap (1=present, 0=missing)",
        elements if elements else ["none"],
        layers if layers else ["none"],
        align_data if align_data else [[0]],
        CHARTS / "layer_alignment_heatmap.png",
        cmap="Greens",
    )

    # Heatmap 2: heuristic target scores by factor
    target_rows = targeting.get("targets", [])
    t_labels = [f"{t.get('priority','?')} {t.get('id','unknown')}" for t in target_rows] or ["none"]
    factor_cols = [
        "formal_gap",
        "runtime_coverage",
        "receipt_integrity",
        "backend_parity",
        "inquisitor_pressure",
        "disconnect_pressure",
        "proof_isolation",
        "semantic_sprawl",
        "outside_pressure",
        "stale_pressure",
    ]
    t_data = [
        [float(t.get("factors", {}).get(col, 0.0)) for col in factor_cols]
        for t in target_rows
    ] or [[0.0] * len(factor_cols)]
    _plot_heatmap(
        "Heuristic Targeting Heatmap (risk factors)",
        t_labels,
        factor_cols,
        t_data,
        CHARTS / "heuristic_targeting_heatmap.png",
        cmap="YlOrRd",
    )

    # Heatmap 3: Inquisitor severity + top rule frequencies
    sev_cols = ["HIGH", "MEDIUM", "LOW"]
    sev_data = [[float(sig.high), float(sig.medium), float(sig.low)]]
    _plot_heatmap(
        "Inquisitor Severity Heatmap",
        ["Current findings summary"],
        sev_cols,
        sev_data,
        CHARTS / "inquisitor_severity_heatmap.png",
        cmap="Reds",
    )

    (ARTIFACTS / "heuristic_targeting.json").write_text(json.dumps(targeting, indent=2), encoding="utf-8")

    top_targets = targeting.get("targets", [])[:5]
    gap_count = len(gap.get("gaps", [])) if isinstance(gap, dict) else 0
    md = [
        "# Heuristic Targeting + Heatmaps",
        "",
        f"Generated: {targeting.get('generated_at')}",
        "",
        "## Heatmaps",
        "",
        "- layer alignment: `artifacts/charts/layer_alignment_heatmap.png`",
        "- heuristic targeting: `artifacts/charts/heuristic_targeting_heatmap.png`",
        "- inquisitor severity: `artifacts/charts/inquisitor_severity_heatmap.png`",
        "",
        "## Integrated Signals",
        "",
        f"- Inquisitor summary: HIGH={sig.high}, MEDIUM={sig.medium}, LOW={sig.low}",
        f"- Gap report items: {gap_count}",
        f"- Connection pressure: {targeting.get('connection_signals', {})}",
        f"- Alignment summary: {matrix.get('summary', {})}",
        "",
        "## Top Heuristic Targets",
        "",
    ]

    if not top_targets:
        md.append("- No backlog targets found.")
    else:
        for idx, t in enumerate(top_targets, start=1):
            md.append(
                f"- {idx}. `{t.get('id')}` ({t.get('priority')}) score={t.get('heuristic_score')} — {t.get('title')}"
            )

    md.extend(
        [
            "",
            "## Programmatic Artifacts",
            "",
            "- `artifacts/heuristic_targeting.json`",
            "- `artifacts/isomorphism_implementation_matrix.json`",
            "- `artifacts/isomorphism_gap_report.json`",
            "- `INQUISITOR_REPORT.md`",
        ]
    )

    (ARTIFACTS / "HEURISTIC_TARGETING.md").write_text("\n".join(md) + "\n", encoding="utf-8")

    print("Wrote artifacts/charts/layer_alignment_heatmap.png")
    print("Wrote artifacts/charts/heuristic_targeting_heatmap.png")
    print("Wrote artifacts/charts/inquisitor_severity_heatmap.png")
    print("Wrote artifacts/heuristic_targeting.json")
    print("Wrote artifacts/HEURISTIC_TARGETING.md")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
