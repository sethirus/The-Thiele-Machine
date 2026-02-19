#!/usr/bin/env python3
"""Generate comprehensive PNG dashboard images for the Thiele Machine isomorphism audit.

Produces:
  artifacts/charts/01_layer_connectivity_map.png   — full cross-layer wiring diagram
  artifacts/charts/02_coverage_heatmap.png         — declared vs discovered per layer
  artifacts/charts/03_proof_dag_overview.png        — proof dependency DAG (top hubs + structure)
  artifacts/charts/04_gap_dashboard.png             — disconnection/gap summary dashboard
  artifacts/charts/05_test_coverage_radar.png       — test coverage radar chart
  artifacts/charts/06_repo_surface_treemap.png      — repo surface area by layer
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any, Dict, List

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = REPO_ROOT / "artifacts"
CHARTS = ARTIFACTS / "charts"


def _load(name: str) -> dict:
    p = ARTIFACTS / name
    if not p.exists():
        return {}
    return json.loads(p.read_text())


def fig1_layer_connectivity_map() -> None:
    """Full cross-layer wiring diagram showing what connects to what."""
    fig, ax = plt.subplots(figsize=(18, 12))
    ax.set_xlim(-1, 11)
    ax.set_ylim(-1, 9)
    ax.set_aspect("equal")
    ax.axis("off")
    fig.patch.set_facecolor("#0d1117")
    ax.set_facecolor("#0d1117")

    # Layer boxes
    layers = [
        {"name": "Coq Kernel\n(308 files)", "x": 1, "y": 7, "color": "#2ea043", "declared": 6, "discovered": 308},
        {"name": "Python VM\n(122 files)", "x": 5, "y": 7, "color": "#1f6feb", "declared": 4, "discovered": 122},
        {"name": "RTL/FPGA\n(15 files)", "x": 9, "y": 7, "color": "#da3633", "declared": 2, "discovered": 15},
        {"name": "Tests\n(111 files)", "x": 5, "y": 1, "color": "#a371f7", "declared": 5, "discovered": 111},
    ]

    # Elements that connect layers
    elements = [
        {"name": "State Shape", "layers": ["coq", "python", "rtl", "tests"], "y": 5.5, "color": "#58a6ff"},
        {"name": "Opcode Alignment", "layers": ["coq", "python", "rtl", "tests"], "y": 5.0, "color": "#58a6ff"},
        {"name": "μ Accounting", "layers": ["coq", "python", "rtl", "tests"], "y": 4.5, "color": "#58a6ff"},
        {"name": "μ-Tensor+Bianchi", "layers": ["coq", "python", "rtl", "tests"], "y": 4.0, "color": "#58a6ff"},
        {"name": "Partition Semantics", "layers": ["coq", "python", "rtl", "tests"], "y": 3.5, "color": "#58a6ff"},
        {"name": "Receipt Integrity", "layers": ["coq", "python", "rtl", "tests"], "y": 3.0, "color": "#58a6ff"},
        {"name": "Cross-Layer Bisim", "layers": ["coq", "python", "rtl", "tests"], "y": 2.5, "color": "#58a6ff"},
    ]

    # Draw layer boxes
    for layer in layers:
        rect = mpatches.FancyBboxPatch(
            (layer["x"] - 1.2, layer["y"] - 0.5), 2.4, 1.2,
            boxstyle="round,pad=0.1", facecolor=layer["color"], alpha=0.3,
            edgecolor=layer["color"], linewidth=2
        )
        ax.add_patch(rect)
        ax.text(layer["x"], layer["y"] + 0.15, layer["name"],
                ha="center", va="center", color="white", fontsize=11, fontweight="bold")
        # Coverage badge
        ratio = layer["declared"] / max(1, layer["discovered"])
        badge_color = "#2ea043" if ratio > 0.5 else "#d29922" if ratio > 0.1 else "#da3633"
        ax.text(layer["x"], layer["y"] - 0.3,
                f"Declared: {layer['declared']}/{layer['discovered']} ({ratio:.1%})",
                ha="center", va="center", color=badge_color, fontsize=8)

    # Draw element connections
    layer_x = {"coq": 1, "python": 5, "rtl": 9, "tests": 5}
    layer_y_top = {"coq": 6.5, "python": 6.5, "rtl": 6.5, "tests": 2.0}

    for elem in elements:
        # Element label
        ax.text(0.0, elem["y"], elem["name"], ha="right", va="center",
                color="#c9d1d9", fontsize=9, fontweight="bold")

        # Connected check mark
        ax.text(0.25, elem["y"], "●", ha="center", va="center",
                color="#2ea043", fontsize=12)

        # Draw lines to each connected layer
        for lname in elem["layers"]:
            lx = layer_x[lname]
            ly = layer_y_top[lname]
            ax.plot([0.4, lx], [elem["y"], ly],
                    color=elem["color"], alpha=0.15, linewidth=1, linestyle="-")

    # Disconnected element
    ax.text(0.0, 1.8, "FullWireSpec Discharge", ha="right", va="center",
            color="#da3633", fontsize=9, fontweight="bold")
    ax.text(0.25, 1.8, "✗", ha="center", va="center",
            color="#da3633", fontsize=12)
    ax.text(0.6, 1.8, "→ Missing Coq instantiation for non-Coq concrete spec",
            ha="left", va="center", color="#f85149", fontsize=8)

    # Unmapped semantic files callout
    ax.text(5, 0.2,
            "UNMAPPED: 261 Coq + 105 Python + 13 RTL + 98 Tests = 477 semantic files outside declared matrix",
            ha="center", va="center", color="#d29922", fontsize=10, fontweight="bold",
            bbox=dict(boxstyle="round,pad=0.4", facecolor="#d29922", alpha=0.15, edgecolor="#d29922"))

    # Title
    ax.text(5, 8.5, "Thiele Machine — Cross-Layer Connectivity Map",
            ha="center", va="center", color="white", fontsize=16, fontweight="bold")
    ax.text(5, 8.1, "7 connected elements, 1 formal gap, 477 unmapped semantic files",
            ha="center", va="center", color="#8b949e", fontsize=11)

    # Legend
    legend_items = [
        mpatches.Patch(color="#2ea043", alpha=0.5, label="Coq Kernel (6 declared)"),
        mpatches.Patch(color="#1f6feb", alpha=0.5, label="Python VM (4 declared)"),
        mpatches.Patch(color="#da3633", alpha=0.5, label="RTL/FPGA (2 declared)"),
        mpatches.Patch(color="#a371f7", alpha=0.5, label="Tests (5 declared)"),
    ]
    ax.legend(handles=legend_items, loc="upper right", facecolor="#161b22",
              edgecolor="#30363d", labelcolor="white", fontsize=9)

    fig.tight_layout()
    fig.savefig(CHARTS / "01_layer_connectivity_map.png", dpi=180, facecolor="#0d1117")
    plt.close(fig)
    print("Wrote 01_layer_connectivity_map.png")


def fig2_coverage_heatmap() -> None:
    """Declared vs discovered per layer with semantic unmapped counts."""
    conn = _load("isomorphism_connection_audit.json")
    coverage = conn.get("coverage_scope", {})

    layers = ["coq", "python", "rtl", "tests"]
    metrics = ["declared", "discovered", "semantic_unmapped_count", "declared_coverage_ratio"]
    labels = ["Declared", "Discovered", "Unmapped", "Coverage %"]

    data = []
    for metric in metrics:
        row = []
        for layer in layers:
            val = coverage.get(layer, {}).get(metric, 0)
            row.append(float(val))
        data.append(row)

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.patch.set_facecolor("#0d1117")
    fig.suptitle("Repo Surface Coverage by Layer", color="white", fontsize=16, fontweight="bold")

    colors = ["#2ea043", "#1f6feb", "#da3633", "#a371f7"]

    # Bar chart: declared vs discovered
    ax = axes[0, 0]
    ax.set_facecolor("#161b22")
    x = np.arange(len(layers))
    declared = [coverage.get(l, {}).get("declared", 0) for l in layers]
    discovered = [coverage.get(l, {}).get("discovered", 0) for l in layers]
    ax.bar(x - 0.2, declared, 0.35, color="#2ea043", label="Declared", alpha=0.8)
    ax.bar(x + 0.2, discovered, 0.35, color="#da3633", label="Discovered", alpha=0.8)
    ax.set_xticks(x)
    ax.set_xticklabels([l.upper() for l in layers], color="white")
    ax.set_title("Declared vs Discovered Files", color="white", fontsize=12)
    ax.legend(facecolor="#161b22", edgecolor="#30363d", labelcolor="white")
    ax.tick_params(colors="white")
    for spine in ax.spines.values():
        spine.set_color("#30363d")

    # Pie: unmapped distribution
    ax = axes[0, 1]
    ax.set_facecolor("#0d1117")
    unmapped = [coverage.get(l, {}).get("semantic_unmapped_count", 0) for l in layers]
    if sum(unmapped) > 0:
        wedges, texts, autotexts = ax.pie(
            unmapped, labels=[f"{l.upper()}\n({u})" for l, u in zip(layers, unmapped)],
            colors=colors, autopct="%1.0f%%", textprops={"color": "white", "fontsize": 9}
        )
        for at in autotexts:
            at.set_color("white")
    ax.set_title("Unmapped Semantic Files Distribution", color="white", fontsize=12)

    # Coverage ratio bars
    ax = axes[1, 0]
    ax.set_facecolor("#161b22")
    ratios = [coverage.get(l, {}).get("declared_coverage_ratio", 0) * 100 for l in layers]
    bars = ax.barh(layers, ratios, color=colors, alpha=0.8)
    ax.set_xlim(0, 100)
    ax.set_title("Declared Coverage Ratio (%)", color="white", fontsize=12)
    ax.tick_params(colors="white")
    for spine in ax.spines.values():
        spine.set_color("#30363d")
    for bar, ratio in zip(bars, ratios):
        ax.text(bar.get_width() + 1, bar.get_y() + bar.get_height()/2,
                f"{ratio:.1f}%", va="center", color="white", fontsize=10)

    # Summary text
    ax = axes[1, 1]
    ax.set_facecolor("#161b22")
    ax.axis("off")
    total_declared = sum(declared)
    total_discovered = sum(discovered)
    total_unmapped = sum(unmapped)
    summary_text = (
        f"TOTAL DECLARED: {total_declared}\n"
        f"TOTAL DISCOVERED: {total_discovered}\n"
        f"TOTAL UNMAPPED: {total_unmapped}\n"
        f"OVERALL COVERAGE: {total_declared/max(1,total_discovered):.1%}\n\n"
        f"The audit matrix declares {total_declared} files.\n"
        f"The repo contains {total_discovered} semantic files.\n"
        f"{total_unmapped} files ({total_unmapped/max(1,total_discovered):.0%}) are\n"
        f"outside the declared audit surface."
    )
    ax.text(0.5, 0.5, summary_text, ha="center", va="center",
            color="#c9d1d9", fontsize=11, fontfamily="monospace",
            bbox=dict(boxstyle="round,pad=0.5", facecolor="#0d1117", edgecolor="#30363d"))

    fig.tight_layout()
    fig.savefig(CHARTS / "02_coverage_heatmap.png", dpi=180, facecolor="#0d1117")
    plt.close(fig)
    print("Wrote 02_coverage_heatmap.png")


def fig3_proof_dag_overview() -> None:
    """Proof dependency DAG visualization showing structure."""
    dag = _load("proof_dependency_dag.json")
    meta = dag.get("meta", {})
    rank = dag.get("rank", {})

    fig, axes = plt.subplots(2, 2, figsize=(16, 12))
    fig.patch.set_facecolor("#0d1117")
    fig.suptitle(
        f"Proof Dependency DAG — {meta.get('nodeCount', 0)} nodes, {meta.get('edgeCount', 0)} edges",
        color="white", fontsize=16, fontweight="bold"
    )

    # Top out-degree hubs
    ax = axes[0, 0]
    ax.set_facecolor("#161b22")
    top_out = rank.get("topOutDegree", [])[:15]
    names = [t["name"][:30] for t in top_out]
    vals = [t["out"] for t in top_out]
    ax.barh(range(len(names)), vals, color="#58a6ff", alpha=0.8)
    ax.set_yticks(range(len(names)))
    ax.set_yticklabels(names, color="white", fontsize=7)
    ax.set_title("Top 15 Out-Degree Hubs (most dependencies)", color="white", fontsize=11)
    ax.tick_params(colors="white")
    ax.invert_yaxis()
    for spine in ax.spines.values():
        spine.set_color("#30363d")

    # Top in-degree (most depended upon)
    ax = axes[0, 1]
    ax.set_facecolor("#161b22")
    top_in = rank.get("topInDegree", [])[:15]
    names = [t["name"][:30] for t in top_in]
    vals = [t["in"] for t in top_in]
    ax.barh(range(len(names)), vals, color="#2ea043", alpha=0.8)
    ax.set_yticks(range(len(names)))
    ax.set_yticklabels(names, color="white", fontsize=7)
    ax.set_title("Top 15 In-Degree (most depended upon)", color="white", fontsize=11)
    ax.tick_params(colors="white")
    ax.invert_yaxis()
    for spine in ax.spines.values():
        spine.set_color("#30363d")

    # Files by declaration count
    ax = axes[1, 0]
    ax.set_facecolor("#161b22")
    top_files = rank.get("topFilesByDecl", [])[:15]
    fnames = [t["file"].split("/")[-1][:25] for t in top_files]
    fcounts = [t["declCount"] for t in top_files]
    ax.barh(range(len(fnames)), fcounts, color="#a371f7", alpha=0.8)
    ax.set_yticks(range(len(fnames)))
    ax.set_yticklabels(fnames, color="white", fontsize=7)
    ax.set_title("Top 15 Files by Declaration Count", color="white", fontsize=11)
    ax.tick_params(colors="white")
    ax.invert_yaxis()
    for spine in ax.spines.values():
        spine.set_color("#30363d")

    # Component structure summary
    ax = axes[1, 1]
    ax.set_facecolor("#161b22")
    ax.axis("off")
    weak = rank.get("weakComponents", {})
    scc = rank.get("stronglyConnectedCycles", {})
    isolated_count = rank.get("isolatedCount", 0)

    summary = (
        f"GRAPH STRUCTURE\n"
        f"{'─'*35}\n"
        f"Nodes:              {meta.get('nodeCount', 0)}\n"
        f"Edges:              {meta.get('edgeCount', 0)}\n"
        f"Roots (no deps):    {rank.get('rootCount', 0)}\n"
        f"Leaves (no users):  {rank.get('leafCount', 0)}\n"
        f"Isolated:           {isolated_count}\n"
        f"Weak Components:    {weak.get('count', 0)}\n"
        f"SCC Cycles:         {scc.get('count', 0)}\n"
        f"{'─'*35}\n"
        f"Largest component:  {weak.get('largest', [{}])[0].get('size', 0) if weak.get('largest') else 0} nodes\n"
    )
    ax.text(0.5, 0.5, summary, ha="center", va="center",
            color="#c9d1d9", fontsize=11, fontfamily="monospace",
            bbox=dict(boxstyle="round,pad=0.5", facecolor="#0d1117", edgecolor="#30363d"))

    fig.tight_layout()
    fig.savefig(CHARTS / "03_proof_dag_overview.png", dpi=180, facecolor="#0d1117")
    plt.close(fig)
    print("Wrote 03_proof_dag_overview.png")


def fig4_gap_dashboard() -> None:
    """Disconnection/gap summary dashboard."""
    conn = _load("isomorphism_connection_audit.json")
    gap = _load("isomorphism_gap_report.json")
    matrix = _load("isomorphism_implementation_matrix.json")

    fig, axes = plt.subplots(2, 2, figsize=(16, 12))
    fig.patch.set_facecolor("#0d1117")
    fig.suptitle("Gap & Disconnection Dashboard", color="white", fontsize=16, fontweight="bold")

    # Connection status donut
    ax = axes[0, 0]
    ax.set_facecolor("#0d1117")
    summary = conn.get("summary", {})
    connected = summary.get("connected_count", 0)
    disconnected = summary.get("disconnected_count", 0)
    weak = summary.get("weak_link_count", 0)
    sizes = [connected, disconnected, weak]
    labels = [f"Connected ({connected})", f"Disconnected ({disconnected})", f"Weak ({weak})"]
    colors = ["#2ea043", "#da3633", "#d29922"]
    if sum(sizes) > 0:
        wedges, texts, autotexts = ax.pie(
            sizes, labels=labels, colors=colors, autopct="%1.0f%%",
            textprops={"color": "white", "fontsize": 10},
            pctdistance=0.75, wedgeprops=dict(width=0.4)
        )
        for at in autotexts:
            at.set_color("white")
    ax.set_title(f"Connection Status (confidence: {summary.get('confidence', '?')})",
                 color="white", fontsize=12)

    # Alignment matrix heatmap
    ax = axes[0, 1]
    ax.set_facecolor("#161b22")
    elements_data = matrix.get("elements", [])
    layers_list = matrix.get("layers", [])
    if elements_data and layers_list:
        data = []
        ylabels = []
        for elem in elements_data:
            per = elem.get("per_layer", {})
            row = [1.0 if per.get(l, False) else 0.0 for l in layers_list]
            data.append(row)
            ylabels.append(elem.get("label", "?")[:35])
        arr = np.array(data)
        im = ax.imshow(arr, cmap="RdYlGn", aspect="auto", vmin=0, vmax=1)
        ax.set_xticks(range(len(layers_list)))
        ax.set_xticklabels([l.upper() for l in layers_list], color="white", fontsize=9)
        ax.set_yticks(range(len(ylabels)))
        ax.set_yticklabels(ylabels, color="white", fontsize=8)
        for i in range(arr.shape[0]):
            for j in range(arr.shape[1]):
                val = arr[i, j]
                symbol = "✓" if val > 0.5 else "✗"
                color = "white" if val > 0.5 else "#da3633"
                ax.text(j, i, symbol, ha="center", va="center", color=color, fontsize=14, fontweight="bold")
    ax.set_title("Cross-Layer Alignment Matrix", color="white", fontsize=12)
    for spine in ax.spines.values():
        spine.set_color("#30363d")

    # Gap items list
    ax = axes[1, 0]
    ax.set_facecolor("#161b22")
    ax.axis("off")
    gaps = gap.get("gaps", [])
    gap_text = "FORMAL GAPS\n" + "─" * 50 + "\n"
    if gaps:
        for g in gaps:
            element = g.get("element", "?")
            missing = ", ".join(g.get("missing_layers", []))
            gap_text += f"  ✗ {element}\n    missing: [{missing}]\n"
    else:
        gap_text += "  None — all surfaces aligned.\n"
    ax.text(0.05, 0.95, gap_text, ha="left", va="top",
            color="#f85149", fontsize=10, fontfamily="monospace", transform=ax.transAxes)

    # Weak links and action items
    ax = axes[1, 1]
    ax.set_facecolor("#161b22")
    ax.axis("off")
    weak_links = conn.get("weak_links", [])
    wl_text = "WEAK LINKS & ACTIONS\n" + "─" * 50 + "\n"
    for wl in weak_links:
        kind = wl.get("kind", "?")
        count = wl.get("count", 0)
        action = wl.get("action", "?")
        wl_text += f"  ⚠ {kind}: count={count} [{action}]\n"
    wl_text += "\n" + "─" * 50 + "\n"
    wl_text += "REMAINING WORK\n"
    wl_text += "  1. Discharge FullWireSpec in Coq\n"
    wl_text += "  2. Expand declared matrix (17→556 files)\n"
    wl_text += "  3. Reintegrate 477 unmapped semantic files\n"
    wl_text += "  4. Review 619 isolated proof declarations\n"
    wl_text += "  5. Archive/delete 32 stale candidates\n"
    ax.text(0.05, 0.95, wl_text, ha="left", va="top",
            color="#d29922", fontsize=10, fontfamily="monospace", transform=ax.transAxes)

    fig.tight_layout()
    fig.savefig(CHARTS / "04_gap_dashboard.png", dpi=180, facecolor="#0d1117")
    plt.close(fig)
    print("Wrote 04_gap_dashboard.png")


def fig5_test_coverage_radar() -> None:
    """Radar chart of test coverage dimensions."""
    conn = _load("isomorphism_connection_audit.json")
    matrix = _load("isomorphism_implementation_matrix.json")

    # Dimensions
    categories = [
        "State Shape", "Opcode Align", "μ Accounting",
        "μ-Tensor/Bianchi", "Partition Sem.", "Receipt Integrity",
        "Cross-Layer Bisim", "FullWireSpec"
    ]
    N = len(categories)

    # Values: 1 if fully aligned, 0.5 if partially, 0 if missing
    elements = matrix.get("elements", [])
    values = []
    for elem in elements:
        values.append(1.0 if elem.get("aligned_surface", False) else 0.0)
    # FullWireSpec
    values.append(0.0)  # Known gap

    angles = [n / float(N) * 2 * math.pi for n in range(N)]
    values_plot = values + values[:1]
    angles_plot = angles + angles[:1]

    fig, ax = plt.subplots(figsize=(10, 10), subplot_kw=dict(polar=True))
    fig.patch.set_facecolor("#0d1117")
    ax.set_facecolor("#0d1117")

    ax.plot(angles_plot, values_plot, "o-", linewidth=2, color="#58a6ff", label="Current Status")
    ax.fill(angles_plot, values_plot, alpha=0.2, color="#58a6ff")

    # Ideal (all 1.0)
    ideal = [1.0] * (N + 1)
    ax.plot(angles_plot, ideal, "--", linewidth=1, color="#2ea043", alpha=0.5, label="Target")
    ax.fill(angles_plot, ideal, alpha=0.05, color="#2ea043")

    ax.set_xticks(angles)
    ax.set_xticklabels(categories, color="white", fontsize=10)
    ax.set_ylim(0, 1.1)
    ax.set_yticks([0.25, 0.5, 0.75, 1.0])
    ax.set_yticklabels(["25%", "50%", "75%", "100%"], color="#8b949e", fontsize=8)
    ax.spines["polar"].set_color("#30363d")
    ax.tick_params(colors="white")
    ax.grid(color="#30363d", alpha=0.5)

    ax.set_title("Isomorphism Coverage Radar\n7/8 dimensions covered, 1 gap (FullWireSpec)",
                 color="white", fontsize=14, fontweight="bold", pad=20)
    ax.legend(loc="lower right", facecolor="#161b22", edgecolor="#30363d", labelcolor="white")

    fig.tight_layout()
    fig.savefig(CHARTS / "05_test_coverage_radar.png", dpi=180, facecolor="#0d1117")
    plt.close(fig)
    print("Wrote 05_test_coverage_radar.png")


def fig6_repo_surface_treemap() -> None:
    """Stacked bar showing repo surface area breakdown by layer."""
    conn = _load("isomorphism_connection_audit.json")
    coverage = conn.get("coverage_scope", {})

    fig, ax = plt.subplots(figsize=(14, 6))
    fig.patch.set_facecolor("#0d1117")
    ax.set_facecolor("#161b22")

    layers = ["coq", "python", "rtl", "tests"]
    colors_declared = ["#2ea043", "#1f6feb", "#da3633", "#a371f7"]
    colors_unmapped = ["#2ea04366", "#1f6feb66", "#da363366", "#a371f766"]

    x = np.arange(len(layers))
    declared = [coverage.get(l, {}).get("declared", 0) for l in layers]
    unmapped = [coverage.get(l, {}).get("semantic_unmapped_count", 0) for l in layers]
    other = [coverage.get(l, {}).get("discovered", 0) - d - u for l, d, u in zip(layers, declared, unmapped)]
    other = [max(0, o) for o in other]

    ax.bar(x, declared, label="Declared (in audit)", color=colors_declared, alpha=0.9, edgecolor="white", linewidth=0.5)
    ax.bar(x, unmapped, bottom=declared, label="Semantic but unmapped", color=colors_declared, alpha=0.3, edgecolor="white", linewidth=0.5)
    ax.bar(x, other, bottom=[d + u for d, u in zip(declared, unmapped)], label="Non-semantic", color="#30363d", alpha=0.5, edgecolor="white", linewidth=0.5)

    ax.set_xticks(x)
    ax.set_xticklabels([l.upper() for l in layers], color="white", fontsize=12)
    ax.set_title("Repo Surface Area by Layer", color="white", fontsize=14, fontweight="bold")
    ax.set_ylabel("Number of files", color="white", fontsize=11)
    ax.tick_params(colors="white")
    ax.legend(facecolor="#161b22", edgecolor="#30363d", labelcolor="white", fontsize=10)
    for spine in ax.spines.values():
        spine.set_color("#30363d")

    # Annotations
    for i, (d, u) in enumerate(zip(declared, unmapped)):
        if d > 0:
            ax.text(i, d / 2, str(d), ha="center", va="center", color="white", fontweight="bold", fontsize=10)
        if u > 0:
            ax.text(i, d + u / 2, str(u), ha="center", va="center", color="white", fontsize=9)

    fig.tight_layout()
    fig.savefig(CHARTS / "06_repo_surface_treemap.png", dpi=180, facecolor="#0d1117")
    plt.close(fig)
    print("Wrote 06_repo_surface_treemap.png")


def main() -> None:
    CHARTS.mkdir(parents=True, exist_ok=True)
    fig1_layer_connectivity_map()
    fig2_coverage_heatmap()
    fig3_proof_dag_overview()
    fig4_gap_dashboard()
    fig5_test_coverage_radar()
    fig6_repo_surface_treemap()
    print("\nAll 6 dashboard images written to artifacts/charts/")


if __name__ == "__main__":
    main()
