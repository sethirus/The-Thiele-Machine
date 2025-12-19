#!/usr/bin/env python3
"""Digitize Jun et al. (arXiv:1408.5089) Fig. 4A from vector paths.

This is intentionally narrow-scope and auditable:
- Takes the arXiv PDF as input
- Locates the left-panel axes (Fig. 4A)
- Extracts the thick red curve (full erasure, p=1)
- Maps PDF coordinates -> (tau, <W>/kT) using detected tick marks
- Writes a prereg-compatible CSV row set into DATA_A/

No manual clicking; no image-based digitization.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import pdfplumber


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PDF = REPO_ROOT / "DATA_A" / "sources" / "jun_2014_arxiv_1408.5089.pdf"
DEFAULT_OUT = REPO_ROOT / "DATA_A" / "jun_2014_arxiv_1408.5089_fig4A_full_erasure_p1.csv"
DEFAULT_RECEIPT = (
    REPO_ROOT / "DATA_A" / "receipts" / "jun_2014_arxiv_1408.5089_fig4A_full_erasure_p1_receipt.json"
)
DEFAULT_OVERLAY = (
    REPO_ROOT / "DATA_A" / "overlays" / "jun_2014_arxiv_1408.5089_fig4A_full_erasure_p1_overlay.png"
)


@dataclass(frozen=True)
class AxisMap:
    # For x we assume log10 scale.
    x_tick_pos_1: float
    x_tick_pos_10: float
    x_tick_pos_100: float
    y_tick_top_3: float
    y_tick_top_0: float


@dataclass(frozen=True)
class AxisTick:
    label_value: float
    page_x: float
    page_y: float


@dataclass(frozen=True)
class AxisFit:
    scale: str  # "linear" or "log10"
    a: float
    b: float
    max_residual_page: float


def _fit_axis(*, page_coords: Sequence[float], label_values: Sequence[float], scale: str) -> AxisFit:
    if len(page_coords) != len(label_values) or len(page_coords) < 3:
        raise RuntimeError("Need >=3 ticks to fit axis")
    vals = list(label_values)
    if scale == "log10":
        vals = [math.log10(v) for v in vals]
    xs = list(page_coords)
    n = float(len(xs))
    mv = sum(vals) / n
    mx = sum(xs) / n
    num = sum((v - mv) * (x - mx) for v, x in zip(vals, xs))
    den = sum((v - mv) * (v - mv) for v in vals) or 1.0
    a = num / den
    b = mx - a * mv
    resid = [abs((a * v + b) - x) for v, x in zip(vals, xs)]
    return AxisFit(scale=scale, a=float(a), b=float(b), max_residual_page=float(max(resid)))


def _render_overlay(*, pdf_path: Path, page_number_1based: int, zoom: float, out_path: Path, pts: Sequence[tuple[float, float]]) -> str:
    import fitz
    from PIL import Image, ImageDraw

    doc = fitz.open(pdf_path.as_posix())
    page = doc.load_page(page_number_1based - 1)
    pix = page.get_pixmap(matrix=fitz.Matrix(zoom, zoom), alpha=False)  # type: ignore[attr-defined]
    img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
    draw = ImageDraw.Draw(img)

    for x, y in pts:
        draw.point([x * zoom, y * zoom], fill=(0, 120, 255))

    out_path.parent.mkdir(parents=True, exist_ok=True)
    img.save(out_path.as_posix())
    return _sha256_file(out_path)


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _approx_eq(a: float, b: float, *, tol: float) -> bool:
    return abs(a - b) <= tol


def _find_left_panel_bottom_axis_line(page) -> dict:
    """Pick the bottom axis line for panel (a) (leftmost plot).

    The Jun 2014 PDF places multiple panels on the same page, and more than
    one panel can still fall within the left half of the page. To
    deterministically select Fig. 4A panel (a), we choose a long gray
    horizontal axis line with the smallest x0 (leftmost).
    """

    gray = (0.467, 0.467, 0.467)
    candidates: list[tuple[float, float, dict]] = []
    for l in page.lines or []:
        if l.get("stroking_color") != gray:
            continue
        if l.get("linewidth") != 1.03:
            continue
        # horizontal-ish
        if not _approx_eq(l["y0"], l["y1"], tol=1e-3):
            continue
        length = abs(l["x1"] - l["x0"])
        x_min = float(min(l["x0"], l["x1"]))
        candidates.append((length, x_min, l))

    if not candidates:
        raise RuntimeError("Could not find left-panel bottom axis line")
    # Prefer long lines, then the leftmost among them.
    candidates.sort(key=lambda t: (-t[0], t[1]))
    # Require a reasonably long axis line to avoid picking tiny segments.
    for length, _x_min, line in candidates:
        if length >= 60.0:
            return line
    raise RuntimeError(f"Found axis line candidates, but none were long enough: {[c[0] for c in candidates[:10]]}")


def _find_left_panel_y_ticks(page, *, x_axis_left: float, y_axis_bottom: float) -> tuple[float, float]:
    """Detect y tick marks and return top-coordinates for y=3 and y=0."""

    gray = (0.467, 0.467, 0.467)
    ticks = []
    for l in page.lines or []:
        if l.get("stroking_color") != gray:
            continue
        if l.get("linewidth") != 1.03:
            continue
        # small horizontal ticks just left of y-axis
        if not _approx_eq(l["y0"], l["y1"], tol=1e-3):
            continue
        length = abs(l["x1"] - l["x0"])
        if not (3.0 <= length <= 4.2):
            continue
        if max(l["x0"], l["x1"]) > x_axis_left + 1.0:
            continue
        if min(l["x0"], l["x1"]) < x_axis_left - 6.0:
            continue

        # page.top coords are available as l['top']
        top = float(l.get("top"))
        # constrain near plot vertical span
        if not (top <= y_axis_bottom + 5.0):
            continue
        ticks.append(top)

    ticks = sorted(set(round(t, 3) for t in ticks))
    if len(ticks) < 4:
        raise RuntimeError(f"Expected >=4 y-ticks, found {len(ticks)}: {ticks}")

    # The four major ticks in this plot are {3,2,1,0} top->bottom.
    major = ticks[:4]
    # Ensure increasing top coords.
    major.sort()
    y3 = major[0]
    y0 = major[-1]
    return y3, y0


def _find_left_panel_x_ticks(page, *, x_axis_left: float, x_axis_right: float, y_axis_bottom: float) -> tuple[float, float, float]:
    """Detect x tick marks and return x positions for ticks (1,10,100)."""

    gray = (0.467, 0.467, 0.467)
    xs = []
    for l in page.lines or []:
        if l.get("stroking_color") != gray:
            continue
        if l.get("linewidth") != 1.03:
            continue
        # vertical ticks just below bottom axis
        if not _approx_eq(l["x0"], l["x1"], tol=1e-3):
            continue
        length = abs(l["y1"] - l["y0"])
        if not (3.0 <= length <= 4.2):
            continue

        x = float(l["x0"])
        if not (x_axis_left - 1.0 <= x <= x_axis_right + 1.0):
            continue

        # Ensure we stay in the left panel (avoid the right panel's ticks).
        if x > page.width * 0.5:
            continue

        # tick top should be near y_axis_bottom
        top = float(l.get("top"))
        if not (y_axis_bottom - 6.0 <= top <= y_axis_bottom + 2.0):
            continue

        xs.append(x)

    xs = sorted(set(round(x, 3) for x in xs))
    # In this plot the 3 major ticks are at 1, 10, 100.
    if len(xs) < 3:
        raise RuntimeError(f"Expected >=3 x-ticks, found {len(xs)}: {xs}")

    x1 = xs[0]
    x100 = xs[-1]
    x10_pred = x1 + (x100 - x1) * 0.5

    # Choose the tick closest to the predicted log-midpoint, excluding endpoints.
    interior = [x for x in xs[1:-1]] or xs
    x10 = min(interior, key=lambda x: abs(x - x10_pred))
    if abs(x10 - x10_pred) > 2.0:
        raise RuntimeError(
            f"x tick sanity failed: x1={x1}, x10={x10} (pred {x10_pred}), x100={x100}; xs={xs}"
        )
    return x1, x10, x100


def _digitize_curve_points(*, pts: Sequence[tuple[float, float]], axis: AxisMap) -> list[tuple[float, float]]:
    """Map (x,y) in PDF top-coordinates to (tau, work_over_kT)."""

    def x_to_tau(x: float) -> float:
        # log10 tau in [0,2] for [1,100]
        t = (x - axis.x_tick_pos_1) / (axis.x_tick_pos_100 - axis.x_tick_pos_1)
        log_tau = 0.0 + t * 2.0
        return 10.0 ** log_tau

    def y_to_work(y: float) -> float:
        # y increases downward in top-coordinates
        t = (y - axis.y_tick_top_3) / (axis.y_tick_top_0 - axis.y_tick_top_3)
        return 3.0 + t * (0.0 - 3.0)

    mapped = []
    for x, y in pts:
        tau = x_to_tau(float(x))
        work = y_to_work(float(y))
        if tau <= 0 or not math.isfinite(work):
            continue
        mapped.append((tau, work))

    # Sort by tau and drop near-duplicates.
    mapped.sort(key=lambda t: t[0])
    dedup: list[tuple[float, float]] = []
    for tau, work in mapped:
        if dedup and abs(tau - dedup[-1][0]) / max(tau, dedup[-1][0]) < 1e-4:
            continue
        dedup.append((tau, work))
    return dedup


def _write_csv(out_path: Path, rows: Iterable[dict[str, str]]) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", newline="") as f:
        w = csv.DictWriter(
            f,
            fieldnames=[
                "paper_id",
                "figure_id",
                "dataset_id",
                "value_kind",
                "tau_unit",
                "tau_s",
                "work_over_kT",
                "work_err_over_kT",
                "info_bits_removed",
                # Standardized digitization columns
                "curve_id",
                "tau_value",
                "digitize_sigma_work",
                "digitize_sigma_logtau",
            ],
            extrasaction="ignore",
        )
        w.writeheader()
        for r in rows:
            w.writerow(r)


def cmd_digitize(args: argparse.Namespace) -> int:
    pdf_path: Path = args.pdf
    if not pdf_path.exists():
        raise FileNotFoundError(str(pdf_path))

    out_csv: Path = args.out_csv
    receipt_path: Path = args.receipt
    overlay_path: Path = args.overlay

    pdf_sha256 = _sha256_file(pdf_path)

    with pdfplumber.open(pdf_path) as pdf:
        page = pdf.pages[args.page - 1]

        bottom_axis = _find_left_panel_bottom_axis_line(page)
        x_left = float(min(bottom_axis["x0"], bottom_axis["x1"]))
        x_right = float(max(bottom_axis["x0"], bottom_axis["x1"]))
        y_bottom_topcoord = float(bottom_axis["top"])

        x1, x10, x100 = _find_left_panel_x_ticks(
            page, x_axis_left=x_left, x_axis_right=x_right, y_axis_bottom=y_bottom_topcoord
        )
        y3, y0 = _find_left_panel_y_ticks(page, x_axis_left=x_left, y_axis_bottom=y_bottom_topcoord)

        axis = AxisMap(
            x_tick_pos_1=x1,
            x_tick_pos_10=x10,
            x_tick_pos_100=x100,
            y_tick_top_3=y3,
            y_tick_top_0=y0,
        )

        # Extract the thick BLUE curve (full erasure p=1) in Fig 4A.
        # (The red curve corresponds to the no-erasure protocol with ΔF≈0.)
        target_color = (0.0, 0.244, 1.0)
        target_lw = 1.03
        candidates = [
            c
            for c in (page.curves or [])
            if c.get("stroking_color") == target_color
            and c.get("linewidth") == target_lw
            and c.get("pts")
        ]
        if not candidates:
            raise RuntimeError("Could not find thick red curve on the specified page")
        curve = max(candidates, key=lambda c: len(c.get("pts") or []))
        pts = list(curve["pts"])

        mapped = _digitize_curve_points(pts=pts, axis=axis)
        if len(mapped) < 20:
            raise RuntimeError(f"Too few digitized points ({len(mapped)}); mapping likely failed")

        paper_id = "JunGavrilovBechhoefer2014_arXiv1408.5089"
        figure_id = "Fig4A"
        dataset_id = "full_erasure_p1_blue"
        curve_id = "Fig4A_full_erasure_p1_blue"

        # Fit axis calibrations with redundancy and report residuals.
        x_ticks = [AxisTick(label_value=v, page_x=px, page_y=y_bottom_topcoord) for v, px in [(1.0, x1), (10.0, x10), (100.0, x100)]]
        # y ticks are {3,2,1,0} top->bottom; we use four positions for redundancy.
        # The existing helper returns (y3,y0). We reconstruct the intermediate ticks by scanning all ticks again.
        # For auditability, we re-scan all y ticks and take the first four unique ones.
        gray = (0.467, 0.467, 0.467)
        yticks = []
        for l in page.lines or []:
            if l.get("stroking_color") != gray:
                continue
            if l.get("linewidth") != 1.03:
                continue
            if abs(l["y0"] - l["y1"]) > 1e-3:
                continue
            length = abs(l["x1"] - l["x0"])
            if not (3.0 <= length <= 4.2):
                continue
            if max(l["x0"], l["x1"]) > x_left + 1.0:
                continue
            if min(l["x0"], l["x1"]) < x_left - 6.0:
                continue
            yticks.append(float(l.get("top")))
        yticks = sorted(set(round(t, 3) for t in yticks))
        if len(yticks) < 4:
            raise RuntimeError("Could not recover 4 y ticks for audit fit")
        y_major = sorted(yticks[:4])
        y_tick_labels = [3.0, 2.0, 1.0, 0.0]
        y_ticks = [AxisTick(label_value=lab, page_x=x_left, page_y=py) for lab, py in zip(y_tick_labels, y_major)]

        x_fit = _fit_axis(page_coords=[t.page_x for t in x_ticks], label_values=[t.label_value for t in x_ticks], scale="log10")
        y_fit = _fit_axis(page_coords=[t.page_y for t in y_ticks], label_values=[t.label_value for t in y_ticks], scale="linear")

        sigma_logtau = float(x_fit.max_residual_page / (abs(x_fit.a) or 1.0))
        sigma_work = float(y_fit.max_residual_page / (abs(y_fit.a) or 1.0))

        rows = []
        for tau, work in mapped:
            rows.append(
                {
                    "paper_id": paper_id,
                    "figure_id": figure_id,
                    "dataset_id": dataset_id,
                    "curve_id": curve_id,
                    "value_kind": "work_over_kT",
                    "tau_unit": "s",
                    "tau_s": f"{tau:.10g}",
                    "tau_value": f"{tau:.10g}",
                    "work_over_kT": f"{work:.10g}",
                    "work_err_over_kT": "",
                    "digitize_sigma_work": f"{sigma_work:.6g}",
                    "digitize_sigma_logtau": f"{sigma_logtau:.6g}",
                    "info_bits_removed": "1.0",
                }
            )

    _write_csv(out_csv, rows)

    overlay_sha256 = _render_overlay(
        pdf_path=pdf_path,
        page_number_1based=int(args.page),
        zoom=float(args.overlay_zoom),
        out_path=overlay_path,
        pts=list(pts),
    )

    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    receipt = {
        "pdf_path": str(pdf_path),
        "pdf_sha256": pdf_sha256,
        "page": int(args.page),
        "paper_id": paper_id,
        "figure_id": figure_id,
        "dataset_id": dataset_id,
        "curve_filter": {
            "stroking_color": list(target_color),
            "linewidth": float(target_lw),
        },
        "axis_ticks": {
            "x": [
                {"label": t.label_value, "page_x": float(t.page_x), "page_y": float(t.page_y)}
                for t in x_ticks
            ],
            "y": [
                {"label": t.label_value, "page_x": float(t.page_x), "page_y": float(t.page_y)}
                for t in y_ticks
            ],
        },
        "axis_fit": {
            "x": {"scale": x_fit.scale, "a": x_fit.a, "b": x_fit.b, "max_residual_page": x_fit.max_residual_page},
            "y": {"scale": y_fit.scale, "a": y_fit.a, "b": y_fit.b, "max_residual_page": y_fit.max_residual_page},
        },
        "overlay": {
            "path": str(overlay_path),
            "sha256": overlay_sha256,
            "zoom": float(args.overlay_zoom),
        },
        "notes": [
            "Digitized from vector paths (no raster/manual clicking).",
            "Work is reported in units of kT per FIG. 4 caption.",
            "Tau is recorded as seconds (tau_unit='s') so PREREG_A's tau-hat-only finite-time tightening term does not apply to this dataset.",
        ],
    }
    receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(f"Wrote {out_csv} ({len(rows)} points)")
    print(f"Wrote {receipt_path}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Digitize Jun et al. Fig 4A -> PREREG_A CSV")
    p.add_argument("--pdf", type=Path, default=DEFAULT_PDF)
    p.add_argument("--page", type=int, default=4)
    p.add_argument("--out-csv", type=Path, default=DEFAULT_OUT)
    p.add_argument("--receipt", type=Path, default=DEFAULT_RECEIPT)
    p.add_argument("--overlay", type=Path, default=DEFAULT_OVERLAY)
    p.add_argument("--overlay-zoom", type=float, default=2.0)
    p.set_defaults(func=cmd_digitize)
    return p


def main() -> int:
    args = build_parser().parse_args()
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
