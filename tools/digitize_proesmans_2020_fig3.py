#!/usr/bin/env python3
"""Digitize Proesmans et al. (arXiv:2006.03242) Fig. 3 from vector paths.

This script treats vector-digitization like an instrument:
- Axis calibration uses >=3 ticks per axis, fit with redundancy
- Receipt records tick labels + page coordinates + fit params + fit residuals
- Saves an overlay PNG: rendered page with extracted points drawn on top

Target:
- Fig. 3: "Minimum entropy production in excess of Landauer bound" with
  multiple red curves (Eb in {0,2,4,6,8}).
- We digitize two curves (Eb=0 and Eb=8), which are drawn as heavier lines.

Interpretation:
- The plotted quantity is the *excess* work/entropy production above Landauer.
  To produce prereg-compatible `work_over_kT`, we add ln(2) so that
  W/kT = ln2 + excess.

No manual clicking; no raster-based digitization.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Sequence

import pdfplumber


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PDF = REPO_ROOT / "DATA_A" / "sources" / "proesmans_2020_arxiv_2006.03242.pdf"
DEFAULT_OUT = REPO_ROOT / "DATA_A" / "proesmans_2020_arxiv_2006.03242_fig3_Eb0_Eb8.csv"
DEFAULT_RECEIPT = (
    REPO_ROOT
    / "DATA_A"
    / "receipts"
    / "proesmans_2020_arxiv_2006.03242_fig3_Eb0_Eb8_receipt.json"
)
DEFAULT_OVERLAY = (
    REPO_ROOT
    / "DATA_A"
    / "overlays"
    / "proesmans_2020_arxiv_2006.03242_fig3_Eb0_Eb8_overlay.png"
)


_NUM_RE = re.compile(r"^[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?$")
_NUM_FIND_RE = re.compile(r"[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?")


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _write_csv(out_path: Path, rows: Iterable[dict[str, str]]) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(
            f,
            fieldnames=[
                # Legacy prereg columns (kept for backward compatibility)
                "paper_id",
                "figure_id",
                "dataset_id",
                "value_kind",
                "tau_unit",
                "tau_s",
                "work_over_kT",
                "work_err_over_kT",
                "info_bits_removed",
                # Standardized digitization columns (preferred)
                "curve_id",
                "tau_value",
                "tau_hat_raw",
                "digitize_sigma_work",
                "digitize_sigma_logtau",
            ],
            extrasaction="ignore",
        )
        w.writeheader()
        for r in rows:
            w.writerow(r)


@dataclass(frozen=True)
class AxisTick:
    label_text: str
    label_value: float
    page_x: float
    page_y: float
    raw_text: str
    method: str  # "text" or "ocr"


@dataclass(frozen=True)
class AxisFit:
    scale: str  # "linear" or "log10"
    a: float
    b: float
    max_residual_page: float


def _fit_axis(*, ticks: Sequence[AxisTick], axis: str, scale: str) -> AxisFit:
    if len(ticks) < 3:
        raise RuntimeError(f"Need >=3 ticks to fit {axis}-axis, got {len(ticks)}")

    xs = [t.page_x if axis == "x" else t.page_y for t in ticks]
    vals = [t.label_value for t in ticks]

    if scale == "log10":
        if any(v <= 0 for v in vals):
            raise RuntimeError(f"log10 axis requires positive labels, got {vals}")
        vals = [math.log10(v) for v in vals]

    # Least squares: page = a * val + b
    n = float(len(vals))
    mv = sum(vals) / n
    mx = sum(xs) / n
    num = sum((v - mv) * (x - mx) for v, x in zip(vals, xs))
    den = sum((v - mv) * (v - mv) for v in vals) or 1.0
    a = num / den
    b = mx - a * mv

    # Residual in page coordinates.
    resid = [abs((a * v + b) - x) for v, x in zip(vals, xs)]
    return AxisFit(scale=scale, a=float(a), b=float(b), max_residual_page=float(max(resid) if resid else 0.0))


def _axis_value_from_page(*, fit: AxisFit, page_coord: float) -> float:
    v = (page_coord - fit.b) / (fit.a or 1.0)
    if fit.scale == "log10":
        return 10.0 ** v
    return v


def _axis_sigma_from_fit(*, fit: AxisFit) -> float:
    """Return an axis sigma in *log10 units* if log10 scale, else in linear units."""
    if fit.scale == "log10":
        return float(fit.max_residual_page / (abs(fit.a) or 1.0))
    return float(fit.max_residual_page / (abs(fit.a) or 1.0))


def _extract_text_in_bbox(page, *, bbox: tuple[float, float, float, float]) -> str:
    """Extract raw text from chars inside bbox=(x0, top, x1, bottom)."""
    x0, top, x1, bottom = bbox
    chars = [c for c in (page.chars or []) if x0 <= c["x0"] <= x1 and top <= c["top"] <= bottom]
    if not chars:
        return ""
    # Sort left-to-right; keep '.' and '-'.
    chars.sort(key=lambda c: (round(float(c["top"]), 1), float(c["x0"])))
    return "".join(c["text"] for c in chars).strip()


def _ocr_text_in_bbox(*, pdf_path: Path, page_number_1based: int, bbox: tuple[float, float, float, float]) -> str:
    """OCR-render a PDF region and return raw text.

    Used only as a fallback when tick labels are encoded as vector glyphs
    (common for TeX math text).
    """

    import fitz
    import pytesseract
    from PIL import Image

    doc = fitz.open(pdf_path.as_posix())
    page = doc.load_page(page_number_1based - 1)

    x0, top, x1, bottom = bbox
    clip = fitz.Rect(x0, top, x1, bottom)
    zoom = 6.0
    pix = page.get_pixmap(matrix=fitz.Matrix(zoom, zoom), clip=clip, alpha=False)  # type: ignore[attr-defined]
    img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)

    # Make OCR more stable.
    img = img.convert("L")

    # psm 6 works better for small tick labels than psm 7.
    cfg = "--psm 6 -c tessedit_char_whitelist=0123456789.-eE+"
    try:
        out = pytesseract.image_to_string(img, config=cfg)
    except Exception:
        out = ""
    return (out or "").strip().replace("\n", " ")


def _parse_label(text: str) -> float | None:
    t = (text or "").strip()
    if not t:
        return None
    t = t.replace(" ", "")
    # Some PDFs separate the decimal point; try to recover common cases.
    if _NUM_RE.match(t):
        try:
            return float(t)
        except ValueError:
            return None

    candidates: list[float] = []
    for m in _NUM_FIND_RE.findall(t):
        try:
            candidates.append(float(m))
        except ValueError:
            continue
    positives = [c for c in candidates if c > 0 and math.isfinite(c)]
    if positives:
        return min(positives)
    if candidates:
        # Fall back to the first finite candidate.
        for c in candidates:
            if math.isfinite(c):
                return c

    # Heuristic: "01" -> "0.1", "021" -> "0.21".
    if t.isdigit() and len(t) >= 2 and t.startswith("0"):
        t2 = "0." + t[1:]
        if _NUM_RE.match(t2):
            return float(t2)

    return None


def _fit_axis_best(*, ticks: Sequence[AxisTick], axis: str) -> AxisFit:
    """Fit axis using both linear and log10 (when possible), choose lower residual."""

    best = _fit_axis(ticks=ticks, axis=axis, scale="linear")
    if all(t.label_value > 0 for t in ticks):
        log_fit = _fit_axis(ticks=ticks, axis=axis, scale="log10")
        if log_fit.max_residual_page < best.max_residual_page:
            best = log_fit
    return best


def _curve_bbox(pts: Sequence[tuple[float, float]]) -> tuple[float, float, float, float]:
    xs = [p[0] for p in pts]
    ys = [p[1] for p in pts]
    return (min(xs), min(ys), max(xs), max(ys))


def _bbox_area(b: tuple[float, float, float, float]) -> float:
    x0, y0, x1, y1 = b
    return max(0.0, x1 - x0) * max(0.0, y1 - y0)


def _bbox_intersects(a: tuple[float, float, float, float], b: tuple[float, float, float, float]) -> bool:
    ax0, ay0, ax1, ay1 = a
    bx0, by0, bx1, by1 = b
    return (ax0 <= bx1) and (bx0 <= ax1) and (ay0 <= by1) and (by0 <= ay1)


def _digitize_curve_points(
    *,
    pts: Sequence[tuple[float, float]],
    plot_bbox: tuple[float, float, float, float],
    x_fit: AxisFit,
    y_fit: AxisFit,
) -> list[tuple[float, float, float, float]]:
    """Return points: (tau, work_over_kT, page_x, page_y) sorted by tau."""

    x0, y0, x1, y1 = plot_bbox

    mapped: list[tuple[float, float, float, float]] = []
    for px, py in pts:
        if not (x0 - 2 <= px <= x1 + 2 and y0 - 2 <= py <= y1 + 2):
            continue
        tau = _axis_value_from_page(fit=x_fit, page_coord=float(px))
        excess = _axis_value_from_page(fit=y_fit, page_coord=float(py))
        if not (math.isfinite(tau) and math.isfinite(excess)):
            continue
        if tau <= 0:
            continue
        work = math.log(2.0) + float(excess)
        mapped.append((float(tau), float(work), float(px), float(py)))

    mapped.sort(key=lambda t: t[0])
    # Dedup by tau.
    out: list[tuple[float, float, float, float]] = []
    for tau, work, px, py in mapped:
        if out and abs(tau - out[-1][0]) / max(tau, out[-1][0]) < 1e-4:
            continue
        out.append((tau, work, px, py))
    return out


def _render_overlay(
    *,
    pdf_path: Path,
    page_number_1based: int,
    zoom: float,
    overlay_path: Path,
    series: dict[str, list[tuple[float, float, float, float]]],
    ticks_x: Sequence[AxisTick],
    ticks_y: Sequence[AxisTick],
) -> str:
    import fitz
    from PIL import Image, ImageDraw

    doc = fitz.open(pdf_path.as_posix())
    page = doc.load_page(page_number_1based - 1)
    pix = page.get_pixmap(matrix=fitz.Matrix(zoom, zoom), alpha=False)  # type: ignore[attr-defined]

    img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
    draw = ImageDraw.Draw(img)

    # Draw ticks.
    for t in ticks_x:
        x = t.page_x * zoom
        y = t.page_y * zoom
        draw.ellipse([x - 4, y - 4, x + 4, y + 4], outline=(0, 200, 0), width=2)
    for t in ticks_y:
        x = t.page_x * zoom
        y = t.page_y * zoom
        draw.ellipse([x - 4, y - 4, x + 4, y + 4], outline=(0, 200, 0), width=2)

    palette = {
        "Eb0": (255, 0, 0),
        "Eb8": (0, 120, 255),
    }

    for name, pts in series.items():
        color = palette.get(name, (255, 128, 0))
        for _tau, _work, px, py in pts:
            x = px * zoom
            y = py * zoom
            draw.point([x, y], fill=color)

    overlay_path.parent.mkdir(parents=True, exist_ok=True)
    img.save(overlay_path.as_posix())
    return _sha256_file(overlay_path)


def cmd_digitize(args: argparse.Namespace) -> int:
    pdf_path: Path = args.pdf
    if not pdf_path.exists():
        raise FileNotFoundError(str(pdf_path))

    pdf_sha256 = _sha256_file(pdf_path)

    out_csv: Path = args.out_csv
    receipt_path: Path = args.receipt
    overlay_path: Path = args.overlay

    paper_id = "ProesmansEhrichBechhoefer2020_arXiv2006.03242"
    figure_id = "Fig3"
    dataset_id = "Fig3_main_plot"

    # IMPORTANT: The paper plots reduced time \hat{\tau}. Our PREREG_A model
    # interprets tau_unit="D_tau_over_Var" as D·tau/Var(x). Under the common
    # convention \hat{\tau} = D·tau/(2x0)^2 and Var(x)=x0^2, we have:
    #   D·tau/Var(x) = 4 * \hat{\tau}
    # We therefore store tau_hat_raw (from axis labels) and write tau_s/tau_value
    # as 4 * tau_hat_raw in the D_tau_over_Var convention.
    TAU_HAT_TO_D_TAU_OVER_VAR = 4.0

    page_no = int(args.page)

    with pdfplumber.open(pdf_path) as pdf:
        page = pdf.pages[page_no - 1]

        # Select red-ish curves (Fig.3 caption: red curves for different Eb).
        redish: list[dict[str, Any]] = []
        for c in (page.curves or []):
            col = c.get("stroking_color")
            if not (isinstance(col, tuple) and len(col) == 3):
                continue
            r, g, b = col
            if r == 1 and g in {0, 0.5} and b in {0, 0.5} and c.get("pts"):
                redish.append(c)

        if not redish:
            raise RuntimeError("No red-ish curves found; PDF structure changed?")

        # Determine the main plot bbox by taking the largest curve bbox.
        bboxes = []
        for c in redish:
            pts = list(c.get("pts") or [])
            bb = _curve_bbox(pts)
            bboxes.append((_bbox_area(bb), bb, c))
        bboxes.sort(key=lambda t: t[0], reverse=True)
        plot_bbox = bboxes[0][1]

        # Add a small margin.
        x0, y0, x1, y1 = plot_bbox
        plot_bbox = (x0 - 2.0, y0 - 2.0, x1 + 2.0, y1 + 2.0)

        # Identify candidate tick marks.
        # Heuristic: short lines clustered at bottom (x ticks) and left (y ticks).
        x_ticks: list[tuple[float, float, float]] = []  # (page_x, page_y, length)
        y_ticks: list[tuple[float, float, float]] = []  # (page_x, page_y, length)

        for l in (page.lines or []):
            # IMPORTANT: pdfplumber stores y0/y1 in PDF coordinates (bottom-origin),
            # but curve point y values are in top-origin coordinates. Use top/bottom.
            x0l, x1l = float(l["x0"]), float(l["x1"])
            top = float(l.get("top"))
            bottom = float(l.get("bottom"))
            dx = abs(x1l - x0l)
            dy = abs(bottom - top)
            length = math.hypot(dx, dy)
            if length < 1.0 or length > 6.0:
                continue

            # pdfplumber uses "top" coordinates for some objects; y0/y1 are also top-based for lines.
            mx = 0.5 * (x0l + x1l)
            my = 0.5 * (top + bottom)

            if dx < 0.2:  # vertical tick
                # near bottom of plot
                if plot_bbox[0] <= mx <= plot_bbox[2] and abs(my - plot_bbox[3]) <= 12.0:
                    x_ticks.append((mx, my, float(length)))
            elif dy < 0.2:  # horizontal tick
                # near left of plot
                if plot_bbox[1] <= my <= plot_bbox[3] and abs(mx - plot_bbox[0]) <= 12.0:
                    y_ticks.append((mx, my, float(length)))

        # Dedup ticks.
        def _dedup(pts: list[tuple[float, float, float]], key_idx: int) -> list[tuple[float, float, float]]:
            pts = sorted(pts, key=lambda p: p[key_idx])
            out: list[tuple[float, float, float]] = []
            for x, y, length in pts:
                if out and abs((x if key_idx == 0 else y) - (out[-1][0] if key_idx == 0 else out[-1][1])) < 0.75:
                    # Keep the longer of the two (major tick should win).
                    ox, oy, ol = out[-1]
                    if length > ol:
                        out[-1] = (x, y, length)
                    continue
                out.append((x, y, length))
            return out

        x_ticks = _dedup(x_ticks, 0)
        y_ticks = _dedup(y_ticks, 1)

        if len(x_ticks) < 3:
            raise RuntimeError(f"Too few x tick marks detected: {len(x_ticks)}")
        if len(y_ticks) < 3:
            raise RuntimeError(f"Too few y tick marks detected: {len(y_ticks)}")

        # Major ticks are longer; we calibrate only on majors to avoid unlabeled minors.
        x_ticks_major = [t for t in x_ticks if t[2] >= 3.5]
        y_ticks_major = [t for t in y_ticks if t[2] >= 3.5]
        if len(x_ticks_major) < 3:
            raise RuntimeError(f"Too few major x ticks: {len(x_ticks_major)}")
        if len(y_ticks_major) < 3:
            raise RuntimeError(f"Too few major y ticks: {len(y_ticks_major)}")

        # Extract tick labels from nearby text. If missing/garbled (common for
        # TeX glyphs), fall back to OCR on a rendered crop.
        x_axis_ticks: list[AxisTick] = []
        for tx, ty, _length in x_ticks_major:
            # Crop just under the tick mark; keep below axis but above caption.
            bbox = (tx - 30, ty + 2, tx + 30, ty + 35)
            raw_ocr = _ocr_text_in_bbox(pdf_path=pdf_path, page_number_1based=page_no, bbox=bbox)
            val = _parse_label(raw_ocr)
            method = "ocr"
            raw = raw_ocr
            if val is None:
                raw_txt = _extract_text_in_bbox(page, bbox=bbox)
                val = _parse_label(raw_txt)
                if val is None:
                    continue
                raw = raw_txt
                method = "text"
            x_axis_ticks.append(
                AxisTick(
                    label_text=str(val),
                    label_value=float(val),
                    page_x=float(tx),
                    page_y=float(plot_bbox[3]),
                    raw_text=raw,
                    method=method,
                )
            )

        y_axis_ticks: list[AxisTick] = []
        for _tx, ty, _length in y_ticks_major:
            # Tight crop close to axis to avoid unrelated text.
            bbox = (plot_bbox[0] - 55, ty - 20, plot_bbox[0] - 2, ty + 20)
            raw_ocr = _ocr_text_in_bbox(pdf_path=pdf_path, page_number_1based=page_no, bbox=bbox)
            val = _parse_label(raw_ocr)
            method = "ocr"
            raw = raw_ocr
            if val is None:
                raw_txt = _extract_text_in_bbox(page, bbox=bbox)
                val = _parse_label(raw_txt)
                if val is None:
                    continue
                raw = raw_txt
                method = "text"
            y_axis_ticks.append(
                AxisTick(
                    label_text=str(val),
                    label_value=float(val),
                    page_x=float(plot_bbox[0]),
                    page_y=float(ty),
                    raw_text=raw,
                    method=method,
                )
            )

        # Require >=3 ticks with parseable labels.
        x_axis_ticks.sort(key=lambda t: t.page_x)
        y_axis_ticks.sort(key=lambda t: t.page_y)

        if len({t.label_value for t in x_axis_ticks}) < 3:
            raise RuntimeError(
                f"Axis calibration failed: need >=3 labeled x ticks, got {len(x_axis_ticks)} parsed from {len(x_ticks)} marks"
            )
        if len({t.label_value for t in y_axis_ticks}) < 3:
            raise RuntimeError(
                f"Axis calibration failed: need >=3 labeled y ticks, got {len(y_axis_ticks)} parsed from {len(y_ticks)} marks"
            )

        x_fit = _fit_axis_best(ticks=x_axis_ticks, axis="x")
        y_fit = _fit_axis_best(ticks=y_axis_ticks, axis="y")

        # Digitize two heavy curves: select the longest curve among each red shade.
        curves_in_plot = [
            c
            for (_area, bb, c) in bboxes
            if _bbox_intersects(bb, plot_bbox) and c.get("pts")
        ]

        def _pick_curve(color: tuple[float, float, float]) -> dict[str, Any]:
            cands = [c for c in curves_in_plot if c.get("stroking_color") == color]
            if not cands:
                raise RuntimeError(f"No curves found for color={color}")
            return max(cands, key=lambda c: len(c.get("pts") or []))

        # Dark red likely corresponds to one extreme Eb; light red to another.
        curve_dark = _pick_curve((1, 0, 0))
        curve_light = _pick_curve((1, 0.5, 0.5))

        series: dict[str, list[tuple[float, float, float, float]]] = {}
        series["Eb0"] = _digitize_curve_points(
            pts=list(curve_dark.get("pts") or []),
            plot_bbox=plot_bbox,
            x_fit=x_fit,
            y_fit=y_fit,
        )
        series["Eb8"] = _digitize_curve_points(
            pts=list(curve_light.get("pts") or []),
            plot_bbox=plot_bbox,
            x_fit=x_fit,
            y_fit=y_fit,
        )

        if len(series["Eb0"]) < 20 or len(series["Eb8"]) < 20:
            raise RuntimeError(
                f"Too few digitized points: Eb0={len(series['Eb0'])}, Eb8={len(series['Eb8'])}"
            )

        # Uncertainty proxies from axis fit residuals.
        sigma_logtau = _axis_sigma_from_fit(fit=x_fit) if x_fit.scale == "log10" else 0.0
        if x_fit.scale != "log10":
            # Provide a log-tau sigma anyway (approx).
            sigma_logtau = float(
                (x_fit.max_residual_page / (abs(x_fit.a) or 1.0))
                / max(1e-12, math.log(10.0) * max(t.label_value for t in x_axis_ticks))
            )

        # Work sigma in absolute units.
        if y_fit.scale == "log10":
            sigma_logwork = _axis_sigma_from_fit(fit=y_fit)
            # Convert roughly at Landauer scale.
            sigma_work = float(math.log(2.0) * math.log(10.0) * sigma_logwork)
        else:
            sigma_work = float(_axis_sigma_from_fit(fit=y_fit))

        rows: list[dict[str, str]] = []
        for name, pts in series.items():
            curve_id = f"Fig3_{name}_heavy"
            for tau, work, _px, _py in pts:
                tau_hat_raw = float(tau)
                tau_converted = float(TAU_HAT_TO_D_TAU_OVER_VAR) * tau_hat_raw
                rows.append(
                    {
                        "paper_id": paper_id,
                        "figure_id": figure_id,
                        "dataset_id": dataset_id,
                        "curve_id": curve_id,
                        "value_kind": "work_over_kT",
                        "tau_unit": "D_tau_over_Var",
                        "tau_s": f"{tau_converted:.10g}",
                        "tau_value": f"{tau_converted:.10g}",
                        "tau_hat_raw": f"{tau_hat_raw:.10g}",
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
        page_number_1based=page_no,
        zoom=float(args.overlay_zoom),
        overlay_path=overlay_path,
        series=series,
        ticks_x=x_axis_ticks,
        ticks_y=y_axis_ticks,
    )

    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    receipt = {
        "pdf_path": str(pdf_path),
        "pdf_sha256": pdf_sha256,
        "page": int(page_no),
        "paper_id": paper_id,
        "figure_id": figure_id,
        "dataset_id": dataset_id,
        "curve_filters": {
            "Eb0": {
                "stroking_color": list(curve_dark.get("stroking_color") or ()),
                "linewidth": float(curve_dark.get("linewidth") or 0.0),
                "n_pts": len(curve_dark.get("pts") or []),
            },
            "Eb8": {
                "stroking_color": list(curve_light.get("stroking_color") or ()),
                "linewidth": float(curve_light.get("linewidth") or 0.0),
                "n_pts": len(curve_light.get("pts") or []),
            },
        },
        "plot_bbox": {
            "x0": float(plot_bbox[0]),
            "y0": float(plot_bbox[1]),
            "x1": float(plot_bbox[2]),
            "y1": float(plot_bbox[3]),
        },
        "axis_ticks": {
            "x": [
                {
                    "label": t.label_text,
                    "label_value": float(t.label_value),
                    "page_x": float(t.page_x),
                    "page_y": float(t.page_y),
                    "raw_text": t.raw_text,
                    "method": t.method,
                }
                for t in x_axis_ticks
            ],
            "y": [
                {
                    "label": t.label_text,
                    "label_value": float(t.label_value),
                    "page_x": float(t.page_x),
                    "page_y": float(t.page_y),
                    "raw_text": t.raw_text,
                    "method": t.method,
                }
                for t in y_axis_ticks
            ],
        },
        "axis_fit": {
            "x": {
                "scale": x_fit.scale,
                "a": float(x_fit.a),
                "b": float(x_fit.b),
                "max_residual_page": float(x_fit.max_residual_page),
            },
            "y": {
                "scale": y_fit.scale,
                "a": float(y_fit.a),
                "b": float(y_fit.b),
                "max_residual_page": float(y_fit.max_residual_page),
            },
        },
        "overlay": {
            "path": str(overlay_path),
            "sha256": overlay_sha256,
            "zoom": float(args.overlay_zoom),
        },
        "outputs": {
            "csv_path": str(out_csv),
            "csv_sha256": _sha256_file(out_csv),
        },
        "checks": {
            "axis_ticks_x": len({t.label_value for t in x_axis_ticks}),
            "axis_ticks_y": len({t.label_value for t in y_axis_ticks}),
        },
        "notes": [
            "Digitized from vector paths (no raster/manual clicking).",
            "Interpretation: plotted quantity is excess above Landauer; reported work_over_kT adds ln2.",
            "Tau conversion: axis labels are tau_hat; CSV stores tau_unit=D_tau_over_Var with tau = 4 * tau_hat_raw (assumes Var(x)=x0^2 and tau_hat=D·tau/(2x0)^2).",
        ],
        "tau_conversion": {
            "axis_label": "tau_hat",
            "csv_tau_unit": "D_tau_over_Var",
            "tau_hat_to_D_tau_over_Var": float(TAU_HAT_TO_D_TAU_OVER_VAR),
        },
    }
    receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(f"Wrote {out_csv} ({len(rows)} rows)")
    print(f"Wrote {receipt_path}")
    print(f"Wrote {overlay_path}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Digitize Proesmans 2020 Fig 3 -> PREREG_A CSV")
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
