"""Genesis Compression: a 2D reversible CA under a μ-like compression budget.

This module is intentionally pragmatic:
- The *update rule* is reversible (Margolus HPP-style lattice gas on 2x2 blocks).
- The *budget enforcement* step is lossy and acts like a selection pressure.

The goal is not to claim "life is inevitable", but to provide a falsifiable,
replayable experiment that shows how a compressibility constraint biases emergent
structure.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

import numpy as np
from PIL import Image, ImageDraw, ImageFont


ArrayU8 = np.ndarray


@dataclass(frozen=True)
class GenesisConfig:
    width: int
    height: int
    steps: int
    seed: int
    rule: str
    budget_bits: int
    dictionary_size: int
    pressure_stride: int
    sample_every: int
    sample_steps: Tuple[int, ...]
    include_control: bool
    display_phase_invert: bool
    gif_path: Path | None = None
    gif_scale: int = 4
    gif_fps: int = 30
    init_density: float = 0.25
    init_patch_frac: float = 0.40
    render_hud: bool = True
    render_delta: bool = True
    render_motion: bool = True
    render_trail: bool = True
    trail_decay: int = 240
    trail_threshold: int = 64


@dataclass(frozen=True)
class Snapshot:
    step: int
    sha256_control: str | None
    sha256_pressured: str
    bits_control: int | None
    bits_pressured: int
    entropy_control: float | None
    entropy_pressured: float
    density_control: float | None
    density_pressured: float

    # Motion/trail coherence metrics computed from the pressured timeline.
    # Motion is the 0/1 mask of cells that changed since the previous *rendered* frame.
    motion_mass: int
    motion_cc_count: int
    motion_cc_max: int
    motion_centroid_x_q: int | None
    motion_centroid_y_q: int | None

    # Trail is a decayed heatmap; metrics use a thresholded binary mask.
    trail_mass: int | None
    trail_cc_count: int | None
    trail_cc_max: int | None
    trail_intensity_sum: int | None


@dataclass(frozen=True)
class GenesisResult:
    snapshots: Tuple[Snapshot, ...]
    pdiscover_count: int
    bits_first: int
    bits_last: int
    bits_first_control: int | None
    bits_last_control: int | None
    video_sha256: str | None

    # Aggregate coherence metrics (integers to keep receipts replay-stable).
    motion_mass_sum: int
    motion_mass_max: int
    motion_cc_count_sum: int
    motion_cc_max_max: int
    motion_centroid_l1_path_q: int
    trail_mass_sum: int | None
    trail_mass_max: int | None
    trail_cc_count_sum: int | None
    trail_cc_max_max: int | None
    trail_intensity_sum: int | None


def _validate_config(cfg: GenesisConfig) -> None:
    if cfg.width <= 0 or cfg.height <= 0:
        raise ValueError("width/height must be positive")
    if cfg.width % 2 != 0 or cfg.height % 2 != 0:
        raise ValueError("width/height must be even (Margolus blocks)")
    if cfg.steps <= 0:
        raise ValueError("steps must be positive")
    if cfg.rule not in {"hpp", "critters"}:
        raise ValueError("rule must be one of: hpp, critters")
    if cfg.budget_bits <= 0:
        raise ValueError("budget_bits must be positive")
    if cfg.dictionary_size <= 0:
        raise ValueError("dictionary_size must be positive")
    if cfg.pressure_stride <= 0:
        raise ValueError("pressure_stride must be positive")
    if cfg.sample_every <= 0:
        raise ValueError("sample_every must be positive")
    if cfg.gif_scale <= 0:
        raise ValueError("gif_scale must be positive")
    if not (0.0 < float(cfg.init_density) < 1.0):
        raise ValueError("init_density must be in (0, 1)")
    if not (0.0 < float(cfg.init_patch_frac) <= 1.0):
        raise ValueError("init_patch_frac must be in (0, 1]")
    if cfg.gif_fps <= 0:
        raise ValueError("gif_fps must be positive")
    if not (0 <= int(cfg.trail_decay) <= 255):
        raise ValueError("trail_decay must be in [0, 255]")
    if not (0 <= int(cfg.trail_threshold) <= 255):
        raise ValueError("trail_threshold must be in [0, 255]")


def _cc_stats_4n(mask: ArrayU8) -> tuple[int, int]:
    """Return (component_count, max_component_size) using 4-neighborhood connectivity."""

    if mask.ndim != 2:
        raise ValueError("mask must be 2D")

    h, w = int(mask.shape[0]), int(mask.shape[1])
    if h == 0 or w == 0:
        return 0, 0

    visited = np.zeros((h, w), dtype=np.uint8)
    count = 0
    max_size = 0

    for y in range(h):
        for x in range(w):
            if mask[y, x] == 0 or visited[y, x] != 0:
                continue
            count += 1
            size = 0
            stack: List[tuple[int, int]] = [(y, x)]
            visited[y, x] = 1
            while stack:
                cy, cx = stack.pop()
                size += 1
                ny = cy - 1
                if ny >= 0 and mask[ny, cx] != 0 and visited[ny, cx] == 0:
                    visited[ny, cx] = 1
                    stack.append((ny, cx))
                ny = cy + 1
                if ny < h and mask[ny, cx] != 0 and visited[ny, cx] == 0:
                    visited[ny, cx] = 1
                    stack.append((ny, cx))
                nx = cx - 1
                if nx >= 0 and mask[cy, nx] != 0 and visited[cy, nx] == 0:
                    visited[cy, nx] = 1
                    stack.append((cy, nx))
                nx = cx + 1
                if nx < w and mask[cy, nx] != 0 and visited[cy, nx] == 0:
                    visited[cy, nx] = 1
                    stack.append((cy, nx))
            if size > max_size:
                max_size = size

    return count, max_size


def _centroid_q(mask: ArrayU8, *, q: int = 1024) -> tuple[int | None, int | None, int]:
    """Return quantized centroid (x_q, y_q, mass) for a binary mask.

    x_q/y_q are in units of 1/q grid cells, using floor division for determinism.
    """

    ys, xs = np.nonzero(mask)
    mass = int(xs.size)
    if mass == 0:
        return None, None, 0
    sum_x = int(xs.sum())
    sum_y = int(ys.sum())
    x_q = (sum_x * q) // mass
    y_q = (sum_y * q) // mass
    return x_q, y_q, mass


def init_noise(*, width: int, height: int, seed: int, density: float, patch_frac: float) -> ArrayU8:
    rng = np.random.default_rng(int(seed))
    state = np.zeros((height, width), dtype=np.uint8)

    ph = max(1, int(round(height * float(patch_frac))))
    pw = max(1, int(round(width * float(patch_frac))))
    y0 = (height - ph) // 2
    x0 = (width - pw) // 2
    patch = (rng.random((ph, pw)) < float(density)).astype(np.uint8)
    state[y0 : y0 + ph, x0 : x0 + pw] = patch
    return state


def _step_margolus_hpp(state: ArrayU8, *, phase: int) -> ArrayU8:
    """Vectorized reversible HPP-like collision on 2x2 Margolus blocks."""

    oy = 0 if (phase & 1) == 0 else 1
    ox = 0 if (phase & 1) == 0 else 1

    shifted = np.roll(state, shift=(-oy, -ox), axis=(0, 1))
    out = shifted.copy()

    a = shifted[0::2, 0::2]
    b = shifted[0::2, 1::2]
    c = shifted[1::2, 0::2]
    d = shifted[1::2, 1::2]

    mask_ad = (a == 1) & (d == 1) & (b == 0) & (c == 0)
    mask_bc = (a == 0) & (d == 0) & (b == 1) & (c == 1)

    # Swap diagonals for the two collision cases.
    out_a = a.copy()
    out_b = b.copy()
    out_c = c.copy()
    out_d = d.copy()

    out_a[mask_ad] = 0
    out_b[mask_ad] = 1
    out_c[mask_ad] = 1
    out_d[mask_ad] = 0

    out_a[mask_bc] = 1
    out_b[mask_bc] = 0
    out_c[mask_bc] = 0
    out_d[mask_bc] = 1

    out[0::2, 0::2] = out_a
    out[0::2, 1::2] = out_b
    out[1::2, 0::2] = out_c
    out[1::2, 1::2] = out_d

    return np.roll(out, shift=(oy, ox), axis=(0, 1))


def _step_margolus_critters(state: ArrayU8, *, phase: int) -> ArrayU8:
    """Vectorized reversible Critters block CA (Toffoli/Margolus).

    Per 2x2 block:
    - If it has exactly two live cells: unchanged
    - Else: flip every cell
    - Additionally, if the original block had exactly three live cells: rotate 180°
    """

    oy = 0 if (phase & 1) == 0 else 1
    ox = 0 if (phase & 1) == 0 else 1

    shifted = np.roll(state, shift=(-oy, -ox), axis=(0, 1))
    out = shifted.copy()

    a = shifted[0::2, 0::2]
    b = shifted[0::2, 1::2]
    c = shifted[1::2, 0::2]
    d = shifted[1::2, 1::2]

    count = a + b + c + d
    flip = (count != 2).astype(np.uint8)

    a2 = a ^ flip
    b2 = b ^ flip
    c2 = c ^ flip
    d2 = d ^ flip

    rot = (count == 3)
    if np.any(rot):
        a3 = a2.copy()
        b3 = b2.copy()
        c3 = c2.copy()
        d3 = d2.copy()
        # 180° rotation swaps (a<->d, b<->c)
        a2[rot] = d3[rot]
        d2[rot] = a3[rot]
        b2[rot] = c3[rot]
        c2[rot] = b3[rot]

    out[0::2, 0::2] = a2
    out[0::2, 1::2] = b2
    out[1::2, 0::2] = c2
    out[1::2, 1::2] = d2

    return np.roll(out, shift=(oy, ox), axis=(0, 1))


def step_margolus(state: ArrayU8, *, phase: int, rule: str) -> ArrayU8:
    if rule == "hpp":
        return _step_margolus_hpp(state, phase=phase)
    if rule == "critters":
        return _step_margolus_critters(state, phase=phase)
    raise ValueError("unknown rule")


def estimate_bits_rle(state: ArrayU8) -> int:
    """Deterministic, cheap MDL proxy: row-wise run-length coding.

    Counts transitions along each row and charges bits per run.
    This is not a real Kolmogorov complexity, but it is stable and monotone-ish
    for "noisy" vs "structured" textures.
    """

    h, w = state.shape
    # transitions per row (including start run)
    transitions = int(np.sum(state[:, 1:] != state[:, :-1])) + h

    # A simple bit model: encode each run length with ~log2(w) bits and the run value with 1 bit.
    bits_per_run = max(1, int(np.ceil(np.log2(max(2, w))))) + 1
    return int(transitions * bits_per_run)


def tile_entropy(state: ArrayU8, *, tile: int = 2) -> float:
    codes = _tile_codes(state, tile=tile).reshape(-1).astype(np.int64)
    if codes.size == 0:
        return 0.0
    counts = np.bincount(codes)
    probs = counts[counts > 0].astype(np.float64) / float(codes.size)
    # Shannon entropy in bits
    return float(-np.sum(probs * np.log2(probs)))


def density(state: ArrayU8) -> float:
    return float(np.mean(state))


def _tile_codes(state: ArrayU8, *, tile: int) -> ArrayU8:
    h, w = state.shape
    if h % tile != 0 or w % tile != 0:
        raise ValueError("state dims must be multiples of tile")
    ty = h // tile
    tx = w // tile

    # Pack each tile into an integer code.
    codes = np.zeros((ty, tx), dtype=np.uint16)
    bit = 0
    for yy in range(tile):
        for xx in range(tile):
            codes |= (state[yy::tile, xx::tile].astype(np.uint16) & 1) << bit
            bit += 1
    return codes


def _apply_tile_codes(state: ArrayU8, *, tile: int, codes: ArrayU8) -> ArrayU8:
    h, w = state.shape
    ty, tx = codes.shape
    if ty * tile != h or tx * tile != w:
        raise ValueError("codes shape mismatch")

    out = np.zeros_like(state)
    bit = 0
    for yy in range(tile):
        for xx in range(tile):
            out[yy::tile, xx::tile] = ((codes >> bit) & 1).astype(np.uint8)
            bit += 1
    return out


def apply_budget_pressure(
    state: ArrayU8,
    *,
    budget_bits: int,
    dictionary_size: int,
    seed: int,
    step: int,
    tile: int = 2,
) -> tuple[ArrayU8, bool]:
    """If estimated bits exceed budget, project state onto a small tile dictionary.

    Deterministic:
    - dictionary = top-K most frequent tiles (ties broken by tile code)
    - each tile is replaced by nearest dictionary tile in Hamming distance
      (ties broken by smaller code).

    Returns (new_state, triggered).
    """

    bits = estimate_bits_rle(state)
    if bits <= budget_bits:
        return state, False

    codes = _tile_codes(state, tile=tile)
    flat = codes.reshape(-1)

    # Count tile frequencies.
    max_code = 1 << (tile * tile)
    counts = np.bincount(flat.astype(np.int64), minlength=max_code)
    # Pick top-K: sort by (-count, code)
    order = np.lexsort((np.arange(max_code), -counts))
    dict_codes = order[: int(dictionary_size)]

    # Precompute nearest dictionary code by Hamming distance.
    # Keep it small: tile=2 => 16 codes.
    def popcount16(x: int) -> int:
        return int(bin(x).count("1"))

    nearest = np.zeros(max_code, dtype=np.uint16)
    for c in range(max_code):
        best = int(dict_codes[0])
        best_d = popcount16(c ^ best)
        for dc in dict_codes[1:]:
            dc_i = int(dc)
            d = popcount16(c ^ dc_i)
            if d < best_d or (d == best_d and dc_i < best):
                best = dc_i
                best_d = d
        nearest[c] = best

    projected = nearest[flat.astype(np.int64)].reshape(codes.shape)

    # Small deterministic jitter to avoid immediate freezing: flip a tiny number of random tiles.
    rng = np.random.default_rng(int(seed) ^ (int(step) * 0x9E3779B97F4A7C15 & 0xFFFFFFFF))
    if projected.size > 0:
        flips = max(1, projected.size // 512)
        idx = rng.integers(0, projected.size, size=flips)
        proj_flat = projected.reshape(-1)
        for j in idx:
            # Toggle lowest bit (still deterministic)
            proj_flat[int(j)] ^= 1

    out = _apply_tile_codes(state, tile=tile, codes=projected)
    return out, True


def state_sha256(state: ArrayU8) -> str:
    return hashlib.sha256(state.tobytes()).hexdigest()


def _resize_nearest(pil: Image.Image, *, scale: int) -> Image.Image:
    if scale == 1:
        return pil
    resample = getattr(getattr(Image, "Resampling", Image), "NEAREST")
    return pil.resize((pil.width * scale, pil.height * scale), resample=resample)


def render_panel(
    state: ArrayU8,
    *,
    scale: int,
    on_rgb: tuple[int, int, int],
    off_rgb: tuple[int, int, int] = (0, 0, 0),
) -> Image.Image:
    on = np.array(on_rgb, dtype=np.uint8)
    off = np.array(off_rgb, dtype=np.uint8)
    img = np.where(state[..., None].astype(bool), on, off).astype(np.uint8)
    pil = Image.fromarray(img, mode="RGB")
    return _resize_nearest(pil, scale=scale)


def render_intensity_panel(
    intensity: ArrayU8,
    *,
    scale: int,
    color: tuple[int, int, int],
    bg: tuple[int, int, int] = (0, 0, 0),
) -> Image.Image:
    h, w = intensity.shape
    img = np.zeros((h, w, 3), dtype=np.uint8)
    if bg != (0, 0, 0):
        img[...] = np.array(bg, dtype=np.uint8)
    inten = intensity.astype(np.uint16)
    img[..., 0] = ((inten * int(color[0])) // 255).astype(np.uint8)
    img[..., 1] = ((inten * int(color[1])) // 255).astype(np.uint8)
    img[..., 2] = ((inten * int(color[2])) // 255).astype(np.uint8)
    pil = Image.fromarray(img, mode="RGB")
    return _resize_nearest(pil, scale=scale)


def _draw_label_bar(
    img: Image.Image,
    *,
    labels: Sequence[str],
    panel_width: int,
    gutter: int,
    bar_h: int,
    text_color: tuple[int, int, int] = (255, 255, 255),
) -> None:
    draw = ImageDraw.Draw(img)
    font = ImageFont.load_default()
    for i, label in enumerate(labels):
        x0 = i * (panel_width + gutter)
        draw.text((x0 + 6, 4), label, fill=text_color, font=font)


def _draw_hud(
    img: Image.Image,
    *,
    hud_lines: Sequence[str],
    bar_h: int,
    text_color: tuple[int, int, int] = (255, 255, 255),
) -> None:
    if not hud_lines:
        return
    draw = ImageDraw.Draw(img)
    font = ImageFont.load_default()
    y = 4
    x = img.width // 2
    for line in hud_lines:
        draw.text((x, y), line, fill=text_color, font=font, anchor="ma")
        y += 12


def render_composite(
    *,
    control: ArrayU8 | None,
    pressured: ArrayU8,
    motion: ArrayU8 | None,
    trail: ArrayU8 | None,
    scale: int,
    render_delta: bool,
    render_motion: bool,
    render_trail: bool,
    render_hud: bool,
    hud_lines: Sequence[str],
) -> Image.Image:
    gutter = max(2, scale)
    bar_h = 32 if render_hud else 20

    panels: List[Image.Image] = []
    labels: List[str] = []

    if control is not None:
        panels.append(render_panel(control, scale=scale, on_rgb=(80, 180, 255)))
        labels.append("CONTROL")
    panels.append(render_panel(pressured, scale=scale, on_rgb=(255, 210, 120)))
    labels.append("PRESSURED")

    if render_delta and control is not None:
        delta = (control != pressured).astype(np.uint8)
        panels.append(render_panel(delta, scale=scale, on_rgb=(255, 80, 80)))
        labels.append("Δ")

    if render_motion and motion is not None:
        panels.append(render_panel(motion, scale=scale, on_rgb=(80, 255, 120)))
        labels.append("MOTION")

    if render_trail and trail is not None:
        panels.append(render_intensity_panel(trail, scale=scale, color=(40, 255, 90)))
        labels.append("TRAIL")

    panel_w = panels[0].width
    panel_h = panels[0].height
    out_w = len(panels) * panel_w + (len(panels) - 1) * gutter
    out_h = bar_h + panel_h
    out = Image.new("RGB", (out_w, out_h), color=(0, 0, 0))

    x = 0
    for p in panels:
        out.paste(p, (x, bar_h))
        x += panel_w + gutter

    # Divider lines between panels.
    draw = ImageDraw.Draw(out)
    x = panel_w
    for _ in range(len(panels) - 1):
        draw.rectangle([x, bar_h, x + gutter - 1, out_h - 1], fill=(20, 20, 20))
        x += panel_w + gutter

    _draw_label_bar(out, labels=labels, panel_width=panel_w, gutter=gutter, bar_h=bar_h)
    if render_hud:
        _draw_hud(out, hud_lines=hud_lines, bar_h=bar_h)
    return out


def save_gif(frames: Sequence[Image.Image], *, path: Path, fps: int = 30) -> str:
    if not frames:
        raise ValueError("no frames")
    path.parent.mkdir(parents=True, exist_ok=True)

    duration_ms = int(1000 / max(1, fps))
    frames[0].save(
        path,
        save_all=True,
        append_images=list(frames[1:]),
        duration=duration_ms,
        loop=0,
        optimize=False,
    )
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_genesis(cfg: GenesisConfig) -> GenesisResult:
    _validate_config(cfg)

    base = init_noise(
        width=cfg.width,
        height=cfg.height,
        seed=cfg.seed,
        density=float(cfg.init_density),
        patch_frac=float(cfg.init_patch_frac),
    )
    state_pressured = base.copy()
    state_control = base.copy() if cfg.include_control else None

    want_steps = set(int(s) for s in cfg.sample_steps if 0 <= int(s) <= cfg.steps)
    for s in range(0, cfg.steps + 1, int(cfg.sample_every)):
        want_steps.add(int(s))
    want_steps.add(0)
    want_steps.add(int(cfg.steps))
    frames: List[Image.Image] = []
    snapshots: List[Snapshot] = []
    last_disp_pressured: ArrayU8 | None = None
    trail: ArrayU8 | None = np.zeros_like(state_pressured, dtype=np.uint8) if cfg.render_trail else None

    pdiscover = 0
    bits_first = estimate_bits_rle(state_pressured)
    bits_first_control = estimate_bits_rle(state_control) if state_control is not None else None

    if 0 in want_steps:
        disp_p = state_pressured
        disp_c = state_control
        if cfg.display_phase_invert and (0 & 1) == 1:
            disp_p = 1 - disp_p
            if disp_c is not None:
                disp_c = 1 - disp_c
        motion = None
        if last_disp_pressured is not None:
            motion = (disp_p != last_disp_pressured).astype(np.uint8)
        else:
            motion = np.zeros_like(disp_p, dtype=np.uint8)

        motion_cc_count, motion_cc_max = _cc_stats_4n(motion)
        motion_x_q, motion_y_q, motion_mass = _centroid_q(motion)

        trail_mass: int | None = None
        trail_cc_count: int | None = None
        trail_cc_max: int | None = None
        trail_intensity_sum: int | None = None

        if trail is not None:
            decay = int(cfg.trail_decay)
            trail_u16 = (trail.astype(np.uint16) * decay) // 255
            trail_u16 = np.clip(trail_u16 + motion.astype(np.uint16) * 255, 0, 255)
            trail = trail_u16.astype(np.uint8)

            trail_mask = (trail >= np.uint8(int(cfg.trail_threshold))).astype(np.uint8)
            trail_cc_count, trail_cc_max = _cc_stats_4n(trail_mask)
            trail_mass = int(trail_mask.sum())
            trail_intensity_sum = int(trail.sum())
        hud = [
            f"step={0}  rule={cfg.rule}  stride={cfg.pressure_stride}",
            f"bits: ctrl={bits_first_control}  press={bits_first}  budget={cfg.budget_bits}",
            f"trail_decay={int(cfg.trail_decay)}",
        ]
        frames.append(
            render_composite(
                control=disp_c,
                pressured=disp_p,
                motion=motion,
                trail=trail,
                scale=cfg.gif_scale,
                render_delta=bool(cfg.render_delta),
                render_motion=bool(cfg.render_motion),
                render_trail=bool(cfg.render_trail),
                render_hud=bool(cfg.render_hud),
                hud_lines=hud,
            )
        )
        last_disp_pressured = disp_p.copy()
        snapshots.append(
            Snapshot(
                step=0,
                sha256_control=state_sha256(state_control) if state_control is not None else None,
                sha256_pressured=state_sha256(state_pressured),
                bits_control=bits_first_control,
                bits_pressured=bits_first,
                entropy_control=tile_entropy(state_control) if state_control is not None else None,
                entropy_pressured=tile_entropy(state_pressured),
                density_control=density(state_control) if state_control is not None else None,
                density_pressured=density(state_pressured),
                motion_mass=int(motion_mass),
                motion_cc_count=int(motion_cc_count),
                motion_cc_max=int(motion_cc_max),
                motion_centroid_x_q=motion_x_q,
                motion_centroid_y_q=motion_y_q,
                trail_mass=trail_mass,
                trail_cc_count=trail_cc_count,
                trail_cc_max=trail_cc_max,
                trail_intensity_sum=trail_intensity_sum,
            )
        )

    for step in range(1, cfg.steps + 1):
        state_pressured = step_margolus(state_pressured, phase=step & 1, rule=cfg.rule)
        if state_control is not None:
            state_control = step_margolus(state_control, phase=step & 1, rule=cfg.rule)

        # Budget pressure at a stride, to emulate intermittent PDISCOVER.
        triggered = False
        if step % cfg.pressure_stride == 0:
            state_pressured, triggered = apply_budget_pressure(
                state_pressured,
                budget_bits=cfg.budget_bits,
                dictionary_size=cfg.dictionary_size,
                seed=cfg.seed,
                step=step,
            )
            if triggered:
                pdiscover += 1

        if step in want_steps:
            disp_p = state_pressured
            disp_c = state_control
            if cfg.display_phase_invert and (step & 1) == 1:
                disp_p = 1 - disp_p
                if disp_c is not None:
                    disp_c = 1 - disp_c

            bits_c = estimate_bits_rle(state_control) if state_control is not None else None
            bits_p = estimate_bits_rle(state_pressured)
            ent_c = tile_entropy(state_control) if state_control is not None else None
            ent_p = tile_entropy(state_pressured)
            den_c = density(state_control) if state_control is not None else None
            den_p = density(state_pressured)
            hud = [
                f"step={step}  rule={cfg.rule}  PDISCOVER={pdiscover}",
                f"bits: ctrl={bits_c}  press={bits_p}  budget={cfg.budget_bits}",
                f"H2x2: ctrl={None if ent_c is None else round(ent_c, 3)}  press={round(ent_p, 3)}  dens: ctrl={None if den_c is None else round(den_c, 3)}  press={round(den_p, 3)}",
            ]

            motion = None
            if last_disp_pressured is not None:
                motion = (disp_p != last_disp_pressured).astype(np.uint8)
            else:
                motion = np.zeros_like(disp_p, dtype=np.uint8)

            motion_cc_count, motion_cc_max = _cc_stats_4n(motion)
            motion_x_q, motion_y_q, motion_mass = _centroid_q(motion)

            trail_mass: int | None = None
            trail_cc_count: int | None = None
            trail_cc_max: int | None = None
            trail_intensity_sum: int | None = None

            if trail is not None:
                decay = int(cfg.trail_decay)
                trail_u16 = (trail.astype(np.uint16) * decay) // 255
                trail_u16 = np.clip(trail_u16 + motion.astype(np.uint16) * 255, 0, 255)
                trail = trail_u16.astype(np.uint8)

                trail_mask = (trail >= np.uint8(int(cfg.trail_threshold))).astype(np.uint8)
                trail_cc_count, trail_cc_max = _cc_stats_4n(trail_mask)
                trail_mass = int(trail_mask.sum())
                trail_intensity_sum = int(trail.sum())

            frames.append(
                render_composite(
                    control=disp_c,
                    pressured=disp_p,
                    motion=motion,
                    trail=trail,
                    scale=cfg.gif_scale,
                    render_delta=bool(cfg.render_delta),
                    render_motion=bool(cfg.render_motion),
                    render_trail=bool(cfg.render_trail),
                    render_hud=bool(cfg.render_hud),
                    hud_lines=hud,
                )
            )
            last_disp_pressured = disp_p.copy()
            snapshots.append(
                Snapshot(
                    step=step,
                    sha256_control=state_sha256(state_control) if state_control is not None else None,
                    sha256_pressured=state_sha256(state_pressured),
                    bits_control=bits_c,
                    bits_pressured=bits_p,
                    entropy_control=ent_c,
                    entropy_pressured=ent_p,
                    density_control=den_c,
                    density_pressured=den_p,
                    motion_mass=int(motion_mass),
                    motion_cc_count=int(motion_cc_count),
                    motion_cc_max=int(motion_cc_max),
                    motion_centroid_x_q=motion_x_q,
                    motion_centroid_y_q=motion_y_q,
                    trail_mass=trail_mass,
                    trail_cc_count=trail_cc_count,
                    trail_cc_max=trail_cc_max,
                    trail_intensity_sum=trail_intensity_sum,
                )
            )

    bits_last = estimate_bits_rle(state_pressured)
    bits_last_control = estimate_bits_rle(state_control) if state_control is not None else None
    video_sha: str | None = None
    if cfg.gif_path is not None:
        video_sha = save_gif(frames, path=cfg.gif_path, fps=int(cfg.gif_fps))

    # Aggregate coherence metrics.
    motion_mass_sum = int(sum(s.motion_mass for s in snapshots))
    motion_mass_max = int(max((s.motion_mass for s in snapshots), default=0))
    motion_cc_count_sum = int(sum(s.motion_cc_count for s in snapshots))
    motion_cc_max_max = int(max((s.motion_cc_max for s in snapshots), default=0))

    motion_centroid_l1_path_q = 0
    prev_x_q: int | None = None
    prev_y_q: int | None = None
    for s in snapshots:
        x_q = s.motion_centroid_x_q
        y_q = s.motion_centroid_y_q
        if x_q is None or y_q is None:
            continue
        if prev_x_q is not None and prev_y_q is not None:
            motion_centroid_l1_path_q += abs(int(x_q) - int(prev_x_q)) + abs(int(y_q) - int(prev_y_q))
        prev_x_q = int(x_q)
        prev_y_q = int(y_q)

    any_trail = any(s.trail_mass is not None for s in snapshots)
    trail_mass_sum: int | None = None
    trail_mass_max: int | None = None
    trail_cc_count_sum: int | None = None
    trail_cc_max_max: int | None = None
    trail_intensity_sum: int | None = None
    if any_trail:
        trail_mass_vals = [int(s.trail_mass or 0) for s in snapshots]
        trail_cc_count_vals = [int(s.trail_cc_count or 0) for s in snapshots]
        trail_cc_max_vals = [int(s.trail_cc_max or 0) for s in snapshots]
        trail_intensity_vals = [int(s.trail_intensity_sum or 0) for s in snapshots]
        trail_mass_sum = int(sum(trail_mass_vals))
        trail_mass_max = int(max(trail_mass_vals))
        trail_cc_count_sum = int(sum(trail_cc_count_vals))
        trail_cc_max_max = int(max(trail_cc_max_vals))
        # Keep the final snapshot's trail intensity as a compact summary.
        trail_intensity_sum = int(trail_intensity_vals[-1]) if trail_intensity_vals else 0

    return GenesisResult(
        snapshots=tuple(snapshots),
        pdiscover_count=int(pdiscover),
        bits_first=int(bits_first),
        bits_last=int(bits_last),
        bits_first_control=int(bits_first_control) if bits_first_control is not None else None,
        bits_last_control=int(bits_last_control) if bits_last_control is not None else None,
        video_sha256=video_sha,
        motion_mass_sum=motion_mass_sum,
        motion_mass_max=motion_mass_max,
        motion_cc_count_sum=motion_cc_count_sum,
        motion_cc_max_max=motion_cc_max_max,
        motion_centroid_l1_path_q=int(motion_centroid_l1_path_q),
        trail_mass_sum=trail_mass_sum,
        trail_mass_max=trail_mass_max,
        trail_cc_count_sum=trail_cc_count_sum,
        trail_cc_max_max=trail_cc_max_max,
        trail_intensity_sum=trail_intensity_sum,
    )
