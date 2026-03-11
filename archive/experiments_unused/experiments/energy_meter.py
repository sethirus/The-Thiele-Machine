"""Minimal energy metering helpers for cloud falsifiability runs.

The thesis thermodynamic bridge experiment needs an energy observable. In most
cloud environments the only practical, directly readable observable is Intel
RAPL energy via Linux powercap sysfs.

This module is intentionally best-effort:
- If RAPL is unavailable or unreadable, callers get a clear exception.
- We sum package-level energy domains to approximate total CPU energy.

References:
- Linux powercap sysfs: /sys/class/powercap/intel-rapl:*/energy_uj
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List


_SYSFS_RAPL_ROOT = Path("/sys/class/powercap")


def _rapl_energy_files() -> List[Path]:
    if not _SYSFS_RAPL_ROOT.exists():
        return []

    # Prefer package domains only: intel-rapl:N/energy_uj.
    # Subdomains (intel-rapl:N:0, etc.) often overlap, so summing them can double count.
    paths: List[Path] = []
    for entry in sorted(_SYSFS_RAPL_ROOT.glob("intel-rapl:*")):
        if ":" in entry.name:
            continue
        energy = entry / "energy_uj"
        if energy.exists():
            paths.append(energy)
    return paths


def rapl_available() -> bool:
    return bool(_rapl_energy_files())


def read_rapl_joules(paths: Iterable[Path] | None = None) -> float:
    """Read summed Intel RAPL energy for package domains in joules."""

    files = list(paths) if paths is not None else _rapl_energy_files()
    if not files:
        raise RuntimeError("Intel RAPL not available (no /sys/class/powercap/intel-rapl:*/energy_uj)")

    total_uj = 0
    for file in files:
        try:
            total_uj += int(file.read_text(encoding="utf-8").strip())
        except PermissionError as exc:
            raise RuntimeError(f"Permission denied reading RAPL energy counter: {file}") from exc
        except OSError as exc:
            raise RuntimeError(f"Failed reading RAPL energy counter: {file}") from exc
        except ValueError as exc:
            raise RuntimeError(f"Unexpected contents in RAPL energy counter: {file}") from exc

    return total_uj / 1_000_000.0


@dataclass(frozen=True)
class RaplEnergyMeter:
    """Energy meter using Linux Intel RAPL counters."""

    energy_files: List[Path]

    @classmethod
    def auto(cls) -> "RaplEnergyMeter":
        files = _rapl_energy_files()
        if not files:
            raise RuntimeError("Intel RAPL not available")
        return cls(files)

    def read_joules(self) -> float:
        return read_rapl_joules(self.energy_files)
