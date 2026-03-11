"""Run metadata helpers.

These helpers make experiment artifacts self-identifying for reproducibility.
We intentionally keep this lightweight and dependency-free so it works on cloud
instances with minimal setup.
"""

from __future__ import annotations

import os
import platform
import subprocess
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Optional


REPO_ROOT = Path(__file__).resolve().parent.parent


def _run(cmd: list[str], *, cwd: Path | None = None) -> Optional[str]:
    try:
        out = subprocess.check_output(cmd, cwd=str(cwd or REPO_ROOT), stderr=subprocess.STDOUT, text=True)
        return out.strip()
    except Exception:
        return None


def _read_first_line(path: Path) -> Optional[str]:
    try:
        return path.read_text(encoding="utf-8", errors="replace").splitlines()[0].strip()
    except Exception:
        return None


def _cpu_model() -> Optional[str]:
    cpuinfo = Path("/proc/cpuinfo")
    if not cpuinfo.exists():
        return None
    try:
        for line in cpuinfo.read_text(encoding="utf-8", errors="replace").splitlines():
            if line.lower().startswith("model name"):
                return line.split(":", 1)[1].strip()
    except Exception:
        return None
    return None


def _git_info() -> Dict[str, Any]:
    sha = _run(["git", "rev-parse", "HEAD"])
    dirty = _run(["git", "status", "--porcelain"])  # non-empty => dirty
    describe = _run(["git", "describe", "--always", "--dirty", "--tags"])  # may be None
    branch = _run(["git", "rev-parse", "--abbrev-ref", "HEAD"])
    return {
        "sha": sha,
        "branch": branch,
        "describe": describe,
        "dirty": bool(dirty),
    }


def capture_run_metadata(*, include_env: bool = False) -> Dict[str, Any]:
    """Return a JSON-serializable metadata dict."""

    meta: Dict[str, Any] = {
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "repo_root": str(REPO_ROOT),
        "git": _git_info(),
        "python": {
            "version": platform.python_version(),
            "implementation": platform.python_implementation(),
        },
        "host": {
            "platform": platform.platform(),
            "machine": platform.machine(),
            "processor": platform.processor(),
            "cpu_model": _cpu_model(),
            "uname": " ".join(platform.uname()),
        },
    }

    if include_env:
        allow = {
            "EVIDENCE_STRICT",
            "ALLOW_MU_NORMALIZE",
            "THERMO_TEMPERATURE_K",
            "THERMO_MEASURE_ENERGY",
            "THERMO_ENERGY_REPETITIONS",
        }
        meta["env"] = {k: os.environ.get(k) for k in sorted(allow) if os.environ.get(k) is not None}

    return meta
