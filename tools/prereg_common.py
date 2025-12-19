"""Shared prereg utilities (manifest binding, hashing, receipts).

This module is intentionally small and dependency-light.
"""

from __future__ import annotations

import hashlib
import json
import os
import platform
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional


REPO_ROOT = Path(__file__).resolve().parents[1]


def utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def write_json(path: Path, payload: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def read_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def tool_hashes(paths: Iterable[Path]) -> Dict[str, str]:
    out: Dict[str, str] = {}
    for p in paths:
        out[str(p.relative_to(REPO_ROOT))] = sha256_file(p)
    return out


def git_head_sha(repo_root: Path) -> str:
    try:
        res = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=str(repo_root),
            check=True,
            capture_output=True,
            text=True,
        )
        return res.stdout.strip()
    except Exception:
        return "unknown"


def environment_snapshot() -> Dict[str, Any]:
    return {
        "python": {
            "executable": sys.executable,
            "version": sys.version,
        },
        "platform": {
            "system": platform.system(),
            "release": platform.release(),
            "machine": platform.machine(),
        },
        "env": {
            "PYTHONNOUSERSITE": os.environ.get("PYTHONNOUSERSITE"),
        },
    }


@dataclass(frozen=True)
class ManifestSpec:
    name: str
    root: Path

    @property
    def path(self) -> Path:
        return self.root / self.name


def init_manifest(
    spec: ManifestSpec,
    *,
    params: Dict[str, Any],
    tool_files: List[Path],
) -> Dict[str, Any]:
    payload: Dict[str, Any] = {
        "created_at": utc_now_iso(),
        "git_head": git_head_sha(REPO_ROOT),
        "params": params,
        "tool_hashes": tool_hashes(tool_files),
        "artifacts": {},
        "environment": environment_snapshot(),
    }
    write_json(spec.path, payload)
    return payload


def require_manifest(spec: ManifestSpec) -> Dict[str, Any]:
    if not spec.path.exists():
        raise FileNotFoundError(f"Missing manifest: {spec.path}")
    return read_json(spec.path)


def verify_tool_hashes(manifest: Dict[str, Any], tool_files: List[Path]) -> None:
    expected = manifest.get("tool_hashes", {})
    current = tool_hashes(tool_files)
    mismatches: List[str] = []
    for k, v in expected.items():
        if current.get(k) != v:
            mismatches.append(f"{k}: expected {v}, got {current.get(k)}")
    if mismatches:
        raise RuntimeError(
            "Tool hash mismatch (prereg invalid; use a new output root/manifest):\n  "
            + "\n  ".join(mismatches)
        )


def verify_params_exact(manifest: Dict[str, Any], actual: Dict[str, Any]) -> None:
    expected = manifest.get("params", {})
    mismatches: List[str] = []
    for k, v in actual.items():
        if expected.get(k) != v:
            mismatches.append(f"{k}: manifest={expected.get(k)!r} args={v!r}")
    if mismatches:
        raise RuntimeError(
            "Parameter mismatch vs manifest (prereg invalid; use a new output root/manifest):\n  "
            + "\n  ".join(mismatches)
        )


def update_manifest_artifacts(spec: ManifestSpec, *, artifact_paths: Dict[str, Path]) -> None:
    manifest = require_manifest(spec)
    artifacts = dict(manifest.get("artifacts", {}))
    for logical_name, file_path in artifact_paths.items():
        if file_path.exists():
            artifacts[logical_name] = sha256_file(file_path)
    manifest["artifacts"] = artifacts
    write_json(spec.path, manifest)


def require_artifact_hashes(spec: ManifestSpec, *, required: Dict[str, Path]) -> None:
    manifest = require_manifest(spec)
    expected = manifest.get("artifacts", {})
    for logical_name, file_path in required.items():
        if not file_path.exists():
            raise FileNotFoundError(f"Missing artifact {logical_name}: {file_path}")
        exp = expected.get(logical_name)
        cur = sha256_file(file_path)
        if exp is not None and exp != cur:
            raise RuntimeError(
                f"Artifact hash mismatch for {logical_name}: expected {exp}, got {cur}"
            )


def safe_relpath(path: Path, root: Path) -> str:
    try:
        return str(path.relative_to(root))
    except Exception:
        return str(path)
