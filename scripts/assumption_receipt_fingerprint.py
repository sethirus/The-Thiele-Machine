#!/usr/bin/env python3
"""Compute the proof-relevant fingerprint used by the assumption receipt.

The full ``Print Assumptions`` corpus is expensive to re-derive. A receipt
may be reused only when the inputs that can change theorem resolution are
unchanged. Coq comments and whitespace are removed from proof sources so
editorial cleanup does not trigger a twelve-thousand-query rebuild; project
mappings, vendor sources, generator code, and the Coq version remain inputs.
"""
from __future__ import annotations

import hashlib
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def _strip_coq_comments(text: str) -> str:
    out: list[str] = []
    depth = 0
    i = 0
    in_string = False
    escaped = False
    pending_space = False

    def emit(char: str) -> None:
        nonlocal pending_space
        if not in_string and char.isspace():
            pending_space = True
            return
        if pending_space and out and out[-1] != "\n":
            out.append(" ")
        pending_space = False
        out.append(char)

    while i < len(text):
        pair = text[i:i + 2]
        if in_string:
            emit(text[i])
            if escaped:
                escaped = False
            elif text[i] == "\\":
                escaped = True
            elif text[i] == '"':
                in_string = False
            i += 1
            continue
        if text[i] == '"':
            emit(text[i])
            in_string = True
            i += 1
            continue
        if pair == "(*":
            depth += 1
            pending_space = True
            i += 2
        elif pair == "*)" and depth:
            depth -= 1
            pending_space = True
            i += 2
        elif depth:
            i += 1
        else:
            emit(text[i])
            i += 1
    return "".join(out).strip()


def _coq_source_paths(root: Path) -> list[Path]:
    project = root / "coq/_CoqProject"
    paths: set[Path] = set()
    if project.exists():
        for line in project.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if line and not line.startswith(("#", "-")) and line.endswith(".v"):
                paths.add(root / "coq" / line)
    for directory in (
        root / "vendor/bbv",
        root / "vendor/kami",
        root / "vendor/coq-undecidability/theories",
    ):
        if directory.exists():
            paths.update(directory.rglob("*.v"))
    return sorted(path for path in paths if path.is_file())


def _tool_inputs(root: Path) -> list[Path]:
    return [
        root / "coq/_CoqProject",
        root / "build/probe/build_full_probe.py",
        root / "build/probe/aggregate_full_probe.py",
        root / "scripts/coq_proof_scope.py",
        root / "scripts/run_assumption_batches.py",
        root / "scripts/assumption_receipt_fingerprint.py",
    ]


def _coq_version(root: Path) -> str:
    try:
        return subprocess.check_output(
            ["coqc", "--version"], cwd=root, text=True
        ).splitlines()[0].strip()
    except (OSError, subprocess.CalledProcessError, IndexError):
        return "coqc-unavailable"


def _digest(path: Path, *, semantic_coq: bool) -> bytes:
    data = path.read_text(encoding="utf-8")
    if semantic_coq:
        data = _strip_coq_comments(data)
    return data.encode("utf-8")


def corpus_digest(root: Path = ROOT) -> str:
    hasher = hashlib.sha256()
    hasher.update(b"thiele-assumption-corpus-v1\0")
    hasher.update(_coq_version(root).encode("utf-8"))
    hasher.update(b"\0")
    for path in _coq_source_paths(root):
        hasher.update(path.relative_to(root).as_posix().encode("utf-8"))
        hasher.update(b"\0")
        hasher.update(_digest(path, semantic_coq=True))
        hasher.update(b"\0")
    for path in _tool_inputs(root):
        if not path.exists():
            continue
        hasher.update(path.relative_to(root).as_posix().encode("utf-8"))
        hasher.update(b"\0")
        hasher.update(_digest(path, semantic_coq=False))
        hasher.update(b"\0")
    return hasher.hexdigest()


def probe_digest(probe: Path | None = None) -> str:
    from coq_proof_scope import FULL_ASSUMPTION_PROBE

    path = probe or (ROOT / FULL_ASSUMPTION_PROBE)
    text = _strip_coq_comments(path.read_text(encoding="utf-8"))
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


if __name__ == "__main__":
    print(corpus_digest())
