#!/usr/bin/env python3
"""Compute the proof-relevant fingerprint used by the assumption receipt.

The full ``Print Assumptions`` corpus is expensive to re-derive. A receipt may
be reused only when the inputs that can change theorem dependencies are
unchanged. Coq comments, formatting, and string payloads are removed from
proof-source fingerprints: none can add or remove a referenced axiom or proof
constant. Project mappings, declarations, proof terms, generator code, and
the Coq version remain inputs.
"""
from __future__ import annotations

import hashlib
import io
import re
import subprocess
import tokenize
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
        if depth:
            if pair == "(*":
                depth += 1
                i += 2
            elif pair == "*)":
                depth -= 1
                i += 2
            else:
                i += 1
            continue
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
        elif text[i] == '"':
            emit(text[i])
            in_string = True
            i += 1
        else:
            emit(text[i])
            i += 1
    return "".join(out).strip()


def _strip_coq_assumption_irrelevant_literals(text: str) -> str:
    """Normalize comments and audit-metadata payloads for dependencies.

    ``Print Assumptions`` reports the constants used by a declaration's proof,
    not the wording of the repository's ``claim_not_imply`` audit metadata.
    Only those explicitly non-proof metadata strings are normalized. String
    literals elsewhere remain significant because they can affect reduction
    and therefore proof-term dependencies.
    """
    text = _strip_coq_comments(text)

    def erase_payloads(match: re.Match[str]) -> str:
        prefix, body, suffix = match.groups()
        out: list[str] = []
        in_string = False
        escaped = False
        for char in body:
            if in_string:
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    in_string = False
                    out.append('"')
                continue
            if char == '"':
                in_string = True
                out.append('"')
            else:
                out.append(char)
        return prefix + "".join(out) + suffix

    return re.sub(
        r"(claim_not_imply\s*:=\s*\[)(.*?)(\]\s*\|\})",
        erase_payloads,
        text,
        flags=re.DOTALL,
    )


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
    ]


def _coq_version(root: Path) -> str:
    try:
        return subprocess.check_output(
            ["coqc", "--version"], cwd=root, text=True
        ).splitlines()[0].strip()
    except (OSError, subprocess.CalledProcessError, IndexError):
        return "coqc-unavailable"


def _python_tokens(text: str) -> bytes:
    """Return Python tokens without comments or formatting-only whitespace."""
    try:
        tokens = tokenize.generate_tokens(io.StringIO(text).readline)
        normalized = []
        for token in tokens:
            if token.type in (tokenize.ENCODING, tokenize.ENDMARKER,
                              tokenize.NL, tokenize.COMMENT):
                continue
            if token.type in (tokenize.INDENT, tokenize.DEDENT,
                              tokenize.NEWLINE):
                normalized.append((token.type, ""))
            else:
                normalized.append((token.type, token.string))
        return repr(normalized).encode("utf-8")
    except (IndentationError, tokenize.TokenError):
        # A syntax-incomplete script must still invalidate the receipt rather
        # than being silently normalized into a reusable fingerprint.
        return text.encode("utf-8")


def _digest(path: Path, *, semantic_coq: bool) -> bytes:
    data = path.read_text(encoding="utf-8")
    if semantic_coq:
        data = _strip_coq_assumption_irrelevant_literals(data)
        return data.encode("utf-8")
    if path.suffix == ".py":
        return _python_tokens(data)
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
