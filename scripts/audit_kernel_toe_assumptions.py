#!/usr/bin/env python3
"""Audit the transitive Coq dependencies of KernelTOE flagship theorems.

Deliverable:
- Enumerate the `.v` files in the coqdep closure of `coq/kernel_toe/TOE.v`.
- Report any occurrences of: `Axiom`, `Parameter`, `Admitted.`, `admit`.
- Strip Coq comments `(* ... *)` (including nesting) before scanning.

Exit codes:
- 0: clean
- 1: findings
- 2: tooling/usage error
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import subprocess
import sys


TOKENS_RE = re.compile(r"\b(Axiom|Parameter|admit)\b|Admitted\.")


def strip_coq_comments(src: str) -> str:
    """Remove nested Coq comments `(* ... *)` conservatively."""

    out: list[str] = []
    i = 0
    depth = 0
    n = len(src)
    while i < n:
        if i + 1 < n and src[i] == "(" and src[i + 1] == "*":
            depth += 1
            i += 2
            continue
        if depth > 0 and i + 1 < n and src[i] == "*" and src[i + 1] == ")":
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(src[i])
        i += 1
    return "".join(out)


@dataclass(frozen=True)
class Finding:
    file: Path
    line: int
    snippet: str


def _coqdep_direct_v_deps(*, repo_root: Path, entry: Path) -> list[Path]:
    coqproject = repo_root / "coq" / "_CoqProject"
    if not coqproject.exists():
        raise FileNotFoundError(f"Missing {coqproject}")

    cmd = [
        "coqdep",
        "-f",
        str(coqproject),
        str(entry),
    ]
    p = subprocess.run(cmd, cwd=repo_root, text=True, capture_output=True)
    if p.returncode != 0:
        raise RuntimeError(f"coqdep failed: {p.stderr.strip()}")

    # Format: <target>.vo: dep1 dep2 ...
    line = p.stdout.strip().splitlines()[-1] if p.stdout.strip() else ""
    if ":" not in line:
        return [entry]

    _, deps_str = line.split(":", 1)
    deps: list[Path] = []
    for tok in deps_str.split():
        # coqdep usually lists `.vo` dependencies; map them back to `.v` sources.
        if tok.endswith((".vo", ".vos", ".vok", ".vio")):
            tok = tok.rsplit(".", 1)[0] + ".v"
        if tok.endswith(".v"):
            deps.append((repo_root / tok).resolve())

    # Dedup, stable order.
    seen: set[Path] = set()
    out: list[Path] = []
    for d in deps:
        if d not in seen:
            seen.add(d)
            out.append(d)
    return out


def coqdep_transitive_v_deps(*, repo_root: Path, entry: Path) -> list[Path]:
    """Compute transitive `.v` dependencies via iterative coqdep expansion."""

    work = [entry.resolve()]
    seen: set[Path] = set()
    out: list[Path] = []

    coq_root = (repo_root / "coq").resolve()

    while work:
        vf = work.pop()
        if vf in seen:
            continue
        seen.add(vf)
        out.append(vf)

        # Only expand within the Coq tree.
        try:
            vf.relative_to(coq_root)
        except Exception:
            continue

        for dep in _coqdep_direct_v_deps(repo_root=repo_root, entry=vf):
            if dep not in seen:
                work.append(dep)

    return out


def scan_files(v_files: list[Path]) -> list[Finding]:
    findings: list[Finding] = []
    for vf in v_files:
        try:
            raw = vf.read_text(encoding="utf-8")
        except Exception:
            continue
        text = strip_coq_comments(raw)
        for idx, line in enumerate(text.splitlines(), start=1):
            if TOKENS_RE.search(line):
                findings.append(Finding(file=vf, line=idx, snippet=line.strip()))
    return findings


def main() -> int:
    repo_root = Path(__file__).resolve().parents[1]
    entry = (repo_root / "coq" / "kernel_toe" / "TOE.v").resolve()
    if not entry.exists():
        print(f"ERROR: missing entry file: {entry}", file=sys.stderr)
        return 2

    try:
        deps = coqdep_transitive_v_deps(repo_root=repo_root, entry=entry)
    except Exception as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 2

    findings = scan_files(deps)
    if not findings:
        print("KERNELTOE AUDIT: OK")
        print(f"Scanned {len(deps)} .v files")
        return 0

    print("KERNELTOE AUDIT: FAIL")
    print(f"Findings: {len(findings)}")
    for f in findings[:200]:
        rel = f.file.relative_to(repo_root)
        print(f"- {rel}:L{f.line} {f.snippet}")
    if len(findings) > 200:
        print(f"... ({len(findings) - 200} more)")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
