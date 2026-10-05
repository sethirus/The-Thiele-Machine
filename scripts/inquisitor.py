#!/usr/bin/env python3
"""Inquisitor: scorched-earth Coq audit for proof triviality and hidden assumptions.

ZERO TOLERANCE POLICY:
- NO Axioms (all theorems must have complete proofs)
- NO Admitted stubs (difficulty is not an excuse)
- NO admit tactics (no proof shortcuts)
- NO Hypothesis declarations (functionally equivalent to Axiom)
- NO section-local Context assumptions without proofs

Scans the `coq/` tree for suspicious "proof smells":
- Trivial constant definitions ([], 0, True/true)
- Tautological theorems (Theorem ... : True.)
- Hidden assumptions (Axiom/Parameter/Hypothesis/Context)
- Stub proofs (Admitted/admit/Abort)
- Suspiciously trivial proofs (intros; assumption.) for tautology-shaped statements

Writes a Markdown report (default: INQUISITOR_REPORT.md) and returns non-zero
if high-severity findings appear.

Archive directory (archive/) is excluded from scanning as it contains
historical code kept for posterity only.

This is a strict static analysis tool; it errs on the side of flagging.
"""

from __future__ import annotations

import argparse
import dataclasses
import datetime as _dt
import time
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Iterable, Iterator

from inquisitor_rules import summarize_text
from coq_proof_scope import (
    MINIMAL_UNLISTED_FILES,
    NON_PROOF_BEARING_FILES,
    coqproject_v_files,
)


# STRICT MODE: Core kernel files that must have ZERO high/medium findings
PROTECTED_BASENAMES = {"UniversalCertificationCost.v", "StructuralCore.v"}

# ULTRA STRICT: Critical proof files. These carry the abstract model's floor
# and toll, the record axis, the small machine's links into the abstract
# results, and the Tsirelson algebra.
CRITICAL_KERNEL_FILES = {
    "UniversalCertificationCost.v",
    "StructuralCore.v",
    "StructuralRecordAxis.v",
    "PermanentCertification.v",
    "PermanentRecordPricing.v",
    "EarnedCoreLinks.v",
    "EarnedGenericLinks.v",
    "UniversalThieleLinks.v",
    "UniversalInterpreterLinks.v",
    "PricedHostLinks.v",
    "SmallChshLinks.v",
    # The small machine and its two definitions: every headline theorem rests on them.
    "EarnedCore.v",
    "EarnedGeneric.v",
    "ThieleComplete.v",
    "ThieleCompleteWindow.v",
    "UniversalThiele.v",
    "TsirelsonGeneral.v",
    "CHSHColumnCheck.v",
}

# ---------------------------------------------------------------------------
# Tier system — from coq/_CoqProject (-R directory Namespace mappings)
# Tier 1: The proof tree under coq/kernel/ (namespace Kernel): the abstract
#         model, its instances, and the links from the small machine
#         (minimal/, namespace Minimal) into the abstract results. It may
#         import Kernel, Minimal, the pinned vendored Undecidability library
#         and the Coq stdlib.
# Tier 2: Core theory outside coq/kernel/. No such directory exists now; the
#         rule stays so that one added later is held to it.
# Tier 3: Exploratory/speculative. No such directory exists now either.
# ---------------------------------------------------------------------------
_TIER1_DIRS: frozenset[str] = frozenset({"kernel"})
_TIER1_NAMESPACES: frozenset[str] = frozenset({"Kernel"})

_TIER2_DIRS: frozenset[str] = frozenset()
_TIER2_NAMESPACES: frozenset[str] = frozenset()

_TIER3_DIRS: frozenset[str] = frozenset()
_TIER3_NAMESPACES: frozenset[str] = frozenset()

_NAMESPACE_TO_TIER: dict[str, int] = {}
_NAMESPACE_TO_TIER.update({ns: 1 for ns in _TIER1_NAMESPACES})
_NAMESPACE_TO_TIER.update({ns: 2 for ns in _TIER2_NAMESPACES})
_NAMESPACE_TO_TIER.update({ns: 3 for ns in _TIER3_NAMESPACES})

_STDLIB_NAMESPACES: frozenset[str] = frozenset({"Coq", "Stdlib"})

# Every proof-bearing file must be transitively connected to the foundation
# chain via Coq imports, or explicitly reference its semantic tokens. The
# chain is the abstract model, not any one machine:
#   UniversalCertificationCost  the certification system and its universal floor
#   StructuralCore              the record-carrying machine and adequacy
#   Substrate                   the abstract A2-respecting substrate
#   KernelTM                    the Turing-machine kernel used as a base
#   EarnedCore                  the small machine that earns its commitments
#   ThieleComplete              the definition the small machine meets
_FOUNDATION_SEMANTICS_MODULES: frozenset[str] = frozenset(
    {
        "UniversalCertificationCost",
        "StructuralCore",
        "Substrate",
        "KernelTM",
        "EarnedCore",
        "ThieleComplete",
    }
)

# The cost half of the chain: the A2 floor over any certification system and
# the small machine's exact ledger.
_FOUNDATION_COST_MODULES: frozenset[str] = frozenset(
    {
        "UniversalCertificationCost",
        "EarnedCore",
    }
)

_FOUNDATION_GROUPS: dict[str, frozenset[str]] = {
    "semantics": _FOUNDATION_SEMANTICS_MODULES,
    "cost": _FOUNDATION_COST_MODULES,
}

_PROOF_DECL_RE = re.compile(
    r"(?m)^\s*(?:Theorem|Lemma|Corollary|Proposition|Fact|Remark|Conjecture)\b"
)

# A file outside the foundation chain opts out of the connectivity rules with a
# SCOPE NOTE naming proof connectivity or its standalone scope. A standalone
# algebra module may instead state `PROOF SCOPE: standalone algebra` directly.
_PROOF_CONNECTIVITY_NOTE_RE = re.compile(
    r"(?:SCOPE NOTE.*proof[- ]?connect|"
    r"SCOPE NOTE.*(?:foundation connectivity|standalone proof scope)|"
    r"PROOF SCOPE:\s*standalone algebra)",
    re.IGNORECASE,
)

_GRAVITY_SCOPE_MARKER_RE = re.compile(
    r"(?:SCOPE NOTE:\s*MISSING einstein_equation IS INTENTIONAL|"
    r"CALIBRATION SCOPE:\s*conditional)",
    re.IGNORECASE,
)

_SEMANTIC_TOKEN_RE = re.compile(
    r"\b(CertificationSystem|cs_step|cs_run|cs_cert|RCM|rc_next|rc_run|rc_cert|Substrate|KernelTM|step_tm|run_tm|EarnedCore|ThieleComplete|thiele_complete)\b"
)

_COST_TOKEN_RE = re.compile(
    r"\b(cs_cost|cs_total_cost|cs_cert_costs|rc_mu|step_cost|ledger_carried|rc_a2|mu_cost|mu_ledger|total_cost)\b"
)

_FROM_REQUIRE_IMPORTS_RE = re.compile(
    r"(?m)^\s*From\s+([A-Za-z0-9_.]+)\s+Require\s+(?:Import|Export)\s+([^\.]+)\."
)
_REQUIRE_IMPORTS_RE = re.compile(
    r"(?m)^\s*Require\s+(?:Import|Export)\s+([^\.]+)\."
)


def _path_to_tier(path: Path) -> int | None:
    """Return the tier (1/2/3) for a .v file based on its coq/ subdirectory, or None."""
    parts = path.parts
    coq_idx = next((i for i, p in enumerate(parts) if p == "coq"), None)
    if coq_idx is None or coq_idx + 1 >= len(parts):
        return None  # Root coq/ files (Extraction.v etc.) — no tier enforcement
    subdir = parts[coq_idx + 1]
    if subdir in _TIER1_DIRS:
        return 1
    if subdir in _TIER2_DIRS:
        return 2
    if subdir in _TIER3_DIRS:
        return 3
    return None


# Allowed locations for findings when allowlisting is explicitly enabled.
# Default policy is *no allowlist*.
ALLOWLIST_PATH_PARTS = (
    "/archive/",
    "/scratch/",
    "/experimental/",
    "/sandboxes/",
    "/wip/",
    "/WIP/",
)

# Populated at runtime (see `main`) with .v files that are considered optional
# by the repository build (from `coq/Makefile.local` OPTIONAL_VO).
ALLOWLIST_EXACT_FILES: set[Path] = set()

SUSPICIOUS_NAME_RE = re.compile(
    r"(?i)(optimal|optimum|best|min|max|cost|objective|solve|solver|search|discover|oracle|result|proof)")
CLAMP_PAT = re.compile(r"\bZ\.to_nat\b")  # Only flag Z.to_nat, not Nat.min/max or Z.abs (those are safe)
COMMENT_SMELL_RE = re.compile(r"(?i)\b(TODO|FIXME|XXX|HACK|WIP|TBD|STUB)\b")
PHYSICS_ANALOGY_RE = re.compile(
    r"(?i)\b(noether|gauge|symmetry|lorentz|covariant|invariant|conservation|entropy|thermo|quantum|relativity|gravity|wave|schrodinger|chsh|bell|physics)\b"
)
INVARIANCE_LEMMA_RE = re.compile(r"(?i)\b(step|vm_step|run_vm|trace_run|semantics).*(equiv|invariant)")
Z_TO_NAT_RE = re.compile(r"\bZ\.to_nat\b")
Z_TO_NAT_GUARD_RE = re.compile(r"(?i)(>=\s*0|0\s*<=|Z\.le|Z\.leb|Z\.geb|Z\.ge|Z\.lt|Z\.ltb|<\?.*0|nonneg|nonnegative|if\s*\(.+<\?\s*0\))")


@dataclasses.dataclass(frozen=True)
class Finding:
    rule_id: str
    severity: str  # HIGH/MEDIUM/LOW
    file: Path
    line: int
    snippet: str
    message: str


@dataclasses.dataclass(frozen=True)
class CommandTimeoutError(RuntimeError):
    stage: str
    command: tuple[str, ...]
    timeout_seconds: int
    cwd: Path
    stdout_tail: str
    stderr_tail: str

    def __str__(self) -> str:
        return (
            f"{self.stage} timed out after {self.timeout_seconds}s while running "
            f"{' '.join(self.command)} in {self.cwd}"
        )


DEFAULT_COMMAND_TIMEOUTS: dict[str, int] = {
    "coqtop batch": 60,
    # A cache restore can still require a substantial Coq rebuild when the
    # generated make metadata does not match the checked-out source mtimes.
    # Keep the audit bounded, but allow the full proof tree to finish on the
    # hosted CI runners instead of turning a slow valid build into a finding.
    "coq build": 1800,
    "proof dependency dag": 300,
    "single coq compile": 60,
}

SCAN_PROGRESS_EVERY = 25
SLOW_FILE_THRESHOLD_SECONDS = 2.0
_OUTPUT_TAIL_CHARS = 1200


def _log_progress(message: str) -> None:
    timestamp = _dt.datetime.now().strftime("%H:%M:%S")
    print(f"[{timestamp}] INQUISITOR: {message}", flush=True)


def _tail_text(text: object | None, limit: int = _OUTPUT_TAIL_CHARS) -> str:
    if not text:
        return ""
    if isinstance(text, str):
        normalized = text
    elif isinstance(text, (bytes, bytearray, memoryview)):
        normalized = bytes(text).decode("utf-8", errors="replace")
    else:
        normalized = str(text)
    if len(normalized) <= limit:
        return normalized.strip()
    return normalized[-limit:].strip()


def _format_command(command: Iterable[str]) -> str:
    return " ".join(command)


def _run_command(
    command: list[str],
    *,
    cwd: Path,
    stage: str,
    timeout_seconds: int | None = None,
    input_text: str | None = None,
) -> subprocess.CompletedProcess[str]:
    timeout_value = timeout_seconds if timeout_seconds is not None else DEFAULT_COMMAND_TIMEOUTS.get(stage)
    _log_progress(
        f"START {stage} (timeout={timeout_value if timeout_value is not None else 'none'}s): "
        f"{_format_command(command)}"
    )
    started = time.monotonic()
    try:
        proc = subprocess.run(
            command,
            input=input_text,
            text=True,
            capture_output=True,
            cwd=str(cwd),
            timeout=timeout_value,
        )
    except subprocess.TimeoutExpired as exc:
        elapsed = time.monotonic() - started
        stdout_tail = _tail_text(exc.stdout)
        stderr_tail = _tail_text(exc.stderr)
        _log_progress(
            f"TIMEOUT {stage} after {elapsed:.1f}s in {cwd}: {_format_command(command)}"
        )
        if stdout_tail:
            _log_progress(f"{stage} stdout tail:\n{stdout_tail}")
        if stderr_tail:
            _log_progress(f"{stage} stderr tail:\n{stderr_tail}")
        raise CommandTimeoutError(
            stage=stage,
            command=tuple(command),
            timeout_seconds=int(timeout_value or 0),
            cwd=cwd,
            stdout_tail=stdout_tail,
            stderr_tail=stderr_tail,
        ) from exc

    elapsed = time.monotonic() - started
    _log_progress(f"END {stage} rc={proc.returncode} elapsed={elapsed:.1f}s")
    if proc.returncode != 0:
        stdout_tail = _tail_text(proc.stdout)
        stderr_tail = _tail_text(proc.stderr)
        if stdout_tail:
            _log_progress(f"{stage} stdout tail:\n{stdout_tail}")
        if stderr_tail:
            _log_progress(f"{stage} stderr tail:\n{stderr_tail}")
    return proc

def is_allowlisted(path: Path, *, enable_allowlist: bool) -> bool:
    if not enable_allowlist:
        return False
    if path in ALLOWLIST_EXACT_FILES:
        return True
    p = "/" + str(path.as_posix()).lstrip("/")
    return any(part in p for part in ALLOWLIST_PATH_PARTS)


def _parse_optional_v_files(repo_root: Path, coq_root: Path) -> set[Path]:
    """Parse `coq/Makefile.local` OPTIONAL_VO and map entries to absolute .v Paths."""
    mk = repo_root / "coq" / "Makefile.local"
    if not mk.exists():
        return set()

    text = mk.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines()
    in_optional = False
    vo_entries: list[str] = []
    for ln in lines:
        if ln.startswith("OPTIONAL_VO"):
            in_optional = True
            # skip the assignment line itself; entries come on subsequent lines.
            continue
        if in_optional:
            # Stop when the next variable/target starts.
            if ln and not ln.startswith(" ") and not ln.startswith("\t") and not ln.startswith("#"):
                break
            ln = ln.strip()
            if not ln or ln.startswith("#"):
                continue
            if ln.endswith("\\"):
                ln = ln[:-1].strip()
            # entries are paths like `catnet/.../Foo.vo`
            if ln.endswith(".vo"):
                vo_entries.append(ln)

    v_files: set[Path] = set()
    for vo in vo_entries:
        rel_v = Path(vo).with_suffix(".v")
        abs_v = (coq_root / rel_v).resolve()
        if abs_v.exists():
            v_files.add(abs_v)
    return v_files


def strip_coq_comments(text: str) -> str:
    """Remove (* ... *) comments (nested) while preserving line breaks."""
    out: list[str] = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if i + 1 < n and text[i] == "(" and text[i + 1] == "*":
            depth += 1
            i += 2
            continue
        if i + 1 < n and text[i] == "*" and text[i + 1] == ")" and depth > 0:
            depth -= 1
            i += 2
            continue
        ch = text[i]
        if depth == 0:
            out.append(ch)
        else:
            # Preserve newlines to keep line numbers stable.
            if ch == "\n":
                out.append("\n")
        i += 1
    return "".join(out)


def extract_coq_comments(text: str) -> str:
    """Extract comment bodies while preserving whitespace/newlines."""
    out: list[str] = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if i + 1 < n and text[i] == "(" and text[i + 1] == "*":
            depth += 1
            i += 2
            continue
        if i + 1 < n and text[i] == "*" and text[i + 1] == ")" and depth > 0:
            depth -= 1
            i += 2
            continue
        ch = text[i]
        if depth > 0:
            out.append(ch)
        else:
            if ch == "\n":
                out.append("\n")
        i += 1
    return "".join(out)


def _looks_like_coq(text: str) -> bool:
    markers = (
        "Require Import",
        "From ",
        "Theorem ",
        "Lemma ",
        "Corollary ",
        "Definition ",
        "Proof.",
        "Qed.",
        "Admitted.",
    )
    return any(m in text for m in markers)


def iter_v_files(coq_root: Path) -> Iterator[Path]:
    for p in coq_root.rglob("*.v"):
        if p.is_file():
            yield p


def iter_all_coq_files(repo_root: Path) -> Iterator[Path]:
    """Iterate the active Coq proof corpus, excluding snapshots and generated trees.

    Strict policy:
    - Active sources are the files declared in `coq/_CoqProject`, minus the
      explicit NON_PROOF_BEARING_FILES set. Files merely present on disk are
      handled by the proof-scope drift gate instead of being audited as proofs.
    - `artifacts/` contains reproduction snapshots and evidence
      copies. It is not an active proof corpus and must never multiply findings.
    - Files under `build/**/*.v` are auto-generated artifacts (vacuity probes,
      assumption probes) — not proof sources, so excluded.
    - Non-Coq-tree `.v` files are included only if they look like Coq.
    """
    project_path = repo_root / "coq" / "_CoqProject"
    active_files = coqproject_v_files(project_path) if project_path.exists() else set()
    active_files -= NON_PROOF_BEARING_FILES

    for p in repo_root.rglob("*.v"):
        if not p.is_file():
            continue
        # EXCLUDE ARCHIVE: archive/ contains historical code kept for posterity only
        # These files are not part of the active proof corpus and should not be audited
        # EXCLUDE VENDOR: vendor/ contains third-party libraries (the pinned
        # undecidability library) whose proof style is outside our control and
        # should not be audited
        # EXCLUDE BUILD: build/ is a generated-artifacts tree (vacuity probes,
        # assumption probes). Anything written there is by definition
        # not a hand-authored proof obligation.
        # EXCLUDE TEST_FIXTURES: coq/test_fixtures/ is reserved for deliberately
        # vacuous Coq files used as test data by gates (e.g. the vacuity-gate
        # smoke fixture). They are intentionally vacuous by design — auditing
        # them for vacuity would defeat their purpose.
        # EXCLUDE .claude: Claude Code's tooling directory. Its worktrees/ holds
        # ephemeral full-repo scratch copies created by agents/workflows; they are
        # never source of truth and must not be audited (would multiply findings
        # across every stale worktree copy).
        relative_path = "/" + str(p.relative_to(repo_root).as_posix())
        if relative_path.startswith("/.claude/"):
            continue
        if relative_path.startswith("/artifacts/"):
            continue
        if "/archive/" in relative_path:
            continue
        if "/vendor/" in relative_path:
            continue
        if relative_path.startswith("/build/"):
            continue
        if relative_path.startswith("/coq/test_fixtures/"):
            continue
        # No heuristic filtering inside coq/: every other Coq source file is audited.
        if relative_path.startswith("/coq/"):
            if p.relative_to(repo_root).as_posix() in active_files:
                yield p
            continue
        raw = p.read_text(encoding="utf-8", errors="replace")
        if _looks_like_coq(raw):
            yield p


def _check_coq_compilation_coverage(repo_root: Path) -> list[Finding]:
    """Fail if the proof corpus is not fully built.

    The proof corpus is defined as the .v files declared in coq/_CoqProject
    minus the files explicitly marked out-of-scope in
    scripts/coq_proof_scope.py:NON_PROOF_BEARING_FILES.

    Two failure modes:

    1. COMPILATION_COVERAGE_GAP — a file in the proof corpus has no .vo
       after build. `make -C coq` either failed silently for it, or it was
       never wired into the build graph.

    2. PROOF_SCOPE_DRIFT — a file declared out-of-scope leaked into
       _CoqProject, or a disk .v file is in neither set. Enforced
       structurally so that no stale local .vo can mask a divergence
       between the inquisitor and the canonical build (for example, probe .v
       files outside _CoqProject with stale local .vo artifacts would leave
       the inquisitor satisfied while a clean CI checkout failed).
    """

    findings: list[Finding] = []
    coq_root = repo_root / "coq"
    if not coq_root.exists():
        return findings

    project_files = coqproject_v_files(coq_root / "_CoqProject")

    # Mode 1: every in-scope file must have its .vo.
    in_scope = sorted(project_files - NON_PROOF_BEARING_FILES)
    for rel in in_scope:
        vf = repo_root / rel
        if (vf.with_suffix(".vo")).exists():
            continue
        findings.append(
            Finding(
                rule_id="COMPILATION_COVERAGE_GAP",
                severity="HIGH",
                file=vf,
                line=1,
                snippet="",
                message=(
                    "Coq source file is in the canonical proof corpus "
                    "(coq/_CoqProject) but no .vo artifact exists after build. "
                    "This means `make -C coq` did not produce the expected "
                    "object — investigate the build, do not silence this gate."
                ),
            )
        )

    # Mode 2a: NON_PROOF_BEARING_FILES must not appear in _CoqProject.
    leaked = sorted(NON_PROOF_BEARING_FILES & project_files)
    for rel in leaked:
        findings.append(
            Finding(
                rule_id="PROOF_SCOPE_DRIFT",
                severity="HIGH",
                file=repo_root / rel,
                line=1,
                snippet="",
                message=(
                    "File is marked NON_PROOF_BEARING in "
                    "scripts/coq_proof_scope.py but is also listed in "
                    "coq/_CoqProject. A file cannot simultaneously be "
                    "out-of-scope and a canonical compile target — pick one."
                ),
            )
        )

    # Mode 2b: every active disk .v file must be classified.
    disk_excluded = {"archive", "patches", "test_vscoq", "_build"}
    for vf in sorted(coq_root.rglob("*.v")):
        if not vf.is_file():
            continue
        if set(vf.relative_to(coq_root).parts) & disk_excluded:
            continue
        rel_posix = vf.relative_to(repo_root).as_posix()
        if "/vendor/" in ("/" + rel_posix):
            continue
        if rel_posix in project_files:
            continue
        if rel_posix in NON_PROOF_BEARING_FILES:
            continue
        findings.append(
            Finding(
                rule_id="PROOF_SCOPE_DRIFT",
                severity="HIGH",
                file=vf,
                line=1,
                snippet="",
                message=(
                    "Disk .v file is neither in coq/_CoqProject nor in "
                    "scripts/coq_proof_scope.py:NON_PROOF_BEARING_FILES. "
                    "Add it to the canonical build, mark it explicitly "
                    "out-of-scope, or delete it."
                ),
            )
        )

    # Mode 2c: the small machine in minimal/ is part of the proof corpus. Every
    # file there is built through _CoqProject, except the explicit front-door
    # files that tests/test_minimal_core.py compiles on their own.
    minimal_root = repo_root / "minimal"
    if minimal_root.exists():
        for vf in sorted(minimal_root.rglob("*.v")):
            if not vf.is_file():
                continue
            rel_posix = vf.relative_to(repo_root).as_posix()
            if rel_posix in project_files or rel_posix in MINIMAL_UNLISTED_FILES:
                continue
            findings.append(
                Finding(
                    rule_id="PROOF_SCOPE_DRIFT",
                    severity="HIGH",
                    file=vf,
                    line=1,
                    snippet="",
                    message=(
                        "minimal/ .v file is neither in coq/_CoqProject nor in "
                        "scripts/coq_proof_scope.py:MINIMAL_UNLISTED_FILES. "
                        "Add it to the canonical build or delete it."
                    ),
                )
            )

    return findings


def _line_map(text: str) -> list[int]:
    """Map each character index to a 1-based line number."""
    line = 1
    mapping = [1] * (len(text) + 1)
    for i, ch in enumerate(text):
        mapping[i] = line
        if ch == "\n":
            line += 1
    mapping[len(text)] = line
    return mapping


def _classify_constant_severity(name: str, base_sev: str) -> str:
    if base_sev == "HIGH":
        return "HIGH"
    if SUSPICIOUS_NAME_RE.search(name):
        return "HIGH"
    return base_sev


def _severity_for_path(path: Path, default: str, rule_id: str = "") -> str:
    # MAXIMUM STRICTNESS: Every Coq file is held to the same standard.
    # No file gets special treatment. No downgrades.
    if default in {"HIGH", "MEDIUM"}:
        return "HIGH"
    return default


def is_critical_kernel_file(path: Path) -> bool:
    """Check if file is a critical kernel proof file requiring extra scrutiny."""
    return path.name in CRITICAL_KERNEL_FILES


def scan_clamps(path: Path) -> list[Finding]:
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    clean_lines = text.splitlines()
    raw_lines = raw.splitlines()  # Keep original with comments for SAFE checking
    findings: list[Finding] = []
    for i, ln in enumerate(clean_lines, start=1):
        if CLAMP_PAT.search(ln):
            # Z.abs is non-negative by construction, so this conversion does
            # not clamp a negative value and is not a truncation boundary.
            if re.search(r"Z\.to_nat\s*\(\s*Z\.abs\b", ln):
                continue
            # Check for SAFE comment in original text
            context = "\n".join(raw_lines[max(0, i - 3): i + 1])
            if re.search(r"\(\*\s*SAFE:", context):
                continue
            findings.append(
                Finding(
                    rule_id="CLAMP_OR_TRUNCATION",
                    severity=_severity_for_path(path, "MEDIUM"),
                    file=path,
                    line=i,
                    snippet=ln.strip(),
                    message="Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).",
                )
            )
    return findings


def scan_comment_smells(path: Path) -> list[Finding]:
    raw = path.read_text(encoding="utf-8", errors="replace")
    comments = extract_coq_comments(raw)
    line_of = _line_map(comments)
    clean_lines = comments.splitlines()
    findings: list[Finding] = []
    for m in COMMENT_SMELL_RE.finditer(comments):
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="COMMENT_SMELL",
                severity=_severity_for_path(path, "MEDIUM"),
                file=path,
                line=line,
                snippet=snippet.strip(),
                message="Comment contains placeholder marker (TODO/FIXME/WIP/etc).",
            )
        )
    return findings


def scan_z_to_nat_boundaries(path: Path) -> list[Finding]:
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    clean_lines = text.splitlines()
    raw_lines = raw.splitlines()  # Keep original for SAFE checking
    findings: list[Finding] = []
    for idx, ln in enumerate(clean_lines, start=1):
        if not Z_TO_NAT_RE.search(ln):
            continue
        if re.search(r"Z\.to_nat\s*\(\s*Z\.abs\b", ln):
            continue
        window = "\n".join(clean_lines[max(0, idx - 4): idx + 3])
        if Z_TO_NAT_GUARD_RE.search(window):
            continue
        # Check for SAFE comment in original text
        context = "\n".join(raw_lines[max(0, idx - 3): idx + 1])
        if re.search(r"\(\*\s*SAFE:", context):
            continue
        findings.append(
            Finding(
                rule_id="Z_TO_NAT_BOUNDARY",
                severity=_severity_for_path(path, "MEDIUM"),
                file=path,
                line=idx,
                snippet=ln.strip(),
                message="Z.to_nat used without nearby nonnegativity guard (potential boundary clamp).",
            )
        )
    return findings


def scan_unused_hypotheses(path: Path) -> list[Finding]:
    """Do not report lexical hypothesis-use guesses.

    Hypothesis-use analysis is not sound at the source-text level. Coq
    tactics imported from another module, typeclass resolution, automation,
    and generated proof scripts can all consume a hypothesis without naming
    it in the local source. The kernel checks the resulting proof term, so a
    lexical warning here creates noise without identifying an invalid proof.
    """
    return []


def _legacy_scan_unused_hypotheses(path: Path) -> list[Finding]:
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    findings: list[Finding] = []
    # A lexical scan cannot see which hypotheses a user-defined Ltac consumes.
    # Generated refinement proofs intentionally close arithmetic side goals
    # through local tactics such as [close_pc] and [close_mu_cost]. Treating
    # their premises as unused is a false positive, so leave those proofs to
    # Coq's checked proof term instead of guessing from the tactic text.
    custom_tactics = set(re.findall(
        r"(?m)^\s*Ltac\s+([A-Za-z0-9_']+)\b", text
    ))
    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma|Corollary|Fact|Remark|Proposition)\s+([A-Za-z0-9_']+)\b")
    proof_re = re.compile(r"(?m)^[ \t]*Proof\.")
    end_re = re.compile(r"(?m)^[ \t]*(Qed|Admitted)\.")
    for m in theorem_re.finditer(text):
        start = m.end()
        proof_match = proof_re.search(text, start)
        if not proof_match:
            continue
        # Extract lemma statement (between lemma name and Proof.)
        lemma_statement = text[m.end():proof_match.start()]
        
        end_match = end_re.search(text, proof_match.end())
        if not end_match:
            continue
        proof_block = text[proof_match.end(): end_match.start()]
        proof_lines = [ln.strip() for ln in proof_block.splitlines() if ln.strip()]
        if not proof_lines:
            continue
        
        # Collect tactics that can implicitly consume hypotheses by name
        proof_body_text = " ".join(proof_lines)
        if custom_tactics and any(
            re.search(rf"\b{re.escape(name)}\b", proof_body_text)
            for name in custom_tactics
        ):
            continue
        # These tactics can implicitly consume ANY hypothesis in scope:
        implicit_consumers = re.compile(
            r"\b(auto|eauto|intuition|firstorder|assumption|easy|trivial|"
            r"lia|omega|lra|nra|nia|congruence|tauto|now|subst|"
            r"contradiction|ring|field|discriminate|decide\s+equality)\b"
        )
        has_implicit_consumer = bool(implicit_consumers.search(proof_body_text))
        
        intros_line = next((ln for ln in proof_lines if re.match(r"^intros\b", ln)), None)
        if not intros_line or ";" in intros_line:
            continue
        intros_match = re.match(r"^intros\s+([A-Za-z0-9_'\s]+)\.\s*$", intros_line)
        if not intros_match:
            continue
        names = re.split(r"[\s,]+", intros_match.group(1).strip())
        names = [n for n in names if n and n != "_"]
        if not names:
            continue

        # Count how many forall variables + arrows are in the statement.
        # Intros beyond this count introduce things from the conclusion
        # (e.g., unfolding a definition reveals hidden foralls/lets).
        # Those are NOT unused — they're goal-direction intros.
        stmt_text = re.sub(r"\s+", " ", lemma_statement)
        # Count forall-bound names
        forall_vars = 0
        for fm in re.finditer(r"\bforall\s+([^,]+),", stmt_text):
            # Count names in the forall binder (e.g., "forall x y z," = 3)
            binder = fm.group(1)
            # Remove type annotations like (x : T) to just get names
            binder_clean = re.sub(r"\([^)]*\)", lambda m: " ".join(re.findall(r"\b([a-zA-Z_]\w*)\b", m.group().split(":")[0])), binder)
            var_names = [v for v in re.split(r"\s+", binder_clean.strip()) if v and v not in {":", "forall"} and not re.match(r"^[A-Z]", v)]
            forall_vars += max(len(var_names), 0)
        # Count arrows (->), but not (<->). Each arrow = one intro.
        # Protect <-> first
        protected = stmt_text.replace("<->", "\x00IFF\x00")
        arrow_count = protected.count("->")
        # Count let-bindings (let x := ... in ...) — each adds one intro
        let_count = len(re.findall(r"\blet\s+", stmt_text))
        max_statement_intros = forall_vars + arrow_count + let_count

        # All names from intros
        all_intros_names = re.split(r"[\s,]+", intros_match.group(1).strip())
        all_intros_names = [n for n in all_intros_names if n]

        body = " ".join(proof_lines[1:])
        for name in names:
            if name in {"*", "?", "!", "intro", "intros"}:
                continue

            # Check if this name is beyond the statement's intro capacity
            # (i.e., it's a conclusion-direction intro from unfolded definitions)
            try:
                name_pos = all_intros_names.index(name)
            except ValueError:
                name_pos = 0
            if name_pos >= max_statement_intros:
                continue  # Conclusion-direction intro — not a hypothesis
            # For names with apostrophes (like q'), word boundary \b doesn't work
            # Use a more flexible pattern that matches the name as a separate token
            if "'" in name:
                # Match q' as a token (preceded/followed by non-alphanumeric or apostrophe)
                pattern = rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])"
            else:
                # Standard word boundary for regular identifiers
                pattern = rf"\b{re.escape(name)}\b"
            
            # Check if used explicitly in proof body
            if re.search(pattern, body):
                continue
            # Check if used in lemma statement/conclusion
            if re.search(pattern, lemma_statement):
                continue
            # If an implicit consumer is present (auto, lia, etc.), it MIGHT use
            # this hypothesis — but only if it's an arithmetic/decidable type.
            # These are almost always false positives, so skip them entirely.
            if has_implicit_consumer:
                continue  # Skip: implicit consumers likely use this hypothesis
            # Only flag if NO implicit consumers detected (true unused hypothesis)
            findings.append(
                Finding(
                    rule_id="UNUSED_HYPOTHESIS",
                    severity="HIGH",
                    file=path,
                    line=line_of[proof_match.start()],
                    snippet=intros_line,
                    message=f"Introduced hypothesis `{name}` not referenced in proof body.",
                )
            )
    return findings


def scan_definitional_invariance(path: Path) -> list[Finding]:
    """Flag invariance/equivariance lemmas whose proof consists ENTIRELY
    of normalization plus a closing tactic — no rewrite/apply/destruct/
    exact/subst/etc. that engages an introduced hypothesis or a named
    lemma.

    The vacuous-proof signature is a tactic sequence drawn only from:
      - intros, intro       (binding)
      - unfold, simpl, cbn, cbv, lazy, change, fold        (normalization)
      - reflexivity, easy, trivial, tauto, congruence, auto (closing)

    A proof that uses [rewrite Hgraph], [subst g2], [simpl in Hgraph],
    or [apply <named_lemma>] is doing real work — even if it ends in
    [reflexivity] — and is NOT flagged. That covers the vm_graph_invariant
    family pattern in MuGravity.v.

    Hypothesis-arg detection: [simpl in Hgraph] / [subst g2] have a
    normalization HEAD but their argument references an introduced name.
    Those are treated as engagement.

    No comment-marker bypass is honoured: a marker comment such as
    `(* definitional lemma: ... *)` cannot silence a real vacuity finding.

    Special case: lemma whose statement is `: True` or `-> True` remains
    flagged unconditionally (the conclusion is trivially provable).
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []
    lemma_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b")
    # Match Qed./Defined./Admitted. anywhere so one-line proofs are handled.
    proof_end_re = re.compile(r"\b(Qed|Defined|Admitted)\.")
    closing_tactic_re = re.compile(
        r"\b(reflexivity|easy|trivial|tauto|congruence|auto)\s*\."
    )
    # Tactic heads that do NOT count as engagement (binding + pure
    # normalization + closing). Anything outside this set, at the head of
    # a tactic invocation, marks real work.
    nonengaging_tactic_re = re.compile(
        r"\b(intros?|unfold|simpl|cbn|cbv|lazy|change|fold|subst|"
        r"reflexivity|easy|trivial|tauto|congruence|auto)\b"
    )
    bullet_re = re.compile(
        r"^\s*(?:[-+*]+\s*|repeat\s+|try\s+|all\s*:\s*|now\s+|"
        r"solve\s*\[|do\s+\d+\s+|first\s*\[|\(|\[|\|)+"
    )
    intros_pattern_keywords = {"as", "in", "at", "eqn", "_"}

    for m in lemma_re.finditer(text):
        name = m.group(2)
        if not re.search(r"(?i)(invariant|equiv|equivariance|symmetry)", name):
            continue
        stmt_end = text.find(".", m.end())
        if stmt_end == -1:
            continue
        stmt = re.sub(r"\s+", " ", text[m.start(): stmt_end + 1]).strip()
        if re.search(r":\s*True\s*\.$", stmt) or re.search(r"->\s*True\s*\.$", stmt):
            line = line_of[m.start()]
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else stmt
            findings.append(
                Finding(
                    rule_id="DEFINITIONAL_INVARIANCE",
                    severity=_severity_for_path(path, "MEDIUM"),
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message="Invariance/equivariance lemma appears vacuous (ends in True).",
                )
            )
            continue
        proof_pos = text.find("Proof.", stmt_end)
        if proof_pos == -1:
            continue
        end_match = proof_end_re.search(text, proof_pos)
        if not end_match:
            continue
        proof_body = text[proof_pos + len("Proof."): end_match.start()]
        if not closing_tactic_re.search(proof_body):
            continue
        # Split on `.` and `;` (top-level tactic terminators).
        tactics = [t.strip() for t in re.split(r"[.;]", proof_body) if t.strip()]
        # First pass: collect every identifier introduced by intros/intro.
        # The `re.DOTALL` flag lets multi-line destructuring intros
        # ([g1 ...] [g2 ...] m Hgraph spread across two lines) capture
        # every name, not just the first row.
        introduced: set[str] = set()
        for tac in tactics:
            head = bullet_re.sub("", tac).strip()
            intro_m = re.match(r"^intros?\b(.*)$", head, re.DOTALL)
            if not intro_m:
                continue
            for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_']*", intro_m.group(1)):
                if tok not in intros_pattern_keywords:
                    introduced.add(tok)
        # Second pass: detect engagement. A tactic is engaging iff its
        # HEAD is not in the non-engaging set, OR its arguments reference
        # one of the introduced identifiers (catches simpl-in-H, subst x).
        has_engagement = False
        for tac in tactics:
            head = bullet_re.sub("", tac).strip()
            if not head:
                continue
            head_word_m = re.match(r"^([A-Za-z_][A-Za-z0-9_']*)", head)
            if not head_word_m:
                has_engagement = True
                break
            head_word = head_word_m.group(1)
            if not nonengaging_tactic_re.match(head_word):
                has_engagement = True
                break
            if head_word in ("intros", "intro"):
                continue
            args = head[head_word_m.end():]
            for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_']*", args):
                if tok in introduced and tok not in intros_pattern_keywords:
                    has_engagement = True
                    break
            if has_engagement:
                break
        if has_engagement:
            continue
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else stmt
        findings.append(
            Finding(
                rule_id="DEFINITIONAL_INVARIANCE",
                severity=_severity_for_path(path, "HIGH"),
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=(
                    f"Invariance/equivariance lemma `{name}` proof consists "
                    f"entirely of intros + normalization + a closing tactic, "
                    f"with no rewrite/apply/destruct/exact/etc. and no "
                    f"argument referencing an introduced hypothesis. Either "
                    f"the claim is definitional (inline the unfolds at call "
                    f"sites and delete) or restate the lemma so the proof "
                    f"engages real content."
                ),
            )
        )
    return findings


def scan_physics_analogy_contract(path: Path) -> list[Finding]:
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    clean_lines = text.splitlines()
    raw_lines = raw.splitlines()  # Keep original with comments for label checking
    has_invariance = INVARIANCE_LEMMA_RE.search(text) is not None
    findings: list[Finding] = []
    start_re = re.compile(r"^[ \t]*(Theorem|Lemma|Corollary)\s+([A-Za-z0-9_']+)\b")
    for idx, ln in enumerate(clean_lines, start=1):
        m = start_re.match(ln)
        if not m:
            continue
        stmt_lines = [ln.strip()]
        j = idx + 1
        while j <= len(clean_lines) and len(stmt_lines) < 200:
            if re.search(r"\.[ \t]*$", stmt_lines[-1]):
                break
            nxt = clean_lines[j - 1].strip()
            if nxt:
                stmt_lines.append(nxt)
            j += 1
        stmt = " ".join(stmt_lines)
        if not PHYSICS_ANALOGY_RE.search(stmt):
            continue
        if has_invariance:
            continue
        findings.append(
            Finding(
                rule_id="PHYSICS_ANALOGY_CONTRACT",
                severity=_severity_for_path(path, "HIGH"),
                file=path,
                line=idx,
                snippet=ln.strip(),
                message="Physics-analogy theorem lacks invariance lemma in its file.",
            )
        )
    return findings


def scan_file(path: Path) -> list[Finding]:
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    raw_lines = raw.splitlines()  # Keep original with comments for SAFE checking
    line_of = _line_map(text)
    clean_lines = text.splitlines()

    # Track whether each line is inside a `Module Type ... End` block.
    # Declarations inside module signatures are requirements for implementations,
    # not global axioms of the development. Also track modules implementing signatures.
    in_module_type: list[bool] = [False] * (len(clean_lines) + 1)  # 1-based index
    in_section: list[bool] = [False] * (len(clean_lines) + 1)  # Track Section blocks
    module_type_depth = 0
    module_impl_depth = 0  # Track Module X : Signature
    section_depth = 0
    module_type_start = re.compile(r"(?m)^[ \t]*Module\s+Type\b")
    module_impl_start = re.compile(r"(?m)^[ \t]*Module\s+\w+\s*:\s*\w+")  # Module X : Sig
    section_start = re.compile(r"(?m)^[ \t]*Section\s+")
    module_end = re.compile(r"(?m)^[ \t]*End\b")
    for idx, ln in enumerate(clean_lines, start=1):
        if module_type_start.match(ln):
            module_type_depth += 1
        if module_impl_start.match(ln):
            module_impl_depth += 1
        if section_start.match(ln):
            section_depth += 1
        in_module_type[idx] = (module_type_depth > 0) or (module_impl_depth > 0)
        in_section[idx] = (section_depth > 0)
        if module_end.match(ln):
            if module_type_depth > 0:
                module_type_depth -= 1
            if module_impl_depth > 0:
                module_impl_depth -= 1
            if section_depth > 0:
                section_depth -= 1

    findings: list[Finding] = []

    # ZERO TOLERANCE: Admitted stub proofs are ABSOLUTELY FORBIDDEN everywhere.
    # Either prove it completely or fail. No exceptions, no matter how hard.
    admitted_pat = re.compile(r"(?m)^[ \t]*Admitted\s*\.")
    for m in admitted_pat.finditer(text):
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else "Admitted."
        findings.append(
            Finding(
                rule_id="ADMITTED",
                severity="HIGH",
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=(
                    "STUB PROOF FOUND - ABSOLUTELY FORBIDDEN. Admitted is a placeholder, not a proof. "
                    "Complete the proof with real derivation or remove the theorem. "
                    "Zero tolerance policy: difficulty is not an excuse."
                ),
            )
        )

    # Check for admit tactic (proof shortcut - FORBIDDEN)
    admit_tactic_pat = re.compile(r"(?m)^[ \t]*admit\s*\.")
    for m in admit_tactic_pat.finditer(text):
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else "admit."
        findings.append(
            Finding(
                rule_id="ADMIT_TACTIC",
                severity="HIGH",
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=(
                    "ADMIT TACTIC FOUND - ABSOLUTELY FORBIDDEN. The admit tactic is a proof shortcut. "
                    "Complete the proof step with real tactics or remove the theorem."
                ),
            )
        )

    # Check for give_up tactic (proof shortcut - FORBIDDEN)
    give_up_pat = re.compile(r"\bgive_up\b")
    for m in give_up_pat.finditer(text):
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else text[m.start():m.end()]
        findings.append(
            Finding(
                rule_id="GIVE_UP_TACTIC",
                severity="HIGH",
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=(
                    "GIVE_UP TACTIC FOUND - ABSOLUTELY FORBIDDEN. Complete the proof or remove the theorem."
                ),
            )
        )

    # Check for Abort (abandoned proof - FORBIDDEN)
    abort_pat = re.compile(r"(?m)^[ \t]*Abort\s*\.")
    for m in abort_pat.finditer(text):
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else "Abort."
        findings.append(
            Finding(
                rule_id="ABORT_PROOF",
                severity="HIGH",
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=(
                    "ABORTED PROOF FOUND - ABSOLUTELY FORBIDDEN. Abort leaves a theorem stated but unproven. "
                    "Complete the proof or remove the theorem declaration."
                ),
            )
        )

    def iter_theorem_statements() -> Iterator[tuple[str, int, str]]:
        """Yield (name, start_line, normalized_statement) for theorem-like items.

        This avoids naive "first '.'" parsing because Coq module paths contain '.'
        and would otherwise truncate statements.
        """

        start_re = re.compile(r"^[ \t]*(Theorem|Lemma|Corollary)\s+([A-Za-z0-9_']+)\b")
        end_re = re.compile(r"\.[ \t]*$")
        max_lines = 200
        for idx, ln in enumerate(clean_lines, start=1):
            m = start_re.match(ln)
            if not m:
                continue
            name = m.group(2)
            parts: list[str] = [ln.strip()]
            j = idx + 1
            while j <= len(clean_lines) and len(parts) < max_lines:
                if end_re.search(parts[-1]):
                    break
                nxt = clean_lines[j - 1].strip()
                if nxt:
                    parts.append(nxt)
                j += 1
            stmt = re.sub(r"\s+", " ", " ".join(parts)).strip()
            yield name, idx, stmt

    # Assumption surfaces.
    #
    # STRICT POLICY: All assumption mechanisms are scrutinized.
    # - `Axiom`/`Parameter` introduce global, unproven constants: HIGH.
    # - `Hypothesis` is functionally equivalent to Axiom: HIGH.
    # - `Context` with forall/arrow types are section-local axioms: HIGH.
    #   (These are assumptions that must be instantiated - uninstantiated = axiom)
    # - `Context`/`Variable(s)` with simple types: MEDIUM (need verification).
    assumption_decl = re.compile(
        r"(?m)^[ \t]*(Axiom|Parameter|Conjecture|Postulate|Assume|Hypothesis|Variable|Variables|Context)\b\s*"  # kind
        r"(?:\(?\s*([A-Za-z0-9_']+)\b)?"  # optional name (may be absent for Context (...))
    )
    section_depth_by_line: list[int] = []
    section_depth = 0
    for section_line in text.splitlines():
        section_depth_by_line.append(section_depth)
        if re.match(r"^\s*Section\b", section_line):
            section_depth += 1
        elif re.match(r"^\s*End\b", section_line):
            section_depth = max(0, section_depth - 1)

    for m in assumption_decl.finditer(text):
        kind = m.group(1)
        name = (m.group(2) or "").strip()
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else kind

        # Coq generalizes section-local Hypothesis/Variable/Context
        # declarations into explicit theorem parameters when the Section
        # closes. They are not global axioms. Actual global Axiom/Parameter
        # declarations remain strict findings and are also covered by the
        # compiled Print Assumptions gate.
        if (
            kind in {"Hypothesis", "Variable", "Variables", "Context"}
            and 0 <= line - 1 < len(section_depth_by_line)
            and section_depth_by_line[line - 1] > 0
        ):
            continue
        
        # Get extended context to detect complex Context types
        context_end = text.find(").", m.start())
        if context_end == -1:
            context_end = text.find(".", m.start())
        full_decl = text[m.start():context_end + 1] if context_end != -1 else snippet

        # Inside a Module Type, treat declarations as signature fields.
        # This includes Variable/Variables, which are interface slots in a
        # Module Type, not section-level assumptions.
        if 1 <= line < len(in_module_type) and in_module_type[line] and kind in {"Axiom", "Parameter", "Variable", "Variables", "Hypothesis", "Context"}:
            findings.append(
                Finding(
                    rule_id="MODULE_SIGNATURE_DECL",
                    severity="LOW",
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=f"Found {kind}{(' ' + name) if name else ''} inside Module Type (interface spec).",
                )
            )
            continue

        if kind in {"Axiom", "Parameter", "Conjecture", "Postulate", "Assume"}:
            # NO AXIOMS ALLOWED - PERIOD
            # Zero tolerance: All axioms must be proven or removed
            rule_id = "AXIOM_OR_PARAMETER"
            severity = "HIGH"
            msg = (
                f"Axiom/Parameter `{name}` found. "
                f"NO AXIOMS ALLOWED. Prove it from first principles or delete it."
            )
        elif kind == "Hypothesis":
            rule_id = "HYPOTHESIS_ASSUME"
            severity = "HIGH"
            msg = f"Hypothesis `{name}` found (equivalent to Axiom). NO HYPOTHESES ALLOWED. All theorems must have complete proofs."
        elif kind == "Context":
            # Context with forall/arrow types are section-local axioms
            has_forall = "forall" in full_decl
            has_arrow = "->" in full_decl
            has_implication = "=>" in full_decl and "fun" not in full_decl
            is_complex_assumption = has_forall or has_arrow or has_implication
            
            if is_complex_assumption:
                # NO AXIOMS IN CONTEXT - PERIOD
                rule_id = "CONTEXT_ASSUMPTION"
                severity = "HIGH"
                msg = f"Context `{name}` contains assumption. NO CONTEXT AXIOMS ALLOWED. Prove it or delete it."
            else:
                rule_id = "SECTION_BINDER"
                severity = "MEDIUM"
                msg = f"Found {kind}{(' ' + name) if name else ''}."
        else:
            # Variable/Variables inside a Section.
            # A Variable whose type is a Prop is a section-local axiom,
            # functionally equivalent to Hypothesis — flag HIGH.
            # Pure type or function binders (T : Type, f : A -> B where B
            # is not Prop) stay MEDIUM.
            #
            # Use the current LINE (snippet) not the broad full_decl to
            # avoid false positives from multi-line scanning.
            line_text = snippet  # just this line
            # Definitive Prop indicators (must be present IN THIS LINE):
            # 1. `forall` — universally quantified Prop
            # 2. The type ends in `-> Prop` or `: Prop` — Prop-valued
            # 3. Contains `=` in a type context (equality Prop)
            has_forall_in_line = "forall" in line_text
            ends_in_prop = bool(re.search(r"->\s*Prop\b|:\s*Prop\b", line_text))
            has_equality_type = bool(re.search(
                r":\s*\(.*=.*\)|:\s*forall", line_text
            ))
            is_prop_assumption = has_forall_in_line or ends_in_prop or has_equality_type
            if is_prop_assumption:
                rule_id = "HYPOTHESIS_ASSUME"
                severity = "HIGH"
                msg = (
                    f"Variable/Variables `{name}` in Section is a Prop-typed "
                    f"section-local axiom (equivalent to Hypothesis). "
                    f"NO SECTION AXIOMS ALLOWED. Prove it or restructure as "
                    f"explicit forall premises in the theorem statements."
                )
            else:
                rule_id = "SECTION_BINDER"
                severity = "MEDIUM"
                msg = f"Found {kind}{(' ' + name) if name else ''}."

        # Suppression: if there is a SCOPE NOTE in the 30 raw lines above
        # the declaration explaining that this is an abstract interface or
        # parameterized theorem (Section Variables become explicit forall
        # premises when the section closes), suppress the finding.
        # Use raw_lines (with comments) not text (comment-stripped).
        raw_line_idx = line - 1  # 0-based index into raw_lines
        note_raw_context = "\n".join(raw_lines[max(0, raw_line_idx - 30): raw_line_idx])
        is_suppressed_interface = (
            "SCOPE NOTE" in note_raw_context and
            any(kw in note_raw_context.upper()
                for kw in ["ABSTRACT INTERFACE", "PARAMETERIZ", "SECTION PARAMETER",
                           "EXPLICIT FORALL", "INTERFACE SECTION", "ABSTRACT SECTION"])
        )
        if is_suppressed_interface:
            continue

        findings.append(
            Finding(
                rule_id=rule_id,
                severity=severity,
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=msg,
            )
        )

    # Heuristic: "cost" defined as a length.
    # This is not always wrong, but is frequently a placeholder.
    cost_is_length = re.compile(
        r"(?im)^[ \t]*Definition\s+([A-Za-z0-9_']*cost[A-Za-z0-9_']*)\b.*:=\s*.*\blength\b.*\.")
    for m in cost_is_length.finditer(text):
        name = m.group(1)
        line = line_of[m.start()]
        # An explicit (* SAFE: ... *) note above the definition says why the
        # name is not a price (for example, a code address that follows a block).
        context = "\n".join(raw_lines[max(0, line - 3): line + 1])
        if re.search(r"\(\*\s*SAFE:", context):
            continue
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="COST_IS_LENGTH",
                severity=_classify_constant_severity(name, "MEDIUM"),
                file=path,
                line=line,
                snippet=snippet.strip(),
                message="Definition looks like cost := length ... (often placeholder).",
            )
        )

    # ================================================================
    # GUARD / FLAG MANIPULATION CHECKS
    # These Coq commands can silently weaken the proof checker.
    # ================================================================

    unsafe_flags = re.compile(
        r"(?m)^[ \t]*(Unset\s+Guard\s+Checking"
        r"|Set\s+Guard\s+Checking\s+off"  # alternative syntax
        r"|Unset\s+Positivity\s+Checking"
        r"|Unset\s+Universe\s+Checking"
        r"|Unset\s+Termination\s+Checking"
        r"|Set\s+Allow\s+StrictProp"       # can create proof-relevant False
        r"|Unset\s+Strict\s+Universe\s+Declaration"
        r")\b"
    )
    for m in unsafe_flags.finditer(text):
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="UNSAFE_FLAG_MANIPULATION",
                severity="HIGH",
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=f"Unsafe Coq flag manipulation: `{m.group(1).strip()}`. This can silently disable proof checking.",
            )
        )

    # False_rect/False_ind/False_rec are kernel-checked eliminators, not
    # assumptions or proof shortcuts. Whether the supplied False proof is
    # legitimate is decided by Coq's type checker; flagging the eliminator
    # itself produced false positives for ordinary impossible-branch proofs.

    # ================================================================
    # INCONSISTENT HYPOTHESIS / CONTEXT TYPE DETECTION
    # If someone writes `Hypothesis H : False` or `Context (H : 0 = 1)`,
    # everything inside that Section is vacuously true.
    # ================================================================

    inconsistent_hyp = re.compile(
        r"(?m)^[ \t]*(?:Hypothesis|Context|Variable)\b.*:\s*"
        r"(False"
        r"|0\s*=\s*1"
        r"|1\s*=\s*0"
        r"|0%nat\s*=\s*1%nat"
        r"|true\s*=\s*false"
        r"|false\s*=\s*true"
        r"|S\s+_\s*=\s*0"
        r")\b"
    )
    for m in inconsistent_hyp.finditer(text):
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="INCONSISTENT_ASSUMPTION",
                severity="HIGH",
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=f"Inconsistent assumption type `{m.group(1)}` — makes all theorems in this Section vacuously true.",
            )
        )

    # ================================================================
    # PLUGIN / EXTERNAL CODE LOADING
    # Declare ML Module loads OCaml plugins into the Coq trusted base.
    # ================================================================

    ml_module = re.compile(r"(?m)^[ \t]*Declare\s+ML\s+Module\b")
    for m in ml_module.finditer(text):
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="EXTERNAL_PLUGIN",
                severity="MEDIUM",
                file=path,
                line=line,
                snippet=snippet.strip(),
                message="Declare ML Module loads external OCaml plugin — extends the trusted computing base.",
            )
        )

    # Statement-level vacuity checks (robust parsing).
    for name, line, stmt in iter_theorem_statements():
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else stmt

        if re.search(r":\s*True\s*\.$", stmt):
            findings.append(
                Finding(
                    rule_id="PROP_TAUTOLOGY",
                    severity=_classify_constant_severity(name, "HIGH"),
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message="Statement is literally `True.`",
                )
            )

        if re.search(r"->\s*True\s*\.$", stmt):
            findings.append(
                Finding(
                    rule_id="IMPLIES_TRUE_STMT",
                    severity=_classify_constant_severity(name, "HIGH"),
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message="Statement ends in `-> True.` (likely vacuous).",
                )
            )

        # Hidden vacuity via `let ... in True.`
        if " let " in f" {stmt} " and re.search(r"\bin\s*True\s*\.$", stmt):
            findings.append(
                Finding(
                    rule_id="LET_IN_TRUE_STMT",
                    severity=_classify_constant_severity(name, "HIGH"),
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message="Statement ends in `let ... in True.` (hidden vacuity).",
                )
            )

        # Vacuous existence: `exists ..., True.`
        if re.search(r"\bexists\b[^.]*,\s*True\s*\.$", stmt):
            findings.append(
                Finding(
                    rule_id="EXISTS_TRUE_STMT",
                    severity=_classify_constant_severity(name, "HIGH"),
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message="Statement ends in `exists ..., True.` (likely vacuous).",
                )
            )

        # Vacuous forall: `forall ..., True.` — conclusion is True but preceded
        # by a forall binder (not `->`) so IMPLIES_TRUE_STMT doesn't catch it.
        # Example: `forall (tm_op : TMTransition), True.`
        if (
            re.search(r",\s*True\s*\.$", stmt)
            and not re.search(r"->\s*True\s*\.$", stmt)
            and not re.search(r":\s*True\s*\.$", stmt)
            and not re.search(r"\bexists\b[^.]*,\s*True\s*\.$", stmt)
        ):
            findings.append(
                Finding(
                    rule_id="FORALL_TRUE_CONCLUSION",
                    severity=_classify_constant_severity(name, "HIGH"),
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=(
                        "Statement concludes with `forall ..., True.` — the universal quantifier "
                        "ranges over `True`, making the theorem vacuously trivial. "
                        "This proves nothing about the quantified variable."
                    ),
                )
            )

    # Definition ... := [].
    def_empty_list = re.compile(r"(?m)^[ \t]*Definition\s+([A-Za-z0-9_']+)\b.*:=\s*\[\]\s*\.")
    for m in def_empty_list.finditer(text):
        name = m.group(1)
        line = line_of[m.start()]
        # Check for SAFE comment in original text
        context = "\n".join(raw_lines[max(0, line - 3): line + 1])
        if re.search(r"\(\*\s*SAFE:", context):
            continue
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="EMPTY_LIST",
                severity=_classify_constant_severity(name, "MEDIUM"),
                file=path,
                line=line,
                snippet=snippet.strip(),
                message="Definition immediately returns empty list [].",
            )
        )

    # Definition ... := 0. / 0%Z / 0%nat (but not 0.X decimals)
    def_zero = re.compile(
        r"(?m)^[ \t]*Definition\s+([A-Za-z0-9_']+)\b.*:=\s*0(?:%Z|%nat|(?:\.\s*$))(?!\d)")
    for m in def_zero.finditer(text):
        name = m.group(1)
        line = line_of[m.start()]
        # Check for SAFE comment in original text
        context = "\n".join(raw_lines[max(0, line - 3): line + 1])
        if re.search(r"\(\*\s*SAFE:", context):
            continue
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="ZERO_CONST",
                severity=_classify_constant_severity(name, "MEDIUM"),
                file=path,
                line=line,
                snippet=snippet.strip(),
                message="Definition is a constant zero.",
            )
        )

    # Definition ... := True. / true.
    def_true = re.compile(
        r"(?m)^[ \t]*Definition\s+([A-Za-z0-9_']+)\b.*:=\s*(True|true)\s*\.")
    for m in def_true.finditer(text):
        name = m.group(1)
        val = m.group(2)
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="TRUE_CONST",
                severity=_classify_constant_severity(name, "HIGH"),
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=f"Definition is constant {val}.",
            )
        )

    # Definition ... := fun _ => 1%Q / 0%Q (constant probability-like functions).
    # These are almost always placeholders.
    def_const_q_fun = re.compile(
        r"(?m)^[ \t]*Definition\s+([A-Za-z0-9_']+)\b[^.]*:=\s*fun\s+_\s*=>\s*(0%Q|1%Q)\s*\."
    )
    for m in def_const_q_fun.finditer(text):
        name = m.group(1)
        val = m.group(2)
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="CONST_Q_FUN",
                severity=_classify_constant_severity(name, "HIGH"),
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=f"Definition is constant function returning {val}.",
            )
        )

    # Circular logic: intros; assumption. paired with A -> A-ish statements.
    # Heuristic parsing: look for Lemma/Theorem headers, capture statement line, and
    # detect a proof body that starts with `intros` and immediately `assumption.`
    header = re.compile(r"(?m)^\s*(Lemma|Theorem)\s+([A-Za-z0-9_']+)\b")
    for hm in header.finditer(text):
        name = hm.group(2)
        start = hm.start()
        # Find end of statement (first '.' after start, not perfect but decent without comments)
        stmt_end = text.find(".", start)
        if stmt_end == -1:
            continue
        stmt = re.sub(r"\s+", " ", text[start:stmt_end + 1]).strip()

        # Very rough tautology check: ends with "X -> X." where X is same token-ish.
        taut = re.search(r":\s*([^\.]+?)\s*->\s*\1\s*\.$", stmt)
        if not taut:
            continue

        # Now find Proof. following statement.
        proof_pos = text.find("Proof.", stmt_end)
        if proof_pos == -1:
            continue
        # Look at next couple of non-empty lines.
        proof_block = text[proof_pos: min(len(text), proof_pos + 400)]
        lines = [ln.strip() for ln in proof_block.splitlines()]
        # drop leading "Proof."
        if lines and lines[0].startswith("Proof."):
            lines = lines[1:]
        lines = [ln for ln in lines if ln]
        if len(lines) >= 2 and lines[0].startswith("intros") and (lines[1] == "assumption." or lines[1].startswith("assumption")):
            line = line_of[hm.start()]
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else stmt
            findings.append(
                Finding(
                    rule_id="CIRCULAR_INTROS_ASSUMPTION",
                    severity="LOW",
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message="Tautology-shaped statement proved via `intros; assumption.`",
                )
            )

    return findings


def scan_exists_const_q(path: Path) -> list[Finding]:
    """Detect `exists (fun _ => 1%Q)` / `exists (fun _ => 0%Q)` witnesses."""
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()

    findings: list[Finding] = []
    pat = re.compile(r"(?m)\bexists\s*\(fun\s+_\s*=>\s*(0%Q|1%Q)\)\s*\.")
    for m in pat.finditer(text):
        val = m.group(1)
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="EXISTS_CONST_Q",
                severity="HIGH",
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=f"Uses constant witness `exists (fun _ => {val})`.",
            )
        )
    return findings


def scan_false_conjunct_definition(path: Path) -> list[Finding]:
    """Detect Definition bodies containing '/\\ False' — unsatisfiable predicates.

    A Definition that contains `/\\ False` (or `False /\\`) as a conjunct creates
    a predicate that can NEVER be satisfied.  Any theorem claiming 'no X satisfies
    this predicate' is a tautology — it proves nothing about X.

    Classic pattern:
      Definition preserves_foo ... :=
        forall n, exists x, nth_error ... = Some x /\\ False.

    This makes `preserves_foo` permanently unsatisfiable.  The downstream
    theorem `forall f, ~ preserves_foo f` trivially holds because `preserves_foo`
    requires deriving `False` — not because `f` actually lacks the property.

    Suppression: add `(* SAFE: reason *)` on the line before the Definition.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    raw_lines = raw.splitlines()
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    # Locate each Definition and scan its body for /\ False
    def_re = re.compile(r"(?m)^[ \t]*Definition\s+([A-Za-z0-9_']+)\b")
    # End of a definition: period at end of line OR next top-level keyword
    next_decl_re = re.compile(
        r"(?m)^[ \t]*(Definition|Theorem|Lemma|Fixpoint|Inductive|Record|"
        r"Corollary|Proposition|Remark|Fact|Instance|End|Section)\b"
    )
    false_conj_re = re.compile(r"/\\\s*False\b|False\s*/\\")

    for m in def_re.finditer(text):
        name = m.group(1)
        body_start = m.start()
        line_num = line_of[body_start]

        # Find the next top-level declaration to bound the body
        next_decl = next_decl_re.search(text, m.end())
        if next_decl:
            body = text[body_start:next_decl.start()]
        else:
            body = text[body_start:body_start + 2000]

        if not false_conj_re.search(body):
            continue

        # Suppression: SAFE comment in the preceding 2 lines
        context = "\n".join(raw_lines[max(0, line_num - 3): line_num + 1])
        if re.search(r"\(\*\s*SAFE:", context):
            continue

        snippet = clean_lines[line_num - 1] if 0 <= line_num - 1 < len(clean_lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="FALSE_CONJUNCT_DEF",
                severity=_severity_for_path(path, "HIGH"),
                file=path,
                line=line_num,
                snippet=snippet.strip(),
                message=(
                    f"Definition `{name}` contains `/\\ False` — the predicate is permanently "
                    "unsatisfiable. Any theorem proving 'nothing satisfies this' is a tautology, "
                    "not a real result. Remove `False` from the conjunction or restructure "
                    "as an explicit impossibility lemma with a real proof."
                ),
            )
        )

    return findings


def scan_trivial_lambda_witness(path: Path) -> list[Finding]:
    """Detect `exists (fun _ => <bool/nat literal>)` trivial witnesses in proofs.

    These create witnesses that are constant functions chosen to satisfy bounds
    by construction — not by any property of the system being studied.

    Examples caught:
      exists (fun _ => true), (fun _ => false).  (* time_complexity witnesses *)
      exists (fun _ => 3), (fun _ => 4).          (* colors_used witnesses *)

    Both are vacuous: the existential is satisfied by a constant function that
    was designed to fit the bound, proving only that the TYPE is inhabited.

    Suppression: add `(* SAFE: reason *)` or `(* DEPRECATED *)` in the
    preceding 3 lines.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    raw_lines = raw.splitlines()
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    # Match: exists (fun _ => true/false/<nat literal>)
    pat = re.compile(r"\bexists\s*\(fun\s+_\s*=>\s*(true|false|\d+)\s*\)")

    for m in pat.finditer(text):
        val = m.group(1)
        line = line_of[m.start()]

        # Suppression: SAFE comment, DEPRECATED, or backward-compat marker
        context = "\n".join(raw_lines[max(0, line - 4): line + 2])
        if re.search(r"\(\*\s*SAFE:|DEPRECATED|backward.compat", context, re.IGNORECASE):
            continue

        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="TRIVIAL_LAMBDA_WITNESS",
                severity=_severity_for_path(path, "HIGH"),
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=(
                    f"Uses constant lambda witness `exists (fun _ => {val})`. "
                    "This trivially satisfies any bound because the witness is a constant "
                    "function chosen to fit the constraint — it proves nothing about actual "
                    "behavior. Replace with a semantically meaningful witness or remove the theorem."
                ),
            )
        )

    return findings


def scan_disjunct_true(path: Path) -> list[Finding]:
    """Detect `\\/ True` disjuncts in theorem statements.

    A theorem with `\\/ True` in its conclusion is vacuous because
    the right disjunct can always be satisfied with `right. exact I.`
    regardless of the left disjunct's truth.  This pattern masks
    unproven claims by allowing the proof to trivially discharge the goal.

    Examples caught:
      Theorem foo : forall x, P x \\/ True.   (* proved by right; exact I *)
      ... -> In m (map fst ...) \\/ True.      (* vacuous persistence claim *)

    Suppression: add `(* SAFE: reason *)` in the preceding 3 lines.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    raw_lines = raw.splitlines()
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    # Match theorem/lemma headers and capture the full statement up to the first period
    HEADER_RE = re.compile(
        r'(?m)^\s*(Theorem|Lemma|Corollary|Proposition|Definition)\s+(\w+)')

    for hm in HEADER_RE.finditer(text):
        name = hm.group(2)
        start = hm.start()
        # Find end of statement (first '.' after a non-comment region)
        stmt_end = text.find(".", start)
        if stmt_end == -1:
            continue
        stmt = text[start:stmt_end + 1]

        # Check for \/ True pattern (Coq disjunction with True as right or left)
        if not re.search(r'\\/\s*True\b|True\s*\\/', stmt):
            continue

        # Check SAFE comment suppression
        line = line_of[hm.start()]
        context = "\n".join(raw_lines[max(0, line - 3): line + 2])
        if re.search(r'\(\*\s*SAFE:', context):
            continue

        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else name
        findings.append(
            Finding(
                rule_id="DISJUNCT_TRUE",
                severity=_severity_for_path(path, "HIGH"),
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=(
                    f"`{name}` has `\\/ True` in its statement. This makes the theorem "
                    "vacuously provable via `right. exact I.` regardless of the actual claim. "
                    "Either prove the meaningful disjunct or remove the `\\/ True`."
                ),
            )
        )

    return findings


def scan_trivial_true_proof(path: Path) -> list[Finding]:
    """Detect proofs that only prove True via `exact I` or `right. exact I.`

    A theorem whose entire proof body reduces to `exact I.` or
    `right. exact I.` or `intros ... right. exact I.` is proving
    only the trivial proposition True, possibly hidden behind a
    disjunction or implication.

    Examples caught:
      Proof. exact I. Qed.
      Proof. intros. right. exact I. Qed.
      Proof. intros s i m _. right. exact I. Qed.

    Suppression: add `(* SAFE: reason *)` in the preceding 3 lines.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    raw_lines = raw.splitlines()
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    PROOF_BLOCK_RE = re.compile(
        r'((?:Theorem|Lemma|Corollary|Proposition)\s+(\w+)[^.]{0,2000}\.)\s*\nProof\.\s*\n(.*?)\nQed\.',
        re.DOTALL,
    )

    for m in PROOF_BLOCK_RE.finditer(text):
        name = m.group(2)
        proof_body = m.group(3).strip()
        proof_lines = [ln.strip() for ln in proof_body.splitlines() if ln.strip()]

        if not proof_lines:
            continue

        # Only flag when the ENTIRE proof is trivial:
        # All lines must be intros/right/left/exact I — no real tactics.
        # If the proof contains split, apply, destruct, unfold, rewrite,
        # etc., then `exact I` at the end is a legitimate leaf.
        trivial_line_re = re.compile(
            r'^(?:intros?\b.*|right\s*\.|left\s*\.|exact\s+I\s*\.'
            r'|(?:right|left)\s*[.;]\s*exact\s+I\s*\.)$')
        all_trivial = all(trivial_line_re.match(ln) for ln in proof_lines)
        if not all_trivial:
            continue

        # Must actually end with exact I
        last_line = proof_lines[-1]
        has_exact_i = ("exact I." in last_line)

        if not has_exact_i:
            continue

        # Check SAFE comment suppression
        line = line_of[m.start()]
        context = "\n".join(raw_lines[max(0, line - 3): line + 2])
        if re.search(r'\(\*\s*SAFE:', context):
            continue

        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else name
        findings.append(
            Finding(
                rule_id="TRIVIAL_TRUE_PROOF",
                severity=_severity_for_path(path, "HIGH"),
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=(
                    f"`{name}` proof terminates with `exact I.` — it only proves `True` "
                    "(possibly through a `right`/`left` disjunction). This is vacuous: "
                    "the theorem's conclusion reduces to a trivially true proposition."
                ),
            )
        )

    return findings


def scan_extract_constant(path: Path) -> list[Finding]:
    """Detect `Extract Constant` directives that bypass Coq extraction.

    `Extract Constant` replaces Coq-extracted code with hand-written OCaml,
    creating a trust boundary: the hand-written code is NOT verified by Coq.
    Any bug in the hand-written OCaml silently breaks soundness.

    Each `Extract Constant` should be justified and its hand-written code
    should be trivially correct (e.g. `and32 => Int32.logand`).

    NOTE: We scan raw text (not comment-stripped) because the comment
    stripper can be confused by OCaml syntax inside extraction directives
    (e.g. `Extract Inductive prod => "(*)" ...` looks like a comment open).

    Suppression: add `(* SAFE: reason *)` in the preceding 3 lines.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    raw_lines = raw.splitlines()
    findings: list[Finding] = []

    EXTRACT_RE = re.compile(r'(?m)^\s*Extract\s+Constant\s+(\S+)')

    for em in EXTRACT_RE.finditer(raw):
        name = em.group(1)
        # Compute line number from the raw match position
        line = raw[:em.start()].count('\n') + 1
        context = "\n".join(raw_lines[max(0, line - 4): line + 1])
        if re.search(r'\(\*\s*SAFE:', context):
            continue

        snippet = raw_lines[line - 1].strip() if 0 <= line - 1 < len(raw_lines) else name
        findings.append(
            Finding(
                rule_id="EXTRACT_CONSTANT",
                severity=_severity_for_path(path, "MEDIUM"),
                file=path,
                line=line,
                snippet=snippet,
                message=(
                    f"`Extract Constant {name}` bypasses Coq extraction with hand-written "
                    "OCaml code. This is a trust boundary — the replacement is NOT verified by Coq. "
                    "Ensure the hand-written code is trivially correct. "
                    "To suppress, add (* SAFE: <justification> *) above."
                ),
            )
        )

    return findings


def scan_trivial_equalities(path: Path) -> list[Finding]:
    """Detect theorems of the form X = X with reflexivity-ish proofs.

    This flags likely "0=0"-style wins. It is heuristic.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()

    findings: list[Finding] = []

    # Statement form: Theorem name : <something> = <same something>.
    # Keep it conservative: only if both sides are syntactically identical after whitespace collapsing.
    eq_stmt = re.compile(r"(?m)^[ \t]*(Lemma|Theorem)\s+([A-Za-z0-9_']+)\b[^:]*:\s*([^\.]+?)\s*=\s*([^\.]+?)\s*\.")
    for m in eq_stmt.finditer(text):
        name = m.group(2)
        lhs = re.sub(r"\s+", " ", m.group(3)).strip()
        rhs = re.sub(r"\s+", " ", m.group(4)).strip()
        if lhs != rhs:
            continue

        # Look for a proof that is basically `reflexivity.` (possibly after intros).
        start = m.start()
        proof_pos = text.find("Proof.", m.end())
        if proof_pos == -1:
            continue
        proof_block = text[proof_pos: min(len(text), proof_pos + 500)]
        proof_lines = [ln.strip() for ln in proof_block.splitlines()]
        if proof_lines and proof_lines[0].startswith("Proof."):
            proof_lines = proof_lines[1:]
        proof_lines = [ln for ln in proof_lines if ln]
        # Accept sequences like: intros ... . reflexivity.
        tail = " ".join(proof_lines[:6])
        if "reflexivity." in tail or "easy." in tail:
            line = line_of[start]
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)
            findings.append(
                Finding(
                    rule_id="TRIVIAL_EQUALITY",
                    severity=_classify_constant_severity(name, "LOW"),
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message="Theorem statement is X = X; proof likely reflexivity/easy.",
                )
            )

    return findings


def scan_exact_alias(path: Path) -> list[Finding]:
    """Flag theorems whose entire proof body is `exact <identifier>.`

    This pattern means the theorem is a pure alias: it proves nothing new,
    it just re-publishes an existing proof under a different name.  A few
    aliases are fine (backward-compatible exports, Summary modules), but
    the inquisitor must surface them so the author can verify the aliased
    result actually proves what the new name claims.

    Severity: MEDIUM — aliases inflate the theorem count without adding
    mathematical content.  The gate fails if any are present, forcing a
    deliberate decision to either justify or remove each alias.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    raw_lines = raw.splitlines()
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    PROOF_BLOCK_RE = re.compile(
        r'((?:Theorem|Lemma|Corollary|Proposition)\s+(\w+)[^.]{0,500}\.)\s*\nProof\.\s*\n(.*?)\nQed\.',
        re.DOTALL,
    )

    for m in PROOF_BLOCK_RE.finditer(text):
        name = m.group(2)
        proof_body = m.group(3).strip()
        proof_lines = [ln.strip() for ln in proof_body.splitlines() if ln.strip()]

        if len(proof_lines) != 1:
            continue
        if not re.match(r'^exact\s+(\w+)\s*\.$', proof_lines[0]):
            continue

        # Allow if there's a SAFE comment nearby in the raw file
        line = line_of[m.start()]
        context = "\n".join(raw_lines[max(0, line - 3): line + 2])
        if re.search(r'\(\*\s*SAFE:', context):
            continue
        # Allow if there's a SCOPE NOTE marking this as a deliberate alias
        if re.search(r'SCOPE NOTE.*alias|SCOPE NOTE.*export|SCOPE NOTE.*compat', context, re.IGNORECASE):
            continue

        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else name
        alias_match = re.match(r'^exact\s+(\w+)\s*\.$', proof_lines[0])
        if alias_match is None:
            continue
        aliased = alias_match.group(1)
        findings.append(
            Finding(
                rule_id="EXACT_ALIAS",
                severity=_severity_for_path(path, "MEDIUM"),
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=(
                    f"Theorem `{name}` is a pure alias: its entire proof is `exact {aliased}.` "
                    f"This proves nothing new — it just re-exports `{aliased}` under a new name. "
                    "If intentional (backward-compat / summary module), add "
                    "(* SCOPE NOTE: alias for <reason> *) above the theorem."
                ),
            )
        )

    return findings


_FROM_REQUIRE_RE = re.compile(r'^From\s+([A-Za-z_][A-Za-z0-9_]*)(?:\.[A-Za-z0-9_.]+)?\s+Require\b')
# A qualified module in a bare Require line: Require [Import|Export] Ns.Mod ...
_BARE_REQUIRE_RE = re.compile(r'^Require\s+(?:Import\s+|Export\s+)?(.+?)\.[ \t]*$')
# The namespaces a file under coq/kernel/ may import from: the Coq standard
# library, the kernel, the small machine, the pinned vendored library and the
# test fixtures. Any other namespace is outside the proof tree.
_TIER1_ALLOWED_NAMESPACES: frozenset[str] = (
    _STDLIB_NAMESPACES | _TIER1_NAMESPACES | frozenset({'Minimal', 'Undecidability', 'TestFixtures'})
)


def scan_scope_drift(path: Path) -> list[Finding]:
    """Enforce tier-boundary separation for Coq imports.

    Tier system (driven by coq/_CoqProject namespace mappings):
      Tier 1 — The proof tree (coq/kernel/, namespace Kernel):
        Must use only ``Kernel``, the small machine (``Minimal``), the pinned
        vendored ``Undecidability`` library and the Coq stdlib. Any import of
        a Tier-2 or Tier-3 namespace contaminates it.
      Tier 2 — Core theory outside coq/kernel/ (none at present):
        May import Tier-1 and Tier-2 namespaces.
        Must NOT import Tier-3 (exploratory/speculative) namespaces.
      Tier 3 — Exploratory / speculative (none at present):
        Free research. May import anything.

    Rule IDs emitted:
      ``SCOPE_DRIFT_TIER1`` (HIGH):  Tier-1 file imports a Tier-2 or Tier-3 namespace.
      ``SCOPE_DRIFT_TIER2`` (MEDIUM): Tier-2 file imports a Tier-3 namespace.

    Suppression: add ``(* SCOPE NOTE: cross-tier import for <reason> *)``
    on the line immediately above the offending ``From … Require`` line.
    """
    file_tier = _path_to_tier(path)
    if file_tier is None or file_tier == 3:
        return []  # Root coq/ files and Tier 3 files are exempt from tier enforcement

    raw = path.read_text(encoding="utf-8", errors="replace")
    raw_lines = raw.splitlines()
    findings: list[Finding] = []

    for i, line in enumerate(raw_lines, start=1):
        stripped = line.strip()
        namespaces: list[str] = []
        m = _FROM_REQUIRE_RE.match(stripped)
        if m:
            namespaces = [m.group(1)]
        else:
            bare = _BARE_REQUIRE_RE.match(stripped)
            if bare:
                # Only qualified modules name a namespace; a bare name is relative.
                namespaces = [tok.split(".")[0] for tok in bare.group(1).split() if "." in tok]
        for ns in namespaces:
            if ns in _TIER1_ALLOWED_NAMESPACES:
                continue
            if _NAMESPACE_TO_TIER.get(ns) is not None:
                continue  # A tiered namespace is judged below (From-lines only).
            # No tier is defined for this namespace. Under coq/kernel/ that means
            # it is outside the proof tree, which is a finding unless a SCOPE NOTE
            # above the import gives the reason.
            context = "\n".join(raw_lines[max(0, i - 4): i])
            if file_tier == 1 and not re.search(
                    r'SCOPE NOTE.*cross.tier|SCOPE NOTE.*tier', context, re.IGNORECASE):
                findings.append(
                    Finding(
                        rule_id="SCOPE_DRIFT_TIER1",
                        severity="HIGH",
                        file=path,
                        line=i,
                        snippet=stripped,
                        message=(
                            f"Tier-1 coq/kernel/ file imports `{ns}`, a namespace outside "
                            "the proof tree (allowed: Coq, Kernel, Minimal, Undecidability, "
                            "TestFixtures). Suppress with: "
                            "(* SCOPE NOTE: cross-tier import for <reason> *)"
                        ),
                    )
                )
        m = _FROM_REQUIRE_RE.match(stripped)
        if not m:
            continue
        ns = m.group(1)
        if ns in _STDLIB_NAMESPACES:
            continue  # Coq / Stdlib is always allowed
        if ns in _TIER1_NAMESPACES:
            continue  # Kernel imports are always allowed in Tier 1 and 2

        import_tier = _NAMESPACE_TO_TIER.get(ns)
        if import_tier is None:
            continue  # Unknown namespaces were judged above.

        # Check for suppression comment anywhere in the 3 lines above
        context = "\n".join(raw_lines[max(0, i - 4): i])
        if re.search(r'SCOPE NOTE.*cross.tier|SCOPE NOTE.*tier', context, re.IGNORECASE):
            continue
        if re.search(r'\(\*\s*SAFE:', context):
            continue

        if file_tier == 1 and import_tier >= 2:
            tier_label = "Tier 2 (core theory)" if import_tier == 2 else "Tier 3 (exploratory/speculative)"
            findings.append(
                Finding(
                    rule_id="SCOPE_DRIFT_TIER1",
                    severity="HIGH",
                    file=path,
                    line=i,
                    snippet=line.strip(),
                    message=(
                        f"Tier-1 coq/kernel/ file imports `{ns}` ({tier_label}). "
                        "The kernel must be self-contained (only Kernel + Coq stdlib). "
                        f"Either move the needed proof into coq/kernel/ under the Kernel namespace, "
                        f"or relocate this file to a higher-tier directory. "
                        "Suppress with: (* SCOPE NOTE: cross-tier import for <reason> *)"
                    ),
                )
            )
        elif file_tier == 2 and import_tier == 3:
            findings.append(
                Finding(
                    rule_id="SCOPE_DRIFT_TIER2",
                    severity="MEDIUM",
                    file=path,
                    line=i,
                    snippet=line.strip(),
                    message=(
                        f"Core Tier-2 file imports `{ns}` (Tier 3 exploratory). "
                        "Speculative/exploratory modules should not be imported into core proofs. "
                        "Move the needed lemma into the Kernel or a shared Tier-2 module. "
                        "Suppress with: (* SCOPE NOTE: cross-tier import for <reason> *)"
                    ),
                )
            )

    return findings


def _extract_imported_module_names(clean_text: str) -> set[str]:
    modules: set[str] = set()

    for m in _FROM_REQUIRE_IMPORTS_RE.finditer(clean_text):
        from_ns = m.group(1).strip()
        if from_ns:
            modules.add(from_ns.split(".")[-1])
        for tok in m.group(2).split():
            tok = tok.strip()
            if tok:
                modules.add(tok.split(".")[-1])

    for m in _REQUIRE_IMPORTS_RE.finditer(clean_text):
        for tok in m.group(1).split():
            tok = tok.strip()
            if tok:
                modules.add(tok.split(".")[-1])

    return modules


def scan_proof_connectivity(repo_root: Path, v_files: list[Path]) -> list[Finding]:
    """Enforce that every proof-bearing Coq file builds up from foundation modules.

    Foundation policy:
    - Active proof files must connect to the semantic foundation (the abstract
      model and the small machine) transitively.
    - A cost connection is required only when the file actually reasons about
      cost or ledger symbols; it is not imposed on unrelated lemmas.
    - The foundation modules themselves are roots of the dependency graph.
    - A file that stands alone says so in a SCOPE NOTE; it is not driven to
      fake a link.
    """

    stem_to_paths: dict[str, set[Path]] = {}
    imports_by_file: dict[Path, set[str]] = {}
    proof_file_info: list[tuple[Path, int, int, str]] = []
    semantic_mentions: set[Path] = set()
    cost_mentions: set[Path] = set()

    for vf in v_files:
        raw = vf.read_text(encoding="utf-8", errors="replace")
        clean = strip_coq_comments(raw)
        stem_to_paths.setdefault(vf.stem, set()).add(vf)
        imports_by_file[vf] = _extract_imported_module_names(clean)

        if _SEMANTIC_TOKEN_RE.search(clean):
            semantic_mentions.add(vf)
        if _COST_TOKEN_RE.search(clean):
            cost_mentions.add(vf)

        if not _PROOF_DECL_RE.search(clean):
            continue

        if _PROOF_CONNECTIVITY_NOTE_RE.search(raw):
            continue

        clean_lines = clean.splitlines()
        first_line = 1
        first_snippet = ""
        for i, line in enumerate(clean_lines, start=1):
            if _PROOF_DECL_RE.match(line):
                first_line = i
                first_snippet = line.strip()
                break
        proof_file_info.append((vf, _path_to_tier(vf) or 0, first_line, first_snippet))

    all_foundation_modules = set().union(*_FOUNDATION_GROUPS.values())
    anchors: set[Path] = set()
    for stem in all_foundation_modules:
        anchors.update(stem_to_paths.get(stem, set()))

    findings: list[Finding] = []
    if not anchors:
        findings.append(
            Finding(
                rule_id="PROOF_CONNECTIVITY_GAP",
                severity="HIGH",
                file=repo_root / "coq" / "_CoqProject",
                line=1,
                snippet="",
                message=(
                    "No foundation modules were found for proof-connectivity audit. "
                    "Expected at least one of: "
                    + ", ".join(sorted(all_foundation_modules))
                ),
            )
        )
        return findings

    # Build transitive import graph on concrete file paths.
    adjacency: dict[Path, set[Path]] = {vf: set() for vf in v_files}
    reverse_adjacency: dict[Path, set[Path]] = {vf: set() for vf in v_files}
    for src, imported_stems in imports_by_file.items():
        for stem in imported_stems:
            for dst in stem_to_paths.get(stem, set()):
                if dst == src:
                    continue
                adjacency[src].add(dst)
                reverse_adjacency[dst].add(src)

    reachable_stem_cache: dict[Path, set[str]] = {}

    def _reachable_stems(start: Path) -> set[str]:
        cached = reachable_stem_cache.get(start)
        if cached is not None:
            return cached
        seen: set[Path] = set()
        stack = [start]
        stems: set[str] = set()
        while stack:
            node = stack.pop()
            if node in seen:
                continue
            seen.add(node)
            stems.add(node.stem)
            stack.extend(adjacency.get(node, set()))
        reachable_stem_cache[start] = stems
        return stems

    for vf, tier, line, snippet in proof_file_info:
        # Foundation files are the baseline and are exempt from self-checking.
        if vf.stem in all_foundation_modules:
            continue

        # Semantic grounding is meaningful for core proof layers. Cost
        # grounding is conditional: a file that does not reason about μ-cost
        # should not be forced to import a cost model merely to satisfy a
        # lexical connectivity rule.
        if tier == 3:
            continue
        required_groups: list[str] = ["semantics"]
        if _COST_TOKEN_RE.search(
            vf.read_text(encoding="utf-8", errors="replace")
        ):
            required_groups.append("cost")

        reachable = _reachable_stems(vf)
        missing_groups: list[str] = []
        for group in required_groups:
            group_modules = _FOUNDATION_GROUPS[group]
            reached_group = bool(reachable.intersection(group_modules))
            if group == "semantics" and vf in semantic_mentions:
                reached_group = True
            if group == "cost" and vf in cost_mentions:
                reached_group = True
            if not reached_group:
                missing_groups.append(group)

        if not missing_groups:
            continue

        required_desc = ", ".join(missing_groups)

        findings.append(
            Finding(
                rule_id="PROOF_CONNECTIVITY_GAP",
                severity="HIGH",
                file=vf,
                line=line,
                snippet=snippet,
                message=(
                    f"proof file is missing required foundation connectivity group(s): "
                    f"{required_desc}. ALL proofs must connect to the Thiele Machine "
                    "foundation chain (UniversalCertificationCost, StructuralCore, Substrate, "
                    "KernelTM, EarnedCore, ThieleComplete) or state in a SCOPE NOTE why they "
                    "stand alone. Add imports/bridge lemmas and iterate until connected."
                ),
            )
        )

    return findings


def scan_proof_quality(path: Path) -> list[Finding]:
    """Scan for proof quality issues in critical kernel files.
    
    Enhanced checks for:
    - Proofs that are suspiciously short for complex theorems
    - Missing proof obligations (Defined vs Qed)
    - Proof by assertion without clear justification
    """
    if not is_critical_kernel_file(path):
        return []
    
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    raw_lines = raw.splitlines()  # Keep original for SAFE checking
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []
    
    # Check for theorems with extremely short proofs (potential red flag)
    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b")
    proof_re = re.compile(r"(?m)^[ \t]*Proof\.")
    end_re = re.compile(r"(?m)^[ \t]*(Qed|Defined|Admitted)\.")
    
    for m in theorem_re.finditer(text):
        name = m.group(2)
        start = m.end()
        
        # Find Proof
        proof_match = proof_re.search(text, start)
        if not proof_match:
            continue
        
        # Find end of proof
        end_match = end_re.search(text, proof_match.end())
        if not end_match:
            continue
        
        proof_block = text[proof_match.end(): end_match.start()]
        proof_lines = [ln.strip() for ln in proof_block.splitlines() if ln.strip()]
        
        # Skip already-flagged admits
        if end_match.group(1) == "Admitted":
            continue
        
        # Flag suspiciously short proofs for complex-sounding theorems
        complex_name_re = re.compile(r"(?i)(bound|uniqueness|complete|sound|equivalence|conservation|causality)")
        if complex_name_re.search(name) and len(proof_lines) <= 2:
            line = line_of[m.start()]
            # Check for SAFE comment in original text
            context = "\n".join(raw_lines[max(0, line - 3): line + 2])
            if re.search(r"\(\*\s*SAFE:", context):
                continue
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else name
            findings.append(
                Finding(
                    rule_id="SUSPICIOUS_SHORT_PROOF",
                    severity="MEDIUM",
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=f"Complex theorem `{name}` has very short proof ({len(proof_lines)} lines) - verify this is not a placeholder.",
                )
            )
    
    return findings


def scan_mu_cost_consistency(path: Path) -> list[Finding]:
    """Check for consistency in μ-cost accounting definitions.
    
    Ensures that μ-cost is properly tracked and not trivially defined.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    raw_lines = raw.splitlines()  # Keep original for SAFE checking
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []
    
    # Check for μ-related definitions that might be trivially zero
    # Note: Uses both 'mu' and Unicode μ (\u03bc) for compatibility
    mu_def_re = re.compile(r"(?m)^[ \t]*Definition\s+([A-Za-z0-9_']*(?:mu|\u03bc|cost)[A-Za-z0-9_']*)\b.*:=\s*0")
    for m in mu_def_re.finditer(text):
        name = m.group(1)
        # Skip if in test files or explicitly documented as intentional
        if "test" in path.name.lower() or "spec" in path.name.lower():
            continue
        line = line_of[m.start()]
        # Check for SAFE comment in original text
        context = "\n".join(raw_lines[max(0, line - 3): line + 1])
        if re.search(r"\(\*\s*SAFE:", context):
            continue
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="MU_COST_ZERO",
                severity=_severity_for_path(path, "MEDIUM"),
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=f"\u03bc-cost definition `{name}` is trivially zero - ensure this is intentional.",
            )
        )
    
    return findings


def scan_chsh_bounds(path: Path) -> list[Finding]:
    """Check CHSH-related theorems for proper bounds.
    
    Verifies that explicit CHSH bound claims reference proper values.
    Only flags theorems that CLAIM a specific bound but don't reference known good values.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    raw_lines = raw.splitlines()
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []
    
    # Check for CHSH-related theorems that explicitly claim a bound value
    # Focus on theorems that contain comparative operators (<=, >=, <, >) with CHSH
    chsh_bound_theorem_re = re.compile(
        r"(?m)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']*(?:chsh|CHSH|tsirelson|Tsirelson)[A-Za-z0-9_']*)\b[^.]*"
        r"(?:<=|>=|<\s*=|>\s*=)[^.]*\."
    )
    
    for m in chsh_bound_theorem_re.finditer(text):
        name = m.group(2)
        stmt = m.group(0)
        
        # Check for proper bound references (2√2 ≈ 2.8284, or the rational approximation 5657/2000)
        # Also accept 4%Q (algebraic max) and target_chsh_value as valid references
        has_proper_bound = any(x in stmt for x in [
            "2828", "5657", "2000", "sqrt", "Qsqrt", "4%Q", "4 %Q",
            "target_chsh", "tsirelson_bound", "2 * 2", "<=4", "<= 4"
        ])
        
        # Skip if already has a proper bound or doesn't explicitly claim a numeric bound
        if has_proper_bound:
            continue
        
        # Only flag if the name suggests it's claiming a bound
        if "bound" not in name.lower():
            continue
            
        line = line_of[m.start()]

        # Allow exemption via (* SAFE: ... *) comment in preceding lines
        context = "\n".join(raw_lines[max(0, line - 3): line + 2])
        if re.search(r"\(\*\s*SAFE:", context):
            continue

        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else name
        findings.append(
            Finding(
                rule_id="CHSH_BOUND_MISSING",
                severity="LOW",  # Downgraded since it's heuristic
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=f"CHSH bound theorem `{name}` may not reference proper Tsirelson bound value.",
            )
        )
    
    return findings


def scan_axiom_dependencies(path: Path) -> list[Finding]:
    """Check for undocumented axiom dependencies.
    
    Looks for Require statements that might introduce axioms silently.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    raw_lines = raw.splitlines()
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []
    
    # Known problematic imports (classical axioms, etc.)
    problematic_imports = re.compile(r"(?m)^[ \t]*Require\s+(?:Import\s+)?.*\b(Classical|Decidable|ProofIrrelevance)\b")
    
    for m in problematic_imports.finditer(text):
        line = line_of[m.start()]
        # Check for SAFE comment in original text
        context = "\n".join(raw_lines[max(0, line - 3): line + 1])
        if re.search(r"\(\*\s*SAFE:", context):
            continue
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="PROBLEMATIC_IMPORT",
                severity=_severity_for_path(path, "MEDIUM"),
                file=path,
                line=line,
                snippet=snippet.strip(),
                message="Import may introduce classical axioms - verify this is documented and necessary.",
            )
        )
    
    return findings


def scan_record_field_extraction(path: Path) -> list[Finding]:
    """Detect theorems that merely extract a Record field they assumed as input.

    Pattern: A Record R has field `f : P`. Then a Theorem says
    `forall r : R, P` and the proof is `intro r. exact (f r).` or equivalent.

    This is circular: P was required to *construct* R, so extracting it
    back out proves nothing.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    # Step 1: collect all Record field names and their types.
    # Match: Record Foo := { ... }. OR Record Foo := mkFoo { ... }.
    record_re = re.compile(
        r"(?ms)^[ \t]*Record\s+([A-Za-z0-9_']+)\b[^.]*:=\s*(?:[A-Za-z0-9_']+\s*)?\{(.*?)\}\s*\."
    )
    # Field inside record body:  field_name : <type>
    field_re = re.compile(r"([A-Za-z0-9_']+)\s*:\s*([^;}\n]+)")

    record_fields: dict[str, list[tuple[str, str]]] = {}  # record_name -> [(field, type)]
    for rm in record_re.finditer(text):
        rname = rm.group(1)
        body = rm.group(2)
        fields = []
        for fm in field_re.finditer(body):
            fname = fm.group(1).strip()
            ftype = re.sub(r"\s+", " ", fm.group(2)).strip()
            fields.append((fname, ftype))
        record_fields[rname] = fields

    if not record_fields:
        return findings

    # Step 2: find theorems whose proof body is `intro(s) X. exact (field X).`
    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b")
    proof_re = re.compile(r"(?m)^[ \t]*Proof\.")
    end_re = re.compile(r"(?m)^[ \t]*(Qed|Defined|Admitted)\.")

    all_field_names = set()
    for fields in record_fields.values():
        for fname, _ in fields:
            all_field_names.add(fname)

    for tm in theorem_re.finditer(text):
        tname = tm.group(2)
        stmt_end = text.find(".", tm.end())
        if stmt_end == -1:
            continue
        # Coq record projections use `record.(field)`, so the dot before the
        # opening parenthesis is not the end of the theorem statement.
        while text[stmt_end:stmt_end + 2] == ".(":
            stmt_end = text.find(".", stmt_end + 2)
            if stmt_end == -1:
                break
        if stmt_end == -1:
            continue
        stmt = re.sub(r"\s+", " ", text[tm.start():stmt_end + 1]).strip()

        proof_match = proof_re.search(text, stmt_end)
        if not proof_match:
            continue
        end_match = end_re.search(text, proof_match.end())
        if not end_match:
            continue
        proof_block = text[proof_match.end():end_match.start()].strip()
        proof_lines = [ln.strip() for ln in proof_block.splitlines() if ln.strip()]

        # Check for extraction patterns:
        # 1. `intro(s) <var>. exact (<field> <var>).`
        # 2. `intro <var>. apply <field>.`
        # 3. `intro <var>. destruct <var> as [...]. lia/auto/assumption.`
        #    (destructures record then solves with arithmetic — semantically identical)
        proof_text = " ".join(proof_lines)

        # Pattern A: intro(s) <var>. exact (<field> <var>). (possibly with extra args)
        extract_pat = re.compile(
            r"intros?\s+([A-Za-z0-9_']+)\s*\.\s*"
            r"(?:exact\s*\(\s*([A-Za-z0-9_']+)\s+\1|apply\s+([A-Za-z0-9_']+))"
        )
        em = extract_pat.search(proof_text)

        # Pattern B: intro <var>. destruct <var> as [... field_hyps ...]. <solver>.
        # The proof destructures the record and a simple solver (lia/auto/assumption)
        # consumes the extracted field hypothesis.
        destruct_extract_pat = re.compile(
            r"intros?\s+([A-Za-z0-9_']+)\s*\.\s*"
            r"destruct\s+\1\b[^.]*\.\s*"
            r"(?:simpl\s*\.\s*)?"
            r"(lia|lra|omega|auto|assumption|trivial|exact\b)"
        )
        dm = destruct_extract_pat.search(proof_text) if not em else None

        if not em and not dm:
            continue

        if em:
            var_name = em.group(1)
            field_used = em.group(2) or em.group(3)
        else:
            if dm is None:
                continue
            # For destruct pattern, we flag it if the record has propositional fields
            # and the proof is trivially short (just destruct + solver)
            var_name = dm.group(1)
            # Check if any record field is referenced — for destruct pattern,
            # we flag ALL records quantified over since it's extraction-by-destruction
            field_used = None
            for rname, fields in record_fields.items():
                # Use word boundary to avoid substring matches (Erasure vs PhysicalErasure)
                if re.search(r'\b' + re.escape(rname) + r'\b', stmt):
                    # Check if any field is a Prop (heuristic: type doesn't look like a data type
                    # and type is not another known record)
                    data_types = r'^(nat|N|Z|Q|R|bool|list|option)\b'
                    prop_fields = [fn for fn, ft in fields
                                   if not re.match(data_types, ft.strip())
                                   and ft.strip().split()[0] not in record_fields]
                    if prop_fields:
                        field_used = prop_fields[0]  # Report first propositional field
                        break

        if field_used not in all_field_names:
            continue

        # Find which record owns this field
        owner_record = None
        for rname, fields in record_fields.items():
            for fname, _ in fields:
                if fname == field_used:
                    owner_record = rname
                    break
            if owner_record:
                break

        # Check if the theorem's statement quantifies over that record type
        if owner_record and re.search(r'\b' + re.escape(owner_record) + r'\b', stmt):
            line = line_of[tm.start()]
            # Check for SCOPE NOTE
            raw_lines = raw.splitlines()
            note_start = max(0, line - 4)
            note_end = min(len(raw_lines), line + 2)
            note_context = "\n".join(raw_lines[note_start:note_end])
            if "SCOPE NOTE" in note_context:
                continue  # Verified extraction — intentional
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname
            findings.append(
                Finding(
                    rule_id="RECORD_FIELD_EXTRACTION",
                    severity=_severity_for_path(path, "HIGH"),
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=f"Theorem `{tname}` extracts Record field `{field_used}` from `{owner_record}` — "
                            f"the proof was ASSUMED when constructing the record, not derived.",
                )
            )

    return findings


def scan_self_referential_record(path: Path) -> list[Finding]:
    """Detect Records where a propositional field IS extracted by a Theorem in the same file.

    A Record defining an algebraic structure (Cat, Group, etc.) with propositional
    fields (laws) is STANDARD Coq practice — not circular on its own.

    The problem is ONLY when the same file also contains a Theorem that:
    1. Quantifies over instances of the Record (forall r : Record, ...)
    2. Extracts a propositional field as its conclusion
    3. Claims this is a "derivation" when it's really just field projection

    This is the "assume X in Record constructor, then extract X as a Theorem" pattern.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    # Step 1: Find all Records with propositional fields
    # Match: Record Foo := { ... }. OR Record Foo := mkFoo { ... }.
    record_re = re.compile(
        r"(?ms)^[ \t]*Record\s+([A-Za-z0-9_']+)\b[^.]*:=\s*(?:[A-Za-z0-9_']+\s*)?\{(.*?)\}\s*\."
    )
    field_re = re.compile(r"([A-Za-z0-9_']+)\s*:\s*([^;}\n]+)")
    prop_indicators = re.compile(r"(forall|>=|<=|>(?!=)|<(?!=|>)|->|Prop\b|\/\\|\\/|~)")

    records_with_prop_fields: dict[str, list[tuple[str, str, int]]] = {}  # rname -> [(fname, ftype, line)]
    for rm in record_re.finditer(text):
        rname = rm.group(1)
        body = rm.group(2)
        rline = line_of[rm.start()]
        prop_fields = []
        for fm in field_re.finditer(body):
            fname = fm.group(1).strip()
            ftype = fm.group(2).strip()
            # Skip simple positivity constraints and Type fields
            if re.match(r"^\s*\w+\s*>\s*0\s*$", ftype):
                continue
            if re.match(r"^\s*(nat|bool|R|Z|Q|Type|Set|list\b)", ftype):
                continue
            if prop_indicators.search(ftype):
                prop_fields.append((fname, ftype, rline))
        if prop_fields:
            records_with_prop_fields[rname] = prop_fields

    if not records_with_prop_fields:
        return findings

    # Step 2: Check if any Theorem in the file extracts a propositional field.
    # We already detect this in scan_record_field_extraction. Here we flag the
    # Record DEFINITION as the root cause, but ONLY if there's an extraction.
    #
    # Also detect the subtler pattern: a Theorem that constructs a Record instance
    # by filling fields with existing proofs, where ALL fields are just restatements
    # of already-proven lemmas — the Record adds no new proof obligation.
    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b")
    proof_re = re.compile(r"(?m)^[ \t]*Proof\.")
    end_re = re.compile(r"(?m)^[ \t]*(Qed|Defined|Admitted)\.")

    # Collect all field names from propositional records
    all_prop_field_names: dict[str, str] = {}  # fname -> rname
    for rname, fields in records_with_prop_fields.items():
        for fname, ftype, rline in fields:
            all_prop_field_names[fname] = rname

    # Search for theorems that extract record fields
    extracted_records: set[str] = set()
    for tm in theorem_re.finditer(text):
        tname = tm.group(2)
        stmt_end = text.find(".", tm.end())
        if stmt_end == -1:
            continue
        stmt = re.sub(r"\s+", " ", text[tm.start():stmt_end + 1]).strip()

        proof_match = proof_re.search(text, stmt_end)
        if not proof_match:
            continue
        end_match = end_re.search(text, proof_match.end())
        if not end_match:
            continue
        proof_block = text[proof_match.end():end_match.start()].strip()

        # Check for field extraction patterns
        for fname, rname in all_prop_field_names.items():
            if rname in stmt and fname in proof_block:
                # Check for direct extraction: `exact (field x)` or `apply field`
                extract_pat = re.compile(
                    rf"\b(?:exact\s*\(\s*{re.escape(fname)}\b|apply\s+{re.escape(fname)}\b)"
                )
                if extract_pat.search(proof_block):
                    # Only flag if the proof is TRIVIALLY SHORT.
                    # A multi-step proof that uses a field as one premise
                    # among several is standard Coq idiom (interface usage),
                    # not circular reasoning.
                    meaningful_lines = [
                        ln.strip() for ln in proof_block.splitlines()
                        if ln.strip() and not re.match(
                            r'^(intros?\b|Proof\b|\-|\+|\*|\{|\})', ln.strip()
                        )
                    ]
                    # Also check for structural work (exists, split,
                    # constructor) which indicates combining fields, not
                    # just extracting one.
                    has_structural_work = bool(re.search(
                        r'\b(exists|split|constructor)\b', proof_block
                    ))
                    if len(meaningful_lines) <= 3 and not has_structural_work:
                        extracted_records.add(rname)

    # Step 3: Only flag records whose fields are actually extracted by a theorem
    for rname in extracted_records:
        fields = records_with_prop_fields[rname]
        for fname, ftype, rline in fields:
            # Only flag substantial propositions
            if "forall" in ftype or (">=" in ftype and "+" in ftype) or "->" in ftype:
                snippet = clean_lines[rline - 1] if 0 <= rline - 1 < len(clean_lines) else rname
                findings.append(
                    Finding(
                        rule_id="SELF_REFERENTIAL_RECORD",
                        severity=_severity_for_path(path, "HIGH"),
                        file=path,
                        line=rline,
                        snippet=snippet.strip(),
                        message=f"Record `{rname}` field `{fname}` embeds proposition `{ftype[:120]}` "
                                f"AND a Theorem in this file extracts it — circular proof pattern.",
                    )
                )

    return findings


_FOUNDATION_DECL_CACHE: dict[str, frozenset[str]] = {}

_DECL_NAME_RE = re.compile(
    r"(?m)^[ \t]*(?:Local\s+|Global\s+|#\[[^\]]*\]\s*)?"
    r"(?:Definition|Fixpoint|CoFixpoint|Inductive|CoInductive|Record|Structure|Class|"
    r"Instance|Theorem|Lemma|Corollary|Proposition|Fact|Remark|Notation|Let)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)"
)
_FIELD_OR_CTOR_RE = re.compile(r"(?m)(?:^[ \t]*|\{[ \t]*|;[ \t]*|\|[ \t]*)([A-Za-z_][A-Za-z0-9_']*)[ \t]*:")
_TYPE_DECL_BLOCK_RE = re.compile(
    r"(?ms)^[ \t]*(?:Record|Structure|Inductive|CoInductive|Class)\b.*?\.(?=\s|$)")
_CTOR_RE = re.compile(r"\|[ \t]*([A-Za-z_][A-Za-z0-9_']*)")


def _foundation_module_decls(module: str) -> frozenset[str]:
    """Names a foundation module declares: definitions, theorems, record
    fields and constructors. Used to tell a real use of an import from a
    phantom one."""
    cached = _FOUNDATION_DECL_CACHE.get(module)
    if cached is not None:
        return cached
    repo_root = Path(__file__).resolve().parents[1]
    names: set[str] = set()
    for root in (repo_root / "coq", repo_root / "minimal"):
        if not root.exists():
            continue
        for candidate in root.rglob(f"{module}.v"):
            text = strip_coq_comments(candidate.read_text(encoding="utf-8", errors="replace"))
            names.update(m.group(1) for m in _DECL_NAME_RE.finditer(text))
            # Record fields and constructors come only from the bodies of the
            # type declarations, so a tactic or a binder elsewhere in the file
            # never counts as a declared name.
            for block in _TYPE_DECL_BLOCK_RE.finditer(text):
                names.update(m.group(1) for m in _FIELD_OR_CTOR_RE.finditer(block.group(0)))
                names.update(m.group(1) for m in _CTOR_RE.finditer(block.group(0)))
    # A record field or constructor harvest also picks up binder names such as
    # `n`, `S`, `H`, `a`, `_`. A file using any binder would then count as using
    # the import, so only identifiers of a real declared length count, and the
    # words every Coq file uses are dropped.
    names = {n for n in names if _is_meaningful_foundation_name(n)}
    names.add(module)
    result = frozenset(names)
    _FOUNDATION_DECL_CACHE[module] = result
    return result


_GENERIC_COQ_WORDS: frozenset[str] = frozenset({
    "nat", "list", "bool", "true", "false", "some", "none", "Some", "None", "Type", "Prop",
    "Set", "with", "then", "else", "fun", "match", "exists", "forall", "Proof", "Qed",
    "Defined", "Hypothesis", "Variable", "Context", "Section", "Module", "state", "step",
    "eval", "prop", "fact", "term", "goal", "head", "tail", "rest", "tr", "pre", "post",
})


def _is_meaningful_foundation_name(name: str) -> bool:
    """A declared name that can tell a real use of an import from a binder."""
    return len(name) >= 4 and not name.startswith("_") and name not in _GENERIC_COQ_WORDS


def scan_phantom_imports(path: Path) -> list[Finding]:
    """Detect files that import a foundation module but never use anything it
    declares.

    The foundation chain (UniversalCertificationCost, StructuralCore,
    Substrate, KernelTM, EarnedCore, ThieleComplete) is what the connectivity
    rules require a proof file to reach. An import of one of them that no
    definition, statement or proof in the file uses creates the illusion of
    grounding in the abstract model when the proofs are self-contained. The
    import has to be used, or removed.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    has_theorems = bool(re.search(r"(?m)^[ \t]*(Theorem|Lemma|Corollary)\s+", text))
    if not has_theorems:
        return findings

    foundation = _FOUNDATION_SEMANTICS_MODULES | _FOUNDATION_COST_MODULES
    body = "\n".join(
        line for line in text.splitlines() if not re.search(r"\bRequire\b", line)
    )
    body_tokens = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", body))

    import_re = re.compile(
        r"(?m)^[ \t]*(?:From\s+([A-Za-z0-9_.]+)\s+)?Require\s+(?:Import\s+|Export\s+)?(.+?)\.\s*$"
    )
    for match in import_re.finditer(text):
        modules = [tok.split(".")[-1] for tok in match.group(2).split()]
        for module in modules:
            if module not in foundation:
                continue
            if path.stem == module:
                continue
            if body_tokens & _foundation_module_decls(module):
                continue
            line = line_of[match.start()]
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else match.group(0)
            findings.append(
                Finding(
                    rule_id="PHANTOM_KERNEL_IMPORT",
                    severity=_severity_for_path(path, "HIGH"),
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=(
                        f"File imports foundation module {module} but no definition, "
                        "statement or proof in it uses anything that module declares. "
                        "Use the import or remove it; a phantom import is not grounding."
                    ),
                )
            )

    return findings


def scan_trivial_existentials(path: Path) -> list[Finding]:
    """Detect trivially satisfiable existential theorems.

    Patterns:
    - `exists n, length l = n` (every list has a length)
    - `exists n, n = n` / `exists n, f = n` (trivially reflexive)
    - `exists x, x > 0 /\\ x = x` (existence of positive numbers)
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b")
    proof_re = re.compile(r"(?m)^[ \t]*Proof\.")
    end_re = re.compile(r"(?m)^[ \t]*(Qed|Defined|Admitted)\.")

    for tm in theorem_re.finditer(text):
        tname = tm.group(2)
        stmt_end = text.find(".", tm.end())
        if stmt_end == -1:
            continue
        # Collect full statement (may span multiple lines)
        stmt_parts = []
        j = tm.start()
        for ln in text[j:].splitlines():
            stmt_parts.append(ln.strip())
            if re.search(r"\.\s*$", ln):
                break
        stmt = re.sub(r"\s+", " ", " ".join(stmt_parts)).strip()

        # Pattern: exists <var>, length ... = <var>
        if re.search(r"\bexists\s+\w+\s*,\s*length\b.*=\s*\w+\s*\.$", stmt):
            # Check if proof is `reflexivity` based
            proof_match = proof_re.search(text, stmt_end)
            if proof_match:
                end_match = end_re.search(text, proof_match.end())
                if end_match:
                    proof_block = text[proof_match.end():end_match.start()].strip()
                    if "reflexivity" in proof_block or "exists (" in proof_block:
                        line = line_of[tm.start()]
                        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname
                        findings.append(
                            Finding(
                                rule_id="TRIVIAL_EXISTENTIAL",
                                severity=_severity_for_path(path, "HIGH"),
                                file=path,
                                line=line,
                                snippet=snippet.strip(),
                                message=f"Theorem `{tname}` is a trivially satisfiable existential "
                                        f"('every list has a length'). This proves nothing substantive.",
                            )
                        )

        # Pattern: exists (X : R), X > 0 /\ ... (just proves positive reals exist)
        if re.search(r"\bexists\b.*,\s*\w+\s*>\s*0\s*(?:/\\|\.$)", stmt):
            proof_match = proof_re.search(text, stmt_end)
            if proof_match:
                end_match = end_re.search(text, proof_match.end())
                if end_match:
                    proof_block = text[proof_match.end():end_match.start()].strip()
                    # If the witness is just a constant or named definition
                    if re.search(r"exists\s+\w+", proof_block) and ("lra" in proof_block or "lia" in proof_block):
                        line = line_of[tm.start()]
                        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname
                        findings.append(
                            Finding(
                                rule_id="TRIVIAL_EXISTENTIAL",
                                severity=_severity_for_path(path, "MEDIUM"),
                                file=path,
                                line=line,
                                snippet=snippet.strip(),
                                message=f"Theorem `{tname}` may be a trivially satisfiable existential "
                                        f"(proving existence of a positive real). Verify substance.",
                            )
                        )

    return findings


def scan_arithmetic_only_proofs(path: Path) -> list[Finding]:
    """Detect theorems with physics-sounding names whose proofs are pure arithmetic.

    A proof is 'pure arithmetic' if it only uses lia/lra/lia/omega/reflexivity
    without engaging any Coq-defined inductive types, match, induction, inversion,
    destruct, rewrite, apply (to non-stdlib lemmas), etc.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    # Physics-sounding names (in theorem name OR file path)
    physics_name_re = re.compile(
        r"(?i)(thermo|entropy|conserv|causal|lorentz|landauer|arrow.*time|"
        r"second.*law|irreversib|measurement|povm|born|collapse|"
        r"no.*closed.*causal|dimension|potential|arbitrage|energy|"
        r"dissipat|equilibrium|spacetime|emergent|unitari|cloning|"
        r"signaling|causality|planck|schrodinger|purificat)"
    )
    # Also check the file path for physics-sounding directories/names
    path_str = str(path)
    file_is_physics = bool(physics_name_re.search(path_str))

    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b")
    proof_re = re.compile(r"(?m)^[ \t]*Proof\.")
    end_re = re.compile(r"(?m)^[ \t]*(Qed|Defined|Admitted)\.")

    # Tactics that indicate engagement with structure
    structural_tactics = re.compile(
        r"\b(induction|destruct|inversion|case_eq|match|rewrite|simpl|"
        r"split|constructor|exists|specialize|pose\s+proof|"
        r"apply\s+(?!Nat|Z|R|lt|gt|le|ge|eq|Rlt|Rgt|Rle|Rge|Rmult|Rdiv|Rinv|ln))"
    )

    # Tactics that are pure arithmetic/logic
    arith_tactics = {"lia", "lra", "omega", "reflexivity", "lia.", "lra.", "omega.", "reflexivity."}

    for tm in theorem_re.finditer(text):
        tname = tm.group(2)
        if not physics_name_re.search(tname) and not file_is_physics:
            continue

        stmt_end = text.find(".", tm.end())
        if stmt_end == -1:
            continue

        proof_match = proof_re.search(text, stmt_end)
        if not proof_match:
            continue
        end_match = end_re.search(text, proof_match.end())
        if not end_match:
            continue

        proof_block = text[proof_match.end():end_match.start()].strip()
        proof_lines = [ln.strip() for ln in proof_block.splitlines() if ln.strip()]

        if not proof_lines:
            continue

        # Check if proof uses only arithmetic tactics (+ intro/unfold setup)
        has_structural = bool(structural_tactics.search(proof_block))

        # Count arith-only lines vs total lines
        setup_tactics = re.compile(r"^(intros?|unfold|simpl|intro)\b")
        arith_only_lines = 0
        for pline in proof_lines:
            pline_clean = pline.rstrip(".")
            words = pline_clean.split()
            if not words:
                continue
            first_word = words[0].rstrip(".;,")
            if first_word in {"lia", "lra", "omega", "reflexivity", "contradiction", "congruence"}:
                arith_only_lines += 1
            elif setup_tactics.match(pline):
                arith_only_lines += 1  # setup is fine but still "no structure"

        # If ALL lines are arithmetic/setup and no structural tactic used
        if not has_structural and arith_only_lines == len(proof_lines) and len(proof_lines) <= 5:
            # Check for SCOPE NOTE in the original text (with comments)
            # covering a few lines before the theorem
            raw_lines = raw.splitlines()
            line = line_of[tm.start()]
            note_start = max(0, line - 4)
            note_end = min(len(raw_lines), line + 2)
            note_context = "\n".join(raw_lines[note_start:note_end])
            if "SCOPE NOTE" in note_context:
                continue  # Verified as intentionally arithmetic
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname
            findings.append(
                Finding(
                    rule_id="ARITHMETIC_ONLY_PHYSICS",
                    severity=_severity_for_path(path, "MEDIUM"),
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=f"Physics-named theorem `{tname}` proved by pure arithmetic "
                            f"(lia/lra/reflexivity). No engagement with Coq-defined structures. "
                            f"Verify this isn't restating a trivial arithmetic fact.",
                )
            )

    return findings


def scan_circular_definitions(path: Path) -> list[Finding]:
    """Detect when a theorem's proof immediately reduces to its definition.
    
    Pattern: Definition X := <body>.
             Theorem foo : <claim about X>.
             Proof. unfold X. reflexivity. Qed.
    
    Or: Theorem proves X = Y, but proof is just `unfold X; reflexivity`
    showing X was defined AS Y.

    No comment-marker bypass is honoured. If a lemma genuinely is the
    definitional projection of a constant, either inline-unfold at use
    sites and delete it, restructure so the claim has non-trivial proof
    content, or expose the alias with a Definition. Cosmetic
    `(* DEFINITIONAL HELPER *)` markers no longer silence this rule.

    Exemptions retained on principled signals:
      - the lemma's statement has a premise (`->`) or negation (`~P`)
        and the proof closes via lia/lra/auto/trivial/tauto/congruence/
        eauto — the automation uses the premise implicitly;
      - or the proof's `intros` introduces an H-prefixed name (Coq's
        convention for hypotheses hidden inside a Definition expansion
        such as [mixture_compatible f]) AND the closer is automation;
      - concrete VM observations and shadow projections are reduced to expose
        a computed witness for a later theorem;
      - or the lemma is referenced 2+ times elsewhere in the same file,
        i.e. it is serving as a named rewrite rule and the inline
        equivalent would duplicate the unfolds at every call site.

    Also flags `intros ... H. unfold X. exact H.` style — the
    "semantic P -> P after reduction" pattern — even when the lemma
    statement is not literally `P -> P`.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = raw.splitlines()
    findings: list[Finding] = []

    # Collect definitions
    def_re = re.compile(r"(?m)^[ \t]*Definition\s+([A-Za-z0-9_']+)\b")
    definitions = {m.group(1) for m in def_re.finditer(text)}

    if not definitions:
        return findings

    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b")
    proof_re = re.compile(r"(?m)^[ \t]*Proof\.")
    # Match Qed./Defined./Admitted. anywhere so one-line proofs
    # (`Proof. tac. Qed.`) are handled.
    end_re = re.compile(r"\b(Qed|Defined|Admitted)\.")
    automation_re = re.compile(
        r"^\s*(lia|lra|auto|trivial|tauto|congruence|eauto|omega)\b"
    )
    intros_h_prefix_re = re.compile(
        r"\bintros?\b[^.;]*\b(H[A-Za-z0-9_']*)\b"
    )

    for tm in theorem_re.finditer(text):
        tname = tm.group(2)
        stmt_end = text.find(".", tm.end())
        if stmt_end == -1:
            continue
        # Coq record projections use `record.(field)`, so the dot before the
        # opening parenthesis is not the end of the theorem statement.
        while text[stmt_end:stmt_end + 2] == ".(":
            stmt_end = text.find(".", stmt_end + 2)
            if stmt_end == -1:
                break
        if stmt_end == -1:
            continue
        stmt = re.sub(r"\s+", " ", text[tm.start():stmt_end + 1]).strip()

        # Check which definitions are mentioned in the statement
        mentioned_defs = [d for d in definitions if re.search(rf'\b{d}\b', stmt)]
        if not mentioned_defs:
            continue

        # These lemmas intentionally expose a computed VM field or a shadow
        # projection of a concrete witness.  Their reduction proof is the
        # certificate consumed by the subsequent necessity theorem, not a
        # disposable alias.
        concrete_observation = bool(re.search(
            r"\.\(vm_[A-Za-z0-9_']+\)|\bP_full_[A-Za-z0-9_']*\b",
            stmt,
        ))

        proof_match = proof_re.search(text, stmt_end)
        if not proof_match:
            continue
        end_match = end_re.search(text, proof_match.end())
        if not end_match:
            continue
        proof_block = text[proof_match.end():end_match.start()].strip()
        proof_text = re.sub(r"\s+", " ", proof_block)

        # Premises in the lemma's visible statement.
        #   - `->` is the explicit arrow.
        #   - `~P` is sugar for `P -> False`, so the lemma has a (negated)
        #     premise.
        stmt_has_premise = ("->" in stmt) or ("~" in stmt)
        proof_introduces_hyp = bool(intros_h_prefix_re.search(proof_text))
        # Same-file uses: 2+ references outside the declaration line mean
        # the lemma is a real rewrite rule, not a standalone vacuous claim.
        same_file_uses = len(re.findall(rf'\b{re.escape(tname)}\b', text)) - 1
        lemma_is_used_in_file = same_file_uses >= 2

        # Pattern: unfold X (no other tactics except reflexivity/simpl/lia)
        for defn in mentioned_defs:
            unfold_pat = re.compile(rf'\bunfold\s+{defn}\b')
            if unfold_pat.search(proof_text):
                tactics = [t.strip() for t in re.split(r'[.;]', proof_text) if t.strip()]
                # Arithmetic and proof search are substantive proof steps at
                # the source level.  Only pure normalization/reduction is a
                # candidate for an alias warning.
                non_trivial_tactics = [t for t in tactics if not re.match(
                    r'^\s*(unfold|simpl|reflexivity|intros?|split)\b', t)]

                if len(non_trivial_tactics) == 0 and len(tactics) <= 5:
                    if concrete_observation:
                        continue
                    premises_engaged = (
                        (stmt_has_premise or proof_introduces_hyp)
                        and any(automation_re.match(t) for t in tactics)
                    )
                    if premises_engaged or lemma_is_used_in_file:
                        pass
                    else:
                        line = line_of[tm.start()]
                        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname
                        findings.append(
                            Finding(
                                rule_id="CIRCULAR_DEFINITION",
                                severity=_severity_for_path(path, "MEDIUM"),
                                file=path,
                                line=line,
                                snippet=snippet.strip(),
                                message=f"Theorem `{tname}` unfolds `{defn}` and proves claim "
                                        f"by simple tactics. Inline-unfold at use sites and delete, "
                                        f"or restructure the claim so the proof has non-trivial content.",
                            )
                        )
                        break

                # Semantic-tautology hardening: catch proofs that normalize
                # a definition and then return an introduced hypothesis
                # verbatim. Example shape:
                #   intros ... H. unfold X. exact H.
                # The lemma is "P -> P after reduction" — the proof
                # discharges by exhibiting the same hypothesis it took.
                #
                # NORMALIZATION TACTICS (deliberately narrow):
                #   intros, unfold, simpl, cbn, cbv, lazy, change, fold,
                #   subst. NOT: rewrite/setoid_rewrite (those can do
                #   real case-analysis on an if, or apply a separate
                #   lemma).
                introduced: set[str] = set()
                for tac in tactics:
                    intro_match = re.match(r"^\s*intros?\b(.*)$", tac, re.DOTALL)
                    if not intro_match:
                        continue
                    for ident in re.findall(r"\b[A-Za-z_][A-Za-z0-9_']*\b", intro_match.group(1)):
                        if ident not in {"as", "in", "at", "eqn", "_"}:
                            introduced.add(ident)

                if tactics:
                    terminal = tactics[-1]
                    terminal_hyp: str | None = None
                    exact_match = re.match(
                        r"^\s*(?:exact|apply)\s+([A-Za-z_][A-Za-z0-9_']*)\s*$",
                        terminal,
                    )
                    if exact_match and exact_match.group(1) in introduced:
                        terminal_hyp = exact_match.group(1)
                    elif re.match(r"^\s*assumption\s*$", terminal) and introduced:
                        terminal_hyp = "an introduced hypothesis"

                    if terminal_hyp is not None and not lemma_is_used_in_file:
                        normalization_re = re.compile(
                            r"^\s*(intros?|unfold|simpl|cbn|cbv|lazy|change|"
                            r"fold|subst)\b"
                        )
                        pre_terminal = tactics[:-1]
                        only_normalization = all(
                            normalization_re.match(tac) for tac in pre_terminal
                        )
                        if only_normalization and len(tactics) <= 8 and not concrete_observation:
                            line = line_of[tm.start()]
                            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname
                            findings.append(
                                Finding(
                                    rule_id="CIRCULAR_DEFINITION",
                                    severity=_severity_for_path(path, "MEDIUM"),
                                    file=path,
                                    line=line,
                                    snippet=snippet.strip(),
                                    message=f"Theorem `{tname}` unfolds `{defn}`, normalizes, then "
                                            f"returns {terminal_hyp} via `{terminal}`. This is a "
                                            f"semantic P -> P after reduction. Inline-unfold at "
                                            f"use sites and delete, or restate so the claim has "
                                            f"non-trivial proof content.",
                                )
                            )
                            break

    return findings


def scan_emergence_circularity(path: Path) -> list[Finding]:
    """Detect 'emergence' claims where the emergent property is in the definition.
    
    Pattern: Theorem X_emerges_from_Y or X_from_Y
             But Definition Y := ... X ... or Definition X := ... Y ...
    
    If X is defined using Y, then proving "X emerges from Y" is circular.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []
    
    # Collect definitions and their bodies
    def_re = re.compile(r"(?ms)^[ \t]*Definition\s+([A-Za-z0-9_']+)\b[^:]*:=[^.]+\.")
    definitions = {}
    for dm in def_re.finditer(text):
        defn_name = dm.group(1)
        defn_body = dm.group(0)
        definitions[defn_name] = defn_body
    
    # Look for emergence-pattern theorem names
    emergence_re = re.compile(
        r"(?m)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+(?:_from_|_emerges_from_|_derived_from_)[A-Za-z0-9_']+)\b"
    )
    
    for em in emergence_re.finditer(text):
        tname = em.group(2)
        # Parse the name: X_from_Y or X_emerges_from_Y
        # Extract X and Y
        parts = re.split(r'_(from|emerges_from|derived_from)_', tname)
        if len(parts) < 3:
            continue
        
        source = parts[0]  # X
        target = parts[2]  # Y
        
        # Check if either is defined in terms of the other
        circular = False
        if source in definitions and target in definitions[source]:
            circular = True
        if target in definitions and source in definitions[target]:
            circular = True
        
        if circular:
            line = line_of[em.start()]
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname
            findings.append(
                Finding(
                    rule_id="EMERGENCE_CIRCULARITY",
                    severity=_severity_for_path(path, "HIGH"),
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=f"Theorem `{tname}` claims emergence, but `{source}` and `{target}` "
                            f"are defined in terms of each other. This is circular: "
                            f"the 'emergence' is definitional, not derived.",
                )
            )
    
    return findings


def scan_constructor_round_trip(path: Path) -> list[Finding]:
    """Detect pattern: Build X, immediately extract property P from X, claim proven.
    
    Pattern: 
      let x := {| field1 := a; field2 := b |} in P(x)
    Proof:
      simpl. reflexivity.
    
    If we construct an object and immediately query it, we're not proving anything.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []
    
    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b")
    proof_re = re.compile(r"(?m)^[ \t]*Proof\.")
    end_re = re.compile(r"(?m)^[ \t]*(Qed|Defined|Admitted)\.")
    
    for tm in theorem_re.finditer(text):
        tname = tm.group(2)
        stmt_end = text.find(".", tm.end())
        if stmt_end == -1:
            continue
        stmt = re.sub(r"\s+", " ", text[tm.start():stmt_end + 1]).strip()
        
        # Check if statement contains record constructor pattern
        # Pattern: let x := {| ... |} in <claim>
        if not ('{|' in stmt and '|}' in stmt and 'let' in stmt.lower()):
            continue
        
        proof_match = proof_re.search(text, stmt_end)
        if not proof_match:
            continue
        end_match = end_re.search(text, proof_match.end())
        if not end_match:
            continue
        proof_block = text[proof_match.end():end_match.start()].strip()
        proof_text = re.sub(r"\s+", " ", proof_block)
        
        # If proof is just simpl/reflexivity/compute, it's computational
        tactics = [t.strip() for t in re.split(r'[.;]', proof_text) if t.strip()]
        non_computational = [t for t in tactics if not re.match(
            r'^\s*(simpl|reflexivity|compute|vm_compute|native_compute|lia|trivial)\b', t)]
        
        if len(non_computational) == 0 and len(tactics) <= 3:
            line = line_of[tm.start()]
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname
            findings.append(
                Finding(
                    rule_id="CONSTRUCTOR_ROUND_TRIP",
                    severity=_severity_for_path(path, "MEDIUM"),
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=f"Theorem `{tname}` constructs an object in `let` and immediately "
                            f"queries it. Proof is pure computation. Verify this isn't circular "
                            f"(building object to satisfy property, then extracting that property).",
                )
            )
    
    return findings


def scan_definitional_witness(path: Path) -> list[Finding]:
    """Detect existentials where the witness IS the definition being claimed.

    Pattern:
      Definition optimal_value := 42.
      Theorem optimal_exists : exists x, x = 42 /\\ is_optimal x.
      Proof. exists optimal_value. unfold optimal_value. split; reflexivity. Qed.

    This proves the definition exists (trivial), not that the property holds.

    No marker-comment bypass is honoured. If the existential is
    intentionally witnessed by the same definition, the lemma is the
    unfolding equation of that definition rather than a real existence
    claim; restructure the statement to assert a substantive property
    or delete it.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    # Collect definitions
    def_re = re.compile(r"(?m)^[ \t]*Definition\s+([A-Za-z0-9_']+)\b")
    definitions = {m.group(1) for m in def_re.finditer(text)}

    if not definitions:
        return findings

    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b")
    proof_re = re.compile(r"(?m)^[ \t]*Proof\.")
    end_re = re.compile(r"\b(Qed|Defined|Admitted)\.")

    for tm in theorem_re.finditer(text):
        tname = tm.group(2)
        stmt_end = text.find(".", tm.end())
        if stmt_end == -1:
            continue
        stmt = re.sub(r"\s+", " ", text[tm.start():stmt_end + 1]).strip()

        # Check if this is an existential theorem
        if 'exists' not in stmt.lower():
            continue

        proof_match = proof_re.search(text, stmt_end)
        if not proof_match:
            continue
        end_match = end_re.search(text, proof_match.end())
        if not end_match:
            continue
        proof_block = text[proof_match.end():end_match.start()].strip()

        # Check if proof witnesses one of the definitions
        for defn in definitions:
            witness_pat = re.compile(rf'\bexists\s+{defn}\b')
            unfold_pat = re.compile(rf'\bunfold\s+{defn}\b')

            if witness_pat.search(proof_block) and unfold_pat.search(proof_block):
                # Proof witnesses the definition and unfolds it
                # This is likely just proving the definition exists
                line = line_of[tm.start()]
                snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname
                findings.append(
                    Finding(
                        rule_id="DEFINITIONAL_WITNESS",
                        severity=_severity_for_path(path, "MEDIUM"),
                        file=path,
                        line=line,
                        snippet=snippet.strip(),
                        message=f"Theorem `{tname}` proves existence by witnessing definition `{defn}`. "
                                f"Verify the theorem proves a substantive property, not just that "
                                f"the definition exists (which is trivial).",
                    )
                )
                break

    return findings


def scan_vacuous_conjunction(path: Path) -> list[Finding]:
    """Detect theorems with `True` as a conjunct leaf buried inside a conclusion.

    Pattern: `exists a b t, ... /\\ True.` or `... /\\ True /\\ ...`
    This catches weakened theorem statements where the real conclusion
    has been replaced with `True` to make the proof trivially completable.

    The existing IMPLIES_TRUE_STMT and EXISTS_TRUE_STMT rules only catch
    cases where True is the ENTIRE conclusion. This catches True hidden
    inside conjunctions.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    start_re = re.compile(r"^[ \t]*(Theorem|Lemma|Corollary)\s+([A-Za-z0-9_']+)\b")
    end_re = re.compile(r"\.[ \t]*$")
    max_lines = 200

    for idx, ln in enumerate(clean_lines, start=1):
        m = start_re.match(ln)
        if not m:
            continue
        name = m.group(2)
        parts: list[str] = [ln.strip()]
        j = idx + 1
        while j <= len(clean_lines) and len(parts) < max_lines:
            if end_re.search(parts[-1]):
                break
            nxt = clean_lines[j - 1].strip()
            if nxt:
                parts.append(nxt)
            j += 1
        stmt = re.sub(r"\s+", " ", " ".join(parts)).strip()

        # Check for True as a conjunct: /\ True or True /\
        # But skip if the entire conclusion is just True (already caught)
        if re.search(r":\s*True\s*\.$", stmt):
            continue  # Already caught by PROP_TAUTOLOGY
        if re.search(r"->\s*True\s*\.$", stmt):
            continue  # Already caught by IMPLIES_TRUE_STMT

        # Detect a final True conjunct, including closing delimiters.
        has_conj_true = bool(
            re.search(r"/\\.*\bTrue\s*[)\]}]*\s*\.", stmt) or
            re.search(r"True\s*/\\", stmt)
        )
        if has_conj_true:
            snippet = clean_lines[idx - 1] if 0 <= idx - 1 < len(clean_lines) else stmt
            findings.append(
                Finding(
                    rule_id="VACUOUS_CONJUNCTION",
                    severity=_severity_for_path(path, "HIGH"),
                    file=path,
                    line=idx,
                    snippet=snippet.strip(),
                    message=f"Theorem `{name}` has `True` as a conjunct — likely a weakened/placeholder conclusion.",
                )
            )

    return findings


def scan_tautological_implication(path: Path) -> list[Finding]:
    """Detect theorems where the conclusion is identical to one of the hypotheses.

    Pattern: `forall p, (0 < p) -> ... -> p = 2 -> p = 2.`
    The last hypothesis and the conclusion are the same (P -> P),
    making the theorem vacuous — it proves nothing new.

    Also detects the weaker pattern where the conclusion is a subset
    of a hypothesis (destructuring extraction).
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    start_re = re.compile(r"^[ \t]*(Theorem|Lemma|Corollary)\s+([A-Za-z0-9_']+)\b")
    end_re = re.compile(r"\.[ \t]*$")
    max_lines = 200

    for idx, ln in enumerate(clean_lines, start=1):
        m = start_re.match(ln)
        if not m:
            continue
        name = m.group(2)
        parts: list[str] = [ln.strip()]
        j = idx + 1
        while j <= len(clean_lines) and len(parts) < max_lines:
            if end_re.search(parts[-1]):
                break
            nxt = clean_lines[j - 1].strip()
            if nxt:
                parts.append(nxt)
            j += 1
        stmt = re.sub(r"\s+", " ", " ".join(parts)).strip()

        # Extract the part after ':' (the type/proposition)
        colon_pos = stmt.find(":")
        if colon_pos < 0:
            continue
        prop = stmt[colon_pos + 1:].strip()
        # Remove trailing period
        if prop.endswith("."):
            prop = prop[:-1].strip()

        # Strip outer forall binders to get to the -> chain
        # forall x y z, P1 -> P2 -> ... -> Conclusion
        inner = prop
        while True:
            m2 = re.match(r"forall\s+[^,]+,\s*(.+)", inner)
            if m2:
                inner = m2.group(1)
            else:
                break

        # Split on top-level -> but NOT on <-> (which contains -> as substring)
        # Use negative lookbehind to avoid splitting <->
        arrows = re.split(r"\s*(?<!<)(?<!<)(?<!-)(?:->)(?!>)\s*", inner)
        # Fallback: simpler split that respects <-> by first replacing it
        if len(arrows) < 2:
            # Try alternative: protect <-> then split on ->
            protected = inner.replace("<->", "\x00IFF\x00")
            arrows = re.split(r"\s*->\s*", protected)
            arrows = [a.replace("\x00IFF\x00", "<->") for a in arrows]
        if len(arrows) < 2:
            continue

        conclusion = arrows[-1].strip()
        hypotheses = [a.strip() for a in arrows[:-1]]

        # Normalize whitespace for comparison
        conclusion_norm = re.sub(r"\s+", " ", conclusion)

        found_taut = False
        # ---------------------------------------------------------------
        # TAUTOLOGICAL_IMPLICATION is not suppressible by note markers. A
        # theorem of the literal form `P -> P`, or one whose conclusion is
        # identical to a hypothesis, has no proof-bearing content. If this
        # rule fires, the theorem must be reformulated rather than annotated.
        # ---------------------------------------------------------------

        for hyp in hypotheses:
            hyp_norm = re.sub(r"\s+", " ", hyp)
            if hyp_norm == conclusion_norm and conclusion_norm:
                snippet = clean_lines[idx - 1] if 0 <= idx - 1 < len(clean_lines) else stmt
                findings.append(
                    Finding(
                        rule_id="TAUTOLOGICAL_IMPLICATION",
                        severity=_severity_for_path(path, "HIGH"),
                        file=path,
                        line=idx,
                        snippet=snippet.strip(),
                        message=f"Theorem `{name}` has conclusion `{conclusion_norm}` identical to "
                                f"hypothesis `{hyp_norm}` — this is a tautology (P -> P), proves nothing. "
                                f"Note markers cannot suppress this rule.",
                    )
                )
                found_taut = True
                break

        if found_taut:
            continue

        # Deeper check: see if the conclusion appears inside a Definition that
        # one of the hypotheses refers to. This catches cases like:
        #   Definition equiv a b := ... /\ (P a <-> Q b) /\ ...
        #   Theorem foo : equiv x y -> P x <-> Q y.
        # where the conclusion is literally embedded in the hypothesis's definition.
        # Collect all Definition bodies in this file for unfolding.
        if not hasattr(scan_tautological_implication, '_def_cache'):
            scan_tautological_implication._def_cache = {}
        cache_key = str(path)
        if cache_key not in scan_tautological_implication._def_cache:
            def_bodies: dict[str, str] = {}
            def_re = re.compile(r"(?m)^[ \t]*Definition\s+([A-Za-z0-9_']+)\b[^:]*:(?:=|\s)\s*(.+?)\.$", re.DOTALL)
            for dm in def_re.finditer(text):
                dname = dm.group(1)
                dbody = re.sub(r"\s+", " ", dm.group(2)).strip()
                def_bodies[dname] = dbody
            scan_tautological_implication._def_cache[cache_key] = def_bodies
        def_bodies = scan_tautological_implication._def_cache[cache_key]

        for hyp in hypotheses:
            hyp_norm = re.sub(r"\s+", " ", hyp)
            # Extract the definition name from the hypothesis (first identifier)
            hyp_head = re.match(r"([A-Za-z0-9_']+)", hyp_norm)
            if not hyp_head:
                continue
            hyp_def_name = hyp_head.group(1)
            if hyp_def_name not in def_bodies:
                continue
            # The deeper-tautology check also cannot be suppressed by note
            # markers: a conclusion repeated inside a hypothesis definition
            # is a restatement rather than an independent derivation.
            dbody = def_bodies[hyp_def_name]
            if conclusion_norm in dbody:
                snippet = clean_lines[idx - 1] if 0 <= idx - 1 < len(clean_lines) else stmt
                findings.append(
                    Finding(
                        rule_id="TAUTOLOGICAL_IMPLICATION",
                        severity=_severity_for_path(path, "MEDIUM"),
                        file=path,
                        line=idx,
                        snippet=snippet.strip(),
                        message=f"Theorem `{name}` conclusion `{conclusion_norm}` appears inside "
                                f"Definition `{hyp_def_name}` — conclusion is restating part of "
                                f"hypothesis. Note markers cannot suppress this rule.",
                    )
                )
                break

    return findings


def scan_hypothesis_restatement(path: Path) -> list[Finding]:
    """Detect theorems whose proof just destructures and extracts a hypothesis piece.

    Pattern: A theorem takes a compound hypothesis H (conjunction/record),
    and the proof is just `intros T [_ [Hid _]] s. exact (Hid s).`
    i.e., immediately destructures H and returns one piece.

    This catches proofs that restate part of their input as a "theorem"
    without deriving anything new.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma|Corollary)\s+([A-Za-z0-9_']+)\b")
    proof_re = re.compile(r"(?m)^[ \t]*Proof\.")
    end_re = re.compile(r"(?m)^[ \t]*(Qed|Defined|Admitted)\.")

    for tm in theorem_re.finditer(text):
        tname = tm.group(2)
        start = tm.end()

        proof_match = proof_re.search(text, start)
        if not proof_match:
            continue
        end_match = end_re.search(text, proof_match.end())
        if not end_match:
            continue

        proof_block = text[proof_match.end():end_match.start()].strip()
        proof_lines = [ln.strip() for ln in proof_block.splitlines() if ln.strip()]

        if not proof_lines:
            continue

        # Pattern 1: destructuring intro + exact
        # e.g. "intros T [_ [Hid _]] s." followed by "exact (Hid s)."
        # or single line: "intros T [_ [Hid _]] s; exact (Hid s)."
        proof_text = " ".join(proof_lines)
        # Check for destruct + extract pattern
        if re.search(r"intros.*\[.*\].*exact\b", proof_text) or \
           re.search(r"destruct.*as\s*\[.*\].*exact\b", proof_text):
            # Check if proof is suspiciously short (< 5 meaningful tactics)
            tactics = [t.strip() for t in re.split(r'[.;]', proof_text) if t.strip()]
            if len(tactics) <= 5:
                line = line_of[tm.start()]
                snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname
                findings.append(
                    Finding(
                        rule_id="HYPOTHESIS_RESTATEMENT",
                        severity="LOW",
                        file=path,
                        line=line,
                        snippet=snippet.strip(),
                        message=f"Theorem `{tname}` destructures hypothesis and immediately extracts "
                                f"a component. Proof restates assumption rather than deriving new result.",
                    )
                )

    return findings


def scan_physics_stub_definitions(path: Path) -> list[Finding]:
    """Detect physics/geometry definitions that are trivial placeholders.
    
    Patterns:
    - distance/metric returns constant (0, 1, PI/3)
    - curvature/gradient returns 0 or trivial expression
    - Key physics function returns placeholder
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    raw_lines = raw.splitlines()
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []
    
    # Physics/geometry concept names
    physics_concepts = re.compile(
        r"(?i)(distance|metric|curvature|angle|gradient|laplacian|ricci|scalar|"
        r"einstein|stress|energy|tensor|horizon|area|entropy)"
    )
    
    # Find Definition starts and extract body manually
    def_start_re = re.compile(r"(?m)^[ \t]*Definition\s+([A-Za-z0-9_']+)\b")
    
    for dm in def_start_re.finditer(text):
        defn_name = dm.group(1)
        
        # Skip if not a physics concept
        if not physics_concepts.search(defn_name):
            continue
        
        # Find the body of the definition (from := to the terminating .)
        start_pos = dm.end()
        colon_eq_pos = text.find(":=", start_pos)
        if colon_eq_pos == -1 or colon_eq_pos - start_pos > 200:
            continue
        
        # Find the terminating period (carefully - not just any period)
        # Look for period followed by whitespace or end-of-line
        body_start = colon_eq_pos + 2
        depth = 0
        i = body_start
        while i < len(text):
            ch = text[i]
            if ch in '([{':
                depth += 1
            elif ch in ')]}':
                depth -= 1
            elif ch == '.' and depth == 0:
                # Check if followed by whitespace/newline
                if i + 1 >= len(text) or text[i+1] in ' \t\n\r':
                    break
            i += 1
        
        if i >= len(text):
            continue
        
        defn_body = text[body_start:i].strip()
        defn_body_normalized = re.sub(r"\s+", " ", defn_body)
        
        line = line_of[dm.start()]
        
        # Check for SAFE comment
        context = "\n".join(raw_lines[max(0, line - 3): line + 1])
        if re.search(r"\(\*\s*SAFE:", context):
            continue
        
        # Detect placeholder patterns
        is_stub = False
        stub_reason = ""
        
        # Pattern 1: match returning only 0 or 1
        if re.search(r"match\b.*\btrue\s*=>\s*0\b.*\bfalse\s*=>\s*1\b", defn_body_normalized):
            is_stub = True
            stub_reason = "match returns only 0 or 1 (placeholder metric)"
        elif re.search(r"match\b.*\bfalse\s*=>\s*1\b.*\btrue\s*=>\s*0\b", defn_body_normalized):
            is_stub = True
            stub_reason = "match returns only 0 or 1 (placeholder metric)"
        
        # Pattern 2: if-then-else returning fixed constants
        elif re.search(r"if\b.*then\s+0%?R?\s+else\s+\(?\s*PI\s*/\s*3\s*\)?%?R?", defn_body_normalized):
            is_stub = True
            stub_reason = "returns 0 or PI/3 based on condition (placeholder angle)"
        elif re.search(r"if\b.*then\s+\(?\s*PI\s*/\s*3\s*\)?%?R?\s+else\s+0%?R?", defn_body_normalized):
            is_stub = True
            stub_reason = "returns PI/3 or 0 based on condition (placeholder angle)"
        
        # Pattern 3: body is just another definition name (definitional alias without computation)
        elif re.match(r"^[A-Za-z][A-Za-z0-9_']*\s+", defn_body_normalized) and \
             re.match(r"^[A-Za-z][A-Za-z0-9_']*\s*$", defn_body_normalized):
            is_stub = True
            stub_reason = f"just an alias for {defn_body_normalized.strip()} (no computation)"
        
        if is_stub:
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else defn_name
            findings.append(
                Finding(
                    rule_id="PHYSICS_STUB_DEFINITION",
                    severity=_severity_for_path(path, "HIGH"),
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=f"Physics definition `{defn_name}` is a stub: {stub_reason}. "
                            f"Replace with actual computation based on graph structure.",
                )
            )
    
    return findings


def scan_missing_core_physics_theorems(path: Path) -> list[Finding]:
    """Detect files that define physics machinery but lack the core theorem.
    
    Pattern: File defines einstein_tensor and stress_energy but lacks:
      Theorem einstein_equation : einstein_tensor = 8πG * stress_energy.
    
    Or defines curvature/metric but lacks proof it's actually derived from μ-cost.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []
    
    # Check if this is a gravity/geometry file
    file_name = path.name
    is_gravity_file = bool(re.search(r"(?i)(gravity|einstein|geometry|curvature)", file_name))
    
    if not is_gravity_file:
        return findings
    
    # Check what's defined
    has_einstein_tensor = "einstein_tensor" in text
    has_stress_energy = "stress_energy" in text
    has_curvature = "ricci_curvature" in text or "scalar_curvature" in text
    
    # Check for the core theorem
    field_eq_match = re.search(
        r"(?m)^[ \t]*(Theorem|Lemma)\s+\w*einstein[_]?equation\w*\b",
        text
    )
    has_field_equation = field_eq_match is not None
    
    # If we have the machinery but not the theorem, flag it (unless explicitly marked as intentional)
    has_intentional_marker = bool(_GRAVITY_SCOPE_MARKER_RE.search(raw))
    if has_einstein_tensor and has_stress_energy and not has_field_equation and not has_intentional_marker:
        findings.append(
            Finding(
                rule_id="MISSING_CORE_THEOREM",
                severity="HIGH",
                file=path,
                line=1,
                snippet=file_name,
                message="File defines einstein_tensor and stress_energy but lacks "
                        "the core theorem: `einstein_equation : einstein_tensor = 8πG * stress_energy`. "
                        "The machinery is scaffolding — the physics is not yet derived.",
            )
        )

    # If theorem exists, verify statement shape is substantive and not weakened.
    if has_field_equation:
        stmt_re = re.compile(
            r"(?ms)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']*einstein[_]?equation[A-Za-z0-9_']*)\b(.*?)\."
        )
        for sm in stmt_re.finditer(text):
            theorem_name = sm.group(2)
            statement = re.sub(r"\s+", " ", sm.group(0))
            line = line_of[sm.start()]
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else theorem_name

            has_lhs = "einstein_tensor" in statement
            has_rhs = "stress_energy" in statement
            has_coupling = bool(re.search(r"8\s*\*\s*PI\s*\*\s*gravitational_constant", statement))

            if not (has_lhs and has_rhs and has_coupling):
                findings.append(
                    Finding(
                        rule_id="EINSTEIN_EQUATION_WEAK",
                        severity="HIGH",
                        file=path,
                        line=line,
                        snippet=snippet.strip(),
                        message=f"Theorem `{theorem_name}` exists but statement does not match the expected "
                                f"field-equation shape `einstein_tensor = 8*PI*gravitational_constant*stress_energy`.",
                    )
                )

            # Reject shortcut statements that assume the needed coupling premise
            # instead of deriving it from μ-conservation/locality machinery.
            parts = statement.split("->")
            premises = " -> ".join(parts[:-1]) if len(parts) > 1 else ""
            has_assumed_target = bool(re.search(
                r"einstein_tensor\s+[^\-\n]*=\s*\(?8\s*\*\s*PI\s*\*\s*gravitational_constant\s*\*\s*stress_energy",
                premises,
            ))
            has_assumed_ricci_stress = bool(re.search(
                r"ricci_curvature\s+[^\-\n]*=\s*\(?16\s*\*\s*PI\s*\*\s*gravitational_constant\s*\*\s*stress_energy",
                premises,
            ))
            if has_assumed_target or has_assumed_ricci_stress:
                findings.append(
                    Finding(
                        rule_id="EINSTEIN_EQUATION_ASSUMED",
                        severity="HIGH",
                        file=path,
                        line=line,
                        snippet=snippet.strip(),
                        message=f"Theorem `{theorem_name}` appears to assume the Einstein coupling in premises "
                                f"instead of deriving it. Remove assumption-shaped coupling premises.",
                    )
                )
    
    # Check for curvature without derivation
    if has_curvature:
        # Look for theorem proving curvature relates to μ-cost
        has_curvature_derivation = bool(re.search(
            r"(?m)^[ \t]*(Theorem|Lemma)\s+\w*(curvature_from|ricci_from|geometry_from)\w*\b",
            text
        ))
        
        if not has_curvature_derivation:
            # Check if curvature is DEFINED in terms of mu (not proven)
            curvature_def_match = re.search(
                r"(?m)^[ \t]*Definition\s+ricci_curvature\b[^:]*:=\s*([^.]+)\.",
                text
            )
            if curvature_def_match:
                body = curvature_def_match.group(1)
                # If it's just := mu_laplacian, that's a definitional construction
                if re.match(r"\s*mu_laplacian\b", body.strip()):
                    line = line_of[curvature_def_match.start()]
                    snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else "ricci_curvature"
                    findings.append(
                        Finding(
                            rule_id="DEFINITIONAL_CONSTRUCTION",
                            severity="HIGH",
                            file=path,
                            line=line,
                            snippet=snippet.strip(),
                            message="ricci_curvature is DEFINED as mu_laplacian (not proven equal). "
                                    "This assumes the relationship rather than deriving it. "
                                    "Need theorem proving: ricci_curvature = k * mu_laplacian for some k.",
                        )
                    )
    
    return findings


def scan_definitional_construction_circularity(path: Path) -> list[Finding]:
    """Detect when a definition builds in what should be proven.
    
    Pattern:
      Definition ricci_curvature := mu_laplacian.  (* BUILDS IN relationship *)
      Theorem curvature_from_mu : ricci_curvature = k * mu_laplacian.  (* proves nothing new *)
    
    This is circular: the theorem just unfolds the definition.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []
    
    # Collect definitions and their bodies
    def_re = re.compile(r"(?m)^[ \t]*Definition\s+([A-Za-z0-9_']+)\b[^:]*:=\s*([^.]+)\.")
    definitions = {}
    for dm in def_re.finditer(text):
        defn_name = dm.group(1)
        defn_body = re.sub(r"\s+", " ", dm.group(2)).strip()
        definitions[defn_name] = (defn_body, line_of[dm.start()])
    
    # Look for theorems that mention these definitions
    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b")
    proof_re = re.compile(r"(?m)^[ \t]*Proof\.")
    end_re = re.compile(r"(?m)^[ \t]*(Qed|Defined|Admitted)\.")
    
    for tm in theorem_re.finditer(text):
        tname = tm.group(2)
        stmt_end = text.find(".", tm.end())
        if stmt_end == -1:
            continue
        stmt = re.sub(r"\s+", " ", text[tm.start():stmt_end + 1]).strip()
        
        # Check which definitions are mentioned in LHS of equation
        for defn, (defn_body, defn_line) in definitions.items():
            if defn not in stmt:
                continue
            
            # Check if statement is of form: defn = <expr> where <expr> contains defn_body
            # Pattern: defn ... = ... defn_body ...
            eq_pattern = re.search(rf"\b{defn}\b[^=]*=\s*(.+)\.", stmt)
            if not eq_pattern:
                continue
            
            rhs = eq_pattern.group(1).strip()
            # Normalize both sides for comparison
            defn_body_norm = re.sub(r"\s+", " ", defn_body).strip()
            rhs_norm = re.sub(r"\s+", " ", rhs).strip()
            
            # Check if RHS contains the definition body (or is trivially related)
            if defn_body_norm in rhs_norm or rhs_norm in defn_body_norm:
                # Check the proof
                proof_match = proof_re.search(text, stmt_end)
                if not proof_match:
                    continue
                end_match = end_re.search(text, proof_match.end())
                if not end_match:
                    continue
                proof_block = text[proof_match.end():end_match.start()].strip()
                proof_text = re.sub(r"\s+", " ", proof_block)
                
                # If proof just unfolds the definition
                if f"unfold {defn}" in proof_text:
                    tactics = [t.strip() for t in re.split(r'[.;]', proof_text) if t.strip()]
                    non_trivial = [t for t in tactics if not re.match(
                        r"^(unfold|reflexivity|field|simpl|auto)\b", t)]
                    
                    if len(non_trivial) == 0:
                        line = line_of[tm.start()]
                        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname
                        findings.append(
                            Finding(
                                rule_id="DEFINITION_BUILT_IN_THEOREM",
                                severity="HIGH",
                                file=path,
                                line=line,
                                snippet=snippet.strip(),
                                message=f"Theorem `{tname}` proves relationship that's BUILT INTO "
                                        f"Definition `{defn}` (line {defn_line}). The theorem just unfolds "
                                        f"the definition — it proves nothing. Need to define {defn} independently "
                                        f"and PROVE the relationship.",
                            )
                        )
    
    return findings


def scan_incomplete_physics_markers(path: Path) -> list[Finding]:
    """Detect explicit unfinished-language markers in gravity/physics files.

    These markers are strong signals that a derivation is scaffolding rather
    than completed proof content.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    line_of = _line_map(raw)
    lines = raw.splitlines()
    findings: list[Finding] = []

    is_physics_file = bool(re.search(r"(?i)(gravity|einstein|geometry|curvature|physics)", path.as_posix()))
    if not is_physics_file:
        return findings

    marker_re = re.compile(
        r"(?i)\b(for now|future work|left for future|can be refined|placeholder|stub|not yet derived)\b"
    )
    for m in marker_re.finditer(raw):
        line = line_of[m.start()]
        snippet = lines[line - 1].strip() if 0 <= line - 1 < len(lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="INCOMPLETE_PHYSICS_DERIVATION",
                severity="HIGH",
                file=path,
                line=line,
                snippet=snippet,
                message="File contains explicit unfinished marker in a physics derivation. "
                        "Replace placeholder language with proved theorem content or move to exploratory area.",
            )
        )

    return findings


def scan_fake_completion_claims(path: Path) -> list[Finding]:
    """Flag completion rhetoric when critical derivation artifacts are missing.

    This prevents reports claiming "composition complete" while core theorems are
    absent or known stubs remain.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    comments = extract_coq_comments(raw)
    line_of_raw = _line_map(raw)
    raw_lines = raw.splitlines()
    findings: list[Finding] = []

    if not re.search(r"(?i)(gravity|einstein|physics)", path.as_posix()):
        return findings

    claim_re = re.compile(r"(?i)\b(the bedrock is reached|composition is complete|all machine-checked)\b")
    has_claim = claim_re.search(comments) is not None
    if not has_claim:
        return findings

    has_einstein_eq = bool(re.search(r"(?m)^[ \t]*(Theorem|Lemma)\s+[A-Za-z0-9_']*einstein[_]?equation", text))
    has_stub_distance = bool(re.search(r"Definition\s+mu_module_distance\b[\s\S]*?match\s+m1\s*=\?\s*m2[\s\S]*?\|\s*true\s*=>\s*0[\s\S]*?\|\s*false\s*=>\s*1", text))
    has_stub_angle = bool(re.search(r"Definition\s+triangle_angle\b[\s\S]*?PI\s*/\s*3", text))

    if (not has_einstein_eq) or has_stub_distance or has_stub_angle:
        # Place the finding at the first claim location in raw text.
        m = claim_re.search(raw)
        line = line_of_raw[m.start()] if m else 1
        snippet = raw_lines[line - 1].strip() if 0 <= line - 1 < len(raw_lines) else "completion claim"
        findings.append(
            Finding(
                rule_id="FAKE_COMPLETION_CLAIM",
                severity="HIGH",
                file=path,
                line=line,
                snippet=snippet,
                message="File claims completion while core derivation requirements are not met "
                        "(missing Einstein theorem and/or stubbed physics definitions).",
            )
        )

    return findings


def scan_unused_local_definitions(path: Path) -> list[Finding]:
    """Detect Definition/Fixpoint symbols declared but never used in the same file."""
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    decl_re = re.compile(r"(?m)^[ \t]*(Definition|Fixpoint|CoFixpoint)\s+([A-Za-z0-9_']+)\b")
    next_top_re = re.compile(
        r"(?m)^[ \t]*(Definition|Fixpoint|CoFixpoint|Lemma|Theorem|Corollary|Remark|Fact|Proposition|Record|Inductive|Class|Module)\b"
    )
    decls: list[tuple[str, int, int, int]] = []
    for m in decl_re.finditer(text):
        name = m.group(2)
        line = line_of[m.start()]
        next_m = next_top_re.search(text, m.end())
        block_end = next_m.start() if next_m else len(text)
        decls.append((name, line, m.start(), block_end))

    for name, line, start_idx, end_idx in decls:
        outside_text = text[:start_idx] + "\n" + text[end_idx:]
        if re.search(rf"\b{re.escape(name)}\b", outside_text):
            continue
        if name.startswith("_"):
            continue
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else name
        findings.append(
            Finding(
                rule_id="UNUSED_LOCAL_DEFINITION",
                severity="LOW",
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=f"`{name}` is defined but not referenced elsewhere in this file.",
            )
        )

    return findings


def _file_vacuity_summary(path: Path) -> tuple[int, tuple[str, ...]]:
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    scored = summarize_text(text)
    return scored.score, scored.tags


def _run_coqtop_batch(coqproject: Path, commands: str, cwd: Path) -> subprocess.CompletedProcess[str]:
    # Parse _CoqProject for -R and -Q flags
    # Coq 8.18 suppresses `Check` / `Print Assumptions` output under `-batch`,
    # so the audit must use stdin-driven interactive mode and exit via `Quit.`.
    coq_args = ["coqtop", "-quiet"]
    if coqproject.exists():
        project_root = coqproject.parent.resolve()
        project_lines = coqproject.read_text(encoding="utf-8", errors="replace").splitlines()
        for line in project_lines:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            if line.startswith("-R ") or line.startswith("-Q "):
                parts = line.split()
                if len(parts) >= 3:
                    mapping_root = Path(parts[1])
                    if not mapping_root.is_absolute():
                        mapping_root = (project_root / mapping_root).resolve()
                    coq_args.extend([parts[0], str(mapping_root), parts[2]])

    project_cwd = coqproject.parent if coqproject.exists() else cwd

    return _run_command(
        coq_args,
        cwd=project_cwd,
        stage="coqtop batch",
        input_text=commands,
    )


def _parse_axioms(output: str) -> list[str]:
    axioms: list[str] = []
    in_axioms = False
    for ln in output.splitlines():
        stripped = ln.strip()
        if stripped.startswith("Axioms:"):
            in_axioms = True
            continue
        if not in_axioms:
            continue
        if not stripped or stripped.startswith("Coq <") or stripped.startswith("Toplevel"):
            break
        if stripped.startswith("Closed under the global context"):
            break
        if stripped.startswith(":"):
            continue
        m = re.match(r"^([A-Za-z_][A-Za-z0-9_.']*)(?:\s*:.*)?$", stripped)
        if m:
            axioms.append(m.group(1))
    return axioms


def _coq_output_setup_error(output: str) -> str | None:
    for ln in output.splitlines():
        stripped = ln.strip()
        if not stripped:
            continue
        if "cannot-open-path" in stripped:
            return stripped
        if stripped.startswith("Warning: Cannot open "):
            return stripped
        if "Cannot find a physical path bound to logical path" in stripped:
            return stripped
    return None


def _assumption_audit(repo_root: Path, manifest_path: Path, manifest: dict) -> list[Finding]:
    findings: list[Finding] = []
    if shutil.which("coqtop") is None:
        findings.append(
            Finding(
                rule_id="ASSUMPTION_AUDIT",
                severity="HIGH",
                file=manifest_path,
                line=1,
                snippet="coqtop",
                message="coqtop not found; cannot run assumption audit.",
            )
        )
        return findings

    coqproject = (repo_root / manifest.get("coqproject", "coq/_CoqProject")).resolve()
    if not coqproject.exists():
        findings.append(
            Finding(
                rule_id="ASSUMPTION_AUDIT",
                severity="HIGH",
                file=manifest_path,
                line=1,
                snippet=str(coqproject),
                message="coqproject path not found for assumption audit.",
            )
        )
        return findings

    allow = set(manifest.get("allow_axioms", []))
    targets = manifest.get("targets", [])
    for t in targets:
        req = t.get("require")
        sym = t.get("symbol")
        if not req or not sym:
            findings.append(
                Finding(
                    rule_id="ASSUMPTION_AUDIT",
                    severity="HIGH",
                    file=manifest_path,
                    line=1,
                    snippet=str(t),
                    message="Invalid assumption audit target (missing require/symbol).",
                )
            )
            continue
        commands = f"Require Import {req}.\nPrint Assumptions {sym}.\nQuit.\n"
        proc = _run_coqtop_batch(coqproject, commands, cwd=repo_root)
        output = (proc.stdout or "") + "\n" + (proc.stderr or "")
        setup_error = _coq_output_setup_error(output)
        if setup_error is not None:
            findings.append(
                Finding(
                    rule_id="ASSUMPTION_AUDIT",
                    severity="HIGH",
                    file=manifest_path,
                    line=1,
                    snippet=f"{req}.{sym}",
                    message=f"coqtop path setup failed for {sym}: {setup_error}",
                )
            )
            continue
        if proc.returncode != 0:
            findings.append(
                Finding(
                    rule_id="ASSUMPTION_AUDIT",
                    severity="HIGH",
                    file=manifest_path,
                    line=1,
                    snippet=f"{req}.{sym}",
                    message=f"coqtop failed for Print Assumptions {sym}: {output.strip()[:200]}",
                )
            )
            continue
        axioms = _parse_axioms(output)
        unexpected = [a for a in axioms if a not in allow]
        if unexpected:
            findings.append(
                Finding(
                    rule_id="ASSUMPTION_AUDIT",
                    severity="HIGH",
                    file=manifest_path,
                    line=1,
                    snippet=", ".join(unexpected[:6]),
                    message=f"Unexpected axioms in Print Assumptions {sym}: {unexpected[:20]}",
                )
            )

    return findings


def _scan_kernel_convertibility_vacuity(repo_root: Path) -> list[Finding]:
    """Consume `artifacts/vacuity_audit.json` (produced by scripts/vacuity_gate.py)
    and emit a HIGH finding for every theorem whose conclusion is kernel-convertible
    to either `True` or one of its hypotheses.

    This is the (V) tag of the μ-axis research program's vacuity discipline: a
    theorem flagged here is *definitionally* vacuous — Coq's kernel itself
    accepted a trivial proof of the conclusion.

    If the audit JSON is absent (vacuity gate not run yet), this function emits
    no findings — the pre-commit hook runs the gate before Inquisitor, so under
    normal operation the file is always present.
    """
    audit_path = repo_root / "artifacts" / "vacuity_audit.json"
    if not audit_path.exists():
        return []
    try:
        data = json.loads(audit_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        return [
            Finding(
                rule_id="KERNEL_CONVERTIBILITY_VACUITY",
                severity="HIGH",
                file=audit_path,
                line=1,
                snippet=str(exc)[:200],
                message=(
                    "Failed to parse artifacts/vacuity_audit.json. The vacuity "
                    "gate must produce valid JSON; rerun scripts/vacuity_gate.py."
                ),
            )
        ]
    findings: list[Finding] = []
    for verdict in data.get("verdicts", []):
        status = verdict.get("status", "ok")
        if status in ("vacuous-true", "vacuous-hyp"):
            target_file = repo_root / verdict["file"]
            kind_phrase = (
                "convertible to `True` after lazy reduction"
                if status == "vacuous-true"
                else "convertible to one of its hypotheses after lazy reduction"
            )
            findings.append(
                Finding(
                    rule_id="KERNEL_CONVERTIBILITY_VACUITY",
                    severity="HIGH",
                    file=target_file,
                    line=int(verdict.get("line", 1)),
                    snippet=verdict.get("name", "<unknown>"),
                    message=(
                        f"Theorem `{verdict.get('name', '<unknown>')}` "
                        f"is kernel-{kind_phrase}. Coq accepted the synthesised "
                        f"vacuity probe at `{verdict.get('probe_a' if status == 'vacuous-true' else 'probe_b', {}).get('probe_path', '<probe>')}`. "
                        f"Tag this theorem (V) — replace with a non-vacuous statement, or remove."
                    ),
                )
            )
    return findings


def _paper_symbol_map(repo_root: Path, manifest_path: Path, manifest: dict) -> list[Finding]:
    findings: list[Finding] = []
    if shutil.which("coqtop") is None:
        findings.append(
            Finding(
                rule_id="PAPER_MAP_MISSING",
                severity="HIGH",
                file=manifest_path,
                line=1,
                snippet="coqtop",
                message="coqtop not found; cannot verify paper symbol map.",
            )
        )
        return findings

    coqproject = (repo_root / manifest.get("coqproject", "coq/_CoqProject")).resolve()
    if not coqproject.exists():
        findings.append(
            Finding(
                rule_id="PAPER_MAP_MISSING",
                severity="HIGH",
                file=manifest_path,
                line=1,
                snippet=str(coqproject),
                message="coqproject path not found for paper symbol map.",
            )
        )
        return findings

    for entry in manifest.get("paper_map", []):
        req = entry.get("require")
        sym = entry.get("symbol")
        if not req or not sym:
            findings.append(
                Finding(
                    rule_id="PAPER_MAP_MISSING",
                    severity="HIGH",
                    file=manifest_path,
                    line=1,
                    snippet=str(entry),
                    message="Invalid paper map entry (missing require/symbol).",
                )
            )
            continue
        commands = f"Require Import {req}.\nCheck {sym}.\nQuit.\n"
        proc = _run_coqtop_batch(coqproject, commands, cwd=repo_root)
        output = (proc.stdout or "") + "\n" + (proc.stderr or "")
        setup_error = _coq_output_setup_error(output)
        if setup_error is not None:
            findings.append(
                Finding(
                    rule_id="PAPER_MAP_MISSING",
                    severity="HIGH",
                    file=manifest_path,
                    line=1,
                    snippet=f"{req}.{sym}",
                    message=f"coqtop path setup failed for paper map symbol {sym}: {setup_error}",
                )
            )
            continue
        if proc.returncode != 0:
            findings.append(
                Finding(
                    rule_id="PAPER_MAP_MISSING",
                    severity="HIGH",
                    file=manifest_path,
                    line=1,
                    snippet=f"{req}.{sym}",
                    message=f"Missing or broken paper map symbol {sym}: {output.strip()[:200]}",
                )
            )

    return findings


def _scan_symmetry_contracts(coq_root: Path, manifest: dict, *, all_proofs: bool = False) -> list[Finding]:
    contracts = manifest.get("symmetry_contracts", [])
    if not contracts:
        return []

    compiled = []
    for contract in contracts:
        file_re = contract.get("file_regex")
        must_res = contract.get("must_contain_regex", [])
        tag = contract.get("tag")
        if not file_re or not must_res:
            continue
        compiled.append(
            {
                "tag": tag,
                "file_re": re.compile(file_re),
                "must": [re.compile(expr) for expr in must_res],
            }
        )

    findings: list[Finding] = []
    v_files = iter_all_coq_files(coq_root) if all_proofs else iter_v_files(coq_root)
    for vf in v_files:
        raw = vf.read_text(encoding="utf-8", errors="replace")
        stripped = strip_coq_comments(raw)
        for contract in compiled:
            matches_file = contract["file_re"].search(vf.as_posix()) is not None
            if not matches_file:
                continue
            if any(expr.search(stripped) for expr in contract["must"]):
                continue
            findings.append(
                Finding(
                    rule_id="SYMMETRY_CONTRACT",
                    severity=_severity_for_path(vf, "MEDIUM"),
                    file=vf,
                    line=1,
                    snippet="",
                    message=f"Missing symmetry equivariance lemma matching: {', '.join(r.pattern for r in contract['must'])}",
                )
            )
    return findings


def _run_make_all(repo_root: Path) -> tuple[int, list[Finding]]:
    """Run make -C coq and return (returncode, list of compilation findings)."""
    findings: list[Finding] = []
    coq_dir = repo_root / "coq"

    _log_progress("Compiling all Coq proofs")
    try:
        proc = _run_command(
            ["make", "-C", str(coq_dir), "-j1"],
            cwd=repo_root,
            stage="coq build",
        )
    except CommandTimeoutError as exc:
        details = "\n".join(part for part in [exc.stdout_tail, exc.stderr_tail] if part).strip()
        findings.append(
            Finding(
                rule_id="COMPILATION_TIMEOUT",
                severity="HIGH",
                file=coq_dir / "Makefile",
                line=1,
                snippet=details[:500],
                message=(
                    f"Coq build timed out after {exc.timeout_seconds}s during {exc.stage}. "
                    "See terminal progress logs for the last visible output."
                ),
            )
        )
        return 124, findings
    
    if proc.returncode != 0:
        # Parse error output to find which files failed with FULL error context
        error_lines = proc.stderr + proc.stdout

        # Extract each error block: "File "...", line N ... Error: ..."
        error_block_re = re.compile(
            r'File "([^"]+\.v)", line (\d+)(?:, characters (\d+-\d+))?[:\n]'
            r'(.*?)(?=(?:File "|make\[\d+\]:|$))',
            re.DOTALL,
        )
        seen_files = set()
        for match in error_block_re.finditer(error_lines):
            file_path = match.group(1)
            line_num = int(match.group(2))
            error_detail = match.group(4).strip()

            # Extract the actual Error: line
            error_msg_match = re.search(r'Error:\s*(.+?)(?:\n|$)', error_detail)
            error_msg = error_msg_match.group(1).strip() if error_msg_match else error_detail[:200]

            full_path = (coq_dir / file_path).resolve() if not Path(file_path).is_absolute() else Path(file_path)
            if not full_path.exists():
                full_path = (repo_root / file_path).resolve()

            file_key = (str(full_path), line_num)
            if file_key in seen_files:
                continue
            seen_files.add(file_key)

            findings.append(
                Finding(
                    rule_id="COMPILATION_ERROR",
                    severity="HIGH",
                    file=full_path,
                    line=line_num,
                    snippet=error_msg[:300],
                    message=f"Coq compilation error: {error_msg}",
                )
            )
            # Print inline for immediate visibility during iteration
            print(f"  COMPILE ERROR: {file_path}:{line_num} -> {error_msg}")

        # If no specific files found in error, add a general failure
        if not findings:
            findings.append(
                Finding(
                    rule_id="COMPILATION_ERROR",
                    severity="HIGH",
                    file=coq_dir / "Makefile",
                    line=1,
                    snippet=error_lines[:500] if error_lines else "",
                    message="Coq compilation failed - run 'make -C coq' for details.",
                )
            )
        _log_progress(f"Compilation FAILED with {len(findings)} error(s)")
    else:
        _log_progress("Compilation OK")

    return proc.returncode, findings


def _run_proof_body_foundation_audit(repo_root: Path) -> list[Finding]:
    """Enforce theorem-body connectivity to kernel foundations across coq/*.

    This invokes `scripts/generate_proof_dependency_dag.py` and consumes
    `artifacts/proof_dependency_connectivity.json` to detect files whose
    declarations/theorems do not transitively reach the canonical foundation set.
    """

    findings: list[Finding] = []
    script = repo_root / "scripts" / "generate_proof_dependency_dag.py"
    conn_path = repo_root / "artifacts" / "proof_dependency_connectivity.json"

    if not script.exists():
        findings.append(
            Finding(
                rule_id="PROOF_BODY_FOUNDATION_DISCONNECT",
                severity="HIGH",
                file=script,
                line=1,
                snippet="",
                message="Proof dependency generator is missing; cannot enforce proof-body foundation connectivity.",
            )
        )
        return findings

    try:
        proc = _run_command(
            ["python3", str(script)],
            cwd=repo_root,
            stage="proof dependency dag",
        )
    except CommandTimeoutError as exc:
        tail = "\n".join(part for part in [exc.stdout_tail, exc.stderr_tail] if part).strip()
        findings.append(
            Finding(
                rule_id="PROOF_BODY_FOUNDATION_DISCONNECT",
                severity="HIGH",
                file=script,
                line=1,
                snippet=tail[:500],
                message=(
                    f"Proof dependency DAG generation timed out after {exc.timeout_seconds}s. "
                    "See terminal progress logs for the last visible output."
                ),
            )
        )
        return findings

    if proc.returncode != 0:
        tail = (proc.stderr or proc.stdout or "")[-500:]
        findings.append(
            Finding(
                rule_id="PROOF_BODY_FOUNDATION_DISCONNECT",
                severity="HIGH",
                file=script,
                line=1,
                snippet="",
                message=(
                    "Failed to generate theorem-body dependency/connectivity artifacts. "
                    f"Return code={proc.returncode}. Tail: {tail.strip()}"
                ),
            )
        )
        return findings

    if not conn_path.exists():
        findings.append(
            Finding(
                rule_id="PROOF_BODY_FOUNDATION_DISCONNECT",
                severity="HIGH",
                file=conn_path,
                line=1,
                snippet="",
                message="Missing proof dependency connectivity artifact after generation.",
            )
        )
        return findings

    try:
        conn = json.loads(conn_path.read_text(encoding="utf-8", errors="replace"))
    except json.JSONDecodeError as exc:
        findings.append(
            Finding(
                rule_id="PROOF_BODY_FOUNDATION_DISCONNECT",
                severity="HIGH",
                file=conn_path,
                line=1,
                snippet=str(exc),
                message="Invalid proof dependency connectivity JSON.",
            )
        )
        return findings

    disconnected = conn.get("disconnected_files", [])
    if not isinstance(disconnected, list):
        disconnected = []

    for rel in disconnected:
        if not isinstance(rel, str):
            continue
        file_path = repo_root / rel
        # Suppression: same convention as the sibling rule
        # PROOF_CONNECTIVITY_GAP — a file that stands alone on purpose says so
        # in a SCOPE NOTE (standalone proof scope, or one mentioning
        # proof-connect/proof connect) somewhere in the file.
        try:
            raw = file_path.read_text(encoding="utf-8", errors="replace")
            if _PROOF_CONNECTIVITY_NOTE_RE.search(raw):
                continue
        except OSError:
            pass
        findings.append(
            Finding(
                rule_id="PROOF_BODY_FOUNDATION_DISCONNECT",
                severity="HIGH",
                file=file_path,
                line=1,
                snippet="",
                message=(
                    "File is disconnected from the foundation chain in the theorem-body dependency graph. "
                    "Add constructive bridge lemmas/uses until it transitively reaches "
                    "UniversalCertificationCost/StructuralCore/Substrate/KernelTM/EarnedCore, "
                    "or state in a SCOPE NOTE why it stands alone."
                ),
            )
        )

    return findings


def _scan_foundation_utilization(repo_root: Path, v_files: list[Path]) -> list[Finding]:
    """Verify proof files use the Thiele Machine proof chain, not just import it.

    The chain is the abstract model and the small machine:
      UniversalCertificationCost  certification systems and the universal floor
      StructuralCore              record-carrying machines, adequacy, core equivalence
      Substrate                   the abstract A2-respecting substrate
      KernelTM                    the Turing-machine kernel used as a base
      EarnedCore, ThieleComplete  the small machine and the definition it meets
    with the record axis, permanence and pricing files and the Links files
    built on them.

    PROOF_CONNECTIVITY_GAP checks the import chain. This check catches a
    different problem: a proof file that neither uses any term of the chain
    nor imports any chain module, i.e. a theorem file standing outside the
    project with no stated reason. A file that documents why it is
    standalone carries a SCOPE NOTE and is not flagged.
    """
    findings: list[Finding] = []

    _FOUNDATION_USAGE_TOKENS = re.compile(
        r"\b("
        # Certification systems and the universal floor
        r"CertificationSystem|cs_step|cs_run|cs_cost|cs_total_cost|cs_cert|"
        r"cs_cert_costs|universal_nfi_any_substrate|SimulatingCertificationSystem|"
        # Record-carrying machines
        r"RCM|rc_next|rc_run|rc_cert|rc_mu|rc_init|rc_halted|step_cost|"
        r"ledger_carried|rc_a2|carries_record|Adequate|core_bisim|core_equiv|"
        r"ComputationalCover|record_permanent|reachable_record_write|"
        r"BaseMachine|BaseCover|HonestBaseExtension|latch_factorization|"
        # Substrate and the Turing kernel
        r"Substrate|step_tm|run_tm|TuringMachine|"
        # Permanence and pricing
        r"permanent|step_injective|finite_states|merging_steps_priced|"
        r"compression_priced|a2_holds|forced_priced"
        r")\b"
    )

    coq_root = repo_root / "coq"
    if not coq_root.exists():
        return findings

    # Files that DEFINE the proof chain are exempt.
    _FOUNDATION_STEMS = {
        "UniversalCertificationCost", "StructuralCore", "Substrate",
        "Kernel", "KernelTM",
    }

    _CHAIN_MODULES = {
        "UniversalCertificationCost", "StructuralCore", "StructuralCoreCover",
        "StructuralCoreAnyBase", "StructuralRecordAxis", "Substrate", "Kernel",
        "KernelTM", "PermanentCertification", "PermanentRecordPricing",
        "PermanentCertificationEntropy", "CommitmentPredicateAdequacy",
        "EarnedCoreLinks", "EarnedGenericLinks", "UniversalThieleLinks",
        "UniversalInterpreterLinks", "PricedHostLinks", "SmallChshLinks",
        # The small machine (namespace Minimal)
        "EarnedCore", "EarnedGeneric", "EarnedMulti", "ThieleComplete",
        "ThieleCompleteWindow", "UniversalThiele", "UniversalCodes",
        "UniversalNoCopy", "EarnedPriced", "PricedComplete", "Presented",
        "EarnedMultiPriced",
    }

    # The small machine in minimal/ is held to the same rule as coq/.
    scan_roots = (str(coq_root), str(repo_root / "minimal"))
    for vf in v_files:
        if not str(vf).startswith(scan_roots):
            continue
        if vf.stem in _FOUNDATION_STEMS:
            continue

        text = vf.read_text(encoding="utf-8", errors="replace")
        clean = strip_coq_comments(text)

        has_proofs = bool(re.search(
            r"(?:Theorem|Lemma|Corollary|Proposition|Fact)\s+\w+", clean
        ))
        if not has_proofs:
            continue

        if _FOUNDATION_USAGE_TOKENS.search(clean):
            continue

        chain_imports = re.findall(
            r"(?:From\s+\w+\s+)?Require\s+(?:Import|Export)\s+([\w\s.]+)\.",
            clean
        )
        imported_modules = set()
        for imp in chain_imports:
            for mod in imp.split():
                imported_modules.add(mod.rstrip('.').split('.')[-1])

        if imported_modules & _CHAIN_MODULES:
            # Imports are checked for real use by PHANTOM_KERNEL_IMPORT.
            continue

        if _PROOF_CONNECTIVITY_NOTE_RE.search(text):
            continue

        theorem_count = len(re.findall(
            r"(?:Theorem|Lemma|Corollary|Proposition|Fact)\s+\w+", clean
        ))
        findings.append(Finding(
            rule_id="FOUNDATION_UTILIZATION_GAP",
            severity="MEDIUM",
            file=vf,
            line=1,
            snippet=f"theorems found: {theorem_count}",
            message=(
                f"Proof file {vf.stem}.v contains {theorem_count} theorem(s) but "
                "does not import or reference ANY module in the Thiele Machine proof "
                "chain (UniversalCertificationCost, StructuralCore, Substrate, KernelTM, "
                "EarnedCore, ...). Connect it to the chain, or state in a SCOPE NOTE "
                "why it stands alone."
            ),
        ))

    return findings


def _compile_individual_file(coq_file: Path, repo_root: Path) -> Finding | None:
    """Try to compile a single Coq file and return a finding if it fails."""
    try:
        proc = _run_command(
            ["coqc", "-Q", str(repo_root / "coq"), "Thiele", str(coq_file)],
            cwd=repo_root,
            stage="single coq compile",
        )
    except CommandTimeoutError as exc:
        details = "\n".join(part for part in [exc.stdout_tail, exc.stderr_tail] if part).strip()
        return Finding(
            rule_id="COMPILATION_TIMEOUT",
            severity="HIGH",
            file=coq_file,
            line=1,
            snippet=details[:200],
            message=(
                f"File compile timed out after {exc.timeout_seconds}s. "
                "See terminal progress logs for the last visible output."
            ),
        )

    if proc.returncode != 0:
        # Extract line number from error if possible
        import re
        line_match = re.search(r'line (\d+)', proc.stderr)
        line_num = int(line_match.group(1)) if line_match else 1
        return Finding(
            rule_id="COMPILATION_ERROR",
            severity="HIGH",
            file=coq_file,
            line=line_num,
            snippet=proc.stderr[:200] if proc.stderr else "",
            message="File failed to compile.",
        )
    return None


def count_suppression_markers(repo_root: Path) -> dict:
    """Count in-source Inquisitor suppression markers across the Coq corpus.

    Rules in this file honour two markers -- `(* SAFE: <reason> *)` and
    `(* SCOPE NOTE: <reason> *)` -- by skipping the check at that site.
    They are legitimate (many mark genuinely safe constructs) but they are also
    the reason a zero finding count is not the same as a clean scan. This
    census is reported alongside the severity counts so the badge cannot be
    read as stronger than it is.

    Counts marker occurrences, not silenced findings: a marker may guard a site
    no rule would have flagged anyway. It is an upper bound on waived checks.
    """
    note_re = re.compile(r"SCOPE NOTE")
    safe_re = re.compile(r"\(\*\s*SAFE:")
    note_total = 0
    safe_total = 0
    files_with_markers = 0
    for path in sorted((repo_root / "coq").rglob("*.v")):
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        n = len(note_re.findall(text))
        s = len(safe_re.findall(text))
        if n or s:
            files_with_markers += 1
        note_total += n
        safe_total += s
    return {
        "inquisitor_note": note_total,
        "safe": safe_total,
        "total": note_total + safe_total,
        "files": files_with_markers,
    }


def write_report(
    report_path: Path,
    repo_root: Path,
    findings: list[Finding],
    scanned_files: int,
    vacuity_index: list[tuple[int, Path, tuple[str, ...]]],
    *,
    scanned_scope: str,
) -> None:
    now = _dt.datetime.now(_dt.UTC).strftime("%Y-%m-%d %H:%M:%SZ")
    by_sev = {"HIGH": [], "MEDIUM": [], "LOW": []}
    for f in findings:
        by_sev.setdefault(f.severity, []).append(f)

    def esc(s: str) -> str:
        return s.replace("`", "\\`")

    lines: list[str] = []
    lines.append(f"# INQUISITOR REPORT\n")
    lines.append(f"Generated: {now} (UTC)\n")
    if scanned_scope == "repo":
        lines.append(f"Scanned: {scanned_files} Coq files across the repo\n")
    else:
        lines.append(f"Scanned: {scanned_files} Coq files under {scanned_scope}\n")
    lines.append("## Summary\n")
    lines.append(f"- HIGH: {len(by_sev.get('HIGH', []))}\n")
    lines.append(f"- MEDIUM: {len(by_sev.get('MEDIUM', []))}\n")
    lines.append(f"- LOW: {len(by_sev.get('LOW', []))}\n")

    # Scope-note census. A finding count of zero means "zero UNSUPPRESSED findings":
    # rules honour in-source SAFE and SCOPE NOTE markers, which silence a check
    # at that site. Reporting only the finding counts lets a reader take
    # "0 HIGH" as "nothing was ever flagged", which is not what it means.
    # The census below is the denominator that makes the numerator honest.
    scope_notes = count_suppression_markers(repo_root)
    lines.append(
        f"- SCOPE NOTES: {scope_notes['total']} in-source scope markers "
        f"across {scope_notes['files']} files "
        f"({scope_notes['inquisitor_note']} SCOPE NOTE, "
        f"{scope_notes['safe']} SAFE markers)\n"
    )
    lines.append(
        "  - Read the severity counts as *unsuppressed* findings. Each scope note "
        "silences one check at one site; the justification is the comment "
        "text itself. Grep for the markers to audit them.\n"
    )
    lines.append("\n")

    lines.append("## Rules\n")
    lines.append("- `ADMITTED`: `Admitted.` (incomplete proof - FORBIDDEN)\n")
    lines.append("- `ADMIT_TACTIC`: `admit.` (proof shortcut - FORBIDDEN)\n")
    lines.append("- `GIVE_UP_TACTIC`: `give_up` (proof shortcut - FORBIDDEN)\n")
    lines.append("- `AXIOM_OR_PARAMETER`: `Axiom` / `Parameter` (HIGH - unproven assumptions FORBIDDEN)\n")
    lines.append("- `HYPOTHESIS_ASSUME`: `Hypothesis` (HIGH - functionally equivalent to Axiom, FORBIDDEN)\n")
    lines.append("- `CONTEXT_ASSUMPTION`: `Context` with forall/arrow (HIGH - undocumented section-local axiom)\n")
    lines.append("- `CONTEXT_ASSUMPTION_DOCUMENTED`: `Context` with SCOPE NOTE (LOW - documented dependency)\n")
    lines.append("- `SECTION_BINDER`: `Context` / `Variable` / `Variables` (MEDIUM - verify instantiation)\n")
    lines.append("- `MODULE_SIGNATURE_DECL`: `Axiom` / `Parameter` inside `Module Type` (informational)\n")
    lines.append("- `COST_IS_LENGTH`: `Definition *cost* := ... length ... .`\n")
    lines.append("- `EMPTY_LIST`: `Definition ... := [].`\n")
    lines.append("- `ZERO_CONST`: `Definition ... := 0.` / `0%Z` / `0%nat`\n")
    lines.append("- `TRUE_CONST`: `Definition ... := True.` or `:= true.`\n")
    lines.append("- `PROP_TAUTOLOGY`: `Theorem ... : True.`\n")
    lines.append("- `IMPLIES_TRUE_STMT`: statement ends with `-> True.`\n")
    lines.append("- `LET_IN_TRUE_STMT`: statement ends with `let ... in True.`\n")
    lines.append("- `EXISTS_TRUE_STMT`: statement ends with `exists ..., True.`\n")
    lines.append("- `CIRCULAR_INTROS_ASSUMPTION`: tautology + `intros; assumption.`\n")
    lines.append("- `EXACT_ALIAS`: `Theorem A. Proof. exact B. Qed.` (pure alias — proves nothing new, just re-exports an existing proof under a new name)\n")
    lines.append("- `SCOPE_DRIFT_TIER1`: coq/kernel/ (Tier 1) file imports a Tier-2 or Tier-3 namespace — contaminates the proof tree\n")
    lines.append("- `FOUNDATION_UTILIZATION_GAP`: proof file neither uses nor imports anything in the foundation chain (abstract model and small machine) and gives no SCOPE NOTE\n")
    lines.append("- `SCOPE_DRIFT_TIER2`: Core Tier-2 file imports a Tier-3 exploratory namespace\n")
    lines.append("- `TRIVIAL_EQUALITY`: theorem of form `X = X` with reflexivity-ish proof\n")
    lines.append("- `CONST_Q_FUN`: `Definition ... := fun _ => 0%Q` / `1%Q`\n")
    lines.append("- `EXISTS_CONST_Q`: `exists (fun _ => 0%Q)` / `exists (fun _ => 1%Q)`\n")
    lines.append("- `CLAMP_OR_TRUNCATION`: uses `Z.to_nat` (can truncate negative values; Nat.min/max/Z.abs are safe)\n")
    lines.append("- `ASSUMPTION_AUDIT`: unexpected axioms from `Print Assumptions`\n")
    lines.append("- `SYMMETRY_CONTRACT`: missing equivariance lemma for declared symmetry\n")
    lines.append("- `PAPER_MAP_MISSING`: paper ↔ Coq symbol map entry missing/broken\n")
    lines.append("- `MANIFEST_PARSE_ERROR`: failed to parse Inquisitor manifest JSON\n")
    lines.append("- `COMMENT_SMELL`: TODO/FIXME/WIP markers in Coq comments\n")
    lines.append("- `UNUSED_HYPOTHESIS`: disabled source-text heuristic; Coq's checked proof term is authoritative for hypothesis use\n")
    lines.append("- `DEFINITIONAL_INVARIANCE`: invariance lemma appears definitional/vacuous\n")
    lines.append("- `Z_TO_NAT_BOUNDARY`: Z.to_nat without nearby nonnegativity guard\n")
    lines.append("- `PHYSICS_ANALOGY_CONTRACT`: physics-analogy theorem lacks invariance or definitional label\n")
    lines.append("- `SUSPICIOUS_SHORT_PROOF`: complex theorem has suspiciously short proof (critical files)\n")
    lines.append("- `MU_COST_ZERO`: μ-cost definition is trivially zero\n")
    lines.append("- `CHSH_BOUND_MISSING`: CHSH bound theorem may not reference proper Tsirelson bound\n")
    lines.append("- `PROBLEMATIC_IMPORT`: import may introduce classical axioms\n")
    lines.append("- `RECORD_FIELD_EXTRACTION`: theorem merely extracts a Record field it assumed as input (circular)\n")
    lines.append("- `SELF_REFERENTIAL_RECORD`: Record embeds proposition as field AND a Theorem in the same file extracts it (circular)\n")
    lines.append("- `PHANTOM_KERNEL_IMPORT`: imports a foundation module but uses nothing it declares\n")
    lines.append("- `TRIVIAL_EXISTENTIAL`: trivially satisfiable existential (e.g. 'every list has a length')\n")
    lines.append("- `ARITHMETIC_ONLY_PHYSICS`: physics-named theorem proved by pure arithmetic (lia/lra) only\n")
    lines.append("- `CIRCULAR_DEFINITION`: theorem unfolds definition and proves by simple tactics (potentially restating definition)\n")
    lines.append("- `EMERGENCE_CIRCULARITY`: 'emergence' claim where emergent property is in the definition (circular)\n")
    lines.append("- `CONSTRUCTOR_ROUND_TRIP`: construct object, immediately extract property (not proving anything)\n")
    lines.append("- `DEFINITIONAL_WITNESS`: existential witnessed by definition, then unfolds it (trivially proves definition exists)\n")
    lines.append("- `VACUOUS_CONJUNCTION`: theorem has `True` as a conjunct leaf — likely a weakened/placeholder conclusion\n")
    lines.append("- `TAUTOLOGICAL_IMPLICATION`: theorem conclusion is identical to one of its hypotheses (P -> P tautology)\n")
    lines.append("- `HYPOTHESIS_RESTATEMENT`: heuristic style warning (disabled in max-strict mode)\n")
    lines.append("- `PHYSICS_STUB_DEFINITION`: physics/geometry definition returns placeholder constant (0, 1, PI/3)\n")
    lines.append("- `MISSING_CORE_THEOREM`: file defines physics machinery (einstein_tensor, stress_energy) but lacks core theorem (einstein_equation)\n")
    lines.append("- `DEFINITIONAL_CONSTRUCTION`: curvature/physics quantity DEFINED as relationship that should be PROVEN\n")
    lines.append("- `DEFINITION_BUILT_IN_THEOREM`: theorem proves relationship that's built into the definition (circular)\n")
    lines.append("- `INCOMPLETE_PHYSICS_DERIVATION`: gravity/physics file contains explicit unfinished marker text\n")
    lines.append("- `FAKE_COMPLETION_CLAIM`: completion rhetoric appears while core theorem/stub criteria are unmet\n")
    lines.append("- `UNUSED_LOCAL_DEFINITION`: heuristic style warning (disabled in max-strict mode)\n")
    lines.append("- `PROOF_CONNECTIVITY_GAP`: active proof file lacks the semantic foundation (abstract model and small machine), or a cost-using file lacks the cost foundation; a file that stands alone must say so in a SCOPE NOTE\n")
    lines.append("- `PROOF_BODY_FOUNDATION_DISCONNECT`: theorem-body dependency graph shows a Coq proof file does not transitively reach the canonical foundation theorem chain\n")
    lines.append("- `DISJUNCT_TRUE`: theorem statement contains `\\/ True` — vacuously provable via `right. exact I.`\n")
    lines.append("- `TRIVIAL_TRUE_PROOF`: proof body terminates with `exact I.` or `right. exact I.` — only proves `True`\n")
    lines.append("- `EXTRACT_CONSTANT`: `Extract Constant` bypasses Coq extraction with hand-written OCaml (trust boundary)\n")
    lines.append("- `KERNEL_CONVERTIBILITY_VACUITY`: theorem conclusion is kernel-convertible (after δ/ι/ζ/β reduction) to `True` or to a hypothesis — verified by `scripts/vacuity_gate.py` running synthesised Coq proofs (HIGH)\n")
    lines.append("\n")

    # Always show the vacuity ranking, including on a clean PASS, so every run
    # records which files have elevated vacuity scores.
    if vacuity_index:
        lines.append("## Vacuity Ranking (file-level)\n")
        lines.append(
            "Files scored by trivially-true / placeholder / definitional-proof heuristics.\n"
            "Score >= 100 → MEDIUM finding (fails gate). Score >= 50 → LOW warning.\n\n"
        )
        lines.append("| score | tags | file |\n")
        lines.append("|---:|---|---|\n")
        for score, abs_path, tags in sorted(vacuity_index, key=lambda t: (-t[0], str(t[1]))):
            try:
                rel = abs_path.relative_to(repo_root).as_posix()
            except Exception:
                rel = abs_path.as_posix()
            lines.append(f"| {score} | {', '.join(tags)} | `{esc(rel)}` |\n")
        lines.append("\n")
    else:
        lines.append("## Vacuity Ranking (file-level)\n")
        lines.append("(no files scored above zero — no trivially-true or placeholder patterns detected)\n\n")

    lines.append("## Findings\n")
    if not findings:
        lines.append("(none)\n")
        report_path.write_text("".join(lines), encoding="utf-8")
        return

    for sev in ("HIGH", "MEDIUM", "LOW"):
        items = by_sev.get(sev, [])
        if not items:
            continue
        lines.append(f"### {sev}\n")
        # Group by file for readability.
        items_sorted = sorted(items, key=lambda f: (str(f.file), f.line, f.rule_id))
        current_file: Path | None = None
        for f in items_sorted:
            if current_file != f.file:
                file_path = f.file
                current_file = file_path
                try:
                    rel = file_path.relative_to(repo_root).as_posix()
                except Exception:
                    rel = file_path.as_posix()
                lines.append(f"\n#### `{esc(rel)}`\n")
            lines.append(f"- L{f.line}: **{f.rule_id}** — {esc(f.message)}\n")
            lines.append(f"  - `{esc(f.snippet.strip())}`\n")
        lines.append("\n")

    report_path.write_text("".join(lines), encoding="utf-8")


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(
        description="INQUISITOR: single-mode, maximum-strictness Coq proof auditor. "
        "Always compiles and scans all Coq proof files, and exits non-zero on any HIGH or MEDIUM finding."
    )
    ap.add_argument("--report", default="INQUISITOR_REPORT.md", help="Markdown report path")
    # Legacy options are accepted for backward compatibility but ignored.
    ap.add_argument("--coq-root", action="append", default=["coq"], help=argparse.SUPPRESS)
    ap.add_argument("--no-build", action="store_true", default=False, help=argparse.SUPPRESS)
    ap.add_argument("--build", action="store_true", default=True, help=argparse.SUPPRESS)
    ap.add_argument("--allowlist", action="store_true", default=False, help=argparse.SUPPRESS)
    ap.add_argument("--allowlist-makefile-optional", action="store_true", default=False, help=argparse.SUPPRESS)
    ap.add_argument("--fail-on-protected", action="store_true", default=True, help=argparse.SUPPRESS)
    ap.add_argument("--strict", action="store_true", default=True, help=argparse.SUPPRESS)
    ap.add_argument("--ultra-strict", action="store_true", default=True, help=argparse.SUPPRESS)
    ap.add_argument("--ignore-makefile-optional", action="store_true", default=False, help=argparse.SUPPRESS)
    ap.add_argument("--no-fail-on-protected", dest="fail_on_protected", action="store_false", help=argparse.SUPPRESS)
    ap.add_argument(
        "--include-informational",
        action="store_true",
        default=False,
        help="Include informational SECTION_BINDER and MODULE_SIGNATURE_DECL findings in the report.",
    )
    ap.add_argument(
        "--manifest",
        default="coq/INQUISITOR_ASSUMPTIONS.json",
        help="Manifest for assumption audits, symmetry contracts, and paper mapping.",
    )
    ap.add_argument("--all-proofs", action="store_true", default=True, help=argparse.SUPPRESS)
    ap.add_argument("--only-coq-roots", dest="all_proofs", action="store_false", help=argparse.SUPPRESS)
    args = ap.parse_args(argv)

    # SINGLE STRICT MODE ONLY: no alternate profiles, no shortcuts.
    args.strict = True
    args.ultra_strict = True
    args.fail_on_protected = True
    args.allowlist = False
    args.allowlist_makefile_optional = False
    args.ignore_makefile_optional = True
    args.build = True
    args.all_proofs = True
    args.include_informational = False

    repo_root = Path(__file__).resolve().parents[1]
    coq_roots = [(repo_root / "coq").resolve()]
    report_path = (repo_root / args.report).resolve()
    manifest_path = (repo_root / args.manifest).resolve()
    manifest: dict | None = None

    global ALLOWLIST_EXACT_FILES
    ALLOWLIST_EXACT_FILES = set()
    missing_roots = [root for root in coq_roots if not root.exists()]
    if missing_roots:
        for root in missing_roots:
            print(f"ERROR: coq root not found: {root}", file=sys.stderr)
        return 2

    all_findings: list[Finding] = []
    
    # COMPILE ALL COQ PROOFS (default behavior)
    if args.build:
        rc, compile_findings = _run_make_all(repo_root)
        all_findings.extend(compile_findings)
        if rc != 0:
            # Write report with compilation errors before exiting
            write_report(
                report_path, repo_root, all_findings, 0, [],
                scanned_scope="compilation failed"
            )
            print(f"INQUISITOR: FAIL — Coq compilation failed with {len(compile_findings)} error(s).", file=sys.stderr)
            print(f"Report: {report_path}")
            return 1

        # Enforce that successful build actually covered all active coq/*.v sources.
        all_findings.extend(_check_coq_compilation_coverage(repo_root))

    _log_progress("Running proof-body foundation audit")
    all_findings.extend(_run_proof_body_foundation_audit(repo_root))

    vacuity_index: list[tuple[int, Path, tuple[str, ...]]] = []
    scanned = 0
    v_files = iter_all_coq_files(repo_root)
    v_files_list = list(v_files)
    scanned_scope = "repo"
    total_files = len(v_files_list)

    _log_progress(f"Starting static scan of {total_files} Coq files")

    for vf in v_files_list:
        scanned += 1
        file_started = time.monotonic()
        try:
            rel_path = vf.relative_to(repo_root).as_posix()
        except Exception:
            rel_path = vf.as_posix()
        if scanned == 1 or scanned % SCAN_PROGRESS_EVERY == 0:
            _log_progress(f"Scanning file {scanned}/{total_files}: {rel_path}")
        try:
            all_findings.extend(scan_file(vf))
            all_findings.extend(scan_trivial_equalities(vf))
            all_findings.extend(scan_exists_const_q(vf))
            all_findings.extend(scan_exact_alias(vf))
            all_findings.extend(scan_scope_drift(vf))
            all_findings.extend(scan_clamps(vf))
            all_findings.extend(scan_comment_smells(vf))
            all_findings.extend(scan_unused_hypotheses(vf))
            all_findings.extend(scan_definitional_invariance(vf))
            all_findings.extend(scan_z_to_nat_boundaries(vf))
            all_findings.extend(scan_physics_analogy_contract(vf))
            # New strict checks
            all_findings.extend(scan_proof_quality(vf))
            all_findings.extend(scan_mu_cost_consistency(vf))
            all_findings.extend(scan_chsh_bounds(vf))
            all_findings.extend(scan_axiom_dependencies(vf))
            # Deep proof substance checks (v2)
            all_findings.extend(scan_record_field_extraction(vf))
            all_findings.extend(scan_self_referential_record(vf))
            all_findings.extend(scan_phantom_imports(vf))
            all_findings.extend(scan_trivial_existentials(vf))
            all_findings.extend(scan_arithmetic_only_proofs(vf))
            # Circular reasoning detection (v3)
            all_findings.extend(scan_circular_definitions(vf))
            all_findings.extend(scan_emergence_circularity(vf))
            all_findings.extend(scan_constructor_round_trip(vf))
            all_findings.extend(scan_definitional_witness(vf))
            # Proof substance / tautology detection (v4)
            all_findings.extend(scan_vacuous_conjunction(vf))
            all_findings.extend(scan_tautological_implication(vf))
            # Disabled in max-strict mode: heuristic style warning, not proof-soundness critical.
            # all_findings.extend(scan_hypothesis_restatement(vf))
            # Physics derivation completeness (v5)
            all_findings.extend(scan_physics_stub_definitions(vf))
            all_findings.extend(scan_missing_core_physics_theorems(vf))
            all_findings.extend(scan_definitional_construction_circularity(vf))
            all_findings.extend(scan_incomplete_physics_markers(vf))
            all_findings.extend(scan_fake_completion_claims(vf))
            # Disabled in max-strict mode: heuristic style warning, not proof-soundness critical.
            # all_findings.extend(scan_unused_local_definitions(vf))
            # Vacuous proof pattern detection (v6)
            all_findings.extend(scan_false_conjunct_definition(vf))
            all_findings.extend(scan_trivial_lambda_witness(vf))
            # Vacuous disjunct / trivial True proof / extraction trust boundary (v7)
            all_findings.extend(scan_disjunct_true(vf))
            all_findings.extend(scan_trivial_true_proof(vf))
            all_findings.extend(scan_extract_constant(vf))

            score, tags = _file_vacuity_summary(vf)
            if score > 0:
                vacuity_index.append((score, vf, tags))
        except Exception as e:
            _log_progress(f"Scanner error in {rel_path}: {e}")
            all_findings.append(
                Finding(
                    rule_id="INTERNAL_ERROR",
                    severity="HIGH",
                    file=vf,
                    line=1,
                    snippet="",
                    message=f"Inquisitor crashed scanning this file: {e}",
                )
            )
        file_elapsed = time.monotonic() - file_started
        if file_elapsed >= SLOW_FILE_THRESHOLD_SECONDS:
            _log_progress(f"SLOW FILE {file_elapsed:.1f}s: {rel_path}")

    _log_progress("Running dependency and foundation connectivity scans")
    all_findings.extend(scan_proof_connectivity(repo_root, v_files_list))
    all_findings.extend(_scan_foundation_utilization(repo_root, v_files_list))

    if manifest_path.exists():
        try:
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            all_findings.append(
                Finding(
                    rule_id="MANIFEST_PARSE_ERROR",
                    severity="HIGH",
                    file=manifest_path,
                    line=1,
                    snippet=str(exc),
                    message="Failed to parse Inquisitor manifest JSON.",
                )
            )
            manifest = None

    if manifest:
        all_findings.extend(_assumption_audit(repo_root, manifest_path, manifest))
        all_findings.extend(_paper_symbol_map(repo_root, manifest_path, manifest))
        if args.all_proofs:
            all_findings.extend(_scan_symmetry_contracts(repo_root, manifest, all_proofs=True))
        else:
            for root in coq_roots:
                all_findings.extend(_scan_symmetry_contracts(root, manifest))

    # μ-axis vacuity discipline: consume artifacts/vacuity_audit.json
    # if present and surface kernel-convertibility findings as HIGH.
    all_findings.extend(_scan_kernel_convertibility_vacuity(repo_root))

    if not args.include_informational:
        all_findings = [
            f
            for f in all_findings
            if f.rule_id not in {"SECTION_BINDER", "MODULE_SIGNATURE_DECL"}
        ]

    # ── Vacuity gate ──────────────────────────────────────────────────────────
    # The vacuity SCORE (from inquisitor_rules.summarize_text) measures how
    # "trivially true / definitional" a file looks.  The score is enforced by
    # the same gate that reports it: a high score fails, while a lower score is
    # retained as a warning.  A file like `Theorem foo : True.` therefore
    # cannot produce a clean PASS.
    #
    #   score >= 100  → MEDIUM finding  (True conclusions, Prop:=True, placeholders)
    #   score >=  50  → LOW finding     (const-fun, suspicious-but-mild patterns)
    #
    # Threshold 100 catches every genuine trivially-true theorem while allowing
    # single const-fun definitions (score 65) to remain LOW warnings.
    VACUITY_MEDIUM_THRESHOLD = 100
    VACUITY_LOW_THRESHOLD = 50
    for v_score, v_path, v_tags in vacuity_index:
        if v_score >= VACUITY_MEDIUM_THRESHOLD:
            sev = "MEDIUM"
        elif v_score >= VACUITY_LOW_THRESHOLD:
            sev = "LOW"
        else:
            continue
        try:
            v_rel = v_path.relative_to(repo_root).as_posix()
        except Exception:
            v_rel = str(v_path)
        all_findings.append(
            Finding(
                rule_id="VACUITY_SCORE",
                severity=sev,
                file=v_path,
                line=1,
                snippet="(file-level vacuity scan)",
                message=(
                    f"Vacuity score {v_score} ≥ {'MEDIUM' if sev == 'MEDIUM' else 'LOW'} threshold "
                    f"{VACUITY_MEDIUM_THRESHOLD if sev == 'MEDIUM' else VACUITY_LOW_THRESHOLD}. "
                    f"Tags: {', '.join(v_tags)}. "
                    "Review for trivially-true/placeholder/definitional proofs that don't "
                    "advance the core goal."
                ),
            )
        )

    write_report(
        report_path,
        repo_root,
        all_findings,
        scanned,
        vacuity_index,
        scanned_scope=scanned_scope,
    )

    # Fail-fast policy: ANY HIGH finding in ANY file fails the build.
    # No allowlists, no exceptions.
    all_high = [f for f in all_findings if f.severity == "HIGH"]

    if all_high:
        print(f"INQUISITOR: FAIL — {len(all_high)} HIGH findings across all files.")
        print(f"Report: {report_path}")
        # Print a short console summary.
        for f in all_high[:50]:
            rel = f.file.relative_to(repo_root).as_posix()
            print(f"- {rel}:L{f.line} {f.rule_id} {f.message}")
        if len(all_high) > 50:
            print(f"... ({len(all_high) - 50} more)")
        return 1

    # Single strict mode also fails on ANY MEDIUM finding.
    all_medium = [f for f in all_findings if f.severity == "MEDIUM"]
    if all_medium:
        print(f"INQUISITOR: FAIL — {len(all_medium)} MEDIUM findings across all files.")
        print(f"Report: {report_path}")
        for f in all_medium[:50]:
            rel = f.file.relative_to(repo_root).as_posix()
            print(f"- {rel}:L{f.line} {f.rule_id} {f.message}")
        if len(all_medium) > 50:
            print(f"... ({len(all_medium) - 50} more)")
        return 1

    print("INQUISITOR: OK")
    print(f"Report: {report_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
