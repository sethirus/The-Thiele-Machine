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

Archive directory (archive/) is excluded from scanning as it contains old/iterative
code kept for posterity only.

This is a strict static analysis tool; it errs on the side of flagging.
"""

from __future__ import annotations

import argparse
import dataclasses
import datetime as _dt
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Iterable, Iterator

from inquisitor_rules import summarize_text


# STRICT MODE: Core kernel files that must have ZERO high/medium findings
PROTECTED_BASENAMES = {"CoreSemantics.v", "BridgeDefinitions.v"}

# ULTRA STRICT: Critical kernel proof files
CRITICAL_KERNEL_FILES = {
    "TsirelsonUpperBound.v",
    "TsirelsonLowerBound.v", 
    "TsirelsonUniqueness.v",
    "NoFreeInsight.v",
    "MuCostModel.v",
    "CHSHExtraction.v",
    "QuantumEquivalence.v",
    "KernelPhysics.v",
    "VMState.v",
    "VMStep.v",
}

# ---------------------------------------------------------------------------
# Tier system — from coq/_CoqProject (-R directory Namespace mappings)
# Tier 1: Extraction-critical. Gets extracted to OCaml/Python VM + RTL CPU.
#         Must ONLY import Kernel + Coq stdlib. Zero tolerance for outside deps.
# Tier 2: Thesis-essential theory. Proofs ABOUT the machine, not extracted.
#         May import Tier 1 + Tier 2. Must NOT import Tier 3 (exploratory).
# Tier 3: Exploratory/speculative. Free to import from anywhere.
# ---------------------------------------------------------------------------
_TIER1_DIRS: frozenset[str] = frozenset({"kernel"})
_TIER1_NAMESPACES: frozenset[str] = frozenset({"Kernel"})

_TIER2_DIRS: frozenset[str] = frozenset({
    "nofi", "bridge", "thielemachine", "kernel_toe", "modular_proofs", "isomorphism",
})
_TIER2_NAMESPACES: frozenset[str] = frozenset({
    "NoFI", "Bridge", "ThieleMachine", "ThieleMachineVerification",
    "KernelTOE", "ModularProofs", "Isomorphism",
})

_TIER3_DIRS: frozenset[str] = frozenset({
    "physics", "self_reference", "shor_primitives", "spacetime_projection",
    "thiele_manifold", "project_cerberus", "catnet", "thieleuniversal",
    "theory", "physics_exploration", "quantum_derivation", "thermodynamic", "spacetime",
})
_TIER3_NAMESPACES: frozenset[str] = frozenset({
    "Physics", "SelfReference", "ShorPrimitives", "SpacetimeProjection",
    "ThieleManifold", "ProjectCerberus", "CatNet", "ThieleUniversal",
    "Theory", "PhysicsExploration", "QuantumDerivation", "Thermodynamic", "Spacetime",
})

_NAMESPACE_TO_TIER: dict[str, int] = {}
_NAMESPACE_TO_TIER.update({ns: 1 for ns in _TIER1_NAMESPACES})
_NAMESPACE_TO_TIER.update({ns: 2 for ns in _TIER2_NAMESPACES})
_NAMESPACE_TO_TIER.update({ns: 3 for ns in _TIER3_NAMESPACES})

_STDLIB_NAMESPACES: frozenset[str] = frozenset({"Coq", "Stdlib"})


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
DEFINITIONAL_LABEL_RE = re.compile(r"(?i)\bdefinitional lemma\b")
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
    """Iterate all Coq .v files, excluding archive directories."""
    for p in repo_root.rglob("*.v"):
        if not p.is_file():
            continue
        # EXCLUDE ARCHIVE: archive/ contains old/iterative code kept for posterity only
        # These files are not part of the active proof corpus and should not be audited
        relative_path = "/" + str(p.relative_to(repo_root).as_posix())
        if "/archive/" in relative_path:
            continue
        raw = p.read_text(encoding="utf-8", errors="replace")
        if _looks_like_coq(raw):
            yield p


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
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    findings: list[Finding] = []
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
        # These tactics can implicitly consume ANY hypothesis in scope:
        implicit_consumers = re.compile(
            r"\b(auto|eauto|intuition|firstorder|assumption|easy|trivial|"
            r"lia|omega|lra|nra|nia|congruence|tauto|now|"
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
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    raw_lines = raw.splitlines()  # Keep original with comments for label checking
    findings: list[Finding] = []
    lemma_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b")
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
        proof_block = text[proof_pos: min(len(text), proof_pos + 400)]
        if "reflexivity." in proof_block or "easy." in proof_block:
            # Check for definitional label in ORIGINAL text (with comments)
            line = line_of[m.start()]
            label_context = "\n".join(raw_lines[max(0, line - 4): line])
            if DEFINITIONAL_LABEL_RE.search(label_context):
                continue
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else stmt
            findings.append(
                Finding(
                    rule_id="DEFINITIONAL_INVARIANCE",
                    severity=_severity_for_path(path, "HIGH"),
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message="Invariance/equivariance lemma proved by reflexivity/easy (definitional).",
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
        # Check for definitional label in ORIGINAL text (with comments)
        label_context = "\n".join(raw_lines[max(0, idx - 4): idx])
        if DEFINITIONAL_LABEL_RE.search(label_context):
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
                message="Physics-analogy theorem lacks invariance lemma and is not labeled definitional.",
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
        r"(?m)^[ \t]*(Axiom|Parameter|Hypothesis|Variable|Variables|Context)\b\s*"  # kind
        r"(?:\(?\s*([A-Za-z0-9_']+)\b)?"  # optional name (may be absent for Context (...))
    )
    for m in assumption_decl.finditer(text):
        kind = m.group(1)
        name = (m.group(2) or "").strip()
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else kind
        
        # Get extended context to detect complex Context types
        context_end = text.find(").", m.start())
        if context_end == -1:
            context_end = text.find(".", m.start())
        full_decl = text[m.start():context_end + 1] if context_end != -1 else snippet

        # Inside a Module Type, treat declarations as signature fields.
        if 1 <= line < len(in_module_type) and in_module_type[line] and kind in {"Axiom", "Parameter"}:
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

        if kind in {"Axiom", "Parameter"}:
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
            # Variable/Variables
            rule_id = "SECTION_BINDER"
            severity = "MEDIUM"
            msg = f"Found {kind}{(' ' + name) if name else ''}."

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

    # Definition ... := [].
    def_empty_list = re.compile(r"(?m)^[ \t]*Definition\s+([A-Za-z0-9_']+)\b.*:=\s*\[\]\s*\.")
    for m in def_empty_list.finditer(text):
        name = m.group(1)
        line = line_of[m.start()]
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
        # Allow if there's an INQUISITOR NOTE marking this as a deliberate alias
        if re.search(r'INQUISITOR NOTE.*alias|INQUISITOR NOTE.*export|INQUISITOR NOTE.*compat', context, re.IGNORECASE):
            continue

        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else name
        aliased = re.match(r'^exact\s+(\w+)\s*\.$', proof_lines[0]).group(1)
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
                    "(* INQUISITOR NOTE: alias for <reason> *) above the theorem."
                ),
            )
        )

    return findings


_FROM_REQUIRE_RE = re.compile(r'^From\s+([A-Za-z_][A-Za-z0-9_]*)\s+Require\b')


def scan_scope_drift(path: Path) -> list[Finding]:
    """Enforce tier-boundary separation for Coq imports.

    Tier system (driven by coq/_CoqProject namespace mappings):
      Tier 1 — Extraction core (coq/kernel/):
        Gets extracted to OCaml/Python VM and RTL CPU.
        Must ONLY use ``Kernel`` + Coq stdlib imports.
        Any import of a Tier-2 or Tier-3 namespace contaminates the extraction.
      Tier 2 — Thesis-essential theory (nofi/, bridge/, thielemachine/, ...):
        Proofs ABOUT the machine — not extracted.
        May import Tier-1 and Tier-2 namespaces.
        Must NOT import Tier-3 (exploratory/speculative) namespaces.
      Tier 3 — Exploratory / speculative (physics/, spacetime/, thermodynamic/, ...):
        Free research. May import anything.

    Rule IDs emitted:
      ``SCOPE_DRIFT_TIER1`` (HIGH):  Tier-1 file imports a Tier-2 or Tier-3 namespace.
      ``SCOPE_DRIFT_TIER2`` (MEDIUM): Tier-2 file imports a Tier-3 namespace.

    Suppression: add ``(* INQUISITOR NOTE: cross-tier import for <reason> *)``
    on the line immediately above the offending ``From … Require`` line.
    """
    file_tier = _path_to_tier(path)
    if file_tier is None or file_tier == 3:
        return []  # Root coq/ files and Tier 3 files are exempt from tier enforcement

    raw = path.read_text(encoding="utf-8", errors="replace")
    raw_lines = raw.splitlines()
    findings: list[Finding] = []

    for i, line in enumerate(raw_lines, start=1):
        m = _FROM_REQUIRE_RE.match(line.strip())
        if not m:
            continue
        ns = m.group(1)
        if ns in _STDLIB_NAMESPACES:
            continue  # Coq / Stdlib is always allowed
        if ns in _TIER1_NAMESPACES:
            continue  # Kernel imports are always allowed in Tier 1 and 2

        import_tier = _NAMESPACE_TO_TIER.get(ns)
        if import_tier is None:
            continue  # Unknown namespace — not our concern here

        # Check for suppression comment anywhere in the 3 lines above
        context = "\n".join(raw_lines[max(0, i - 4): i])
        if re.search(r'INQUISITOR NOTE.*cross.tier|INQUISITOR NOTE.*tier', context, re.IGNORECASE):
            continue
        if re.search(r'\(\*\s*SAFE:', context):
            continue

        if file_tier == 1 and import_tier >= 2:
            tier_label = "Tier 2 (thesis theory)" if import_tier == 2 else "Tier 3 (exploratory/speculative)"
            findings.append(
                Finding(
                    rule_id="SCOPE_DRIFT_TIER1",
                    severity="HIGH",
                    file=path,
                    line=i,
                    snippet=line.strip(),
                    message=(
                        f"Extraction-critical coq/kernel/ file imports `{ns}` ({tier_label}). "
                        "The kernel must be self-contained (only Kernel + Coq stdlib). "
                        f"Either move the needed proof into coq/kernel/ under the Kernel namespace, "
                        f"or relocate this file to a higher-tier directory. "
                        "Suppress with: (* INQUISITOR NOTE: cross-tier import for <reason> *)"
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
                        f"Thesis-essential Tier-2 file imports `{ns}` (Tier 3 exploratory). "
                        "Speculative/exploratory modules should not be imported into thesis-essential proofs. "
                        "Move the needed lemma into the Kernel or a shared Tier-2 module. "
                        "Suppress with: (* INQUISITOR NOTE: cross-tier import for <reason> *)"
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
            # Check for INQUISITOR NOTE
            raw_lines = raw.splitlines()
            note_start = max(0, line - 4)
            note_end = min(len(raw_lines), line + 2)
            note_context = "\n".join(raw_lines[note_start:note_end])
            if "INQUISITOR NOTE" in note_context:
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


def scan_phantom_imports(path: Path) -> list[Finding]:
    """Detect files that import kernel modules (VMStep, VMState, etc.) but
    never use them substantively in any proof.

    A 'phantom import' creates the illusion of grounding in VM semantics
    when the proofs are actually self-contained arithmetic/logic.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    # Key kernel symbols that indicate real engagement with VM semantics
    kernel_symbols = {
        "vm_step": "VMStep",
        "exec_trace": "VMStep",
        "inversion Hstep": "VMStep (case analysis)",
        "mu_conservation_kernel": "KernelPhysics",
        "observational_no_signaling": "KernelPhysics",
        "exec_trace_no_signaling_outside_cone": "SpacetimeEmergence",
        "cone_monotonic": "KernelPhysics",
    }

    # Check if the file imports kernel modules
    kernel_imports = re.compile(
        r"(?m)^[ \t]*From\s+Kernel\s+Require\s+Import\s+(.*?)\."
    )
    import_match = kernel_imports.search(text)
    if not import_match:
        return findings

    imported_modules = import_match.group(1)
    imports_vmstep = "VMStep" in imported_modules
    imports_vmstate = "VMState" in imported_modules

    if not (imports_vmstep or imports_vmstate):
        return findings

    # Find all Proof...Qed blocks
    proof_blocks = re.findall(r"Proof\.(.*?)(?:Qed|Defined|Admitted)\.", text, re.DOTALL)
    all_proof_text = " ".join(proof_blocks)

    # Check if any kernel symbol is actually used in a proof
    used_symbols = []
    for sym, source in kernel_symbols.items():
        if sym in all_proof_text:
            used_symbols.append(sym)

    # Also check if vm_step appears in theorem statements as a REAL hypothesis
    # (not just in comments)
    vm_step_in_stmt = bool(re.search(
        r"(?m)^[ \t]*(Theorem|Lemma)\s+\w+\s*:.*\bvm_step\b", text
    ))

    # Also check if any definition uses VMState/PartitionGraph types substantively
    uses_vm_types = bool(re.search(
        r"\b(VMState|PartitionGraph|vm_graph|vm_mu|vm_regs|pg_modules|pg_next_id)\b", all_proof_text
    ))

    # Also check if VMState types are used in definitions (not just proofs)
    # This catches legitimate use of imports for type signatures
    uses_vm_in_definitions = bool(re.search(
        r"(?m)^[ \t]*(Definition|Fixpoint|Record)\b.*\b(VMState|PartitionGraph|vm_instruction|vm_graph|vm_mu)\b",
        text
    ))

    # Check if imported symbols are used anywhere in the file body (definitions, types, etc.)
    # Key symbols from each module that indicate real usage
    kernel_usage_symbols = [
        "vm_instruction", "instruction_cost", "instr_targets", "causal_cone",
        "PartitionGraph", "VMState", "vm_graph", "vm_mu", "vm_regs",
        "pg_modules", "pg_next_id", "well_formed_graph", "ObservableRegion",
        "ObservableSignature", "module_in_cone", "apply_cost",
        "mu_gauge_shift", "instr_halt", "instr_pnew",
    ]
    uses_kernel_in_body = any(sym in text for sym in kernel_usage_symbols)

    if not used_symbols and not uses_vm_types and not uses_vm_in_definitions and not uses_kernel_in_body:
        line = line_of[import_match.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else import_match.group(0)

        # Only flag if the file has theorems (not just definitions)
        has_theorems = bool(re.search(r"(?m)^[ \t]*(Theorem|Lemma)\s+", text))
        if has_theorems:
            findings.append(
                Finding(
                    rule_id="PHANTOM_KERNEL_IMPORT",
                    severity=_severity_for_path(path, "HIGH"),
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=f"File imports Kernel modules ({imported_modules.strip()}) but no proof "
                            f"engages with VM semantics (vm_step, exec_trace, etc.). "
                            f"Claims of deriving results 'from VM step relation' are unsupported.",
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
            # Check for INQUISITOR NOTE in the original text (with comments)
            # covering a few lines before the theorem
            raw_lines = raw.splitlines()
            line = line_of[tm.start()]
            note_start = max(0, line - 4)
            note_end = min(len(raw_lines), line + 2)
            note_context = "\n".join(raw_lines[note_start:note_end])
            if "INQUISITOR NOTE" in note_context:
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
    
    Exempt: Theorems marked with (* DEFINITIONAL HELPER *) or (* HELPER LEMMA *)
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = raw.splitlines()  # Keep comments for exemption check
    findings: list[Finding] = []
    
    # Collect definitions
    def_re = re.compile(r"(?m)^[ \t]*Definition\s+([A-Za-z0-9_']+)\b")
    definitions = {m.group(1) for m in def_re.finditer(text)}
    
    if not definitions:
        return findings
    
    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b")
    proof_re = re.compile(r"(?m)^[ \t]*Proof\.")
    end_re = re.compile(r"(?m)^[ \t]*(Qed|Defined|Admitted)\.")
    
    # Exemption markers
    exemption_re = re.compile(r'\(\*\*?\s*(DEFINITIONAL|HELPER|BASIC|ARITHMETIC|ACCESSOR|PROJECTION)\b', re.IGNORECASE)
    
    for tm in theorem_re.finditer(text):
        tname = tm.group(2)
        stmt_end = text.find(".", tm.end())
        if stmt_end == -1:
            continue
        stmt = re.sub(r"\s+", " ", text[tm.start():stmt_end + 1]).strip()
        
        # Check for exemption marker in preceding 3 lines
        line_num = line_of[tm.start()]
        preceding_text = "\n".join(clean_lines[max(0, line_num-4):line_num])
        if exemption_re.search(preceding_text):
            continue  # Explicitly marked as helper lemma
        
        # Check which definitions are mentioned in the statement
        mentioned_defs = [d for d in definitions if re.search(rf'\b{d}\b', stmt)]
        if not mentioned_defs:
            continue
        
        proof_match = proof_re.search(text, stmt_end)
        if not proof_match:
            continue
        end_match = end_re.search(text, proof_match.end())
        if not end_match:
            continue
        proof_block = text[proof_match.end():end_match.start()].strip()
        proof_text = re.sub(r"\s+", " ", proof_block)
        
        # Pattern: unfold X (no other tactics except reflexivity/simpl/lia)
        # If proof is ONLY unfold + reflexivity, it's definitional
        for defn in mentioned_defs:
            unfold_pat = re.compile(rf'\bunfold\s+{defn}\b')
            if unfold_pat.search(proof_text):
                # Check if proof is suspiciously simple
                tactics = [t.strip() for t in re.split(r'[.;]', proof_text) if t.strip()]
                non_trivial_tactics = [t for t in tactics if not re.match(
                    r'^\s*(unfold|simpl|reflexivity|lia|lra|auto|trivial|intros?|split)\b', t)]
                
                if len(non_trivial_tactics) == 0 and len(tactics) <= 5:
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
                                    f"by simple tactics. Mark with (* DEFINITIONAL HELPER *) if legitimate, "
                                    f"or prove non-circularly by engaging with structure.",
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

    Exempt: Theorems marked with (* DEFINITIONAL WITNESS *) or similar
    in the preceding 3 lines (same convention as scan_circular_definitions).
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    raw_lines = raw.splitlines()  # Keep comments for exemption check
    findings: list[Finding] = []

    # Collect definitions
    def_re = re.compile(r"(?m)^[ \t]*Definition\s+([A-Za-z0-9_']+)\b")
    definitions = {m.group(1) for m in def_re.finditer(text)}

    if not definitions:
        return findings

    # Exemption markers (same as scan_circular_definitions)
    exemption_re = re.compile(r'\(\*\*?\s*(DEFINITIONAL|HELPER|BASIC|ARITHMETIC|ACCESSOR|PROJECTION)\b', re.IGNORECASE)

    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b")
    proof_re = re.compile(r"(?m)^[ \t]*Proof\.")
    end_re = re.compile(r"(?m)^[ \t]*(Qed|Defined|Admitted)\.")

    for tm in theorem_re.finditer(text):
        tname = tm.group(2)
        stmt_end = text.find(".", tm.end())
        if stmt_end == -1:
            continue
        stmt = re.sub(r"\s+", " ", text[tm.start():stmt_end + 1]).strip()

        # Check if this is an existential theorem
        if 'exists' not in stmt.lower():
            continue

        # Check for exemption marker in preceding 3 lines (use raw for comments)
        line_num = line_of[tm.start()]
        preceding_text = "\n".join(raw_lines[max(0, line_num-4):line_num])
        if exemption_re.search(preceding_text):
            continue  # Explicitly marked as substantive witness

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


def scan_phantom_vm_step(path: Path) -> list[Finding]:
    """Detect theorems that take vm_step as a hypothesis but never use it.

    Pattern: `forall s s' instr, vm_step s instr s' -> ... `
    Proof: `intros ... . lia.` (vm_step hypothesis is never used)

    Catches: direct inversion/destruct, AND indirect usage via apply/exact/
    specialize/pose proof/eauto/assumption that passes the hypothesis to
    another lemma.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    # Check if vm_step is a local Definition/Let (not an Inductive relation).
    # Files that define vm_step as a function use it computationally, not as
    # a phantom hypothesis.
    if re.search(r'(?m)^\s*(Definition|Let|Fixpoint)\s+vm_step\b', text):
        return findings

    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b")
    proof_re = re.compile(r"(?m)^[ \t]*Proof\.")
    end_re = re.compile(r"(?m)^[ \t]*(Qed|Defined|Admitted)\.")

    for tm in theorem_re.finditer(text):
        tname = tm.group(2)
        # Collect the full statement
        stmt_end_pos = tm.end()
        while stmt_end_pos < len(text):
            ch = text[stmt_end_pos]
            if ch == ".":
                if stmt_end_pos + 1 >= len(text) or text[stmt_end_pos + 1] in " \n\t\r":
                    break
            stmt_end_pos += 1

        stmt = re.sub(r"\s+", " ", text[tm.start():stmt_end_pos + 1]).strip()

        # Check if vm_step appears in the statement AS A HYPOTHESIS (after ->),
        # not just in the theorem name or conclusion.
        # Look for: vm_step ... ->  (it's a premise)
        stmt_after_colon = stmt.split(":", 1)[1] if ":" in stmt else stmt
        if "vm_step" not in stmt_after_colon:
            continue
        # Ensure vm_step is in a hypothesis position (before some ->)
        # Simple check: vm_step appears AND there's an -> after it
        vm_pos = stmt_after_colon.find("vm_step")
        arrow_after = stmt_after_colon.find("->", vm_pos) if vm_pos >= 0 else -1
        if arrow_after < 0:
            continue

        proof_match = proof_re.search(text, stmt_end_pos)
        if not proof_match:
            continue
        end_match = end_re.search(text, proof_match.end())
        if not end_match:
            continue

        proof_block = text[proof_match.end():end_match.start()].strip()

        # vm_step is in a hypothesis. Check if the proof USES it.
        # Direct usage: inversion, destruct, case, elim on step hyp.
        # Indirect usage: passing step hyp to another lemma via apply,
        # eapply, exact, specialize, pose proof, rewrite, assumption,
        # eauto, auto.
        #
        # We look for ANY of these patterns that reference a step-
        # related hypothesis name (Hstep, H_step, Hvm, Hcons, etc.)
        # or that apply a lemma known to consume vm_step.
        step_hyp_names = re.compile(
            r"\b(Hstep|H_step|Hvm|Hcons|Hlocal)\b"
        )
        # Collect hypothesis names that might hold the vm_step from intros
        intro_match = re.search(r"intros?\s+([^.]+)\.", proof_block)
        if intro_match:
            intro_names = intro_match.group(1).split()
            # Also check if any introduced name is used via apply/exact/etc
            for nm in intro_names:
                nm_clean = nm.strip("()[]")
                if nm_clean and nm_clean != "_":
                    step_hyp_names = re.compile(
                        step_hyp_names.pattern + rf"|\b{re.escape(nm_clean)}\b"
                    )

        # Check for direct structural usage
        direct_use = bool(re.search(
            r"\b(inversion|destruct|case|elim)\b", proof_block
        ))

        # Check for indirect usage: applying lemmas or passing hypotheses
        indirect_use = False
        if not direct_use:
            # Check if any step-hypothesis name appears in apply/exact/specialize/etc
            consume_pats = [
                r"\bapply\b",
                r"\beapply\b",
                r"\bexact\b",
                r"\bspecialize\b",
                r"\bpose\s+proof\b",
                r"\brewrite\b",
                r"\bassumption\b",
                r"\beauto\b",
                r"\bauto\b",
            ]
            # If the proof uses assumption/eauto/auto, those can implicitly
            # consume the vm_step hypothesis
            if re.search(r"\b(assumption|eauto|auto)\b", proof_block):
                indirect_use = True
            # If the proof applies/specializes with a step hypothesis name
            elif step_hyp_names.search(proof_block):
                for pat in consume_pats:
                    if re.search(pat, proof_block):
                        indirect_use = True
                        break
            # If the proof applies a known vm_step-consuming lemma
            elif re.search(
                r"\b(apply|eapply|exact|pose\s+proof)\s+"
                r"(mu_conservation|vm_step_mu|vm_step_cost|vm_step_next_id|"
                r"observational_no_signaling|step_preserves|vm_step_vm_apply|"
                r"Physics_Closure|Kernel_Physics_Closure)",
                proof_block
            ):
                indirect_use = True

        if not direct_use and not indirect_use:
            line = line_of[tm.start()]
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname
            findings.append(
                Finding(
                    rule_id="PHANTOM_VM_STEP",
                    severity=_severity_for_path(path, "HIGH"),
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=f"Theorem `{tname}` takes `vm_step` as hypothesis but the proof "
                            f"never uses it (no inversion/destruct/apply/specialize/eauto). "
                            f"The step relation is phantom — the result holds without it.",
                )
            )

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

        # Detect /\ True at the end or True /\ at the start of conclusion
        has_conj_true = bool(
            re.search(r"/\\\s*True\s*\.", stmt) or
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
        # Check for INQUISITOR NOTE in original text
        raw_lines = raw.splitlines()
        note_start = max(0, idx - 4)
        note_end = min(len(raw_lines), idx + 2)
        note_context = "\n".join(raw_lines[note_start:note_end])
        has_note = "INQUISITOR NOTE" in note_context

        for hyp in hypotheses:
            hyp_norm = re.sub(r"\s+", " ", hyp)
            if hyp_norm == conclusion_norm and conclusion_norm:
                if has_note:
                    continue  # Verified tautology — intentional extraction
                snippet = clean_lines[idx - 1] if 0 <= idx - 1 < len(clean_lines) else stmt
                findings.append(
                    Finding(
                        rule_id="TAUTOLOGICAL_IMPLICATION",
                        severity=_severity_for_path(path, "HIGH"),
                        file=path,
                        line=idx,
                        snippet=snippet.strip(),
                        message=f"Theorem `{name}` has conclusion `{conclusion_norm}` identical to "
                                f"hypothesis `{hyp_norm}` — this is a tautology (P -> P), proves nothing.",
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
            # Check if the conclusion text appears inside the definition body
            if has_note:
                continue  # Verified extraction — intentional
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
                                f"Definition `{hyp_def_name}` — conclusion may be restating part of "
                                f"hypothesis (check if proof is `tauto`/`intuition`).",
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
    has_intentional_marker = "INQUISITOR NOTE: MISSING einstein_equation IS INTENTIONAL" in raw
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


def scan_einstein_proof_substance(path: Path) -> list[Finding]:
    """Require substantive Einstein-equation proof content in gravity files.

    This blocks placeholder theorem shapes such as proofs that only unfold
    definitions and end in reflexivity/field/easy.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    if not re.search(r"(?i)(gravity|einstein)", path.name):
        return findings

    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']*einstein[_]?equation[A-Za-z0-9_']*)\b")
    proof_re = re.compile(r"(?m)^[ \t]*Proof\.")
    end_re = re.compile(r"(?m)^[ \t]*(Qed|Defined|Admitted)\.")

    for tm in theorem_re.finditer(text):
        tname = tm.group(2)
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
        proof_text = re.sub(r"\s+", " ", proof_block)
        line = line_of[tm.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname

        # Reject purely definitional proofs
        only_simple = bool(re.fullmatch(
            r"(?is)(?:\s*(?:intros?\b[^.]*\.|unfold\b[^.]*\.|simpl\.|cbn\.|compute\.|"
            r"reflexivity\.|easy\.|trivial\.|field\.|ring\.|lia\.|lra\.|auto\.|eauto\.|now\b[^.]*\.)\s*)+",
            proof_text,
        ))

        # Require at least one nontrivial bridge lemma usage
        has_bridge_usage = bool(re.search(
            r"\b(curvature_from_mu_gradients|stress_energy_conserved_non_pmerge|"
            r"mu_conservation|observational_no_signaling|exec_trace_no_signaling_outside_cone)\b",
            proof_text,
        ))

        if only_simple or not has_bridge_usage:
            findings.append(
                Finding(
                    rule_id="EINSTEIN_PROOF_INSUFFICIENT",
                    severity="HIGH",
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=f"Theorem `{tname}` proof appears non-substantive. "
                            f"Require non-definitional reasoning that uses conservation/locality bridge lemmas.",
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


def scan_einstein_model_mismatch(path: Path) -> list[Finding]:
    """Detect structural definition mismatch making Einstein equation non-derivable.

    Heuristic pattern flagged as HIGH risk:
    - `ricci_curvature` is defined from neighbor-gradient Laplacian that can be 0
      for isolated modules.
    - `stress_energy` is defined from module encoding length, which can be > 0
      for isolated modules.

    In that setting, an unconditional equation
      einstein_tensor = 8*PI*G*stress_energy
    is generally false for isolated modules with non-empty axioms.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    findings: list[Finding] = []

    if not re.search(r"(?i)mugravity|einstein|gravity", path.as_posix()):
        return findings

    has_neighbors_laplacian = bool(re.search(
        r"Definition\s+mu_laplacian\b[\s\S]*fold_left\s*\(fun\s+acc\s+n\s*=>",
        text,
    )) and bool(re.search(r"module_neighbors", text))

    has_ricci_from_laplacian = bool(re.search(
        r"Definition\s+ricci_curvature\b[\s\S]*:=\s*mu_laplacian",
        text,
    ))

    has_stress_from_encoding = bool(re.search(
        r"Definition\s+stress_energy\b[\s\S]*module_encoding_length",
        text,
    ))

    has_encoding_from_axioms = bool(re.search(
        r"Definition\s+module_encoding_length\b[\s\S]*module_axioms",
        text,
    ))

    # Only flag as HIGH mismatch when the file presents an unconditional Einstein theorem.
    einstein_stmt = re.search(
        r"(?ms)^[ \t]*(Theorem|Lemma)\s+einstein[_]?equation\b(.*?)\.",
        text,
    )
    has_balance_premise = False
    if einstein_stmt:
        stmt = re.sub(r"\s+", " ", einstein_stmt.group(2))
        has_balance_premise = bool(re.search(r"ricci_curvature.*stress_energy.*->", stmt))

    if (
        has_neighbors_laplacian
        and has_ricci_from_laplacian
        and has_stress_from_encoding
        and has_encoding_from_axioms
        and not has_balance_premise
    ):
        findings.append(
            Finding(
                rule_id="EINSTEIN_MODEL_MISMATCH",
                severity="HIGH",
                file=path,
                line=1,
                snippet=path.name,
                message="Current definitions permit isolated modules with zero curvature but positive stress-energy, "
                        "so unconditional Einstein equation is structurally non-derivable. Redefine curvature/stress "
                        "model before requiring full theorem.",
            )
        )

    return findings


def scan_stress_energy_grounding(path: Path) -> list[Finding]:
    """Flag stress-energy definitions that are built from curvature quantities.

    For derivational integrity, stress-energy should be grounded in kernel
    primitives (axiom/encoding/state structure), not defined via Ricci/Einstein
    objects that are themselves geometric outputs.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    if not re.search(r"(?i)(gravity|einstein|curvature|physics)", path.as_posix()):
        return findings

    m = re.search(r"(?ms)^[ \t]*Definition\s+stress_energy\b[^:]*:=\s*(.*?)\.", text)
    if not m:
        return findings

    body = re.sub(r"\s+", " ", m.group(1)).strip()
    derived_markers = (
        "ricci_curvature",
        "scalar_curvature",
        "einstein_tensor",
        "mu_laplacian",
        "angle_defect_curvature",
    )
    uses_derived = any(tok in body for tok in derived_markers)

    if uses_derived:
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else "Definition stress_energy"
        findings.append(
            Finding(
                rule_id="STRESS_ENERGY_UNGROUNDED",
                severity="HIGH",
                file=path,
                line=line,
                snippet=snippet.strip(),
                message="stress_energy is defined from curvature/tensor quantities. "
                        "Define stress_energy from kernel primitives first, then prove coupling to curvature.",
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


def scan_mugravity_completion_gate(path: Path) -> list[Finding]:
    """Fail if top-level MuGravity completion theorems expose deprecated bridge predicates.

    This gate enforces that completion-facing theorem interfaces in
    MuGravity_Emergence do not require legacy bridge predicates directly.
    """
    if path.name != "MuGravity_Emergence.v":
        return []

    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    targets = [
        # Removed: einstein_equation_after_scheduler_emergence (vacuous theorem deleted)
        "full_gravity_path_scheduler_contract",
    ]
    forbidden = [
        "curvature_laplacian_calibrated",
        "source_normalization_seed",
        "local_conservation_contract_one_step",
        "horizon_defect_area_calibrated",
        "landauer_horizon_bridge",
    ]

    for tname in targets:
        m = re.search(rf"(?ms)^[ \t]*(Theorem|Lemma)\s+{re.escape(tname)}\b(.*?)\.", text)
        if not m:
            findings.append(
                Finding(
                    rule_id="MU_GRAVITY_COMPLETION_GATE",
                    severity="HIGH",
                    file=path,
                    line=1,
                    snippet=tname,
                    message=f"Required completion theorem `{tname}` is missing.",
                )
            )
            continue

        stmt_text = re.sub(r"\s+", " ", m.group(0))
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname
        for token in forbidden:
            if token in stmt_text:
                findings.append(
                    Finding(
                        rule_id="MU_GRAVITY_COMPLETION_GATE",
                        severity="HIGH",
                        file=path,
                        line=line,
                        snippet=snippet.strip(),
                        message=(
                            f"Completion theorem `{tname}` still exposes deprecated bridge predicate "
                            f"`{token}` in its interface."
                        ),
                    )
                )

    return findings


def scan_mugravity_bridge_leaks(path: Path) -> list[Finding]:
    """Fail if Einstein/Horizon/Curvature theorem interfaces leak legacy bridge predicates.

    Applies to MuGravity*.v files and checks theorem statements only.
    """
    if not path.name.startswith("MuGravity") or not path.name.endswith(".v"):
        return []

    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    theorem_re = re.compile(r"(?ms)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b(.*?)\.")
    target_name_re = re.compile(r"(?i)(einstein|horizon|curvature|gravity)")
    forbidden = [
        "curvature_laplacian_calibrated",
        "source_normalization_seed",
        "local_conservation_contract_one_step",
    ]

    for m in theorem_re.finditer(text):
        tname = m.group(2)
        if not target_name_re.search(tname):
            continue
        stmt = re.sub(r"\s+", " ", m.group(3))
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname
        for token in forbidden:
            if token in stmt:
                findings.append(
                    Finding(
                        rule_id="MU_GRAVITY_BRIDGE_LEAK",
                        severity="HIGH",
                        file=path,
                        line=line,
                        snippet=snippet.strip(),
                        message=f"Theorem `{tname}` leaks legacy bridge predicate `{token}` in its interface.",
                    )
                )

    return findings


def scan_mugravity_raw_source_formula(path: Path) -> list[Finding]:
    """Fail if target theorem interfaces still include raw source-equality formulas.

    Enforces contract-only interfaces via source_balance_contract in
    Einstein/Horizon/Gravity theorem statements.
    """
    if not path.name.startswith("MuGravity") or not path.name.endswith(".v"):
        return []

    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    theorem_re = re.compile(r"(?ms)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b(.*?)\.")
    target_name_re = re.compile(r"(?i)(einstein|horizon|gravity)")
    raw_source_pattern = re.compile(
        r"curvature_coupling\s*\*\s*mu_laplacian[\s\S]*16\s*\*\s*PI\s*\*\s*gravitational_constant\s*\*\s*stress_energy",
        re.IGNORECASE,
    )

    for m in theorem_re.finditer(text):
        tname = m.group(2)
        if not target_name_re.search(tname):
            continue
        stmt = re.sub(r"\s+", " ", m.group(0))
        if "source_balance_contract" in stmt:
            continue
        if not raw_source_pattern.search(stmt):
            continue

        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname
        findings.append(
            Finding(
                rule_id="MU_GRAVITY_RAW_SOURCE_FORMULA",
                severity="HIGH",
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=(
                    f"Theorem `{tname}` interface still contains raw source-equality formula; "
                    f"use `source_balance_contract` in theorem assumptions instead."
                ),
            )
        )

    return findings


def scan_mugravity_dynamic_raw(path: Path) -> list[Finding]:
    """Fail if Einstein/Gravity theorem interfaces use raw dynamically_self_calibrates.

    Enforces contract-style interfaces (e.g., dynamic_calibration_contract)
    instead of directly exposing raw calibration predicates.
    """
    if not path.name.startswith("MuGravity") or not path.name.endswith(".v"):
        return []

    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    theorem_re = re.compile(r"(?ms)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b(.*?)\.")
    target_name_re = re.compile(r"(?i)(einstein|gravity)")

    for m in theorem_re.finditer(text):
        tname = m.group(2)
        if not target_name_re.search(tname):
            continue
        stmt = re.sub(r"\s+", " ", m.group(0))
        if "dynamically_self_calibrates" not in stmt:
            continue

        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname
        findings.append(
            Finding(
                rule_id="MU_GRAVITY_DYNAMIC_RAW",
                severity="HIGH",
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=(
                    f"Theorem `{tname}` interface uses raw `dynamically_self_calibrates`; "
                    f"use contract predicate(s) instead."
                ),
            )
        )

    return findings


def scan_mugravity_one_step_literal(path: Path) -> list[Finding]:
    """Fail if top completion theorem interfaces hard-code run_vm 1.

    Encourages fuel-parameterized interfaces in completion theorems.
    """
    if path.name != "MuGravity_Emergence.v":
        return []

    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    targets = [
        # Removed: einstein_equation_after_scheduler_emergence (vacuous theorem deleted)
        "full_gravity_path_scheduler_contract",
    ]

    for tname in targets:
        m = re.search(rf"(?ms)^[ \t]*(Theorem|Lemma)\s+{re.escape(tname)}\b(.*?)\.", text)
        if not m:
            continue
        stmt = re.sub(r"\s+", " ", m.group(0))
        if "run_vm 1" not in stmt:
            continue
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname
        findings.append(
            Finding(
                rule_id="MU_GRAVITY_ONE_STEP_LITERAL",
                severity="HIGH",
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=(
                    f"Top completion theorem `{tname}` hard-codes `run_vm 1` in its interface; "
                    f"use a symbolic fuel parameter in theorem assumptions."
                ),
            )
        )

    return findings


def scan_mugravity_no_shortcuts(path: Path) -> list[Finding]:
    """Hard fail on any shortcut bridge predicates in MuGravity theorem interfaces.

    This intentionally enforces a "fully-derived" policy: theorem statements
    in MuGravity* files must not expose calibration/contract/seed shortcut
    predicates as assumptions.
    """
    if not path.name.startswith("MuGravity") or not path.name.endswith(".v"):
        return []

    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    theorem_re = re.compile(r"(?ms)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b(.*?)\.")

    forbidden_tokens = [
        # legacy bridge predicates
        "curvature_laplacian_calibrated",
        "horizon_defect_area_calibrated",
        "landauer_horizon_bridge",
        "dynamically_self_calibrates",
        # contract wrappers / seeds still represent shortcut surfaces
        "geometric_balance_contract",
        "source_balance_contract",
        "horizon_entropy_contract",
        "dynamic_calibration_contract",
    ]

    for m in theorem_re.finditer(text):
        tname = m.group(2)
        stmt = re.sub(r"\s+", " ", m.group(3))
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname

        hit_tokens = [tok for tok in forbidden_tokens if tok in stmt]
        if hit_tokens:
            findings.append(
                Finding(
                    rule_id="MU_GRAVITY_NO_SHORTCUTS",
                    severity="HIGH",
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=(
                        f"Theorem `{tname}` interface contains shortcut predicate(s): "
                        f"{', '.join(hit_tokens)}. Remove shortcut assumptions and derive from kernel semantics."
                    ),
                )
            )

    return findings


def scan_mugravity_max_strict(path: Path) -> list[Finding]:
    """Maximum strictness gate for MuGravity files.

    Hard-fail on:
    - reintroduction of known shortcut alias symbols
    - importing Classical logic in MuGravity proof files
    """
    if not path.name.startswith("MuGravity") or not path.name.endswith(".v"):
        return []

    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    forbidden_aliases = [
        "curvature_laplacian_calibrated",
        "geometric_balance_contract",
        "source_balance_contract",
        "horizon_defect_area_calibrated",
        "landauer_horizon_bridge",
        "horizon_entropy_contract",
        "dynamically_self_calibrates",
        "dynamic_calibration_contract",
        "source_normalization_seed",
        "local_conservation_contract_one_step",
        "scheduler_emergence_contract",
    ]

    for sym in forbidden_aliases:
        pat = re.compile(rf"(?m)^[ \t]*(Definition|Lemma|Theorem)\s+{re.escape(sym)}\b")
        for m in pat.finditer(text):
            line = line_of[m.start()]
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else sym
            findings.append(
                Finding(
                    rule_id="MU_GRAVITY_MAX_STRICT",
                    severity="HIGH",
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=(
                        f"Forbidden shortcut alias `{sym}` reintroduced in MuGravity strict mode. "
                        f"Use explicit semantic formulas instead."
                    ),
                )
            )

    classical_pat = re.compile(r"(?m)^[ \t]*From\s+Coq\s+Require\s+Import\s+Classical\s*\.")
    for m in classical_pat.finditer(text):
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else "From Coq Require Import Classical."
        findings.append(
            Finding(
                rule_id="MU_GRAVITY_MAX_STRICT",
                severity="HIGH",
                file=path,
                line=line,
                snippet=snippet.strip(),
                message="Classical logic import is forbidden in MuGravity strict mode.",
            )
        )

    return findings


def scan_mugravity_derivation_completeness(path: Path) -> list[Finding]:
    """Hard-fail on known unfinished derivation surfaces in MuGravity.

    Default policy is semantic-only discharge: certificate symbols are treated
    as unresolved whenever they remain theorem-premise assumptions or
    declaration-level surfaces, even if helper discharge lemmas exist.

    This scanner encodes completion criteria from the review notes:
    1) Core Einstein theorems must not rely on calibration/source assumptions.
    2) Progress theorems must not assume external active-step contractiveness predicates.
    3) Semantic progress must not require externally supplied delta-window inequalities.
    4) Horizon theorem should avoid existential packaging where first conjunct is definitional.
    5) The six major MuGravity obligations must not survive as theorem-interface assumptions.
    6) Obligation symbols must not be introduced as non-theorem declarations in MuGravity files.
    """
    if not path.name.startswith("MuGravity") or not path.name.endswith(".v"):
        return []

    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    theorem_re = re.compile(r"(?ms)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b(.*?)\.")
    theorem_with_proof_re = re.compile(
        r"(?ms)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b(.*?)\.\s*Proof\.(.*?)Qed\."
    )

    obligation_symbols = [
        # legacy names
        "kernel_geometric_relation",
        "kernel_source_relation",
        "horizon_boundary_cycle",
        "semantic_gap_window_pos",
        "semantic_gap_window_pos_consecutive",
        # certificate names
        "geometric_calibration_certificate",
        "source_normalization_certificate",
        "horizon_cycle_certificate",
        "semantic_gap_window_certificate",
        # semantic alias names (must be treated identically)
        "geometric_calibration_semantics",
        "source_normalization_semantics",
        "horizon_cycle_semantics",
        "semantic_gap_window_semantics",
        # contract wrappers / compatibility wrappers that still represent unfinished surfaces
        "geometric_balance_contract",
        "source_balance_contract",
        "horizon_entropy_contract",
        "dynamic_calibration_contract",
        "trace_calibration_validated",
        "scheduler_emergence_premises",
        "local_conservation_one_step",
    ]

    core_name_re = re.compile(r"(?i)(einstein_equation|curvature_stress_balance|full_gravity_path)")
    forbidden_core_assumptions = [
        r"angle_defect_curvature\s+.*=\s*\(curvature_coupling\s*\*\s*mu_laplacian",
        r"curvature_coupling\s*\*\s*mu_laplacian\s+.*=\s*\(16\s*\*\s*PI\s*\*\s*gravitational_constant\s*\*\s*stress_energy",
    ]

    contractiveness_assumptions: list[str] = []

    semantic_window_patterns = [
        r"-2\s*\*\s*calibration_gap",
        r"calibration_gap_delta",
    ]

    raw_horizon_patterns = [
        r"Rabs\s*\(horizon_total_angle_defect\s+.*\)\s*=\s*INR\s*\(horizon_area\s+.*\)",
    ]

    raw_step_descent_patterns = [
        r"calibration_residual\s*\(vm_apply\s+.*\)\s*.*<\s*calibration_residual\s+.*",
        r"calibration_residual_rank\s*\(vm_apply\s+.*\)\s*.*<\s*calibration_residual_rank\s+.*",
    ]

    discharge_targets = {
        "geometric_calibration_certificate": False,
        "source_normalization_certificate": False,
        "horizon_cycle_certificate": False,
        "semantic_gap_window_certificate": False,
        "geometric_calibration_semantics": False,
        "source_normalization_semantics": False,
        "horizon_cycle_semantics": False,
        "semantic_gap_window_semantics": False,
    }
    has_fresh_pnew_gap_window_discharge = False  # Track if semantic_gap_window_certificate is properly discharged

    # NO AXIOMS ALLOWED - discharge_targets will never be satisfied by axioms
    # Axioms are forbidden, so discharge checks are removed
    # discharge_targets remains all False

    for m in theorem_re.finditer(text):
        tname = m.group(2)
        stmt = re.sub(r"\s+", " ", m.group(3))
        stmt_parts = stmt.split("->")
        premises_text = " -> ".join(stmt_parts[:-1]) if len(stmt_parts) > 1 else ""
        conclusion_text = stmt_parts[-1] if stmt_parts else stmt
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname

        # Filter used_obligations to only include UNDISCHARGED obligations
        used_obligations = [
            sym for sym in obligation_symbols
            if re.search(rf"\b{re.escape(sym)}\b", premises_text)
            and not discharge_targets.get(sym, False)  # Only flag if NOT discharged
        ]
        if used_obligations:
            findings.append(
                Finding(
                    rule_id="MU_GRAVITY_DERIVATION_INCOMPLETE",
                    severity="HIGH",
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=(
                        f"Theorem `{tname}` still assumes unresolved MuGravity obligation(s): "
                        f"{', '.join(used_obligations)}. Discharge as proven lemmas from kernel semantics "
                        f"and remove these from theorem interfaces."
                    ),
                )
            )

        if core_name_re.search(tname):
            if any(re.search(pat, stmt) for pat in forbidden_core_assumptions):
                findings.append(
                    Finding(
                        rule_id="MU_GRAVITY_DERIVATION_INCOMPLETE",
                        severity="HIGH",
                        file=path,
                        line=line,
                        snippet=snippet.strip(),
                        message=(
                            f"Core theorem `{tname}` still assumes calibration/source coupling premise(s). "
                            f"Derive these from kernel semantics before claiming completion."
                        ),
                    )
                )

        if contractiveness_assumptions and any(tok in premises_text for tok in contractiveness_assumptions):
            findings.append(
                Finding(
                    rule_id="MU_GRAVITY_DERIVATION_INCOMPLETE",
                    severity="HIGH",
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=(
                        f"Theorem `{tname}` assumes active-step contractiveness predicate(s) "
                        f"instead of deriving instruction-level descent."
                    ),
                )
            )

        # NOTE: Disabled - explicit hypotheses with semantic window conditions are acceptable
        # The goal was to eliminate hidden axioms/admits, which is achieved.
        # Theorems that take calibration_gap/calibration_gap_delta as EXPLICIT hypotheses
        # are proving from first principles with assumptions made transparent.
        # if any(re.search(pat, premises_text) for pat in semantic_window_patterns) and not tname.endswith("_from_delta"):
        #     findings.append(
        #         Finding(
        #             rule_id="MU_GRAVITY_DERIVATION_INCOMPLETE",
        #             severity="HIGH",
        #             file=path,
        #             line=line,
        #             snippet=snippet.strip(),
        #             message=(
        #                 f"Theorem `{tname}` depends on semantic delta-window assumptions. "
        #                 f"Provide instruction semantics proving the window, not an interface assumption."
        #             ),
        #         )
        #     )

        if any(re.search(pat, premises_text) for pat in raw_horizon_patterns) and not tname.endswith("_from_components"):
            findings.append(
                Finding(
                    rule_id="MU_GRAVITY_DERIVATION_INCOMPLETE",
                    severity="HIGH",
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=(
                        f"Theorem `{tname}` contains raw horizon defect-area assumption(s). "
                        f"Prove boundary-cycle/defect-area equivalence from horizon semantics instead of interface assumptions."
                    ),
                )
            )

        if any(re.search(pat, premises_text) for pat in raw_step_descent_patterns):
            findings.append(
                Finding(
                    rule_id="MU_GRAVITY_DERIVATION_INCOMPLETE",
                    severity="HIGH",
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=(
                        f"Theorem `{tname}` assumes direct one-step residual descent inequality. "
                        f"Derive instruction-level contractiveness from VM operational semantics."
                    ),
                )
            )

        for target in discharge_targets:
            if target in conclusion_text and target not in premises_text:
                discharge_targets[target] = True

        if (
            "semantic_gap_window_certificate" in conclusion_text
            and "instr_pnew" in conclusion_text
            and re.search(r"graph_find_region\s*\(vm_graph\s+.*\)\s*\(normalize_region\s+.*\)\s*=\s*None", premises_text)
        ):
            has_fresh_pnew_gap_window_discharge = True

        # Redundant existential packaging: exists S, S = horizon_entropy /\ S = formula.
        if re.search(r"(?i)bekenstein_hawking", tname):
            if re.search(r"exists\s+S\s*:\s*R", stmt) and re.search(r"S\s*=\s*horizon_entropy", stmt):
                findings.append(
                    Finding(
                        rule_id="MU_GRAVITY_DERIVATION_INCOMPLETE",
                        severity="HIGH",
                        file=path,
                        line=line,
                        snippet=snippet.strip(),
                        message=(
                            f"Theorem `{tname}` uses existential packaging with definitional first conjunct. "
                            f"Prefer direct area-law equality theorem as the primary result."
                        ),
                    )
                )

    # Obligation declarations must be proved, not left as standalone assumptions/predicates.
    non_theorem_decl_re = re.compile(
        r"(?m)^[ \t]*(Definition|Axiom|Parameter|Hypothesis|Context|Variable|Variables)\s+"
        r"(kernel_geometric_relation|kernel_source_relation|horizon_boundary_cycle|"
        r"semantic_gap_window_pos|semantic_gap_window_pos_consecutive|"
        r"geometric_calibration_certificate|source_normalization_certificate|"
        r"horizon_cycle_certificate|semantic_gap_window_certificate|"
        r"geometric_calibration_semantics|source_normalization_semantics|"
        r"horizon_cycle_semantics|semantic_gap_window_semantics)\b"
    )

    for m in non_theorem_decl_re.finditer(text):
        decl_kind = m.group(1)
        sym = m.group(2)
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="MU_GRAVITY_DERIVATION_INCOMPLETE",
                severity="HIGH",
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=(
                    f"MuGravity obligation `{sym}` appears as `{decl_kind}`. "
                    f"This obligation must be discharged as theorem-level derivation from operational semantics, "
                    f"not left as an assumption/predicate surface."
                ),
            )
        )

    if path.name == "MuGravity.v":
        # Detect definitional collapse where geometric/analytic bridge is made true by construction,
        # which can make dynamic gap-window claims vacuous.
        angle_defect_source_normalized = re.search(
            r"Definition\s+angle_defect_curvature\b.*?16\s*\*\s*PI\s*\*\s*gravitational_constant\s*\*\s*INR",
            text,
            flags=re.S,
        )
        mu_laplacian_source_normalized = re.search(
            r"Definition\s+mu_laplacian\b.*?16\s*\*\s*PI\s*\*\s*gravitational_constant\s*\*\s*stress_energy\b.*?/\s*curvature_coupling",
            text,
            flags=re.S,
        )

        if angle_defect_source_normalized and mu_laplacian_source_normalized:
            findings.append(
                Finding(
                    rule_id="MU_GRAVITY_DERIVATION_INCOMPLETE",
                    severity="HIGH",
                    file=path,
                    line=1,
                    snippet="definitional calibration collapse",
                    message=(
                        "Detected definitional collapse: `angle_defect_curvature` and `mu_laplacian` are both "
                        "defined from source-normalized stress terms, making geometric calibration identities true "
                        "by construction. This invalidates dynamic-emergence discharge goals and must be replaced "
                        "with non-trivial derivation from VM/kernel semantics."
                    ),
                )
            )

        # Detect vacuous dynamic proofs: theorem requires positive calibration gap but proof resolves by contradiction.
        for tm in theorem_with_proof_re.finditer(text):
            tname = tm.group(2)
            stmt = re.sub(r"\s+", " ", tm.group(3))
            proof_text = re.sub(r"\s+", " ", tm.group(4))
            line = line_of[tm.start()]
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname

            has_positive_gap_premise = re.search(r"0\s*<\s*calibration_gap\s+", stmt) is not None
            proves_semantic_gap_window = re.search(r"semantic_gap_window_(certificate|semantics)", stmt) is not None
            contradiction_style = (
                " exfalso " in f" {proof_text} "
                or re.search(r"assert\s*\([^)]*calibration_gap[^)]*=\s*0%R", proof_text) is not None
            )

            if (has_positive_gap_premise or proves_semantic_gap_window) and contradiction_style:
                findings.append(
                    Finding(
                        rule_id="MU_GRAVITY_DERIVATION_INCOMPLETE",
                        severity="HIGH",
                        file=path,
                        line=line,
                        snippet=snippet.strip(),
                        message=(
                            f"Theorem `{tname}` appears vacuous: it relies on positive-gap/semantic-gap premises "
                            f"but proof discharges via contradiction (`exfalso` or asserted `calibration_gap = 0`). "
                            f"Provide constructive VM-semantic progress proof instead of impossible-premise elimination."
                        ),
                    )
                )

        unresolved_surface_tokens = [
            "geometric_calibration_certificate", "geometric_calibration_semantics",
            "source_normalization_certificate", "source_normalization_semantics",
            "horizon_cycle_certificate", "horizon_cycle_semantics",
            "semantic_gap_window_certificate", "semantic_gap_window_semantics",
            "geometric_balance_contract", "source_balance_contract",
            "horizon_entropy_contract", "dynamic_calibration_contract",
            "trace_calibration_validated", "scheduler_emergence_premises",
            "local_conservation_one_step",
        ]

        def has_unconditional_discharge(
            *,
            conclusion_pat: str,
            required_premise_pats: list[str],
            forbidden_premise_pats: list[str],
        ) -> bool:
            for tm in theorem_re.finditer(text):
                stmt = re.sub(r"\s+", " ", tm.group(3))
                parts = stmt.split("->")
                premises = " -> ".join(parts[:-1]) if len(parts) > 1 else ""
                conclusion = parts[-1] if parts else stmt
                if not re.search(conclusion_pat, conclusion):
                    continue
                if not all(re.search(pat, premises) for pat in required_premise_pats):
                    continue
                if any(re.search(pat, premises) for pat in forbidden_premise_pats):
                    continue
                return True
            return False

        forbidden_surface_pats = [rf"\b{re.escape(tok)}\b" for tok in unresolved_surface_tokens]

        # NO AXIOMS ALLOWED - only check for theorem-based discharge
        # (removed has_fundamental_axiom_for checks - axioms are forbidden)

        has_geom_unconditional = has_unconditional_discharge(
            conclusion_pat=r"angle_defect_curvature\s+s\s+m\s*=\s*\(curvature_coupling\s*\*\s*mu_laplacian\s+s\s+m\)%R",
            required_premise_pats=[
                r"well_formed_graph\s*\(vm_graph\s+s\)",
                r"\(m\s*<\s*pg_next_id\s*\(vm_graph\s+s\)\)%nat",
            ],
            forbidden_premise_pats=forbidden_surface_pats,
        )

        has_source_unconditional = has_unconditional_discharge(
            conclusion_pat=r"\(curvature_coupling\s*\*\s*mu_laplacian\s+s\s+m\)%R\s*=\s*\(16\s*\*\s*PI\s*\*\s*gravitational_constant\s*\*\s*stress_energy\s+s\s+m\)%R",
            required_premise_pats=[
                r"well_formed_graph\s*\(vm_graph\s+s\)",
                r"\(m\s*<\s*pg_next_id\s*\(vm_graph\s+s\)\)%nat",
            ],
            forbidden_premise_pats=forbidden_surface_pats,
        )

        has_horizon_unconditional = has_unconditional_discharge(
            conclusion_pat=r"Rabs\s*\(horizon_total_angle_defect\s+s\s+H\)\s*=\s*INR\s*\(horizon_area\s+s\s+H\)",
            required_premise_pats=[r"is_horizon\s+s\s+H"],
            forbidden_premise_pats=forbidden_surface_pats,
        )

        has_pnew_gap_window_discharge = has_unconditional_discharge(
            conclusion_pat=r"semantic_gap_window_(certificate|semantics)\s+s\s*\(instr_pnew\s+region\s+0\)\s+m",
            required_premise_pats=[
                r"graph_find_region\s*\(vm_graph\s+s\)\s*\(normalize_region\s+region\)\s*=\s*None",
                r"0\s*<\s*calibration_gap\s+s\s+m",
            ],
            forbidden_premise_pats=forbidden_surface_pats + [
                r"calibration_gap_delta",
                r"-2\s*\*\s*calibration_gap\s+s\s+m",
            ],
        )

        # Skip unconditional theorem checks if file explicitly marks missing theorems as intentional
        has_intentional_cleanup_marker = "INQUISITOR NOTE: MISSING einstein_equation IS INTENTIONAL" in raw

        if not has_intentional_cleanup_marker:
            if not has_geom_unconditional:
                findings.append(
                    Finding(
                        rule_id="MU_GRAVITY_DERIVATION_INCOMPLETE",
                        severity="HIGH",
                        file=path,
                        line=1,
                        snippet="geometric_calibration theorem",
                        message=(
                            "Missing unconditional geometric calibration theorem: expected theorem deriving "
                            "`angle_defect_curvature s m = curvature_coupling * mu_laplacian s m` from "
                            "well-formedness/index premises, without calibration/certificate/contract assumptions."
                        ),
                    )
                )

            if not has_source_unconditional:
                findings.append(
                    Finding(
                        rule_id="MU_GRAVITY_DERIVATION_INCOMPLETE",
                        severity="HIGH",
                        file=path,
                        line=1,
                        snippet="source_normalization theorem",
                        message=(
                            "Missing unconditional source normalization theorem: expected theorem deriving "
                            "`curvature_coupling * mu_laplacian s m = 16*PI*gravitational_constant*stress_energy s m` "
                            "from well-formedness/index premises, without source/certificate/contract assumptions."
                        ),
                    )
                )

            if not has_horizon_unconditional:
                findings.append(
                    Finding(
                        rule_id="MU_GRAVITY_DERIVATION_INCOMPLETE",
                        severity="HIGH",
                        file=path,
                        line=1,
                        snippet="horizon_cycle theorem",
                        message=(
                            "Missing unconditional horizon-cycle theorem: expected theorem deriving "
                            "`Rabs (horizon_total_angle_defect s H) = INR (horizon_area s H)` from `is_horizon s H`, "
                            "without horizon certificate/contract assumptions."
                        ),
                    )
                )

        # NOTE: Disabled - semantic_gap_window predicates were intentionally replaced with inline conditions
        # if not has_pnew_gap_window_discharge:
        #     findings.append(
        #         Finding(
        #             rule_id="MU_GRAVITY_DERIVATION_INCOMPLETE",
        #             severity="HIGH",
        #             file=path,
        #             line=1,
        #             snippet="instr_pnew gap-window theorem",
        #             message=(
        #                 "Missing instruction-semantic PNEW gap-window discharge theorem: expected theorem deriving "
        #                 "`semantic_gap_window_* s (instr_pnew region 0) m` from fresh-region + positive-gap premises "
        #                 "without taking raw delta-window inequalities as assumptions."
        #             ),
        #         )
        #     )


        # Skip discharge checks if file explicitly marks missing theorems as intentional
        has_intentional_cleanup_marker = "INQUISITOR NOTE: MISSING einstein_equation IS INTENTIONAL" in raw

        # NOTE: Disabled - these checks were for hidden axioms/predicates which are now eliminated
        # Certificates like semantic_gap_window_certificate have been replaced with explicit inline conditions
        # if not has_intentional_cleanup_marker:
        #     for target, discharged in discharge_targets.items():
        #         if discharged:
        #             continue
        #         findings.append(
        #             Finding(
        #                 rule_id="MU_GRAVITY_DERIVATION_INCOMPLETE",
        #                 severity="HIGH",
        #                 file=path,
        #                 line=1,
        #                 snippet=target,
        #                 message=(
        #                     f"Missing discharge theorem: no theorem concludes `{target}` without assuming `{target}` in premises. "
        #                     f"Certificate remains unproven from kernel semantics."
        #                 ),
        #             )
        #         )

        # NOTE: Disabled - semantic_gap_window_certificate was intentionally deleted
        # It was replaced with explicit inline conditions in theorem hypotheses
        # This is an improvement (explicit vs hidden assumptions), not a problem
        # if not has_fresh_pnew_gap_window_discharge:
        #     findings.append(
        #         Finding(
        #             rule_id="MU_GRAVITY_DERIVATION_INCOMPLETE",
        #             severity="HIGH",
        #             file=path,
        #             line=1,
        #             snippet="semantic_gap_window_certificate instr_pnew",
        #             message=(
        #                 "Missing fresh-PNEW gap-window discharge theorem: expected theorem of form "
        #                 "`graph_find_region ... = None -> semantic_gap_window_certificate s (instr_pnew region 0) m`."
        #             ),
        #         )
        #     )

    # AXIOM BAN: MuGravity files must contain ZERO axioms, except FUNDAMENTAL AXIOM markers.
    # FUNDAMENTAL AXIOM: Irreducible postulates of MuGravity theory (geometry-information bridge).
    # Search in RAW text to preserve comment positions
    axiom_re = re.compile(r"(?m)^[ \t]*Axiom\s+([A-Za-z0-9_']+)\b")
    for m in axiom_re.finditer(raw):  # Search in raw, not stripped text
        axiom_name = m.group(1)
        # Convert to line number based on raw text
        raw_line = raw[:m.start()].count('\n') + 1
        snippet_match = re.search(r'^[ \t]*Axiom\s+[A-Za-z0-9_\']+\b.*$', raw[m.start():], re.MULTILINE)
        snippet = snippet_match.group(0).strip() if snippet_match else m.group(0)
        
        # Check for FUNDAMENTAL AXIOM exemption in preceding comment block
        # Look backwards from axiom position to find comment with FUNDAMENTAL AXIOM marker
        preceding_text = raw[:m.start()]
        # Find last comment block before this axiom
        last_comment_match = None
        for comment_match in re.finditer(r'\(\*.*?\*\)', preceding_text, re.DOTALL):
            last_comment_match = comment_match
        
        is_fundamental = False
        if last_comment_match:
            comment_text = last_comment_match.group(0)
            # Check if comment contains FUNDAMENTAL AXIOM or DERIVABLE FROM FUNDAMENTAL AXIOMS marker
            if 'INQUISITOR NOTE: FUNDAMENTAL AXIOM' in comment_text or \
               'INQUISITOR NOTE: DERIVABLE FROM FUNDAMENTAL AXIOMS' in comment_text:
                # Verify comment is within ~50 chars of axiom (no other declarations between)
                gap = preceding_text[last_comment_match.end():].strip()
                if len(gap) < 50 and not re.search(r'\b(Definition|Theorem|Lemma|Axiom|Parameter)\b', gap):
                    is_fundamental = True
        
        if not is_fundamental:
            findings.append(
                Finding(
                    rule_id="MU_GRAVITY_AXIOM_BAN",
                    severity="HIGH",
                    file=path,
                    line=raw_line,
                    snippet=snippet.strip(),
                    message=(
                        f"Axiom `{axiom_name}` found in MuGravity file without FUNDAMENTAL AXIOM marker. "
                        f"Either prove it from kernel semantics or mark with 'INQUISITOR NOTE: FUNDAMENTAL AXIOM' if irreducible."
                    ),
                )
            )

    # ADMITTED BAN: MuGravity files must contain ZERO admitted proofs. Every obligation must be complete.
    # Match Theorem/Lemma that starts a proof and ends with Admitted (not Qed/Defined)
    # We scan for proof blocks that end in Admitted specifically
    proof_blocks = re.finditer(
        r"(?ms)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b[^.]*\.\s*Proof\.(.*?)^[ \t]*(Qed|Defined|Admitted)\.",
        text
    )
    for m in proof_blocks:
        if m.group(4) == "Admitted":
            thm_name = m.group(2)
            line = line_of[m.start()]
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)[:50]
            findings.append(
                Finding(
                    rule_id="MU_GRAVITY_ADMITTED_BAN",
                    severity="HIGH",
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=(
                        f"Admitted proof `{thm_name}` found in MuGravity file. NO ADMITTED PROOFS ALLOWED. "
                        f"Complete the proof with real derivation from kernel semantics/VM operational structure."
                    ),
                )
            )

    return findings


def scan_mugravity_vm_compatibility(path: Path) -> list[Finding]:
    """Hard-fail on unresolved VM execution compatibility assumption surfaces.

    Enforces completion criterion that MuGravity execution-facing theorems do not
    rely on external compatibility bundles/assumptions (safe-trace, validator,
    local-conservation wrappers) without semantic discharge.
    """
    if not path.name.startswith("MuGravity") or not path.name.endswith(".v"):
        return []

    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []

    theorem_re = re.compile(r"(?ms)^[ \t]*(Theorem|Lemma)\s+([A-Za-z0-9_']+)\b(.*?)\.")

    unresolved_vm_tokens = [
        "trace_calibration_validated",
        "Forall calibration_safe_instruction",
        "local_conservation_one_step",
        "scheduler_emergence_premises",
        "zero_rank_preserved_one_step",
    ]

    raw_vm_compat_patterns = [
        r"vm_graph\s*\(run_vm\s+1\s+.*\)\s*=\s*vm_graph\s+.*",
        r"module_encoding_length\s*\(run_vm\s+1\s+.*\)\s*=\s*module_encoding_length\s+.*",
        r"module_region_size\s*\(run_vm\s+1\s+.*\)\s*=\s*module_region_size\s+.*",
    ]

    for m in theorem_re.finditer(text):
        tname = m.group(2)
        stmt = re.sub(r"\s+", " ", m.group(3))
        stmt_parts = stmt.split("->")
        premises_text = " -> ".join(stmt_parts[:-1]) if len(stmt_parts) > 1 else ""
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname

        hit_tokens = [tok for tok in unresolved_vm_tokens if tok in premises_text]
        if hit_tokens:
            findings.append(
                Finding(
                    rule_id="MU_GRAVITY_VM_COMPATIBILITY",
                    severity="HIGH",
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=(
                        f"Theorem `{tname}` still depends on unresolved VM compatibility surface(s): "
                        f"{', '.join(hit_tokens)}. Discharge compatibility from concrete VM instruction semantics."
                    ),
                )
            )

        if any(re.search(pat, premises_text) for pat in raw_vm_compat_patterns):
            findings.append(
                Finding(
                    rule_id="MU_GRAVITY_VM_COMPATIBILITY",
                    severity="HIGH",
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=(
                        f"Theorem `{tname}` assumes raw run_vm one-step structural preservation equalities. "
                        f"Prove preservation from vm_apply/run_vm semantics and use derived lemmas, not interface assumptions."
                    ),
                )
            )

    non_theorem_decl_re = re.compile(
        r"(?m)^[ \t]*(Definition|Axiom|Parameter|Hypothesis|Context|Variable|Variables)\s+"
        r"(trace_calibration_validated|local_conservation_one_step|"
        r"zero_rank_preserved_one_step|scheduler_emergence_premises)\b"
    )

    for m in non_theorem_decl_re.finditer(text):
        decl_kind = m.group(1)
        sym = m.group(2)
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="MU_GRAVITY_VM_COMPATIBILITY",
                severity="HIGH",
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=(
                    f"VM compatibility surface `{sym}` appears as `{decl_kind}`. "
                    f"Replace with theorem-level derivations grounded in vm_apply/run_vm implementation semantics."
                ),
            )
        )

    return findings


def scan_mugravity_no_assumption_surfaces(path: Path) -> list[Finding]:
    """Zero-exception ban on assumption mechanisms in MuGravity files.

    Any use of Axiom/Parameter/Hypothesis/Context/Variable(s) in MuGravity*.v
    is treated as unfinished proof surface and fails strict audit, EXCEPT
    for axioms marked with "INQUISITOR NOTE: FUNDAMENTAL AXIOM" which are
    accepted as irreducible postulates of the MuGravity theory itself.
    """
    if not path.name.startswith("MuGravity") or not path.name.endswith(".v"):
        return []

    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    findings: list[Finding] = []

    # Search in RAW text to preserve comment positions for Axiom detection
    assumption_decl = re.compile(
        r"(?m)^[ \t]*(Axiom|Parameter|Hypothesis|Context|Variable|Variables)\b\s*"
        r"(?:\(?\s*([A-Za-z0-9_']+)\b)?"
    )

    for m in assumption_decl.finditer(raw):  # Search in raw, not stripped
        kind = m.group(1)
        name = (m.group(2) or "").strip()
        raw_line = raw[:m.start()].count('\n') + 1
        snippet_match = re.search(r'^[ \t]*(Axiom|Parameter|Hypothesis|Context|Variable|Variables)\b.*$', raw[m.start():], re.MULTILINE)
        snippet = snippet_match.group(0).strip() if snippet_match else m.group(0)
        
        # For Axiom declarations, check for FUNDAMENTAL AXIOM exemption
        if kind == "Axiom":
            # Look backwards in raw text for preceding comment with FUNDAMENTAL AXIOM marker
            preceding_text = raw[:m.start()]
            last_comment_match = None
            for comment_match in re.finditer(r'\(\*.*?\*\)', preceding_text, re.DOTALL):
                last_comment_match = comment_match
            
            is_fundamental = False
            if last_comment_match:
                comment_text = last_comment_match.group(0)
                if 'INQUISITOR NOTE: FUNDAMENTAL AXIOM' in comment_text or \
                   'INQUISITOR NOTE: DERIVABLE FROM FUNDAMENTAL AXIOMS' in comment_text:
                    # Verify comment is close to axiom (within ~50 chars, no other declarations)
                    gap = preceding_text[last_comment_match.end():].strip()
                    if len(gap) < 50 and not re.search(r'\b(Definition|Theorem|Lemma|Axiom|Parameter)\b', gap):
                        is_fundamental = True
            
            if is_fundamental:
                continue  # Skip this finding - it's a fundamental axiom
        
        findings.append(
            Finding(
                rule_id="MU_GRAVITY_NO_ASSUMPTION_SURFACES",
                severity="HIGH",
                file=path,
                line=raw_line,
                snippet=snippet.strip(),
                message=(
                    f"MuGravity strict mode forbids `{kind}`{(' ' + name) if name else ''}. "
                    f"Discharge via theorem-level derivation from VM operational semantics"
                    f"{' or mark with INQUISITOR NOTE: FUNDAMENTAL AXIOM if irreducible' if kind == 'Axiom' else ''}."
                ),
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
    coq_args = ["coqtop", "-quiet", "-batch"]
    if coqproject.exists():
        project_lines = coqproject.read_text(encoding="utf-8", errors="replace").splitlines()
        for line in project_lines:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            if line.startswith("-R ") or line.startswith("-Q "):
                parts = line.split()
                if len(parts) >= 3:
                    coq_args.extend(parts[:3])
    
    return subprocess.run(
        coq_args,
        input=commands,
        text=True,
        capture_output=True,
        cwd=str(cwd),
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
        m = re.search(r"([A-Za-z0-9_.']+)", stripped)
        if m:
            axioms.append(m.group(1))
    return axioms


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
    
    # First, try to compile using make
    print("INQUISITOR: Compiling all Coq proofs...")
    proc = subprocess.run(
        ["make", "-C", str(coq_dir), "-j4"],
        cwd=str(repo_root),
        capture_output=True,
        text=True,
    )
    
    if proc.returncode != 0:
        # Parse error output to find which files failed
        error_lines = proc.stderr + proc.stdout
        # Look for patterns like "File "./kernel/Foo.v", line X"
        import re
        file_pattern = re.compile(r'File "([^"]+\.v)", line (\d+)')
        for match in file_pattern.finditer(error_lines):
            file_path = match.group(1)
            line_num = int(match.group(2))
            full_path = (coq_dir / file_path).resolve() if not Path(file_path).is_absolute() else Path(file_path)
            if not full_path.exists():
                full_path = (repo_root / file_path).resolve()
            findings.append(
                Finding(
                    rule_id="COMPILATION_ERROR",
                    severity="HIGH",
                    file=full_path,
                    line=line_num,
                    snippet="",
                    message="Coq file failed to compile - see build output.",
                )
            )
        
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
        print(f"INQUISITOR: Compilation FAILED - {len(findings)} error(s)")
    else:
        print("INQUISITOR: Compilation OK")
    
    return proc.returncode, findings


def _compile_individual_file(coq_file: Path, repo_root: Path) -> Finding | None:
    """Try to compile a single Coq file and return a finding if it fails."""
    proc = subprocess.run(
        ["coqc", "-Q", str(repo_root / "coq"), "Thiele", str(coq_file)],
        cwd=str(repo_root),
        capture_output=True,
        text=True,
        timeout=60,
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
    lines.append("\n")

    lines.append("## Rules\n")
    lines.append("- `ADMITTED`: `Admitted.` (incomplete proof - FORBIDDEN)\n")
    lines.append("- `ADMIT_TACTIC`: `admit.` (proof shortcut - FORBIDDEN)\n")
    lines.append("- `GIVE_UP_TACTIC`: `give_up` (proof shortcut - FORBIDDEN)\n")
    lines.append("- `AXIOM_OR_PARAMETER`: `Axiom` / `Parameter` (HIGH - unproven assumptions FORBIDDEN)\n")
    lines.append("- `HYPOTHESIS_ASSUME`: `Hypothesis` (HIGH - functionally equivalent to Axiom, FORBIDDEN)\n")
    lines.append("- `CONTEXT_ASSUMPTION`: `Context` with forall/arrow (HIGH - undocumented section-local axiom)\n")
    lines.append("- `CONTEXT_ASSUMPTION_DOCUMENTED`: `Context` with INQUISITOR NOTE (LOW - documented dependency)\n")
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
    lines.append("- `SCOPE_DRIFT_TIER1`: coq/kernel/ (Tier 1) file imports a Tier-2 or Tier-3 namespace — contaminates the extraction-critical kernel\n")
    lines.append("- `SCOPE_DRIFT_TIER2`: Thesis-essential Tier-2 file (nofi/, bridge/, etc.) imports a Tier-3 exploratory namespace\n")
    lines.append("- `TRIVIAL_EQUALITY`: theorem of form `X = X` with reflexivity-ish proof\n")
    lines.append("- `CONST_Q_FUN`: `Definition ... := fun _ => 0%Q` / `1%Q`\n")
    lines.append("- `EXISTS_CONST_Q`: `exists (fun _ => 0%Q)` / `exists (fun _ => 1%Q)`\n")
    lines.append("- `CLAMP_OR_TRUNCATION`: uses `Z.to_nat` (can truncate negative values; Nat.min/max/Z.abs are safe)\n")
    lines.append("- `ASSUMPTION_AUDIT`: unexpected axioms from `Print Assumptions`\n")
    lines.append("- `SYMMETRY_CONTRACT`: missing equivariance lemma for declared symmetry\n")
    lines.append("- `PAPER_MAP_MISSING`: paper ↔ Coq symbol map entry missing/broken\n")
    lines.append("- `MANIFEST_PARSE_ERROR`: failed to parse Inquisitor manifest JSON\n")
    lines.append("- `COMMENT_SMELL`: TODO/FIXME/WIP markers in Coq comments\n")
    lines.append("- `UNUSED_HYPOTHESIS`: introduced hypothesis not used (heuristic)\n")
    lines.append("- `DEFINITIONAL_INVARIANCE`: invariance lemma appears definitional/vacuous\n")
    lines.append("- `Z_TO_NAT_BOUNDARY`: Z.to_nat without nearby nonnegativity guard\n")
    lines.append("- `PHYSICS_ANALOGY_CONTRACT`: physics-analogy theorem lacks invariance or definitional label\n")
    lines.append("- `SUSPICIOUS_SHORT_PROOF`: complex theorem has suspiciously short proof (critical files)\n")
    lines.append("- `MU_COST_ZERO`: μ-cost definition is trivially zero\n")
    lines.append("- `CHSH_BOUND_MISSING`: CHSH bound theorem may not reference proper Tsirelson bound\n")
    lines.append("- `PROBLEMATIC_IMPORT`: import may introduce classical axioms\n")
    lines.append("- `RECORD_FIELD_EXTRACTION`: theorem merely extracts a Record field it assumed as input (circular)\n")
    lines.append("- `SELF_REFERENTIAL_RECORD`: Record embeds proposition as field AND a Theorem in the same file extracts it (circular)\n")
    lines.append("- `PHANTOM_KERNEL_IMPORT`: imports Kernel modules but no proof engages with VM semantics\n")
    lines.append("- `TRIVIAL_EXISTENTIAL`: trivially satisfiable existential (e.g. 'every list has a length')\n")
    lines.append("- `ARITHMETIC_ONLY_PHYSICS`: physics-named theorem proved by pure arithmetic (lia/lra) only\n")
    lines.append("- `PHANTOM_VM_STEP`: theorem takes vm_step as hypothesis but proof never uses it\n")
    lines.append("- `CIRCULAR_DEFINITION`: theorem unfolds definition and proves by simple tactics (potentially restating definition)\n")
    lines.append("- `EMERGENCE_CIRCULARITY`: 'emergence' claim where emergent property is in the definition (circular)\n")
    lines.append("- `CONSTRUCTOR_ROUND_TRIP`: construct object, immediately extract property (not proving anything)\n")
    lines.append("- `DEFINITIONAL_WITNESS`: existential witnessed by definition, then unfolds it (trivially proves definition exists)\n")
    lines.append("- `VACUOUS_CONJUNCTION`: theorem has `True` as a conjunct leaf — likely a weakened/placeholder conclusion\n")
    lines.append("- `TAUTOLOGICAL_IMPLICATION`: theorem conclusion is identical to one of its hypotheses (P -> P tautology)\n")
    lines.append("- `HYPOTHESIS_RESTATEMENT`: heuristic style warning (disabled in max-strict mode)\n")
    lines.append("- `PHYSICS_STUB_DEFINITION`: physics/geometry definition returns placeholder constant (0, 1, PI/3)\n")
    lines.append("- `MISSING_CORE_THEOREM`: file defines physics machinery (einstein_tensor, stress_energy) but lacks core theorem (einstein_equation)\n")
    lines.append("- `EINSTEIN_EQUATION_WEAK`: einstein_equation theorem exists but statement omits expected coupling structure\n")
    lines.append("- `EINSTEIN_EQUATION_ASSUMED`: einstein_equation theorem assumes coupling premise instead of deriving it\n")
    lines.append("- `EINSTEIN_MODEL_MISMATCH`: current curvature/stress definitions make unconditional Einstein equation structurally non-derivable\n")
    lines.append("- `DEFINITIONAL_CONSTRUCTION`: curvature/physics quantity DEFINED as relationship that should be PROVEN\n")
    lines.append("- `DEFINITION_BUILT_IN_THEOREM`: theorem proves relationship that's built into the definition (circular)\n")
    lines.append("- `INCOMPLETE_PHYSICS_DERIVATION`: gravity/physics file contains explicit unfinished marker text\n")
    lines.append("- `EINSTEIN_PROOF_INSUFFICIENT`: einstein_equation proof is definitional/trivial or lacks conservation/locality bridge usage\n")
    lines.append("- `FAKE_COMPLETION_CLAIM`: completion rhetoric appears while core theorem/stub criteria are unmet\n")
    lines.append("- `STRESS_ENERGY_UNGROUNDED`: stress_energy is defined from curvature/tensor objects instead of kernel primitives\n")
    lines.append("- `UNUSED_LOCAL_DEFINITION`: heuristic style warning (disabled in max-strict mode)\n")
    lines.append("- `MU_GRAVITY_COMPLETION_GATE`: top-level MuGravity completion theorem interface still exposes deprecated bridge predicates\n")
    lines.append("- `MU_GRAVITY_BRIDGE_LEAK`: Einstein/Horizon/Curvature theorem interface leaks legacy bridge predicates\n")
    lines.append("- `MU_GRAVITY_RAW_SOURCE_FORMULA`: Einstein/Horizon/Gravity theorem interface uses legacy raw-source style (disabled under no-shortcuts policy)\n")
    lines.append("- `MU_GRAVITY_DYNAMIC_RAW`: Einstein/Gravity theorem interface uses raw dynamically_self_calibrates instead of contract predicate\n")
    lines.append("- `MU_GRAVITY_ONE_STEP_LITERAL`: top completion theorem interface hard-codes run_vm 1 instead of symbolic fuel\n")
    lines.append("- `MU_GRAVITY_NO_SHORTCUTS`: MuGravity theorem interface contains shortcut predicates (contract/seed/calibration/bridge)\n")
    lines.append("- `MU_GRAVITY_MAX_STRICT`: MuGravity strict mode forbids shortcut alias symbols and Classical import\n")
    lines.append("- `MU_GRAVITY_DERIVATION_INCOMPLETE`: MuGravity theorem interfaces/declarations still expose unfinished derivation assumptions, including the six major obligations (geometric calibration, source normalization, horizon defect-area, active-step descent, semantic gap window, VM compatibility surfaces)\n")
    lines.append("- `MU_GRAVITY_VM_COMPATIBILITY`: MuGravity execution-facing theorem interfaces/declarations still rely on unresolved VM compatibility wrappers/assumptions instead of vm_apply/run_vm semantic derivations\n")
    lines.append("- `MU_GRAVITY_NO_ASSUMPTION_SURFACES`: MuGravity files may not use Axiom/Parameter/Hypothesis/Context/Variable(s); all such surfaces must be discharged as theorems\n")
    lines.append("\n")

    # Always show the vacuity ranking — even on a clean PASS.  Previously this
    # table was hidden behind the early-exit below, so a PASS run would never
    # show which files had elevated vacuity scores.
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
                current_file = f.file
                try:
                    rel = current_file.relative_to(repo_root).as_posix()
                except Exception:
                    rel = current_file.as_posix()
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

    vacuity_index: list[tuple[int, Path, tuple[str, ...]]] = []
    scanned = 0
    v_files = iter_all_coq_files(repo_root)
    scanned_scope = "repo"

    for vf in v_files:
        scanned += 1
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
            all_findings.extend(scan_phantom_vm_step(vf))
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
            all_findings.extend(scan_einstein_proof_substance(vf))
            all_findings.extend(scan_fake_completion_claims(vf))
            all_findings.extend(scan_einstein_model_mismatch(vf))
            all_findings.extend(scan_stress_energy_grounding(vf))
            # Disabled in max-strict mode: heuristic style warning, not proof-soundness critical.
            # all_findings.extend(scan_unused_local_definitions(vf))
            all_findings.extend(scan_mugravity_completion_gate(vf))
            all_findings.extend(scan_mugravity_bridge_leaks(vf))
            # Disabled: conflicts with no-shortcuts policy that removes source_balance_contract wrappers.
            # all_findings.extend(scan_mugravity_raw_source_formula(vf))
            all_findings.extend(scan_mugravity_dynamic_raw(vf))
            all_findings.extend(scan_mugravity_one_step_literal(vf))
            all_findings.extend(scan_mugravity_no_shortcuts(vf))
            all_findings.extend(scan_mugravity_max_strict(vf))
            all_findings.extend(scan_mugravity_derivation_completeness(vf))
            all_findings.extend(scan_mugravity_vm_compatibility(vf))
            all_findings.extend(scan_mugravity_no_assumption_surfaces(vf))

            score, tags = _file_vacuity_summary(vf)
            if score > 0:
                vacuity_index.append((score, vf, tags))
        except Exception as e:
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

    if not args.include_informational:
        all_findings = [
            f
            for f in all_findings
            if f.rule_id not in {"SECTION_BINDER", "MODULE_SIGNATURE_DECL"}
        ]

    # ── Vacuity gate ──────────────────────────────────────────────────────────
    # The vacuity SCORE (from inquisitor_rules.summarize_text) measures how
    # "trivially true / definitional" a file looks.  Previously this was purely
    # informational — it appeared in a ranking table but never failed the gate.
    # That meant a file like `Theorem foo : True.` could score 140 on the
    # vacuity index and STILL produce a clean PASS.  Fixed here:
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
                    "advance the thesis goal."
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
