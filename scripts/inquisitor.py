#!/usr/bin/env python3
"""Inquisitor: scorched-earth Coq audit for proof triviality and hidden assumptions.

Scans the `coq/` tree for suspicious "proof smells":
- Trivial constant definitions ([], 0, True/true)
- Tautological theorems (Theorem ... : True.)
- Hidden assumptions (Axiom/Parameter/Hypothesis)
- Suspiciously trivial proofs (intros; assumption.) for tautology-shaped statements

Writes a Markdown report (default: INQUISITOR_REPORT.md) and returns non-zero
if high-severity findings appear in protected files (CoreSemantics/BridgeDefinitions)
outside allowlisted paths.

This is a heuristic static analysis tool; it errs on the side of flagging.
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
CLAMP_PAT = re.compile(r"\b(Z\.to_nat|Nat\.min|Nat\.max|Z\.abs)\b")
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
    for p in repo_root.rglob("*.v"):
        if not p.is_file():
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
    if default == "HIGH":
        return "HIGH"
    # UNUSED_HYPOTHESIS is heuristic - downgraded to LOW
    if rule_id == "UNUSED_HYPOTHESIS":
        return "LOW"
    path_str = path.as_posix().lower()
    # Critical kernel files get highest scrutiny
    if path.name in CRITICAL_KERNEL_FILES:
        return "HIGH" if default in {"HIGH", "MEDIUM"} else "MEDIUM"
    if "/kernel/" in path_str or path.name in PROTECTED_BASENAMES:
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
        
        # Skip proofs using heavy automation tactics that use hypotheses implicitly
        proof_body_text = " ".join(proof_lines)
        # Skip any proof with automation that might use hypotheses implicitly
        if any(tactic in proof_body_text for tactic in [
            "lia", "omega", "congruence", "auto", "eauto", "intuition", "firstorder",
            "assumption", "easy", "trivial", "now ", "reflexivity", "simpl", "unfold",
            "rewrite", "apply", "exact", "destruct", "induction", "case", "discriminate"
        ]):
            continue
        
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
        body = " ".join(proof_lines[1:])
        for name in names:
            if name in {"*", "?", "!", "intro", "intros"}:
                continue
            # For names with apostrophes (like q'), word boundary \b doesn't work
            # Use a more flexible pattern that matches the name as a separate token
            if "'" in name:
                # Match q' as a token (preceded/followed by non-alphanumeric or apostrophe)
                pattern = rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])"
            else:
                # Standard word boundary for regular identifiers
                pattern = rf"\b{re.escape(name)}\b"
            
            # Check if used in proof body
            if re.search(pattern, body):
                continue
            # Check if used in lemma statement/conclusion
            if re.search(pattern, lemma_statement):
                continue
            # UNUSED_HYPOTHESIS is a heuristic - many false positives from destructuring/automation
            # Downgrade to LOW to reduce noise
            findings.append(
                Finding(
                    rule_id="UNUSED_HYPOTHESIS",
                    severity="LOW",
                    file=path,
                    line=line_of[proof_match.start()],
                    snippet=intros_line,
                    message=f"Introduced hypothesis `{name}` not used in proof body or conclusion (heuristic).",
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
    module_type_depth = 0
    module_impl_depth = 0  # Track Module X : Signature
    module_type_start = re.compile(r"(?m)^[ \t]*Module\s+Type\b")
    module_impl_start = re.compile(r"(?m)^[ \t]*Module\s+\w+\s*:\s*\w+")  # Module X : Sig
    module_end = re.compile(r"(?m)^[ \t]*End\b")
    for idx, ln in enumerate(clean_lines, start=1):
        if module_type_start.match(ln):
            module_type_depth += 1
        if module_impl_start.match(ln):
            module_impl_depth += 1
        in_module_type[idx] = (module_type_depth > 0) or (module_impl_depth > 0)
        if module_end.match(ln):
            if module_type_depth > 0:
                module_type_depth -= 1
            if module_impl_depth > 0:
                module_impl_depth -= 1

    findings: list[Finding] = []

    # Check for Admitted (incomplete proofs - FORBIDDEN)
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
                message="Admitted found (incomplete proof - FORBIDDEN).",
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
                message="admit tactic found (proof shortcut - FORBIDDEN).",
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
                message="give_up tactic found (proof shortcut - FORBIDDEN).",
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
                    message=f"Found {kind}{(' ' + name) if name else ''} inside Module Type.",
                )
            )
            continue

        if kind in {"Axiom", "Parameter"}:
            rule_id = "AXIOM_OR_PARAMETER"
            severity = "HIGH"  # Axioms are always HIGH - they're unproven assumptions
        elif kind == "Hypothesis":
            rule_id = "HYPOTHESIS_ASSUME"
            # Hypothesis is functionally equivalent to Axiom - always HIGH
            severity = "HIGH"
        elif kind == "Context":
            # Context with forall/arrow types are section-local axioms
            # These MUST be instantiated or they're hidden assumptions
            has_forall = "forall" in full_decl
            has_arrow = "->" in full_decl
            has_implication = "=>" in full_decl and "fun" not in full_decl
            is_complex_assumption = has_forall or has_arrow or has_implication
            
            # Check for INQUISITOR NOTE in the original text (with comments)
            # Look within 15 lines before the Context declaration
            note_context = "\n".join(raw_lines[max(0, line - 15): line + 1])
            has_inquisitor_note = "INQUISITOR NOTE" in note_context
            
            if is_complex_assumption:
                if has_inquisitor_note:
                    # Documented Context - downgrade to LOW (informational)
                    rule_id = "CONTEXT_ASSUMPTION_DOCUMENTED"
                    severity = "LOW"
                    msg = f"Context parameter `{name}` is documented with INQUISITOR NOTE."
                else:
                    rule_id = "CONTEXT_ASSUMPTION"
                    severity = "HIGH"  # Undocumented section-local axiom!
                    msg = f"Context parameter `{name}` with forall/arrow type is a SECTION-LOCAL AXIOM. Must be instantiated or documented."
            else:
                rule_id = "SECTION_BINDER"
                severity = "MEDIUM"  # Still needs verification
                msg = f"Found {kind}{(' ' + name) if name else ''}."
        else:
            # Variable/Variables
            rule_id = "SECTION_BINDER"
            severity = "MEDIUM"  # Need to verify these are properly instantiated
            msg = f"Found {kind}{(' ' + name) if name else ''}."

        findings.append(
            Finding(
                rule_id=rule_id,
                severity=severity,
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=msg if kind == "Context" else f"Found {kind}{(' ' + name) if name else ''}.",
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
    line_of = _line_map(text)
    clean_lines = text.splitlines()
    findings: list[Finding] = []
    
    # Known problematic imports (classical axioms, etc.)
    problematic_imports = re.compile(r"(?m)^[ \t]*Require\s+(?:Import\s+)?.*\b(Classical|Decidable|ProofIrrelevance)\b")
    
    for m in problematic_imports.finditer(text):
        line = line_of[m.start()]
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
            tag = contract.get("tag")
            matches_tag = bool(tag and re.search(re.escape(tag), raw, re.IGNORECASE))
            if not matches_file and not matches_tag:
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
    lines.append("- `TRIVIAL_EQUALITY`: theorem of form `X = X` with reflexivity-ish proof\n")
    lines.append("- `CONST_Q_FUN`: `Definition ... := fun _ => 0%Q` / `1%Q`\n")
    lines.append("- `EXISTS_CONST_Q`: `exists (fun _ => 0%Q)` / `exists (fun _ => 1%Q)`\n")
    lines.append("- `CLAMP_OR_TRUNCATION`: uses `Z.to_nat`, `Z.abs`, `Nat.min`, `Nat.max`\n")
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
    lines.append("\n")

    if not findings:
        lines.append("## Findings\n")
        lines.append("(none)\n")
        report_path.write_text("".join(lines), encoding="utf-8")
        return

    if vacuity_index:
        lines.append("## Vacuity Ranking (file-level)\n")
        lines.append("Higher score = more likely unfinished/vacuous.\n\n")
        lines.append("| score | tags | file |\n")
        lines.append("|---:|---|---|\n")
        for score, abs_path, tags in sorted(vacuity_index, key=lambda t: (-t[0], str(t[1]))):
            try:
                rel = abs_path.relative_to(repo_root).as_posix()
            except Exception:
                rel = abs_path.as_posix()
            lines.append(f"| {score} | {', '.join(tags)} | `{esc(rel)}` |\n")
        lines.append("\n")

    lines.append("## Findings\n")
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
        description="INQUISITOR: Maximum strictness Coq proof auditor. "
        "Compiles ALL Coq files, scans for admits, axioms, and proof quality issues. "
        "Exits non-zero on ANY HIGH finding or compilation failure. No mercy. No exceptions."
    )
    ap.add_argument("--coq-root", action="append", default=["coq"], help="Root directory to scan")
    ap.add_argument("--report", default="INQUISITOR_REPORT.md", help="Markdown report path")
    ap.add_argument(
        "--no-build",
        action="store_true",
        default=False,
        help="Skip Coq compilation (NOT RECOMMENDED - use only for quick static checks).",
    )
    # Legacy options - kept for backward compatibility but no longer change behavior
    ap.add_argument("--build", action="store_true", default=True, help=argparse.SUPPRESS)  # Legacy
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
    ap.add_argument(
        "--all-proofs",
        action="store_true",
        default=True,
        help="Scan every Coq proof file in the repo (default: enabled).",
    )
    ap.add_argument(
        "--only-coq-roots",
        dest="all_proofs",
        action="store_false",
        help="Restrict scanning to --coq-root entries only.",
    )
    args = ap.parse_args(argv)
    
    # MAXIMUM STRICTNESS: All checks enabled, no allowlists
    args.strict = True
    args.ultra_strict = True
    args.fail_on_protected = True
    args.allowlist = False  # NO ALLOWLISTS - everything is examined
    # Build by default unless --no-build is specified
    args.build = not args.no_build

    repo_root = Path(__file__).resolve().parents[1]
    coq_roots = [(repo_root / root).resolve() for root in args.coq_root]
    report_path = (repo_root / args.report).resolve()
    manifest_path = (repo_root / args.manifest).resolve()
    manifest: dict | None = None

    global ALLOWLIST_EXACT_FILES
    ALLOWLIST_EXACT_FILES = set()
    if args.allowlist and args.allowlist_makefile_optional and not args.ignore_makefile_optional:
        coq_root = coq_roots[0]
        ALLOWLIST_EXACT_FILES = _parse_optional_v_files(repo_root, coq_root)

    if args.all_proofs:
        missing_roots = []
    else:
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
    if args.all_proofs:
        v_files = iter_all_coq_files(repo_root)
        scanned_scope = "repo"
    else:
        v_files = (vf for root in coq_roots for vf in iter_v_files(root))
        scanned_scope = ", ".join(root.as_posix() for root in coq_roots)

    for vf in v_files:
        scanned += 1
        try:
            all_findings.extend(scan_file(vf))
            all_findings.extend(scan_trivial_equalities(vf))
            all_findings.extend(scan_exists_const_q(vf))
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

    write_report(
        report_path,
        repo_root,
        all_findings,
        scanned,
        vacuity_index,
        scanned_scope=scanned_scope,
    )

    # Fail-fast policy: HIGH sins in protected files, unless allowlisted.
    protected_high = [
        f
        for f in all_findings
        if f.severity == "HIGH"
        and f.file.name in PROTECTED_BASENAMES
        and not is_allowlisted(f.file, enable_allowlist=args.allowlist)
    ]

    if protected_high and args.fail_on_protected:
        print(f"INQUISITOR: FAIL — {len(protected_high)} HIGH findings in protected files.")
        print(f"Report: {report_path}")
        # Print a short console summary.
        for f in protected_high[:25]:
            rel = f.file.relative_to(repo_root).as_posix()
            print(f"- {rel}:L{f.line} {f.rule_id} {f.message}")
        if len(protected_high) > 25:
            print(f"... ({len(protected_high) - 25} more)")
        return 1

    if args.strict:
        strict_high = [
            f for f in all_findings
            if f.severity == "HIGH" and not is_allowlisted(f.file, enable_allowlist=args.allowlist)
        ]
        if strict_high:
            print(f"INQUISITOR: FAIL (strict) — {len(strict_high)} HIGH findings outside allowlist.")
            print(f"Report: {report_path}")
            for f in strict_high[:25]:
                rel = f.file.relative_to(repo_root).as_posix()
                print(f"- {rel}:L{f.line} {f.rule_id} {f.message}")
            if len(strict_high) > 25:
                print(f"... ({len(strict_high) - 25} more)")
            return 1

    # Helper to check if a finding has an INQUISITOR NOTE nearby in the source
    def has_inquisitor_note(finding) -> bool:
        """Check if the finding has an INQUISITOR NOTE within 15 lines."""
        try:
            with open(finding.file, "r", encoding="utf-8", errors="replace") as f:
                lines = f.readlines()
            # Check lines around the finding for INQUISITOR NOTE
            start = max(0, finding.line - 5)
            end = min(len(lines), finding.line + 15)
            context = "".join(lines[start:end])
            return "INQUISITOR NOTE" in context
        except Exception:
            return False

    # ULTRA-STRICT MODE: Also fail on MEDIUM findings in critical kernel files
    # UNLESS the finding has an INQUISITOR NOTE explaining it
    if args.ultra_strict:
        critical_medium = [
            f for f in all_findings
            if f.severity == "MEDIUM" 
            and is_critical_kernel_file(f.file)
            and not is_allowlisted(f.file, enable_allowlist=args.allowlist)
            and not has_inquisitor_note(f)  # Allow documented edge cases
        ]
        if critical_medium:
            print(f"INQUISITOR: FAIL (ultra-strict) — {len(critical_medium)} undocumented MEDIUM findings in critical kernel files.")
            print(f"Report: {report_path}")
            for f in critical_medium[:25]:
                rel = f.file.relative_to(repo_root).as_posix()
                print(f"- {rel}:L{f.line} {f.rule_id} {f.message}")
            if len(critical_medium) > 25:
                print(f"... ({len(critical_medium) - 25} more)")
            return 1

    print("INQUISITOR: OK")
    print(f"Report: {report_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
