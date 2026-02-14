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
            # Check for INQUISITOR NOTE in the original text (with comments)
            # Look within 15 lines before the Axiom declaration
            note_context = "\n".join(raw_lines[max(0, line - 15): line + 1])
            has_inquisitor_note = "INQUISITOR NOTE" in note_context
            if has_inquisitor_note:
                # Documented interface axiom — INQUISITOR NOTE present, skip
                continue
            else:
                rule_id = "AXIOM_OR_PARAMETER"
                severity = "HIGH"  # Undocumented axioms are unproven assumptions
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
                    # Documented Context — INQUISITOR NOTE present, skip
                    continue
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

        # Check for destructuring pattern: brackets [ ] in intros
        has_destruct_intro = bool(re.search(r"intros?\s+[^.]*\[", proof_text))
        if not has_destruct_intro:
            continue

        # Check if proof is very short (1-3 meaningful lines)
        if len(proof_lines) > 4:
            continue

        # Extract variable names introduced by destructuring intros
        # e.g., "intros T [_ [Hid _]] s." → intro names = {T, Hid, s}
        intro_m = re.search(r"intros?\s+([^.;]+)", proof_text)
        intro_names: set[str] = set()
        if intro_m:
            intro_raw = intro_m.group(1)
            for tok in re.findall(r"[A-Za-z][A-Za-z0-9_']*", intro_raw):
                intro_names.add(tok)

        # Check if proof ends with exact/apply whose PRIMARY target
        # is one of the intro'd variables (not a named lemma).
        # "exact (Hid s)." → target = Hid (from intros) → flag
        # "exact (chain_links_mu_head n c Hmu)." → target = chain_links_mu_head (not from intros) → skip
        exact_m = re.search(
            r"\b(?:exact|apply)\b\s*\(?(\s*[A-Za-z][A-Za-z0-9_']*)",
            proof_text
        )
        target_is_intro_var = False
        if exact_m:
            target_name = exact_m.group(1).strip()
            target_is_intro_var = target_name in intro_names

        if target_is_intro_var:
            line = line_of[tm.start()]
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else tname
            findings.append(
                Finding(
                    rule_id="HYPOTHESIS_RESTATEMENT",
                    severity="MEDIUM",  # Advisory: field extraction is a code smell, not a proof defect
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=f"Theorem `{tname}` destructures a hypothesis and extracts one piece "
                            f"as its conclusion — this restates an assumption, not a derived result.",
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
    lines.append("- `HYPOTHESIS_RESTATEMENT`: proof destructures hypothesis and extracts one piece (restating assumption, not deriving)\n")
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
            all_findings.extend(scan_hypothesis_restatement(vf))

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

    # Fail-fast policy: ANY HIGH finding in ANY file fails the build.
    # No protected-file distinction. Every proof is held to the same standard.
    all_high = [
        f
        for f in all_findings
        if f.severity == "HIGH"
        and not is_allowlisted(f.file, enable_allowlist=args.allowlist)
    ]

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

    # ULTRA-STRICT MODE: Also fail on MEDIUM findings in ANY file
    # UNLESS the finding has an INQUISITOR NOTE explaining it
    if args.ultra_strict:
        all_medium = [
            f for f in all_findings
            if f.severity == "MEDIUM"
            and not is_allowlisted(f.file, enable_allowlist=args.allowlist)
            and not has_inquisitor_note(f)  # Allow documented edge cases
        ]
        if all_medium:
            print(f"INQUISITOR: FAIL (ultra-strict) — {len(all_medium)} undocumented MEDIUM findings.")
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
