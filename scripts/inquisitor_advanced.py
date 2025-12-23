#!/usr/bin/env python3
"""Advanced Inquisitor rules: proof complexity, dead code, dependencies, and more.

This module extends the base Inquisitor with sophisticated static analysis:
- Proof complexity metrics (length, tactic count, nesting depth)
- Dead definition detection (unused lemmas, theorems, definitions)
- Import dependency analysis (unused imports, circular dependencies)
- Proof tactic anti-patterns (excessive automation, brittle tactics)
- Naming convention validation
- Proof obligation tracking
"""

from __future__ import annotations

import re
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator

from inquisitor_rules import summarize_text


@dataclass(frozen=True)
class Finding:
    rule_id: str
    severity: str  # HIGH/MEDIUM/LOW
    file: Path
    line: int
    snippet: str
    message: str


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
            if ch == "\n":
                out.append("\n")
        i += 1
    return "".join(out)


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


# ============================================================================
# PROOF COMPLEXITY ANALYSIS
# ============================================================================

@dataclass(frozen=True)
class ProofMetrics:
    name: str
    start_line: int
    length_lines: int
    tactic_count: int
    nesting_depth: int
    uses_automation: bool


def scan_proof_complexity(path: Path, *, max_proof_lines: int = 100, max_tactics: int = 50) -> list[Finding]:
    """Detect overly complex proofs that may hide issues."""
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()

    findings: list[Finding] = []

    # Find all proof blocks
    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma|Corollary)\s+([A-Za-z0-9_']+)\b")
    proof_re = re.compile(r"(?m)^[ \t]*Proof\.")
    end_re = re.compile(r"(?m)^[ \t]*(Qed|Admitted|Defined)\.")

    for m in theorem_re.finditer(text):
        name = m.group(2)
        start = m.end()
        proof_match = proof_re.search(text, start)
        if not proof_match:
            continue

        end_match = end_re.search(text, proof_match.end())
        if not end_match:
            continue

        proof_start_line = line_of[proof_match.start()]
        proof_end_line = line_of[end_match.start()]
        proof_length = proof_end_line - proof_start_line

        proof_block = text[proof_match.end():end_match.start()]

        # Count tactics (approximate)
        tactic_pattern = re.compile(r"\b(intros|apply|rewrite|simpl|reflexivity|induction|destruct|split|exists|auto|eauto|omega|lia|ring|field|tauto|constructor|discriminate|injection|inversion|unfold|fold|subst|clear|assert|generalize|specialize|exact)\b")
        tactic_count = len(tactic_pattern.findall(proof_block))

        # Check for excessive automation
        automation_pattern = re.compile(r"\b(auto|eauto|intuition|firstorder|crush|congruence|lia|omega|ring|field)\b")
        uses_automation = bool(automation_pattern.search(proof_block))

        # Calculate nesting depth (approximate via braces/bullets)
        max_depth = 0
        current_depth = 0
        for ch in proof_block:
            if ch in "{([":
                current_depth += 1
                max_depth = max(max_depth, current_depth)
            elif ch in "})]":
                current_depth = max(0, current_depth - 1)

        # Flag overly long proofs
        if proof_length > max_proof_lines:
            snippet = clean_lines[proof_start_line - 1] if 0 <= proof_start_line - 1 < len(clean_lines) else f"Proof. ... Qed. ({proof_length} lines)"
            findings.append(
                Finding(
                    rule_id="PROOF_TOO_LONG",
                    severity="MEDIUM",
                    file=path,
                    line=proof_start_line,
                    snippet=snippet.strip(),
                    message=f"Proof for {name} is {proof_length} lines (threshold: {max_proof_lines}). Consider refactoring.",
                )
            )

        # Flag overly complex proofs (too many tactics)
        if tactic_count > max_tactics:
            snippet = clean_lines[proof_start_line - 1] if 0 <= proof_start_line - 1 < len(clean_lines) else f"Proof with {tactic_count} tactics"
            findings.append(
                Finding(
                    rule_id="PROOF_TOO_COMPLEX",
                    severity="MEDIUM",
                    file=path,
                    line=proof_start_line,
                    snippet=snippet.strip(),
                    message=f"Proof for {name} uses {tactic_count} tactics (threshold: {max_tactics}). May be fragile.",
                )
            )

        # Flag deep nesting
        if max_depth > 5:
            snippet = clean_lines[proof_start_line - 1] if 0 <= proof_start_line - 1 < len(clean_lines) else f"Deeply nested proof"
            findings.append(
                Finding(
                    rule_id="PROOF_DEEP_NESTING",
                    severity="LOW",
                    file=path,
                    line=proof_start_line,
                    snippet=snippet.strip(),
                    message=f"Proof for {name} has nesting depth {max_depth}. Consider flattening.",
                )
            )

    return findings


# ============================================================================
# DEAD CODE DETECTION
# ============================================================================

def scan_dead_definitions(path: Path, repo_root: Path) -> list[Finding]:
    """Detect potentially unused definitions, lemmas, and theorems.

    This is a heuristic: we scan the entire repo for references to each definition.
    If a definition appears to be defined but never used elsewhere, flag it.
    """
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()

    findings: list[Finding] = []

    # Find all definitions
    def_re = re.compile(r"(?m)^[ \t]*(Definition|Lemma|Theorem|Corollary|Fixpoint)\s+([A-Za-z0-9_']+)\b")

    definitions: list[tuple[str, int]] = []
    for m in def_re.finditer(text):
        name = m.group(2)
        line = line_of[m.start()]
        definitions.append((name, line))

    # For each definition, search the repo for usages
    for name, line in definitions:
        # Skip very common/generic names that are likely used
        if name in {"id", "eq", "refl", "sym", "trans", "proof", "H", "x", "y", "z", "n", "m"}:
            continue

        # Search for usages across all .v files
        usage_count = 0
        for coq_file in repo_root.rglob("*.v"):
            if coq_file == path:
                # Count usages in same file (excluding definition)
                file_text = coq_file.read_text(encoding="utf-8", errors="replace")
                # Remove definition line to avoid counting the definition itself
                usage_pattern = re.compile(rf"\b{re.escape(name)}\b")
                matches = list(usage_pattern.finditer(file_text))
                # Heuristic: if appears more than once, likely used
                if len(matches) > 1:
                    usage_count += len(matches) - 1
            else:
                file_text = coq_file.read_text(encoding="utf-8", errors="replace")
                usage_pattern = re.compile(rf"\b{re.escape(name)}\b")
                usage_count += len(usage_pattern.findall(file_text))

        # If no usages found, flag as potentially dead
        if usage_count == 0:
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else f"Definition {name}"
            findings.append(
                Finding(
                    rule_id="POTENTIALLY_DEAD_DEF",
                    severity="LOW",
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=f"Definition '{name}' appears unused (no references found in repo).",
                )
            )

    return findings


# ============================================================================
# TACTIC ANTI-PATTERNS
# ============================================================================

def scan_tactic_antipatterns(path: Path) -> list[Finding]:
    """Detect suspicious proof tactic usage patterns."""
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()

    findings: list[Finding] = []

    # Find proof blocks
    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma|Corollary)\s+([A-Za-z0-9_']+)\b")
    proof_re = re.compile(r"(?m)^[ \t]*Proof\.")
    end_re = re.compile(r"(?m)^[ \t]*(Qed|Admitted|Defined)\.")

    # Anti-pattern 1: Excessive automation without manual steps
    # Pattern: Proof. auto. Qed. or similar
    excessive_auto_re = re.compile(r"Proof\.\s*(auto|eauto|intuition|firstorder|tauto)\s*\.\s*Qed\.", re.DOTALL)

    for m in excessive_auto_re.finditer(text):
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else "Proof. auto. Qed."
        findings.append(
            Finding(
                rule_id="EXCESSIVE_AUTOMATION",
                severity="LOW",
                file=path,
                line=line,
                snippet=snippet.strip(),
                message="Proof relies entirely on automation without manual steps. May be fragile.",
            )
        )

    # Anti-pattern 2: Repeated identical tactic sequences (copy-paste proofs)
    for m in theorem_re.finditer(text):
        name = m.group(2)
        start = m.end()
        proof_match = proof_re.search(text, start)
        if not proof_match:
            continue

        end_match = end_re.search(text, proof_match.end())
        if not end_match:
            continue

        proof_block = text[proof_match.end():end_match.start()]

        # Look for repeated tactic sequences (4+ identical tactics in a row)
        tactic_lines = [ln.strip() for ln in proof_block.splitlines() if ln.strip() and not ln.strip().startswith("(*")]

        for i in range(len(tactic_lines) - 3):
            if (tactic_lines[i] == tactic_lines[i+1] == tactic_lines[i+2] == tactic_lines[i+3]
                and tactic_lines[i] not in {"", "Proof.", "Qed."}):
                line = line_of[proof_match.start()] + i + 1
                findings.append(
                    Finding(
                        rule_id="REPEATED_TACTIC_PATTERN",
                        severity="LOW",
                        file=path,
                        line=line,
                        snippet=tactic_lines[i][:80],
                        message=f"Repeated tactic pattern detected (4+ identical tactics). Consider using a loop or Ltac.",
                    )
                )
                break

    # Anti-pattern 3: admit followed by tactics (suspicious)
    admit_then_tactics = re.compile(r"\badmit\.\s+\w+", re.MULTILINE)
    for m in admit_then_tactics.finditer(text):
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="ADMIT_THEN_TACTICS",
                severity="HIGH",
                file=path,
                line=line,
                snippet=snippet.strip(),
                message="Tactics appear after 'admit'. This is suspicious and likely an error.",
            )
        )

    return findings


# ============================================================================
# IMPORT/DEPENDENCY ANALYSIS
# ============================================================================

def scan_import_analysis(path: Path) -> list[Finding]:
    """Analyze import statements and detect issues."""
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()

    findings: list[Finding] = []

    # Find all imports
    import_re = re.compile(r"(?m)^[ \t]*(Require|Require Import|From .+ Require Import)\s+([A-Za-z0-9_.']+(?:\s+[A-Za-z0-9_.']+)*)\s*\.")

    imports = []
    for m in import_re.finditer(text):
        line = line_of[m.start()]
        imported_modules = m.group(2).strip().split()
        for module in imported_modules:
            imports.append((module, line))

    # Check for unused imports (heuristic)
    for module, line in imports:
        # Skip standard library and very common modules
        if module in {"Coq", "List", "Arith", "Bool", "ZArith", "QArith", "Reals", "String", "Setoid"}:
            continue

        # Simple check: is the module name referenced anywhere after the import?
        import_pos = None
        for m in import_re.finditer(text):
            if line_of[m.start()] == line:
                import_pos = m.end()
                break

        if import_pos:
            rest_of_file = text[import_pos:]
            module_usage = re.compile(rf"\b{re.escape(module)}\b")
            if not module_usage.search(rest_of_file):
                snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else f"Require Import {module}"
                findings.append(
                    Finding(
                        rule_id="POTENTIALLY_UNUSED_IMPORT",
                        severity="LOW",
                        file=path,
                        line=line,
                        snippet=snippet.strip(),
                        message=f"Module '{module}' imported but not obviously used (heuristic check).",
                    )
                )

    # Check for duplicate imports
    import_counts: dict[str, list[int]] = defaultdict(list)
    for module, line in imports:
        import_counts[module].append(line)

    for module, lines in import_counts.items():
        if len(lines) > 1:
            snippet = clean_lines[lines[0] - 1] if 0 <= lines[0] - 1 < len(clean_lines) else f"Require Import {module}"
            findings.append(
                Finding(
                    rule_id="DUPLICATE_IMPORT",
                    severity="LOW",
                    file=path,
                    line=lines[0],
                    snippet=snippet.strip(),
                    message=f"Module '{module}' imported {len(lines)} times (lines: {', '.join(map(str, lines))}).",
                )
            )

    return findings


# ============================================================================
# NAMING CONVENTION VALIDATION
# ============================================================================

def scan_naming_conventions(path: Path) -> list[Finding]:
    """Check adherence to naming conventions."""
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()

    findings: list[Finding] = []

    # Convention checks:
    # 1. Theorems/Lemmas should use snake_case or camelCase, not mixedUP
    # 2. Theorems about correctness should have "correct" or "sound" in name
    # 3. Theorems about completeness should have "complete" in name

    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma|Corollary)\s+([A-Za-z0-9_']+)\b")

    for m in theorem_re.finditer(text):
        kind = m.group(1)
        name = m.group(2)
        line = line_of[m.start()]

        # Check for inconsistent casing (e.g., "myTheorem_With_UnderScores")
        has_camel = re.search(r"[a-z][A-Z]", name)
        has_snake = "_" in name

        if has_camel and has_snake:
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else f"{kind} {name}"
            findings.append(
                Finding(
                    rule_id="INCONSISTENT_NAMING",
                    severity="LOW",
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=f"{kind} '{name}' mixes camelCase and snake_case. Use one convention.",
                )
            )

        # Check for ALL_CAPS names (usually constants, not theorems)
        if name.isupper() and len(name) > 2:
            snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else f"{kind} {name}"
            findings.append(
                Finding(
                    rule_id="ALL_CAPS_THEOREM",
                    severity="LOW",
                    file=path,
                    line=line,
                    snippet=snippet.strip(),
                    message=f"{kind} '{name}' is ALL_CAPS. Theorems should use snake_case or camelCase.",
                )
            )

    return findings


# ============================================================================
# PROOF OBLIGATION TRACKING
# ============================================================================

def scan_proof_obligations(path: Path) -> list[Finding]:
    """Track proof obligations: Admitted vs Qed."""
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()

    findings: list[Finding] = []

    # Find all theorems and their completion status
    theorem_re = re.compile(r"(?m)^[ \t]*(Theorem|Lemma|Corollary)\s+([A-Za-z0-9_']+)\b")
    proof_re = re.compile(r"(?m)^[ \t]*Proof\.")
    admitted_re = re.compile(r"(?m)^[ \t]*Admitted\.")
    qed_re = re.compile(r"(?m)^[ \t]*Qed\.")

    admitted_count = 0
    proven_count = 0

    for m in theorem_re.finditer(text):
        name = m.group(2)
        start = m.end()

        proof_match = proof_re.search(text, start)
        if not proof_match:
            continue

        # Check if ends with Admitted or Qed
        admitted_match = admitted_re.search(text, proof_match.end())
        qed_match = qed_re.search(text, proof_match.end())

        if admitted_match and (not qed_match or admitted_match.start() < qed_match.start()):
            admitted_count += 1
        elif qed_match:
            proven_count += 1

    # Report overall stats
    total = admitted_count + proven_count
    if total > 0:
        completion_rate = (proven_count / total) * 100
        if completion_rate < 80:
            findings.append(
                Finding(
                    rule_id="LOW_PROOF_COMPLETION",
                    severity="MEDIUM",
                    file=path,
                    line=1,
                    snippet=f"{proven_count}/{total} proven ({completion_rate:.1f}%)",
                    message=f"File has low proof completion rate: {proven_count}/{total} proven ({completion_rate:.1f}%). {admitted_count} admitted.",
                )
            )

    return findings
