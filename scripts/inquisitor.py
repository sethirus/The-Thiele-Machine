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
import os
import re
import sys
from pathlib import Path
from typing import Iterable, Iterator


PROTECTED_BASENAMES = {"CoreSemantics.v", "BridgeDefinitions.v"}

# Pure interface files (Module Type signatures). Declarations inside are not
# "sins" and should not appear as findings.
INTERFACE_BASENAMES = {
    "Spaceland.v",
    "SpacelandCore.v",
    "Spaceland_Simple.v",
    "ThieleMachineSig.v",
}

# Allowed locations for "sins" (demos / WIP / archived scratch).
ALLOWLIST_PATH_PARTS = (
    "/demos/",
    "/demo/",
    "/wip/",
    "/WIP/",
    "/archive/",
    "/scratch/",
    "/experimental/",
    "/sandboxes/",
)

# Populated at runtime (see `main`) with .v files that are considered optional
# by the repository build (from `coq/Makefile.local` OPTIONAL_VO).
ALLOWLIST_EXACT_FILES: set[Path] = set()

SUSPICIOUS_NAME_RE = re.compile(
    r"(?i)(optimal|optimum|best|min|max|cost|objective|solve|solver|search|discover|oracle|result|proof)")


@dataclasses.dataclass(frozen=True)
class Finding:
    rule_id: str
    severity: str  # HIGH/MEDIUM/LOW
    file: Path
    line: int
    snippet: str
    message: str


def is_allowlisted(path: Path) -> bool:
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


def iter_v_files(coq_root: Path) -> Iterator[Path]:
    for p in coq_root.rglob("*.v"):
        if p.is_file():
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


def scan_file(path: Path) -> list[Finding]:
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    line_of = _line_map(text)
    clean_lines = text.splitlines()

    # Track whether each line is inside a `Module Type ... End` block.
    # Declarations inside module signatures are requirements for implementations,
    # not global axioms of the development.
    in_module_type: list[bool] = [False] * (len(clean_lines) + 1)  # 1-based index
    module_type_depth = 0
    module_type_start = re.compile(r"(?m)^[ \t]*Module\s+Type\b")
    module_end = re.compile(r"(?m)^[ \t]*End\b")
    for idx, ln in enumerate(clean_lines, start=1):
        if module_type_start.match(ln):
            module_type_depth += 1
        in_module_type[idx] = module_type_depth > 0
        if module_end.match(ln) and module_type_depth > 0:
            module_type_depth -= 1

    findings: list[Finding] = []

    # Assumption surfaces.
    #
    # Important distinction:
    # - `Axiom`/`Parameter` introduce global, unproven constants: treat as HIGH.
    # - `Hypothesis` introduces an assumption; often acceptable in generic lemmas but can also
    #   hide an oracle. Treat as MEDIUM, escalated to HIGH if the name looks suspicious.
    # - `Context`/`Variable(s)` are typically just binders for polymorphism inside a section.
    #   They are not "lies" by themselves, but we still report them for visibility.
    assumption_decl = re.compile(
        r"(?m)^[ \t]*(Axiom|Parameter|Hypothesis|Variable|Variables|Context)\b\s*"  # kind
        r"(?:\(?\s*([A-Za-z0-9_']+)\b)?"  # optional name (may be absent for Context (...))
    )
    for m in assumption_decl.finditer(text):
        kind = m.group(1)
        name = (m.group(2) or "").strip()
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else kind

        # Inside a Module Type, treat declarations as signature fields.
        if (
            1 <= line < len(in_module_type)
            and in_module_type[line]
            and kind in {"Axiom", "Parameter"}
        ):
            # In interface-only files, these are the *law*: do not report them.
            if path.name in INTERFACE_BASENAMES:
                continue
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
            severity = "HIGH"
        elif kind == "Hypothesis":
            rule_id = "HYPOTHESIS_ASSUME"
            severity = "HIGH" if (name and SUSPICIOUS_NAME_RE.search(name)) else "MEDIUM"
        else:
            rule_id = "SECTION_BINDER"
            severity = "LOW"

        findings.append(
            Finding(
                rule_id=rule_id,
                severity=severity,
                file=path,
                line=line,
                snippet=snippet.strip(),
                message=f"Found {kind}{(' ' + name) if name else ''}.",
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

    # Theorem ... : True.
    theorem_true = re.compile(r"(?m)^[ \t]*Theorem\s+([A-Za-z0-9_']+)\b[^:]*:\s*True\s*\.")
    for m in theorem_true.finditer(text):
        name = m.group(1)
        line = line_of[m.start()]
        snippet = clean_lines[line - 1] if 0 <= line - 1 < len(clean_lines) else m.group(0)
        findings.append(
            Finding(
                rule_id="PROP_TAUTOLOGY",
                severity=_classify_constant_severity(name, "HIGH"),
                file=path,
                line=line,
                snippet=snippet.strip(),
                message="Theorem statement is literally True.",
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

    # Definition ... := 0. / 0%Z / 0%nat
    def_zero = re.compile(
        r"(?m)^[ \t]*Definition\s+([A-Za-z0-9_']+)\b.*:=\s*0(?:%Z|%nat)?\s*\.")
    for m in def_zero.finditer(text):
        name = m.group(1)
        line = line_of[m.start()]
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


def write_report(report_path: Path, repo_root: Path, findings: list[Finding], scanned_files: int) -> None:
    now = _dt.datetime.now(_dt.UTC).strftime("%Y-%m-%d %H:%M:%SZ")
    by_sev = {"HIGH": [], "MEDIUM": [], "LOW": []}
    for f in findings:
        by_sev.setdefault(f.severity, []).append(f)

    def esc(s: str) -> str:
        return s.replace("`", "\\`")

    lines: list[str] = []
    lines.append(f"# INQUISITOR REPORT\n")
    lines.append(f"Generated: {now} (UTC)\n")
    lines.append(f"Scanned: {scanned_files} Coq files under `coq/`\n")
    lines.append("## Summary\n")
    lines.append(f"- HIGH: {len(by_sev.get('HIGH', []))}\n")
    lines.append(f"- MEDIUM: {len(by_sev.get('MEDIUM', []))}\n")
    lines.append(f"- LOW: {len(by_sev.get('LOW', []))}\n")
    lines.append("\n")

    lines.append("## Rules\n")
    lines.append("- `AXIOM_OR_PARAMETER`: `Axiom` / `Parameter`\n")
    lines.append("- `HYPOTHESIS_ASSUME`: `Hypothesis` (escalates to HIGH for suspicious names)\n")
    lines.append("- `SECTION_BINDER`: `Context` / `Variable` / `Variables` (informational)\n")
    lines.append("- `MODULE_SIGNATURE_DECL`: `Axiom` / `Parameter` inside `Module Type` (informational)\n")
    lines.append("- `COST_IS_LENGTH`: `Definition *cost* := ... length ... .`\n")
    lines.append("- `EMPTY_LIST`: `Definition ... := [].`\n")
    lines.append("- `ZERO_CONST`: `Definition ... := 0.` / `0%Z` / `0%nat`\n")
    lines.append("- `TRUE_CONST`: `Definition ... := True.` or `:= true.`\n")
    lines.append("- `PROP_TAUTOLOGY`: `Theorem ... : True.`\n")
    lines.append("- `CIRCULAR_INTROS_ASSUMPTION`: tautology + `intros; assumption.`\n")
    lines.append("- `TRIVIAL_EQUALITY`: theorem of form `X = X` with reflexivity-ish proof\n")
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
    ap = argparse.ArgumentParser()
    ap.add_argument("--coq-root", default="coq", help="Root directory to scan (default: coq)")
    ap.add_argument("--report", default="INQUISITOR_REPORT.md", help="Markdown report path")
    ap.add_argument(
        "--fail-on-protected",
        action="store_true",
        default=True,
        help="Exit non-zero on HIGH findings in protected files (default: on)",
    )
    ap.add_argument(
        "--strict",
        action="store_true",
        default=False,
        help="Fail on any HIGH finding outside allowlisted paths (scorched earth).",
    )
    ap.add_argument(
        "--ignore-makefile-optional",
        action="store_true",
        default=False,
        help="Do not treat coq/Makefile.local OPTIONAL_VO files as allowlisted.",
    )
    ap.add_argument(
        "--no-fail-on-protected",
        dest="fail_on_protected",
        action="store_false",
        help="Do not fail on protected findings",
    )
    ap.add_argument(
        "--include-informational",
        action="store_true",
        default=False,
        help="Include informational SECTION_BINDER and MODULE_SIGNATURE_DECL findings in the report.",
    )
    args = ap.parse_args(argv)

    repo_root = Path(__file__).resolve().parents[1]
    coq_root = (repo_root / args.coq_root).resolve()
    report_path = (repo_root / args.report).resolve()

    global ALLOWLIST_EXACT_FILES
    if not args.ignore_makefile_optional:
        ALLOWLIST_EXACT_FILES = _parse_optional_v_files(repo_root, coq_root)
    else:
        ALLOWLIST_EXACT_FILES = set()

    if not coq_root.exists():
        print(f"ERROR: coq root not found: {coq_root}", file=sys.stderr)
        return 2

    all_findings: list[Finding] = []
    scanned = 0
    for vf in iter_v_files(coq_root):
        scanned += 1
        try:
            all_findings.extend(scan_file(vf))
            all_findings.extend(scan_trivial_equalities(vf))
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

    if not args.include_informational:
        all_findings = [
            f
            for f in all_findings
            if f.rule_id not in {"SECTION_BINDER", "MODULE_SIGNATURE_DECL"}
        ]

    write_report(report_path, repo_root, all_findings, scanned)

    # Fail-fast policy: HIGH sins in protected files, unless allowlisted.
    protected_high = [
        f
        for f in all_findings
        if f.severity == "HIGH"
        and f.file.name in PROTECTED_BASENAMES
        and not is_allowlisted(f.file)
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
            if f.severity == "HIGH" and not is_allowlisted(f.file)
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

    print("INQUISITOR: OK")
    print(f"Report: {report_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
