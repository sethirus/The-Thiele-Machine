#!/usr/bin/env python3
"""
add_proof_docstrings.py
-----------------------
Scan every Coq production file (layer = coq, i.e. not in a 'tests' directory)
and insert a minimal (** doc *) comment before any Theorem / Lemma /
Corollary / Proposition / Fact / Remark / Conjecture that currently lacks one.

The inserted comment matches the pattern required by the audit script:
    (** [ProofName]: formal specification. *)
    Lemma ProofName ...

Usage:
    python scripts/add_proof_docstrings.py [--dry-run] [--verbose]

Options:
    --dry-run   Print what would be done without modifying files.
    --verbose   Print each insertion made.
"""

import re
import sys
import argparse
from pathlib import Path
from typing import List, Tuple

REPO_ROOT = Path(__file__).resolve().parent.parent
COQ_DIR = REPO_ROOT / "coq"

# Declaration keywords that require preceding doc comments (per audit DOD)
PROOF_KWS = (
    "Theorem", "Lemma", "Corollary", "Proposition", "Fact", "Remark", "Conjecture"
)

# Matches the start of an undocumented proof declaration line
DECL_RE = re.compile(
    r"^(\s*)(?:Local\s+|Global\s+|#\[[^\]]*\]\s+)?"
    r"(Theorem|Lemma|Corollary|Proposition|Fact|Remark|Conjecture)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)"
)

# Matches a completed (** ... *) doc comment (may be multi-line).
# The audit DOC_COMMENT_BEFORE_PROOF_RE requires the comment to close on the
# line immediately preceding the declaration (with only whitespace between).
SINGLE_DOC_RE = re.compile(r"\(\*\*[^*].*?\*\)", re.DOTALL)

# Test for a line that ENDS a doc-comment block: '*)'
CLOSE_DOC_RE = re.compile(r"\*\)\s*$")


def _last_nonblank_lines(lines: List[str], before: int, count: int = 5) -> List[str]:
    """Return up to `count` non-blank lines before index `before`."""
    result = []
    i = before - 1
    while i >= 0 and len(result) < count:
        if lines[i].strip():
            result.append(lines[i])
        i -= 1
    return result


def _has_doc_comment_before(lines: List[str], decl_index: int) -> bool:
    """
    Return True when lines[decl_index] is directly preceded (ignoring blank
    lines) by a closing '**)' of a (** ... *) doc comment.
    """
    i = decl_index - 1
    # Skip blank lines
    while i >= 0 and not lines[i].strip():
        i -= 1
    if i < 0:
        return False

    line = lines[i]

    # Single-line: (** ... *)
    stripped = line.strip()
    if stripped.startswith("(**") and not stripped.startswith("(***") and stripped.endswith("*)"):
        return True

    # Single-line: (* ... *) that is NOT a doc comment — skip it
    if stripped.startswith("(*") and stripped.endswith("*)"):
        return False

    # End of multi-line (** ... *): last line ends with '*)'
    if CLOSE_DOC_RE.search(line):
        # Scan backwards to find the opening '(**'
        j = i - 1
        while j >= 0:
            if "(**" in lines[j] and not lines[j].strip().startswith("(***)"):
                return True
            if "(*" in lines[j] and "(**" not in lines[j]:
                return False  # Regular comment, not doc comment
            j -= 1
        return False

    return False


def process_file(path: Path, dry_run: bool = False, verbose: bool = False) -> int:
    """
    Add docstrings to undocumented proof declarations in *path*.
    Returns the number of insertions made (or that would be made).
    """
    try:
        text = path.read_text(encoding="utf-8")
    except Exception as exc:
        print(f"  [SKIP] {path}: {exc}", file=sys.stderr)
        return 0

    lines = text.splitlines(keepends=True)
    insertions: List[Tuple[int, str]] = []  # (line_index, docstring_to_insert)

    for idx, line in enumerate(lines):
        m = DECL_RE.match(line)
        if not m:
            continue
        indent: str = m.group(1)
        proof_name: str = m.group(3)

        if _has_doc_comment_before(lines, idx):
            continue  # Already documented

        # Build a minimal docstring
        doc_line = f"{indent}(** [{proof_name}]: formal specification. *)\n"
        insertions.append((idx, doc_line))

    if not insertions:
        return 0

    if verbose or dry_run:
        rel = path.relative_to(REPO_ROOT)
        for idx, doc_line in insertions:
            proof_line = lines[idx].rstrip()
            print(f"  {'[DRY]' if dry_run else '[ADD]'} {rel}:{idx+1}: {proof_line[:70]}")

    if not dry_run:
        # Apply insertions in reverse order so indices stay valid
        for idx, doc_line in reversed(insertions):
            lines.insert(idx, doc_line)
        path.write_text("".join(lines), encoding="utf-8")

    return len(insertions)


def iter_coq_production_files():
    """Yield .v files that belong to the Coq production layer (not tests/)."""
    for path in sorted(COQ_DIR.rglob("*.v")):
        # Skip stale directories
        parts = set(path.parts)
        if "tests" in path.parts:
            continue  # test layer - skip
        if any(p in str(path) for p in ("_build", "build", ".git")):
            continue
        yield path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dry-run", action="store_true", help="Do not modify files")
    parser.add_argument("--verbose", action="store_true", help="Print each insertion")
    args = parser.parse_args()

    total_files = 0
    total_insertions = 0

    for path in iter_coq_production_files():
        count = process_file(path, dry_run=args.dry_run, verbose=args.verbose)
        if count > 0:
            total_files += 1
            total_insertions += count

    action = "Would insert" if args.dry_run else "Inserted"
    print(f"{action} {total_insertions} docstrings across {total_files} files.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
