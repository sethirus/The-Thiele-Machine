#!/usr/bin/env python3
"""
Generate README.md files for Coq proof directories that lack them.

Scans coq/ subdirectories for .v files, extracts theorem/lemma names,
counts admits, and generates a README matching the project style.

Idempotent: skips directories that already have a README.md.
"""

import os
import re
import sys
from pathlib import Path
from typing import Dict, List, Tuple

COQ_ROOT = Path("/workspaces/The-Thiele-Machine/coq")

# Directories to skip entirely
SKIP_DIRS = {
    COQ_ROOT,                          # root coq/ already has README
    COQ_ROOT / "physics_exploration",  # already has README
    COQ_ROOT / "quantum_derivation",   # already has README
    COQ_ROOT / ".benchmarks",
    COQ_ROOT / "artifacts",
    COQ_ROOT / "scripts",
    COQ_ROOT / "patches",
}

# Regex to extract named declarations
DECL_RE = re.compile(
    r"^\s*(Theorem|Lemma|Definition|Fixpoint|Inductive|Record|Class|Instance)"
    r"\s+(\w+)",
    re.MULTILINE,
)

# Regex to count Admitted.
ADMITTED_RE = re.compile(r"\bAdmitted\s*\.", re.MULTILINE)


def dir_title(dir_path: Path) -> str:
    """Convert a directory path to a human-readable title.

    E.g. coq/kernel_toe -> 'Kernel TOE'
         coq/thielemachine/coqproofs -> 'Thiele Machine - Coq Proofs'
    """
    parts = dir_path.relative_to(COQ_ROOT).parts
    titles = []
    for part in parts:
        # Convert snake_case / lowercase to Title Case with special handling
        replacements = {
            "coqproofs": "Coq Proofs",
            "thielemachine": "Thiele Machine",
            "thieleuniversal": "Thiele Universal",
            "thiele_manifold": "Thiele Manifold",
            "kernel_toe": "Kernel Theory of Everything",
            "modular_proofs": "Modular Proofs",
            "shor_primitives": "Shor Algorithm Primitives",
            "self_reference": "Self Reference",
            "spacetime_projection": "Spacetime Projection",
            "project_cerberus": "Project Cerberus",
            "test_vscoq": "VSCoq Tests",
            "nofi": "No-Free-Insight (NoFI)",
            "catnet": "Categorical Networks",
            "physics": "Physics Models",
            "bridge": "Bridge Embeddings",
            "theory": "Core Theory",
            "thermodynamic": "Thermodynamic Proofs",
            "tests": "Coq Tests",
            "kernel": "Kernel",
            "isomorphism": "Isomorphism",
            "spacetime": "Spacetime",
            "verification": "Verification",
            "modular": "Modular",
        }
        if part in replacements:
            titles.append(replacements[part])
        else:
            titles.append(part.replace("_", " ").title())
    return " - ".join(titles)


def infer_purpose(dir_path: Path, v_files: List[Path],
                  all_decls: Dict[str, List[Tuple[str, str]]]) -> str:
    """Generate a brief purpose description from directory name and contents."""
    name = dir_path.relative_to(COQ_ROOT).parts[0]
    # Collect all declaration names for keyword analysis
    all_names = []
    for decls in all_decls.values():
        all_names.extend(d[1] for d in decls)
    names_lower = " ".join(n.lower() for n in all_names)

    purposes = {
        "kernel": "Core structural constraint proofs, optimization bounds, and bisimulation results for the Thiele Machine kernel.",
        "kernel_toe": "Theory of Everything cone proofs and no-go theorems derived from kernel axioms.",
        "thielemachine": "Main Thiele Machine proofs including Bell inequality verification, deliverables, and machine semantics.",
        "thieleuniversal": "Universal Turing Machine simulation proofs demonstrating Thiele Machine universality.",
        "modular_proofs": "Modular encoding, Minsky machine simulation, and Turing machine reduction proofs.",
        "physics": "Physics model formalizations including Landauer bridge and wave/discrete duality.",
        "bridge": "Embedding proofs connecting external frameworks (BoxWorld, quantum, entropy, causality) to the kernel.",
        "nofi": "No-Free-Insight abstraction proofs establishing fundamental limits on information extraction.",
        "catnet": "Categorical network proofs formalizing compositional structure.",
        "isomorphism": "Universe isomorphism proofs establishing structural equivalences.",
        "self_reference": "Self-reference exploration proofs examining fixed-point and diagonal arguments.",
        "spacetime": "Spacetime structure proofs derived from partition dynamics.",
        "spacetime_projection": "Spacetime projection proofs connecting abstract partitions to geometric structure.",
        "thiele_manifold": "Thiele manifold proofs bridging abstract machine theory to physical constants and geometry.",
        "shor_primitives": "Shor algorithm primitive proofs including modular arithmetic, period finding, and Euclidean algorithms.",
        "project_cerberus": "Project Cerberus formal verification proofs.",
        "test_vscoq": "VSCoq integration test proofs.",
        "theory": "Core theoretical framework proofs including separation, universality, no-free-lunch, and genesis theorems.",
        "thermodynamic": "Thermodynamic formalization proofs connecting information-theoretic costs to physical thermodynamics.",
        "tests": "Coq test files for verification and necessity checking.",
    }

    return purposes.get(name, f"Formal Coq proofs for the {name} module.")


def file_description(filename: str, decls: List[Tuple[str, str]]) -> str:
    """Generate a short description for a .v file based on its name and declarations."""
    stem = filename.replace(".v", "")
    # Convert CamelCase to spaced words
    words = re.sub(r"(?<=[a-z])(?=[A-Z])", " ", stem)
    words = words.replace("_", " ")

    # Build description from key declarations
    theorems = [d[1] for d in decls if d[0] in ("Theorem", "Lemma")]
    defs = [d[1] for d in decls if d[0] in ("Definition", "Fixpoint")]
    types = [d[1] for d in decls if d[0] in ("Inductive", "Record", "Class")]

    parts = []
    if types:
        parts.append(f"Defines: {', '.join(types[:3])}")
        if len(types) > 3:
            parts[-1] += f" (+{len(types)-3} more)"
    if theorems:
        parts.append(f"Key results: {', '.join(theorems[:3])}")
        if len(theorems) > 3:
            parts[-1] += f" (+{len(theorems)-3} more)"
    if not parts and defs:
        parts.append(f"Definitions: {', '.join(defs[:3])}")
        if len(defs) > 3:
            parts[-1] += f" (+{len(defs)-3} more)"

    desc = words
    if parts:
        desc += " - " + "; ".join(parts)
    return desc


def parse_v_file(filepath: Path) -> Tuple[List[Tuple[str, str]], int]:
    """Parse a .v file returning (declarations, admit_count)."""
    try:
        content = filepath.read_text(encoding="utf-8", errors="replace")
    except Exception:
        return [], 0

    decls = DECL_RE.findall(content)
    admits = len(ADMITTED_RE.findall(content))
    return decls, admits


def generate_readme(dir_path: Path, v_files: List[Path]) -> str:
    """Generate README.md content for a directory."""
    all_decls: Dict[str, List[Tuple[str, str]]] = {}
    all_admits: Dict[str, int] = {}

    for vf in sorted(v_files):
        decls, admits = parse_v_file(vf)
        all_decls[vf.name] = decls
        all_admits[vf.name] = admits

    title = dir_title(dir_path)
    purpose = infer_purpose(dir_path, v_files, all_decls)

    lines = []
    lines.append(f"# {title}")
    lines.append("")
    lines.append(f"**Mission:** {purpose}")
    lines.append("")

    # Structure section
    lines.append("## Structure")
    lines.append("")
    for vf in sorted(v_files):
        desc = file_description(vf.name, all_decls[vf.name])
        lines.append(f"- `{vf.name}` - {desc}")
    lines.append("")

    # Verification status table
    lines.append("## Verification Status")
    lines.append("")
    lines.append("| File | Admits | Status |")
    lines.append("|:---|:---:|:---:|")
    for vf in sorted(v_files):
        admits = all_admits[vf.name]
        status = "\u2705" if admits == 0 else f"\u274c ({admits} admits)"
        lines.append(f"| `{vf.name}` | {admits} | {status} |")
    lines.append("")

    total_admits = sum(all_admits.values())
    if total_admits == 0:
        lines.append(f"**Result:** All {len(v_files)} files verified with 0 admits.")
    else:
        lines.append(f"**Result:** {total_admits} total admits across {len(v_files)} files.")
    lines.append("")

    return "\n".join(lines)


def find_proof_dirs() -> List[Path]:
    """Find all directories under coq/ that contain .v files."""
    dirs = set()
    for vf in COQ_ROOT.rglob("*.v"):
        dirs.add(vf.parent)
    return sorted(dirs)


def main():
    generated = []
    skipped = []

    for dir_path in find_proof_dirs():
        # Check skip list
        if dir_path in SKIP_DIRS:
            skipped.append((dir_path, "in skip list"))
            continue

        # Check if any ancestor is in skip list (for .benchmarks, artifacts, etc.)
        skip = False
        for skip_dir in SKIP_DIRS:
            try:
                dir_path.relative_to(skip_dir)
                if skip_dir != COQ_ROOT:
                    skip = True
                    break
            except ValueError:
                pass
        if skip:
            skipped.append((dir_path, "under skipped parent"))
            continue

        readme_path = dir_path / "README.md"
        if readme_path.exists():
            skipped.append((dir_path, "README.md already exists"))
            continue

        # Collect .v files in this directory (not recursively)
        v_files = sorted(dir_path.glob("*.v"))
        if not v_files:
            skipped.append((dir_path, "no .v files"))
            continue

        content = generate_readme(dir_path, v_files)
        readme_path.write_text(content, encoding="utf-8")
        generated.append(dir_path)
        print(f"  Generated: {readme_path}")

    print(f"\nSummary: {len(generated)} READMEs generated, {len(skipped)} directories skipped.")
    for d, reason in skipped:
        print(f"  Skipped {d.relative_to(COQ_ROOT)}: {reason}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
