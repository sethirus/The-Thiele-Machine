#!/usr/bin/env python3
"""Build and verify the frozen Item 1.1 citation inventory.

The inventory is occurrence based. It never treats an unresolved code token
as proof that the token is not a theorem. Every ambiguous proof name needs an
explicit binding. Names in a ``Key results`` list and LaTeX theorem labels
must resolve to proof declarations.

This script extracts documentation and Coq source facts. It does not decide
the event-genericity class of a theorem.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import re
import subprocess
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
ARCHIVED_RELEASE = Path(
    "research/rounds/inputs/2026-09-30-v3.4.0-release-notes.md"
)
PRIOR_PART1_RECORD = Path("research/rounds/2026-09-30-part1-event-swap.md")
DEFAULT_BINDINGS = Path(
    "research/rounds/2026-09-30-part1-item1.1-round2-bindings.tsv"
)
DEFAULT_LABELS = Path(
    "research/rounds/2026-09-30-part1-item1.1-round2-labels.tsv"
)
DEFAULT_MANIFEST = Path(
    "research/rounds/2026-09-30-part1-item1.1-round2-sources.tsv"
)
DEFAULT_OCCURRENCES = Path(
    "research/rounds/2026-09-30-part1-item1.1-round2-occurrences.tsv"
)
DEFAULT_PREDICTIONS = Path(
    "research/rounds/2026-09-30-part1-item1.1-round2-predictions.tsv"
)

DECL_RE = re.compile(
    r"^\s*(?:#\[[^\]]*\]\s*)?"
    r"(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+|Private\s+)?"
    r"(?:Program\s+)?"
    r"(Theorem|Lemma|Corollary|Fact|Proposition|Remark|Property|Example)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)"
)
NONPROOF_DECL_RE = re.compile(
    r"^\s*(?:#\[[^\]]*\]\s*)?"
    r"(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+|Private\s+)?"
    r"(?:Program\s+)?"
    r"(Definition|Fixpoint|CoFixpoint|Inductive|CoInductive|Record|Class|"
    r"Instance|Axiom|Parameter|Conjecture)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)"
)
MODULE_OPEN_RE = re.compile(
    r"^\s*Module\s+(Type\s+|Import\s+|Export\s+)?"
    r"([A-Za-z_][A-Za-z0-9_']*)(\s*\([^.]*(?:\.[^)]*)?\))?\s*([:.<])"
)
MODULE_END_RE = re.compile(r"^\s*End\s+([A-Za-z_][A-Za-z0-9_']*)\s*\.\s*$")
IDENT_RE = re.compile(
    r"(?<![A-Za-z0-9_.'])[A-Za-z][A-Za-z0-9_.']*(?![A-Za-z0-9_.'])"
)


@dataclass(frozen=True)
class ProofDecl:
    identity: str
    name: str
    kind: str
    source: str
    line: int
    addressability: str


@dataclass(frozen=True)
class RawOccurrence:
    source: str
    line: int
    syntax: str
    raw_span: str
    token: str


@dataclass(frozen=True)
class TypedOccurrence:
    source: str
    line: int
    syntax: str
    raw_span: str
    token: str
    occurrence_kind: str
    declaration_kind: str
    identity: str
    resolution: str


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _git_tracked(root: Path) -> set[str]:
    result = subprocess.run(
        ["git", "ls-files", "-z"],
        cwd=root,
        check=True,
        stdout=subprocess.PIPE,
    )
    return {item.decode() for item in result.stdout.split(b"\0") if item}


def discover_sources(root: Path = ROOT) -> list[Path]:
    """Return the literal human-facing claim surface for Item 1.1.

    Generated reports, unrelated process records, fixtures, and the derived
    theorem meanings registry are excluded. The prior Part 1 claim record is
    included because it cites proof ingredients that the published documents
    do not name. The archived release draft is an explicit input because it
    originated outside the repository.
    """

    tracked = _git_tracked(root)
    selected: set[str] = set()
    for rel in tracked:
        path = Path(rel)
        if len(path.parts) == 1:
            if path.suffix == ".md" and path.name != "INQUISITOR_REPORT.md":
                selected.add(rel)
            elif rel in {"CITATION.cff", "THIELE_MACHINE.txt"}:
                selected.add(rel)
        elif path.parts[0] == ".github" and path.suffix == ".md":
            selected.add(rel)
        elif path.parts[0] == "coq" and path.name == "README.md":
            selected.add(rel)
        elif path.parts[0] == "docs" and path.suffix == ".md":
            if rel != "docs/THEOREM_MEANINGS.md":
                selected.add(rel)
        elif path.parts[0] == "examples" and path.name == "README.md":
            selected.add(rel)
        elif rel in {
            "monograph/monograph.tex",
            "monograph/thiele_machine_math_spec.tex",
        }:
            selected.add(rel)

    archived = root / ARCHIVED_RELEASE
    if not archived.exists():
        raise ValueError(f"missing archived release input: {ARCHIVED_RELEASE}")
    selected.add(ARCHIVED_RELEASE.as_posix())
    prior_record = root / PRIOR_PART1_RECORD
    if not prior_record.exists():
        raise ValueError(f"missing prior Part 1 record: {PRIOR_PART1_RECORD}")
    selected.add(PRIOR_PART1_RECORD.as_posix())
    return [Path(rel) for rel in sorted(selected)]


def _logical_mappings(root: Path) -> list[tuple[Path, str]]:
    out: list[tuple[Path, str]] = []
    coq_root = root / "coq"
    for line in (coq_root / "_CoqProject").read_text().splitlines():
        match = re.match(r"^-[RQ]\s+(\S+)\s+(\S+)\s*$", line.strip())
        if match:
            out.append(((coq_root / match.group(1)).resolve(), match.group(2)))
    out.sort(key=lambda item: len(item[0].parts), reverse=True)
    return out


def _logical_module(
    root: Path, rel_in_coq: Path, mappings: list[tuple[Path, str]]
) -> str:
    stem = rel_in_coq.stem
    abs_dir = (root / "coq" / rel_in_coq).resolve().parent
    for physical, logical in mappings:
        try:
            middle = abs_dir.relative_to(physical)
        except ValueError:
            continue
        return ".".join([logical, *middle.parts, stem])
    return stem


def _strip_comments_preserve_lines(text: str) -> str:
    out: list[str] = []
    index = 0
    depth = 0
    while index < len(text):
        if text[index : index + 2] == "(*":
            depth += 1
            out.extend("  ")
            index += 2
        elif depth and text[index : index + 2] == "*)":
            depth -= 1
            out.extend("  ")
            index += 2
        elif depth:
            out.append("\n" if text[index] == "\n" else " ")
            index += 1
        else:
            out.append(text[index])
            index += 1
    return "".join(out)


def proof_declarations(root: Path = ROOT) -> dict[str, ProofDecl]:
    coq_root = root / "coq"
    mappings = _logical_mappings(root)
    sources: list[Path] = []
    for raw in (coq_root / "_CoqProject").read_text().splitlines():
        line = raw.strip()
        if line.endswith(".v") and not line.startswith("-"):
            path = coq_root / line
            if path.exists():
                sources.append(Path(line))

    declarations: dict[str, ProofDecl] = {}
    for rel in sources:
        module = _logical_module(root, rel, mappings)
        source_path = coq_root / rel
        clean = _strip_comments_preserve_lines(source_path.read_text(errors="replace"))
        stack: list[tuple[str, bool, str]] = []
        for line_number, line in enumerate(clean.splitlines(), 1):
            end = MODULE_END_RE.match(line)
            if end:
                if stack and stack[-1][0] == end.group(1):
                    stack.pop()
                continue
            if re.match(
                r"^\s*Module\s+[A-Za-z_][A-Za-z0-9_']*\s*:=\s*.*\.\s*$",
                line,
            ):
                continue
            opened = MODULE_OPEN_RE.match(line)
            if opened:
                module_kind = (opened.group(1) or "").strip()
                name = opened.group(2)
                parameters = opened.group(3)
                if module_kind == "Type":
                    stack.append((name, False, "module_type"))
                elif parameters is not None:
                    stack.append((name, False, "functor"))
                else:
                    stack.append((name, True, "addressable"))
                continue
            declared = DECL_RE.match(line)
            if not declared:
                continue
            kind, name = declared.groups()
            local = ".".join([*(frame[0] for frame in stack), name])
            identity = f"{module}.{local}"
            blockers = [frame[2] for frame in stack if not frame[1]]
            addressability = blockers[-1] if blockers else "addressable"
            entry = ProofDecl(
                identity=identity,
                name=name,
                kind=kind,
                source=f"coq/{rel.as_posix()}",
                line=line_number,
                addressability=addressability,
            )
            if identity in declarations:
                raise ValueError(f"duplicate proof identity: {identity}")
            declarations[identity] = entry
    return declarations


def nonproof_declarations(root: Path = ROOT) -> dict[str, list[str]]:
    out: dict[str, list[str]] = defaultdict(list)
    for path in sorted((root / "coq").rglob("*.v")):
        rel = path.relative_to(root).as_posix()
        if rel.startswith(("coq/archive/", "coq/vendor/")):
            continue
        clean = _strip_comments_preserve_lines(path.read_text(errors="replace"))
        for line_number, line in enumerate(clean.splitlines(), 1):
            match = NONPROOF_DECL_RE.match(line)
            if match:
                kind, name = match.groups()
                out[name].append(f"{kind}@{rel}:{line_number}")
    return dict(out)


def _line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def _tokens(raw: str) -> Iterable[str]:
    normalized = raw.replace(r"\allowbreak{}", "").replace(r"\_", "_")
    yield from IDENT_RE.findall(normalized)


def raw_occurrences(path: Path, source_name: str) -> list[RawOccurrence]:
    text = path.read_text(errors="replace")
    found: list[RawOccurrence] = []

    def collect(syntax: str, match: re.Match[str], group: int = 1) -> None:
        raw = match.group(group).strip()
        for token in _tokens(raw):
            found.append(
                RawOccurrence(
                    source=source_name,
                    line=_line_number(text, match.start()),
                    syntax=syntax,
                    raw_span=raw,
                    token=token,
                )
            )

    patterns = (
        ("markdown_code", re.compile(r"(?<!`)`([^`\n]+)`(?!`)")),
        (
            "latex_code",
            re.compile(r"\\(?:code|texttt)\{((?:\\allowbreak\{\}|[^{}])*)\}"),
        ),
        (
            "latex_small",
            re.compile(
                r"\\textit\{\\small\s+((?:\\allowbreak\{\}|[^{}])*)\}"
            ),
        ),
    )
    for syntax, pattern in patterns:
        for match in pattern.finditer(text):
            collect(syntax, match)

    for match in re.finditer(r"Key results:\s*(.*)$", text, re.MULTILINE):
        raw = re.sub(r"\s*\(\+\d+ more\)\s*$", "", match.group(1)).strip()
        synthetic = RawOccurrence(
            source=source_name,
            line=_line_number(text, match.start()),
            syntax="key_results",
            raw_span=raw,
            token="",
        )
        for token in _tokens(raw):
            found.append(
                RawOccurrence(
                    source=synthetic.source,
                    line=synthetic.line,
                    syntax=synthetic.syntax,
                    raw_span=synthetic.raw_span,
                    token=token,
                )
            )

    for match in re.finditer(
        r"\\label\{thm:([A-Za-z_][A-Za-z0-9_']*)\}", text
    ):
        collect("latex_theorem_label", match)

    return found


def load_bindings(path: Path) -> dict[str, str]:
    with path.open(newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        expected = {"raw_name", "logical_identity", "reason"}
        if set(reader.fieldnames or ()) != expected:
            raise ValueError(f"binding columns must be {sorted(expected)}")
        out: dict[str, str] = {}
        for row in reader:
            raw = row["raw_name"]
            if raw in out:
                raise ValueError(f"duplicate binding: {raw}")
            out[raw] = row["logical_identity"]
    return out


def load_label_decisions(path: Path) -> dict[str, tuple[str, list[str]]]:
    with path.open(newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        expected = {"raw_name", "decision", "logical_identities", "reason"}
        if set(reader.fieldnames or ()) != expected:
            raise ValueError(f"label columns must be {sorted(expected)}")
        out: dict[str, tuple[str, list[str]]] = {}
        for row in reader:
            raw = row["raw_name"]
            if raw in out:
                raise ValueError(f"duplicate label decision: {raw}")
            decision = row["decision"]
            identities = [item for item in row["logical_identities"].split(";") if item]
            if decision not in {"proof", "aggregate"}:
                raise ValueError(f"invalid label decision: {raw} -> {decision}")
            if decision == "proof" and len(identities) != 1:
                raise ValueError(f"proof label needs one identity: {raw}")
            if decision == "aggregate" and len(identities) < 2:
                raise ValueError(f"aggregate label needs at least two identities: {raw}")
            out[raw] = (decision, identities)
    return out


def _suffix_index(declarations: dict[str, ProofDecl]) -> dict[str, set[str]]:
    out: dict[str, set[str]] = defaultdict(set)
    for identity in declarations:
        parts = identity.split(".")
        for start in range(len(parts)):
            out[".".join(parts[start:])].add(identity)
    return dict(out)


def type_occurrences(
    root: Path, bindings_path: Path
) -> tuple[list[TypedOccurrence], dict[str, ProofDecl], list[str]]:
    declarations = proof_declarations(root)
    nonproof = nonproof_declarations(root)
    suffixes = _suffix_index(declarations)
    bindings = load_bindings(root / bindings_path)
    label_decisions = load_label_decisions(root / DEFAULT_LABELS)
    errors: list[str] = []
    used_label_decisions: set[str] = set()
    for raw, identity in bindings.items():
        if identity not in declarations:
            errors.append(f"binding target is not a proof declaration: {raw} -> {identity}")
    for raw, (_, identities) in label_decisions.items():
        for identity in identities:
            if identity not in declarations:
                errors.append(
                    f"label target is not a proof declaration: {raw} -> {identity}"
                )

    typed: list[TypedOccurrence] = []
    for rel in discover_sources(root):
        for occurrence in raw_occurrences(root / rel, rel.as_posix()):
            token = occurrence.token
            bound = bindings.get(token)
            candidates = suffixes.get(bound or token, set())
            if len(candidates) == 1:
                identity = next(iter(candidates))
                declaration = declarations[identity]
                typed.append(
                    TypedOccurrence(
                        source=occurrence.source,
                        line=occurrence.line,
                        syntax=occurrence.syntax,
                        raw_span=occurrence.raw_span,
                        token=token,
                        occurrence_kind="proof",
                        declaration_kind=declaration.kind,
                        identity=identity,
                        resolution="explicit_binding" if bound else "unique_suffix",
                    )
                )
            elif len(candidates) > 1:
                errors.append(
                    f"ambiguous proof token {occurrence.source}:{occurrence.line}: "
                    f"{token} -> {sorted(candidates)}"
                )
            elif occurrence.syntax == "latex_theorem_label" and token in label_decisions:
                decision, identities = label_decisions[token]
                used_label_decisions.add(token)
                for identity in identities:
                    declaration = declarations[identity]
                    typed.append(
                        TypedOccurrence(
                            source=occurrence.source,
                            line=occurrence.line,
                            syntax=occurrence.syntax,
                            raw_span=occurrence.raw_span,
                            token=token,
                            occurrence_kind="proof",
                            declaration_kind=declaration.kind,
                            identity=identity,
                            resolution=f"label_{decision}",
                        )
                    )
            elif occurrence.syntax in {"key_results", "latex_theorem_label"}:
                errors.append(
                    f"unknown theorem-context token {occurrence.source}:"
                    f"{occurrence.line}: {token}"
                )
            else:
                declarations_found = nonproof.get(token, [])
                typed.append(
                    TypedOccurrence(
                        source=occurrence.source,
                        line=occurrence.line,
                        syntax=occurrence.syntax,
                        raw_span=occurrence.raw_span,
                        token=token,
                        occurrence_kind="nonproof",
                        declaration_kind=(
                            ",".join(sorted({item.split("@", 1)[0] for item in declarations_found}))
                            if declarations_found
                            else "nonproof_token"
                        ),
                        identity="",
                        resolution=(
                            ";".join(sorted(declarations_found))
                            if declarations_found
                            else "excluded_nonproof_token"
                        ),
                    )
                )

    unused_label_decisions = sorted(set(label_decisions) - used_label_decisions)
    if unused_label_decisions:
        errors.append(f"unused label decisions: {unused_label_decisions}")

    # The binding table also freezes bindings inherited from the theorem
    # meanings registry. Some names do not occur on the selected claim surface
    # in this round, but their targets still have to remain valid declarations.
    typed.sort(
        key=lambda row: (
            row.source,
            row.line,
            row.syntax,
            row.raw_span,
            row.token,
            row.identity,
        )
    )
    return typed, declarations, errors


def _tsv(rows: Iterable[Iterable[object]]) -> str:
    def clean(value: object) -> str:
        return str(value).replace("\t", r"\t").replace("\n", r"\n")

    return "\n".join("\t".join(clean(value) for value in row) for row in rows) + "\n"


def render_manifest(root: Path = ROOT) -> str:
    rows: list[list[str]] = [["path", "sha256", "role"]]
    for rel in discover_sources(root):
        role = "external_release_input" if rel == ARCHIVED_RELEASE else "claim_document"
        rows.append([rel.as_posix(), sha256(root / rel), role])
    return _tsv(rows)


def render_occurrences(root: Path, bindings_path: Path) -> tuple[str, list[str]]:
    typed, _, errors = type_occurrences(root, bindings_path)
    rows: list[list[object]] = [[
        "source_path",
        "line",
        "syntax",
        "raw_span",
        "token",
        "occurrence_kind",
        "declaration_kind",
        "logical_identity",
        "resolution",
    ]]
    for item in typed:
        rows.append([
            item.source,
            item.line,
            item.syntax,
            item.raw_span,
            item.token,
            item.occurrence_kind,
            item.declaration_kind,
            item.identity,
            item.resolution,
        ])
    return _tsv(rows), errors


def render_prediction_template(
    root: Path, bindings_path: Path
) -> tuple[str, list[str]]:
    typed, declarations, errors = type_occurrences(root, bindings_path)
    universe = sorted({item.identity for item in typed if item.occurrence_kind == "proof"})
    rows: list[list[object]] = [[
        "logical_identity",
        "declaration_file",
        "declaration_line",
        "declaration_kind",
        "addressability",
        "predicted_class",
        "prediction_basis",
    ]]
    for identity in universe:
        declaration = declarations[identity]
        rows.append([
            identity,
            declaration.source,
            declaration.line,
            declaration.kind,
            declaration.addressability,
            "",
            "",
        ])
    return _tsv(rows), errors


def _read_text(root: Path, rel: Path) -> str:
    return (root / rel).read_text()


def verify(root: Path, bindings_path: Path) -> list[str]:
    errors: list[str] = []
    expected_manifest = render_manifest(root)
    expected_occurrences, scan_errors = render_occurrences(root, bindings_path)
    errors.extend(scan_errors)
    if _read_text(root, DEFAULT_MANIFEST) != expected_manifest:
        errors.append(f"source manifest drift: {DEFAULT_MANIFEST}")
    if _read_text(root, DEFAULT_OCCURRENCES) != expected_occurrences:
        errors.append(f"occurrence inventory drift: {DEFAULT_OCCURRENCES}")

    typed, _, more_errors = type_occurrences(root, bindings_path)
    errors.extend(more_errors)
    universe = sorted({item.identity for item in typed if item.occurrence_kind == "proof"})
    with (root / DEFAULT_PREDICTIONS).open(newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        rows = list(reader)
    predicted = [row["logical_identity"] for row in rows]
    if predicted != universe:
        errors.append("prediction universe differs from the occurrence universe")
    allowed = {"G", "C", "I", "M", "N"}
    invalid = [
        row["logical_identity"]
        for row in rows
        if row["predicted_class"] not in allowed or not row["prediction_basis"].strip()
    ]
    if invalid:
        errors.append(f"incomplete prediction rows: {invalid}")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "command",
        choices=("summary", "render-manifest", "render-occurrences", "render-template", "verify"),
    )
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--bindings", type=Path, default=DEFAULT_BINDINGS)
    args = parser.parse_args()
    root = args.root.resolve()

    if args.command == "render-manifest":
        sys.stdout.write(render_manifest(root))
        return 0
    if args.command == "render-occurrences":
        output, errors = render_occurrences(root, args.bindings)
        if errors:
            print("\n".join(errors), file=sys.stderr)
            return 1
        sys.stdout.write(output)
        return 0
    if args.command == "render-template":
        output, errors = render_prediction_template(root, args.bindings)
        if errors:
            print("\n".join(errors), file=sys.stderr)
            return 1
        sys.stdout.write(output)
        return 0
    if args.command == "verify":
        errors = verify(root, args.bindings)
        if errors:
            print("\n".join(errors), file=sys.stderr)
            return 1
        print("event-genericity inventory: verified")
        return 0

    typed, declarations, errors = type_occurrences(root, args.bindings)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    proof_rows = [item for item in typed if item.occurrence_kind == "proof"]
    nonproof_rows = [item for item in typed if item.occurrence_kind == "nonproof"]
    universe = {item.identity for item in proof_rows}
    unaddressable = {
        identity
        for identity in universe
        if declarations[identity].addressability != "addressable"
    }
    print(f"sources={len(discover_sources(root))}")
    print(f"proof_occurrences={len(proof_rows)}")
    print(f"nonproof_occurrences={len(nonproof_rows)}")
    print(f"proof_identities={len(universe)}")
    print(f"unaddressable_proof_identities={len(unaddressable)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
