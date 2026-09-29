"""Every theorem the documents cite has a plain-sentence entry.

docs/THEOREM_MEANINGS.md holds one sentence per cited theorem saying what
the Coq statement asserts. A cited name without an entry, or an entry for a
theorem that no longer exists, fails here.
"""

from __future__ import annotations

import re
from functools import lru_cache
from pathlib import Path

from build.probe.build_full_probe import parse_theorems, qualified_module_name

ROOT = Path(__file__).resolve().parents[1]
MEANINGS = ROOT / "docs" / "THEOREM_MEANINGS.md"
DOCS = [
    "README.md",
    "TECHNICAL_DISCLOSURE.md",
    "THIELE_MACHINE.txt",
    "monograph/monograph.tex",
    "monograph/thiele_machine_math_spec.tex",
]
ENTRY = re.compile(
    r"^- `([A-Za-z_][A-Za-z0-9_.']*)`(?: \(`([A-Za-z_][A-Za-z0-9_.']*)`\))?: \S",
    re.M,
)


@lru_cache(maxsize=1)
def project_theorems() -> set[str]:
    names: set[str] = set()
    for line in (ROOT / "coq" / "_CoqProject").read_text().splitlines():
        line = line.strip()
        if not line.endswith(".v") or line.startswith("-"):
            continue
        path = ROOT / "coq" / line
        if path.exists():
            module = qualified_module_name(Path(line))
            source = path.read_text(errors="ignore")
            # Examples are named proofs too; the receipt parser indexes
            # theorem declarations but deliberately omits this keyword.
            source = re.sub(r"^(\s*)Example(\s+)", r"\1Lemma\2", source, flags=re.M)
            parsed = parse_theorems(source)
            names.update(f"{module}.{name}" for name, _ in parsed["addressable"])
    return names


def citation_spans(text: str) -> list[str]:
    # The claim ledger uses textit with a small declaration, while tables
    # and prose use code, texttt, or Markdown code spans.
    text = text.replace(r"\allowbreak{}", "")
    return (
        re.findall(r"\\code\{([^}]*)\}", text)
        + re.findall(r"`([^`\s]+)`", text)
        + re.findall(r"\\texttt\{([^}]*)\}", text)
        + re.findall(r"\\textit\{\\small\s+([^}]*)\}", text)
    )


def citation_identifiers(text: str) -> set[str]:
    names = set()
    for span in citation_spans(text):
        span = span.replace("\\_", "_")
        for part in re.split(r"[\s,/]+", span):
            part = part.strip(".()[]")
            if re.fullmatch(r"[A-Za-z][A-Za-z0-9_.']*", part):
                names.add(part)
    return names


def cited_names() -> dict[str, set[str]]:
    cited: dict[str, set[str]] = {}
    for doc in DOCS:
        for name in citation_identifiers((ROOT / doc).read_text()):
            cited.setdefault(name, set()).add(doc)
    return cited


def entries() -> list[tuple[str, str]]:
    return ENTRY.findall(MEANINGS.read_text())


def candidates(name: str, theorems: set[str]) -> set[str]:
    return {full for full in theorems if full == name or full.endswith("." + name)}


def meanings_by_full_name() -> dict[str, str]:
    out = {}
    for name, binding in entries():
        matches = candidates(binding or name, project_theorems())
        assert len(matches) == 1, f"meaning {name} needs one source theorem: {sorted(matches)}"
        out[next(iter(matches))] = name
    return out


def test_every_cited_theorem_has_a_meaning() -> None:
    theorems = project_theorems()
    have = meanings_by_full_name()
    bindings = {name: binding for name, binding in entries() if binding}
    missing = []
    for name, docs in cited_names().items():
        matches = candidates(name, theorems)
        if not matches:
            continue  # Instructions, record fields, and definitions are not theorems.
        if len(matches) > 1 and name in bindings:
            matches = candidates(bindings[name], theorems)
        if len(matches) != 1 or not matches <= have.keys():
            missing.append(f"{name} (cited in {', '.join(sorted(docs))}): {sorted(matches)}")
    missing.sort()
    assert not missing, "cited theorems with no entry in docs/THEOREM_MEANINGS.md:\n" + "\n".join(missing)


def test_every_meaning_names_a_theorem() -> None:
    theorems = project_theorems()
    stale = sorted(name for name, binding in entries() if not candidates(binding or name, theorems))
    assert not stale, "entries naming no Coq theorem in the project:\n" + "\n".join(stale)


def test_no_duplicate_meanings() -> None:
    seen: set[str] = set()
    dup = sorted({name for name, _ in entries() if name in seen or seen.add(name)})
    assert not dup, "duplicate entries: " + ", ".join(dup)


def test_meaning_resolution_keeps_module_identity() -> None:
    names = {"Kernel.First.bound", "Kernel.Second.bound", "Other.First.bound"}
    assert candidates("bound", names) == names
    assert candidates("First.bound", names) == {"Kernel.First.bound", "Other.First.bound"}
    assert candidates("Kernel.Second.bound", names) == {"Kernel.Second.bound"}
    assert candidates("Kernel.Missing.bound", names) == set()


def test_claim_ledger_and_wrapped_citations_are_seen() -> None:
    text = r"\textit{\small first\_theorem / second\_theorem} \code{Kernel.\allowbreak{}M.third\_theorem}"
    assert citation_spans(text) == [r"Kernel.M.third\_theorem", r"first\_theorem / second\_theorem"]


def test_theorem_identifiers_need_not_contain_underscores() -> None:
    assert citation_identifiers(r"\code{Kernel.M.sound} `complete`") == {
        "Kernel.M.sound", "complete"
    }
