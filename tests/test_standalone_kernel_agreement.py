"""The standalone file and the modular kernel define the same VM.

coq/ThieleMachineComplete.v carries its own copy of the VM so it can be read
as one file. That copy is not proved equal to the kernel's inside Coq; the two
state types are distinct inductives. This test is the agreement check instead:
every definition reachable from the kernel's vm_apply, instruction_cost,
is_cert_setterb, VMState, and vm_instruction must appear in the standalone
file with the same text, after comments, whitespace, and module qualifiers are
removed. vm_instruction is compared by constructor names and argument types,
because binder names do not change the type.

A tested edge, named as one: textual identity of definitions, not a Coq
theorem.
"""
from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
COQ = ROOT / "coq"
STANDALONE = COQ / "ThieleMachineComplete.v"
KERNEL_SOURCES = [
    COQ / "kernel/foundation/VMState.v",
    COQ / "kernel/foundation/VMStep.v",
    COQ / "kernel/foundation/SimulationProof.v",
]
ROOTS = ["vm_apply", "instruction_cost", "is_cert_setterb", "VMState", "vm_instruction"]
DEF_RE = re.compile(
    r"(?m)^\s*(?:Definition|Fixpoint|Inductive|Record)\s+(\w+)(.*?)(?=\.\s*\n)", re.S
)
QUALIFIER_RE = re.compile(r"\bVMStep\.|\bVMState\.")


def _strip_comments(text: str) -> str:
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            i += 2
            continue
        if depth and text.startswith("*)", i):
            depth -= 1
            i += 2
            continue
        if not depth:
            out.append(text[i])
        i += 1
    return "".join(out)


def _definitions(paths: list[Path]) -> dict[str, str]:
    defs: dict[str, str] = {}
    for path in paths:
        for match in DEF_RE.finditer(_strip_comments(path.read_text(encoding="utf-8"))):
            body = QUALIFIER_RE.sub("", " ".join(match.group(2).split()))
            defs.setdefault(match.group(1), body)
    return defs


def _reachable(defs: dict[str, str]) -> set[str]:
    seen: set[str] = set()
    todo = list(ROOTS)
    while todo:
        name = todo.pop()
        if name in seen or name not in defs:
            continue
        seen.add(name)
        for word in set(re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", defs[name])):
            if word in defs and word not in seen:
                todo.append(word)
    return seen


def _constructor_signatures(body: str) -> list[tuple[str, list[str]]]:
    """Constructor names with argument types, binder names dropped."""
    signatures = []
    for ctor in re.split(r"\|\s*", body)[1:]:
        name = ctor.split()[0]
        types = []
        for group in re.findall(r"\(([^()]*)\)", ctor):
            binders, _, typ = group.partition(":")
            types.extend([typ.strip()] * len(binders.split()))
        signatures.append((name, types))
    return signatures


def test_every_reachable_kernel_definition_is_in_the_standalone_file() -> None:
    kernel = _definitions(KERNEL_SOURCES)
    standalone = _definitions([STANDALONE])
    missing = sorted(n for n in _reachable(kernel) if n not in standalone)
    assert not missing, f"standalone file lacks kernel definitions: {missing}"


def test_reachable_definitions_have_identical_text() -> None:
    kernel = _definitions(KERNEL_SOURCES)
    standalone = _definitions([STANDALONE])
    differing = sorted(
        n
        for n in _reachable(kernel)
        if n != "vm_instruction" and n in standalone and standalone[n] != kernel[n]
    )
    assert not differing, f"standalone and kernel definitions differ: {differing}"


def test_instruction_sets_agree_up_to_binder_names() -> None:
    kernel = _definitions(KERNEL_SOURCES)["vm_instruction"]
    standalone = _definitions([STANDALONE])["vm_instruction"]
    k_sig = _constructor_signatures(kernel)
    s_sig = _constructor_signatures(standalone)
    assert len(k_sig) == 51
    assert s_sig == k_sig
