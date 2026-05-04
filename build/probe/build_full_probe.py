#!/usr/bin/env python3
"""Generate a Coq probe that runs Print Assumptions against every directly
addressable proof-bearing declaration in every .v file we made.

We track Module/Module Type/Functor nesting:
- "Module M." (plain) -> push M as addressable
- "Module M : SIG." or "Module M <: SIG." -> push M as addressable
- "Module M (X : SIG)." -> push M as UNADDRESSABLE (functor body)
- "Module Type M." -> push M as UNADDRESSABLE (signature)
- "Module M := X." (alias, single line) -> no push

Theorems inside an unaddressable frame cannot be probed via their declared
name; they are recorded in the inventory under a separate list so the user
knows about them. (For functors that are instantiated elsewhere, the
instantiated names ARE addressable and will be probed naturally as part of
the file containing the instantiation.)
"""
import re
import json
from pathlib import Path

ROOT = Path("/workspaces/The-Thiele-Machine")
BUILD = ROOT / "build" / "probe"
BUILD.mkdir(parents=True, exist_ok=True)

NS_MAP = [
    ("kernel", "Kernel"),
    ("nofi", "NoFI"),
    ("kami_hw", "KamiHW"),
    ("spacetime", "Spacetime"),
    ("thielemachine", "ThieleMachine"),
    ("physics", "Physics"),
    ("self_reference", "SelfReference"),
    ("thiele_manifold", "ThieleManifold"),
    ("thermodynamic", "Thermodynamic"),
    ("tests", "Tests"),
]

PROOF_KINDS = ("Theorem", "Lemma", "Corollary", "Fact", "Proposition",
               "Remark", "Property")

DECL_RE = re.compile(
    r"^\s*(?:#\[[^\]]*\]\s*)?(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+|Private\s+)?"
    r"(?:Program\s+)?"
    r"(Theorem|Lemma|Corollary|Fact|Proposition|Remark|Property)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)\b"
)
# Matches:
#   Module M.
#   Module M : SIG.
#   Module M <: SIG.
#   Module M (X : SIG) ...
#   Module M (X : SIG) (Y : SIG2) ...
#   Module Type M.
#   Module Import M.
#   Module Export M.
MODULE_OPEN_RE = re.compile(
    r"^\s*Module\s+(Type\s+|Import\s+|Export\s+)?([A-Za-z_][A-Za-z0-9_']*)"
    r"(\s*\([^.]*\))?\s*([:.<])"
)
MODULE_END_RE = re.compile(r"^\s*End\s+([A-Za-z_][A-Za-z0-9_']*)\s*\.\s*$")


def strip_comments(text):
    out = []
    i, depth = 0, 0
    n = len(text)
    while i < n:
        if text[i:i+2] == "(*":
            depth += 1
            i += 2
        elif depth > 0 and text[i:i+2] == "*)":
            depth -= 1
            i += 2
        elif depth == 0:
            out.append(text[i])
            i += 1
        else:
            i += 1
    return "".join(out)


def qualified_module_name(rel_in_coq):
    parts = rel_in_coq.parts
    base = parts[-1][:-2]
    if len(parts) == 1:
        return base
    head = parts[0]
    for d, ns in NS_MAP:
        if head == d:
            mid = list(parts[1:-1])
            return ".".join([ns] + mid + [base])
    return base


def parse_theorems(text):
    """Returns dict with:
        addressable: list of (qualified_local, kind)
        unaddressable: list of (qualified_local, kind, reason)
    """
    text = strip_comments(text)
    stack = []                  # list of (name, addressable_bool, reason_if_not)
    addressable = []
    unaddressable = []
    for raw_line in text.splitlines():
        line = raw_line
        # End first
        m_end = MODULE_END_RE.match(line)
        if m_end:
            if stack and stack[-1][0] == m_end.group(1):
                stack.pop()
            continue
        # Module alias on a single line: "Module M := X."
        if re.match(r"^\s*Module\s+[A-Za-z_][A-Za-z0-9_']*\s*:=\s*.*\.\s*$", line):
            continue
        # Module open
        m_open = MODULE_OPEN_RE.match(line)
        if m_open:
            mod_kind = (m_open.group(1) or "").strip()
            name = m_open.group(2)
            params = m_open.group(3)  # e.g. "(X : SIG)"
            after = m_open.group(4)   # ":" or "." or "<"
            if mod_kind == "Type":
                stack.append((name, False, "module_type"))
            elif params is not None:
                stack.append((name, False, "functor"))
            else:
                # plain Module M., Module M : SIG., Module M <: SIG.
                stack.append((name, True, None))
            continue
        # Theorem-like declaration
        m_decl = DECL_RE.match(line)
        if m_decl:
            kind = m_decl.group(1)
            name = m_decl.group(2)
            if kind in PROOF_KINDS:
                # Determine addressability
                bad_reason = None
                modnames = []
                for mn, ok, reason in stack:
                    modnames.append(mn)
                    if not ok:
                        bad_reason = reason
                local = ".".join(modnames + [name])
                if bad_reason:
                    unaddressable.append((local, kind, bad_reason))
                else:
                    addressable.append((local, kind))
    return {"addressable": addressable, "unaddressable": unaddressable}


def main():
    coq_files = []
    for vfile in ROOT.rglob("*.v"):
        rel = vfile.relative_to(ROOT)
        s = str(rel)
        if s.startswith("vendor/") or s.startswith("build/") or s.startswith("coq/archive/"):
            continue
        if s in ("coq/AssumptionsProbe.v", "coq/AssumptionsProbeAll.v"):
            continue
        if not vfile.with_suffix(".vo").exists():
            continue
        coq_files.append(vfile)

    coq_files.sort()
    print(f"# Coq files: {len(coq_files)}")

    probe_lines = [
        "(** Comprehensive Print Assumptions probe — every addressable proof-bearing",
        "    declaration across every .v file in the repository (excluding vendor/kami,",
        "    coq/archive/). Generated; do not edit. Functor and Module-Type interiors",
        "    are skipped here and recorded separately in the inventory. *)",
        "",
    ]

    inventory = []
    require_lines = []
    print_lines = []
    total_addr = 0
    total_unaddr = 0

    for vfile in coq_files:
        rel = vfile.relative_to(ROOT)
        if rel.parts[0] != "coq":
            continue
        rel_in_coq = Path(*rel.parts[1:])
        qmod = qualified_module_name(rel_in_coq)
        text = vfile.read_text(encoding="utf-8", errors="replace")
        parsed = parse_theorems(text)
        require_lines.append(f"Require {qmod}.")
        addr = parsed["addressable"]
        unaddr = parsed["unaddressable"]
        if addr:
            print_lines.append(f"(* === {qmod} : {len(addr)} addressable theorems "
                               f"(unaddressable: {len(unaddr)}) === *)")
            for local, kind in addr:
                print_lines.append(f"Print Assumptions {qmod}.{local}.")
        elif unaddr:
            print_lines.append(f"(* === {qmod} : 0 addressable, {len(unaddr)} unaddressable === *)")
        inventory.append({
            "file": str(rel),
            "qualified_module": qmod,
            "addressable_count": len(addr),
            "unaddressable_count": len(unaddr),
            "addressable": [{"local_name": l, "kind": k, "full_name": f"{qmod}.{l}"} for l, k in addr],
            "unaddressable": [{"local_name": l, "kind": k, "reason": r,
                                "full_name_unaddressable": f"{qmod}.{l}"}
                              for l, k, r in unaddr],
        })
        total_addr += len(addr)
        total_unaddr += len(unaddr)

    probe_lines += require_lines
    probe_lines += [""]
    probe_lines += print_lines

    # Extras: explicit probes for theorems that come from functor instantiation.
    # The Coq sources show:
    #   coq/nofi/Instance_Kernel.v: Module KernelNoFI_Theorem := NoFreeInsight_Theorem.NoFreeInsight(KernelNoFI).
    # So the functor-internal theorem `no_free_insight` is reachable as
    # NoFI.Instance_Kernel.KernelNoFI_Theorem.no_free_insight.
    probe_lines.append("")
    probe_lines.append("(* === Explicit probes for functor-instantiated names === *)")
    probe_lines.append("Print Assumptions NoFI.Instance_Kernel.KernelNoFI_Theorem.no_free_insight.")

    extras = [{
        "full_name": "NoFI.Instance_Kernel.KernelNoFI_Theorem.no_free_insight",
        "source_functor": "NoFI.NoFreeInsight_Theorem.NoFreeInsight",
        "instantiation_site": "coq/nofi/Instance_Kernel.v:102",
    }]

    probe_text = "\n".join(probe_lines) + "\n"
    out_v = ROOT / "coq" / "AssumptionsProbeAll.v"
    out_v.write_text(probe_text)

    inv = {
        "schema": "thiele-print-assumptions-inventory-v2",
        "files_probed": len(inventory),
        "total_addressable": total_addr,
        "total_unaddressable": total_unaddr,
        "extras_addressable_via_instantiation": extras,
        "files": inventory,
    }
    (BUILD / "probe_inventory.json").write_text(json.dumps(inv, indent=2))
    print(f"# probe -> {out_v} ({len(probe_lines)} lines)")
    print(f"# addressable theorems probed: {total_addr}")
    print(f"# unaddressable (in functor/module-type): {total_unaddr}")
    print(f"# inventory -> {BUILD / 'probe_inventory.json'}")


if __name__ == "__main__":
    main()
