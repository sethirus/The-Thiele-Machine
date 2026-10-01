#!/usr/bin/env python3
"""Give the Kami-printed system top module a pin interface.

The Kami Bluespec printer prints a composition as one module per Kami
module (mkModule1, mkModule2, ...) plus a top module that instantiates them
and passes each module's called methods in as arguments. The printed top
module declares no methods, so bsc can compile it but nothing reaches it
from outside. This script adds exactly that and nothing else:

- an interface made of the methods of the outermost modules, the ones no
  other module calls into, each declared as the printer declared it; a
  module another module calls into stays inside the design;
- a top module that keeps the printed instantiation lines verbatim and
  forwards each of those methods to the module that defines it;
- a synthesize attribute on mkModule1, so the CPU compiles to its own
  Verilog module, the same one the CPU-only pipeline produces.

No expression, register, or rule is written here: every line of logic in
the output comes from the printer.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

INTERFACE = re.compile(r"^interface\s+(Module\d+)\s*;(.*?)^endinterface", re.S | re.M)
METHOD = re.compile(
    r"method\s+(Action(?:Value\s*#\s*\((?P<ret>.*?)\))?)\s+(?P<name>\w+)\s*\((?P<args>.*)\)")
INSTANCE = re.compile(r"(Module\d+)\s+(m\d+)\s*<-\s*(mkModule\d+)\s*\((.*?)\)\s*;", re.S)


def top_block(text: str, top: str) -> re.Match[str]:
    match = re.search(rf"^module\s+mk{top}\b.*?^endmodule\s*$", text, re.S | re.M)
    if match is None:
        raise SystemExit(f"kami_system_top: printed top module mk{top} not found")
    return match


def interfaces(text: str) -> dict[str, list[dict[str, str]]]:
    result: dict[str, list[dict[str, str]]] = {}
    for ifc in INTERFACE.finditer(text):
        body = " ".join(ifc.group(2).split())
        methods = []
        for decl in body.split(";"):
            decl = decl.strip()
            if not decl:
                continue
            m = METHOD.fullmatch(decl)
            if m is None:
                raise SystemExit(f"kami_system_top: unrecognised method declaration: {decl}")
            methods.append({"decl": decl, "name": m.group("name"),
                            "value": m.group("ret") is not None,
                            "args": m.group("args").strip()})
        result[ifc.group(1)] = methods
    return result


def build(text: str, top: str) -> str:
    block = top_block(text, top)
    instances = INSTANCE.findall(block.group(0))
    if not instances:
        raise SystemExit("kami_system_top: no module instances in the printed top module")
    ifcs = interfaces(text)
    inner = set()
    for _ifc, _inst, _mk, args in instances:
        inner.update(re.findall(r"\b(m\d+)\.\w+", args))
    lines = [f"interface {top};"]
    forwards = []
    for ifc_name, inst, _mk, _args in instances:
        if inst in inner:
            continue
        for meth in ifcs.get(ifc_name, []):
            lines.append(f"    {meth['decl']};")
            arg_names = ", ".join(a.split()[-1] for a in meth["args"].split(",") if a.strip())
            call = f"{inst}.{meth['name']}({arg_names})"
            if meth["value"]:
                body = f"        let r <- {call};\n        return r;"
            else:
                body = f"        {call};"
            forwards.append(f"    {meth['decl']};\n{body}\n    endmethod")
    lines.append("endinterface")
    lines.append("")
    lines.append("(* synthesize *)")
    lines.append(f"module mk{top} ({top});")
    for ifc_name, inst, mk, args in instances:
        lines.append(f"    {ifc_name} {inst} <- {mk} ({' '.join(args.split())});")
    lines.extend(forwards)
    lines.append("endmodule")
    replaced = text[:block.start()] + "\n".join(lines) + text[block.end():]
    cpu = re.compile(r"^(module\s+mkModule1\b)", re.M)
    if not cpu.search(replaced):
        raise SystemExit("kami_system_top: mkModule1 not found")
    return cpu.sub(r"(* synthesize *)\n\1", replaced, count=1)


def main() -> int:
    if len(sys.argv) != 4:
        print("usage: kami_system_top.py TOP_NAME IN.bsv OUT.bsv", file=sys.stderr)
        return 2
    top, src, dst = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3])
    dst.write_text(build(src.read_text(), top), newline="\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
