#!/usr/bin/env python3
"""Make the property-carrying copies of the extracted Verilog, and run SymbiYosys.

The extracted files thielecpu/hardware/rtl/thiele_cpu_kami.v and
thiele_system.v are never edited. This script writes copies under
build/formal/ with one line added before the named module's final
`endmodule`:

  thiele_cpu_kami_props.v   mkModule1 + `include "cpu_props.vh"
  thiele_system_props.v     mkThieleSystem + `include "system_props.vh"

plus plain copies of thiele_cpu_kami.v and RegFile.v, so formal/thiele.sby
reads every file from one directory. The copies are checked to differ from
the originals in that one line only.

  python3 scripts/formal_prepare.py                    # copies only
  python3 scripts/formal_prepare.py --run TASK [TASK]  # copies, then sby
Tasks are the [tasks] of formal/thiele.sby. Each runs in build/formal/<task>/;
the script exits non-zero unless sby reports PASS.
"""
from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RTL = ROOT / "thielecpu" / "hardware" / "rtl"
FORMAL = ROOT / "formal"
OUT = ROOT / "build" / "formal"

CI_TASKS = ["cpu_prove_pt", "cpu_prove_ctrl", "cpu_cover", "sys_prove", "sys_cover"]


def with_include(src: Path, module: str, include: str) -> str:
    text = src.read_text(encoding="utf-8")
    marker = f"endmodule  // {module}"
    if text.count(marker) != 1:
        raise SystemExit(f"{src}: expected exactly one '{marker}'")
    out = text.replace(marker, f'`include "{include}"\n{marker}')
    original = set(text.splitlines())
    added = [ln for ln in out.splitlines() if ln not in original]
    if added != [f'`include "{include}"']:
        raise SystemExit(f"{src}: the copy differs by more than the include line")
    return out


def prepare() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "thiele_cpu_kami_props.v").write_text(
        with_include(RTL / "thiele_cpu_kami.v", "mkModule1", "cpu_props.vh"), encoding="utf-8")
    (OUT / "thiele_system_props.v").write_text(
        with_include(RTL / "thiele_system.v", "mkThieleSystem", "system_props.vh"), encoding="utf-8")
    shutil.copyfile(RTL / "thiele_cpu_kami.v", OUT / "thiele_cpu_kami.v")
    shutil.copyfile(RTL / "RegFile.v", OUT / "RegFile.v")
    for vh in ("cpu_props.vh", "system_props.vh"):
        shutil.copyfile(FORMAL / vh, OUT / vh)


def run_task(task: str) -> bool:
    workdir = OUT / task
    if workdir.exists():
        shutil.rmtree(workdir)
    # The [files] entries in thiele.sby are relative to formal/, not the caller.
    # Stream solver progress so a long proof does not look like a hung job.
    # SymbiYosys also keeps the full logs in workdir for artifact upload.
    proc = subprocess.run(["sby", "-d", str(workdir), str(FORMAL / "thiele.sby"), task],
                          cwd=FORMAL, capture_output=False, text=True)
    status = (workdir / "status").read_text().strip() if (workdir / "status").exists() else ""
    print(f"[formal] {task}: {status or 'no status'} (sby exit {proc.returncode})", flush=True)
    return proc.returncode == 0 and status.startswith("PASS")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--run", nargs="*", metavar="TASK",
                    help=f"sby tasks to run (no names: {' '.join(CI_TASKS)})")
    args = ap.parse_args()
    prepare()
    if args.run is None:
        return 0
    tasks = args.run or CI_TASKS
    results = {t: run_task(t) for t in tasks}
    return 0 if all(results.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
