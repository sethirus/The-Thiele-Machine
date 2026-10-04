#!/usr/bin/env python3
"""Prove A3-A8 by reset, frame, and exhaustive one-step induction obligations.

The two SAT frames express ONE arbitrary transition, not a bounded execution
claim. The base establishes J and disjointness after reset. Three bounds/trap
obligations preserve J and A7 for opcodes 0, 1, 2. The frame obligation proves
A8 for every opcode and preserves the entire table for all other transitions.

For A6, each old allocation counter 1..64 and each partition opcode is checked.
The two arbitrary constant indices cover every pair. The assumed old predicate
contains J and six disjointness facts implied by the induction hypothesis;
the assertion establishes disjointness for the selected pair in the new state.
PSPLIT splits its pairs into old/left-child/right-child cases, using symmetry
of disjointness. Every one of the 316 cases is mandatory. Thus induction covers every finite
execution from reset, provided ALL obligations pass.

RAM read values are overapproximated by independent arbitrary inputs. In the
A6 obligations only, step eligibility is also overapproximated. No table state,
counter width, or arithmetic is replaced. Case splitting fixes the instruction
opcode and constrains the allocation counter in the OLD frame only.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
RTL = ROOT / "thielecpu/hardware/rtl"
PROPERTY_FILE = ROOT / "formal/cpu_partition_induction.vh"
MODES = {"base": ("PT_BASE_CASE", 5), "bounds": ("PT_BOUNDS", 6),
         "frame": ("PT_FRAME", 1), "disjoint": ("PT_DISJOINT", 1)}
READS = " ".join("mkModule1/w:" + name for name in (
    "imem$D_OUT*", "mem$D_OUT*", "module_tensors$D_OUT*",
    "lassert_cbuf$D_OUT*", "lassert_fbuf$D_OUT*"))
SUCCESS = "SAT proof finished - no model found: SUCCESS!"


def quoted(path: Path) -> str:
    return '"' + path.resolve().as_posix() + '"'


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cases() -> list[dict]:
    obligations = [{"name": "base", "mode": "base"},
            {"name": "frame", "mode": "frame"}] + [
        {"name": f"bounds-op{op}", "mode": "bounds", "opcode": op}
        for op in range(3)]
    for counter in range(1, 65):
        for op in range(3):
            roles = ("old", "left", "right") if op == 1 and counter <= 62 else ("all",)
            for role in roles:
                suffix = "" if role == "all" else f"-{role}"
                obligations.append({"name": f"disjoint-op{op}-next{counter:02d}{suffix}",
                                    "mode": "disjoint", "opcode": op,
                                    "counter": counter, "pair_case": role})
    return obligations


def prepare_script(mode: str, work: Path, *, lower_checks: bool = False) -> str:
    define, count = MODES[mode]
    step_cut = ("select -assert-count 1 mkModule1/w:WILL_FIRE_RL_step\n"
                "cutpoint mkModule1/w:WILL_FIRE_RL_step\n") if mode == "disjoint" else ""
    return f"""verilog_defines -DBSV_NO_INITIAL_BLOCKS -D{define}
read -formal RegFile.v cpu.v
hierarchy -top mkModule1
proc
{'chformal -lower' if lower_checks else ''}
select -assert-count 9 {READS}
cutpoint {READS}
{step_cut}select *
delete -output mkModule1/o:*
prep -flatten -top mkModule1
memory_map
check -assert
select -assert-count {count} mkModule1/t:$assert
write_rtlil {quoted(work / (mode + '.il'))}
"""


def case_script(case: dict, work: Path, timeout: int) -> str:
    mode = case["mode"]
    constrain_opcode = ""
    if "opcode" in case:
        # The read bus has already been made an arbitrary input. Fixing these
        # eight bits selects one opcode without constraining any CPU state.
        constrain_opcode = ("cd mkModule1\nconnect -set imem$D_OUT_1[31:24] "
                            f"8'b{case['opcode']:08b}\ncd ..\n")
    constraints = ""
    if mode == "base":
        constraints = "-set-at 1 RST_N 0 -set-at 2 RST_N 1"
    elif mode == "disjoint":
        constraints = f"-set-at 1 pt_next_id {case['counter']}"
        if case["pair_case"] == "old":
            constraints += " -set-at 1 ptf_old_pair 1"
        elif case["pair_case"] in ("left", "right"):
            index = case["counter"] + (case["pair_case"] == "right")
            constraints += f" -set ptf_a {index}"
    return f"""read_rtlil {quoted(work / (mode + '.il'))}
{constrain_opcode}opt -full
wreduce
opt -full
async2sync
dffunmap
opt_clean
check -assert
select -assert-count {MODES[mode][1]} mkModule1/t:$assert
sat -seq 2 -prove-asserts -set-assumes -verify -timeout {timeout} {constraints} -dump_vcd {quoted(work / (case['name'] + '.vcd'))}
"""


def execute(yosys: str, work: Path, name: str, script: str,
            timeout: int, *, proof: bool) -> dict:
    script_file, log = work / f"{name}.ys", work / f"{name}.log"
    script_file.write_text(script, encoding="utf-8", newline="\n")
    started = time.monotonic()
    status, code = "ERROR", None
    with (work / f"{name}.console.log").open("w", encoding="utf-8") as output:
        try:
            proc = subprocess.run([yosys, "-ql", str(log), "-s", str(script_file)],
                                  cwd=work, stdout=output, stderr=subprocess.STDOUT,
                                  timeout=timeout + 60)
            code = proc.returncode
            text = log.read_text(encoding="utf-8", errors="replace") if log.exists() else ""
            clean = "Found and reported 0 problems." in text
            conflict = "Driver-driver conflict" in text or "multiple conflicting drivers" in text
            if code == 0 and clean and not conflict and (not proof or SUCCESS in text):
                status = "PASS"
            else:
                status = "FAIL"
        except subprocess.TimeoutExpired:
            status = "TIMEOUT"
    return {"name": name, "status": status, "exit_code": code,
            "seconds": round(time.monotonic() - started, 3), "log": log.name,
            "script_sha256": sha256(script_file)}


def complete(results: list[dict]) -> bool:
    expected = {case["name"]: case for case in cases()}
    names = [result["name"] for result in results]
    return (len(names) == len(expected) and set(names) == set(expected) and
            all(result["status"] == "PASS" and
                all(result.get(key) == value for key, value in expected[result["name"]].items())
                for result in results))


def prove(work: Path, *, yosys: str = "yosys", jobs: int = 2,
          timeout: int = 900) -> bool:
    from formal_prepare import with_include

    work = work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    (work / "status").write_text("INCOMPLETE\n", encoding="utf-8")
    (work / "cpu.v").write_text(with_include(RTL / "thiele_cpu_kami.v", "mkModule1",
                                           PROPERTY_FILE.name), encoding="utf-8", newline="\n")
    shutil.copyfile(RTL / "RegFile.v", work / "RegFile.v")
    shutil.copyfile(PROPERTY_FILE, work / PROPERTY_FILE.name)
    version = subprocess.run([yosys, "-V"], capture_output=True, text=True, check=True).stdout.strip()
    # Recent frontends emit $check; Yosys 0.33 emits $assert/$assume directly.
    # Lowering changes their representation, not their predicate or activation.
    formal_help = subprocess.run([yosys, "-Q", "-T", "-p", "help chformal"],
                                 capture_output=True, text=True, check=True).stdout
    lower_checks = "-lower" in formal_help
    report = {"status": "INCOMPLETE", "method": "exhaustive one-step induction",
              "yosys": version, "expected_obligations": len(cases()),
              "inputs": {str(p.relative_to(ROOT)): sha256(p) for p in
                         (RTL / "thiele_cpu_kami.v", RTL / "RegFile.v", PROPERTY_FILE,
                          Path(__file__).resolve())},
              "preparation": [], "obligations": []}

    def save() -> None:
        temporary = work / "report.json.tmp"
        temporary.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        temporary.replace(work / "report.json")

    save()
    for mode in MODES:
        result = execute(yosys, work, f"prepare-{mode}",
                         prepare_script(mode, work, lower_checks=lower_checks),
                         timeout, proof=False)
        report["preparation"].append(result)
        save()
        print(f"[partition] {result['name']}: {result['status']}", flush=True)
        if result["status"] != "PASS":
            report["status"] = "FAIL"
            save()
            (work / "status").write_text("FAIL\n", encoding="utf-8")
            return False

    # Establish the auxiliary invariant and frame/trap guarantees first.
    # Disjointness is never accepted if these prerequisites fail.
    for phase in (cases()[:5], cases()[5:]):
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            futures = {pool.submit(execute, yosys, work, case["name"],
                                   case_script(case, work, timeout), timeout, proof=True): case
                       for case in phase}
            for future in as_completed(futures):
                result = future.result()
                result.update({key: value for key, value in futures[future].items() if key != "name"})
                report["obligations"].append(result)
                save()
                print(f"[partition] {result['name']}: {result['status']} "
                      f"({len(report['obligations'])}/{len(cases())})", flush=True)
        if any(result["status"] != "PASS" for result in report["obligations"]):
            break

    ok = complete(report["obligations"])
    report["status"] = "PASS" if ok else "FAIL"
    save()
    (work / "status").write_text(report["status"] + "\n", encoding="utf-8")
    print(f"[partition] {report['status']}: {len(report['obligations'])}/{len(cases())} obligations", flush=True)
    return ok


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workdir", type=Path, default=ROOT / "build/formal/cpu_prove_pt")
    parser.add_argument("--yosys", default="yosys")
    parser.add_argument("--jobs", type=int, default=min(2, os.cpu_count() or 1))
    parser.add_argument("--timeout", type=int, default=900)
    args = parser.parse_args()
    if args.jobs < 1 or args.timeout < 1:
        parser.error("jobs and timeout must be positive")
    return 0 if prove(args.workdir, yosys=args.yosys, jobs=args.jobs, timeout=args.timeout) else 1


if __name__ == "__main__":
    raise SystemExit(main())
