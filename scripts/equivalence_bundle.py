#!/usr/bin/env python3
"""
Generate a compact cross-layer equivalence bundle:
- Deterministic compute trace checked across Python VM, Coq-extracted runner, and RTL.
- μ-ledger step trace for the Python execution of that program.
- A toy "No Free Insight" table showing μ paid vs. information-theoretic lower bounds.

Outputs JSON to results/equivalence_bundle.json. Set `EVIDENCE_STRICT=1` to
forbid μ normalization entirely; otherwise set `ALLOW_MU_NORMALIZE=1` to adopt
the Python μ when other layers emit 0/None (the substitution is recorded in the
output).
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Dict, List, Tuple, Iterable, Any

from thielecpu.mu import mu_breakdown
from thielecpu.state import State
from thielecpu.vm import VM

REPO_ROOT = Path(__file__).resolve().parent.parent
HARDWARE_DIR = REPO_ROOT / "thielecpu" / "hardware"
BUILD_DIR = REPO_ROOT / "build"
RESULTS_PATH = REPO_ROOT / "results" / "equivalence_bundle.json"
ALLOW_MU_NORMALIZE = os.environ.get("ALLOW_MU_NORMALIZE", "").lower() in {"1", "true", "yes"}
EVIDENCE_STRICT = os.environ.get("EVIDENCE_STRICT", "").lower() in {"1", "true", "yes"}
FORCE_ZERO_MU_EXTRACTED = os.environ.get("FORCE_ZERO_MU_EXTRACTED", "").lower() in {"1", "true", "yes"}
FORCE_ZERO_MU_RTL = os.environ.get("FORCE_ZERO_MU_RTL", "").lower() in {"1", "true", "yes"}


def _write_hex_words(path: Path, words: List[int]) -> None:
    path.write_text("\n".join(f"{w & 0xFFFFFFFF:08x}" for w in words) + "\n", encoding="utf-8")


def _encode_word(opcode: int, a: int = 0, b: int = 0, cost: int = 0) -> int:
    return ((opcode & 0xFF) << 24) | ((a & 0xFF) << 16) | ((b & 0xFF) << 8) | (cost & 0xFF)


def _run_python_vm(init_mem: List[int], init_regs: List[int], program_text: List[Tuple[str, str]], outdir: Path) -> Dict[str, object]:
    state = State()
    vm = VM(state)
    vm.register_file = [r & 0xFFFFFFFF for r in init_regs]
    vm.data_memory = [m & 0xFFFFFFFF for m in init_mem]

    outdir.mkdir(parents=True, exist_ok=True)
    # Disable implicit MDLACC for cross-layer isomorphism runs: μ must be driven
    # by the instruction stream, matching Coq/RTL.
    vm.run(program_text, outdir, auto_mdlacc=False)

    ledger = json.loads((outdir / "mu_ledger.json").read_text())
    summary = json.loads((outdir / "summary.json").read_text())

    mu_total = int(summary.get("mu_total", 0))
    mu_discovery = int(summary.get("mu_discovery", summary.get("mu_information", 0)))
    mu_execution = int(summary.get("mu_execution", summary.get("mu_operational", 0)))

    regs = [int(v) & 0xFFFFFFFF for v in vm.register_file]
    mem = [int(v) & 0xFFFFFFFF for v in vm.data_memory]

    modules: List[Dict[str, object]] = []
    for mid, region in sorted(state.regions.modules.items(), key=lambda kv: int(kv[0])):
        region_set = set(region)
        if not region_set:
            continue
        modules.append({"id": int(mid), "region": sorted(region_set)})

    return {
        "regs": regs,
        "mem": mem,
        "modules": modules,
        "summary": summary,
        "mu_ledger": ledger,
        "mu": mu_total,
        "mu_raw": mu_total,
        "mu_normalized": False,
        "mu_normalize_reason": None,
        "mu_discovery": mu_discovery,
        "mu_execution": mu_execution,
    }


def _run_extracted(init_mem: List[int], init_regs: List[int], trace_lines: List[str]) -> Dict[str, object]:
    runner = BUILD_DIR / "extracted_vm_runner"

    # Allow tests to skip invoking the extracted runner when exercising gates
    # (e.g. ORACLE_HALTS) that the extracted binary cannot handle.
    if os.environ.get("SKIP_EXTRACTED_RUNNER", "").lower() in {"1", "true", "yes"}:
        print("Skipping extracted runner (SKIP_EXTRACTED_RUNNER=1); using placeholder extracted output.", file=sys.stderr)
        return {"regs": [], "mem": [], "mu": None, "modules": []}

    if not runner.exists():
        print(
            "Warning: missing extracted runner; proceeding with placeholder extracted output. Run scripts/forge_artifact.sh to build it.",
            file=sys.stderr,
        )
        return {"regs": [], "mem": [], "mu": None, "modules": []}

    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        trace_path = td_path / "trace.txt"
        prefix = []
        for r, v in enumerate(init_regs):
            prefix.append(f"INIT_REG {r} {v & 0xFFFFFFFF}")
        for a, v in enumerate(init_mem):
            prefix.append(f"INIT_MEM {a} {v & 0xFFFFFFFF}")
        trace_path.write_text("\n".join(prefix + trace_lines) + "\n", encoding="utf-8")

        result = subprocess.run(
            [str(runner), str(trace_path)], capture_output=True, text=True, check=True,
            env={**os.environ, "OCAMLRUNPARAM": os.environ.get("OCAMLRUNPARAM", "l=64M")},
        )
        payload = json.loads(result.stdout)

    regs = [int(v) & 0xFFFFFFFF for v in payload["regs"]]
    mem = [int(v) & 0xFFFFFFFF for v in payload["mem"]]
    mu_val = int(payload.get("mu", 0))
    if FORCE_ZERO_MU_EXTRACTED:
        mu_val = 0
    return {
        "regs": regs,
        "mem": mem,
        "mu": mu_val,
        "modules": payload.get("graph", {}).get("modules", []),
    }


def _run_rtl(program_words: List[int], data_words: List[int]) -> Dict[str, object]:
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        sim_out = td_path / "thiele_cpu_tb.out"
        program_hex = td_path / "tb_program.hex"
        data_hex = td_path / "tb_data.hex"

        _write_hex_words(program_hex, program_words)
        _write_hex_words(data_hex, data_words)

        subprocess.run(
            [
                "iverilog",
                "-g2012",
                "-I",
                "rtl",
                "-o",
                str(sim_out),
                "rtl/thiele_cpu_unified.v",
                "testbench/thiele_cpu_tb.v",
            ],
            cwd=str(HARDWARE_DIR),
            capture_output=True,
            text=True,
            check=True,
        )

        run = subprocess.run(
            [
                "vvp",
                str(sim_out),
                f"+PROGRAM={program_hex}",
                f"+DATA={data_hex}",
            ],
            cwd=str(td_path),
            capture_output=True,
            text=True,
            check=True,
        )

        out = run.stdout
        # Find JSON start - look for opening brace followed by "status" or "partition_ops"
        start = out.find('{\n  "status":')
        if start == -1:
            start = out.find('{ "status":')
        if start == -1:
            start = out.find('{"status":')
        if start == -1:
            start = out.find('{\n  "partition_ops":')
        if start == -1:
            start = out.find('{ "partition_ops":')
        if start == -1:
            start = out.find('{"partition_ops":')
        if start == -1:
            raise AssertionError(f"No JSON found in RTL stdout.\nSTDOUT:\n{out}\nSTDERR:\n{run.stderr}")
        decoder = json.JSONDecoder()
        payload, _end = decoder.raw_decode(out[start:])

    regs = [int(v) & 0xFFFFFFFF for v in payload["regs"]]
    mem = [int(v) & 0xFFFFFFFF for v in payload["mem"]]
    # thiele_cpu_tb.v exports the accumulator as JSON field "mu".
    mu_val = int(payload.get("mu", payload.get("mu_acc", payload.get("mu_total", 0))))
    if FORCE_ZERO_MU_RTL:
        mu_val = 0
    modules = [m for m in payload.get("modules", []) if int(m.get("id", -1)) >= 0]
    return {
        "regs": regs,
        "mem": mem,
        "mu": mu_val,
        "modules": modules,
    }


def _canonical_regions(modules: Iterable[Any]) -> List[Tuple[int, ...]]:
    regions: List[Tuple[int, ...]] = []
    for m in modules:
        if not isinstance(m, dict):
            continue
        raw_region = m.get("region")
        if not isinstance(raw_region, list):
            continue
        region = tuple(sorted(int(x) for x in raw_region))
        if not region:
            continue
        regions.append(region)
    regions.sort()
    return regions


def _safe_modules_list(payload: Dict[str, object]) -> List[Any]:
    raw = payload.get("modules")
    return raw if isinstance(raw, list) else []


def _no_free_insight_cases() -> List[Dict[str, object]]:
    # Toy search spaces: Ω has size 2^n; constraints cut it down.
    scenarios = [
        ("single bit fixed", 2 ** 8, 2 ** 7, "(assert (= b0 1))"),
        ("two bits fixed", 2 ** 8, 2 ** 6, "(assert (and (= b0 1) (= b1 0)))"),
        ("parity even", 2 ** 8, 2 ** 7, "(assert (even-parity bytes))"),
    ]
    rows: List[Dict[str, object]] = []
    for name, before, after, expr in scenarios:
        breakdown = mu_breakdown(expr, before, after)
        lower_bound = breakdown.information_gain
        rows.append(
            {
                "instance": name,
                "omega_before": before,
                "omega_after": after,
                "log2_ratio": lower_bound,
                "mu_paid": breakdown.question_bits,
                "mu_minus_lower_bound": breakdown.question_bits - lower_bound,
                "canonical": breakdown.canonical,
            }
        )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate a compact cross-layer equivalence bundle")
    parser.add_argument(
        "--scenario",
        choices=["pnew_only", "multiop_compute", "psplit_odd", "magic_ops", "oracle_halts"],
        default="pnew_only",
        help="Which deterministic trace to run (default: pnew_only)",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=RESULTS_PATH,
        help="Path to write the bundle JSON (default: results/equivalence_bundle.json)",
    )
    args = parser.parse_args()

    init_regs = [0] * 32
    init_mem = [0] * 256
    init_mem[0] = 0x29
    init_mem[1] = 0x12
    init_mem[2] = 0x22
    init_mem[3] = 0x03

    # Canonical μ-cost for singleton {1} under the spec: popcount=1 plus an
    # additional 1 bit to encode the element (bit_length(1)=1) => 2.
    pnew_mu = 2

    scenario = args.scenario
    if scenario == "pnew_only":
        program_words = [
            _encode_word(0x00, 1, 0, pnew_mu),  # PNEW singleton module {1}
            _encode_word(0xFF, 0, 0, 0),        # HALT
        ]

        program_text = [
            ("PNEW", f"{{1}} {pnew_mu}"),
            ("HALT", ""),
        ]

        trace_lines = [
            f"PNEW {{1}} {pnew_mu}",
        ]
    elif scenario == "multiop_compute":
        # Multi-op compute trace: drives regs/mem deterministically while also
        # exercising explicit μ-deltas for compute instructions.
        op_cost = 1
        program_words = [
            _encode_word(0x00, 1, 0, pnew_mu),         # PNEW singleton module {1}
            _encode_word(0x0A, 0, 0, op_cost),         # XOR_LOAD r0 <= mem[0]
            _encode_word(0x0A, 1, 1, op_cost),         # XOR_LOAD r1 <= mem[1]
            _encode_word(0x0B, 0, 1, op_cost),         # XOR_ADD  r0 ^= r1
            _encode_word(0x0C, 0, 1, op_cost),         # XOR_SWAP r0 <-> r1
            _encode_word(0x0D, 2, 0, op_cost),         # XOR_RANK r2 := popcount(r0)
            # RTL operand order for XFER is (dest, src) - matches execute_xfer task signature.
            _encode_word(0x07, 3, 2, op_cost),         # XFER     r3 <- r2
            _encode_word(0xFF, 0, 0, 0),               # HALT
        ]

        program_text = [
            ("PNEW", f"{{1}} {pnew_mu}"),
            ("XOR_LOAD", f"0 0 {op_cost}"),
            ("XOR_LOAD", f"1 1 {op_cost}"),
            ("XOR_ADD", f"0 1 {op_cost}"),
            ("XOR_SWAP", f"0 1 {op_cost}"),
            ("XOR_RANK", f"2 0 {op_cost}"),
            ("XFER", f"3 2 {op_cost}"),
            ("HALT", "0"),
        ]

        trace_lines = [
            f"PNEW {{1}} {pnew_mu}",
            f"XOR_LOAD 0 0 {op_cost}",
            f"XOR_LOAD 1 1 {op_cost}",
            f"XOR_ADD 0 1 {op_cost}",
            f"XOR_SWAP 0 1 {op_cost}",
            f"XOR_RANK 2 0 {op_cost}",
            f"XFER 3 2 {op_cost}",
            "HALT 0",
        ]
    elif scenario == "psplit_odd":
        # Partition gate: build {1,2,3,4} via singleton PNEW + PMERGE, then PSPLIT
        # using RTL predicate byte for "odd" (mode=00, param=1 => 0x01).
        # Costs are explicit and must match across Python/Coq-extracted/RTL.
        def pnew_cost(x: int) -> int:
            return 1 + int(x).bit_length()

        p1, p2, p3, p4 = (pnew_cost(1), pnew_cost(2), pnew_cost(3), pnew_cost(4))
        merge_cost = 4
        split_cost = 64
        pred_odd = 0x01

        # Module IDs start at 1 (RTL reset convention); build merge chain 1&2->5, 5&3->6, 6&4->7.
        program_words = [
            _encode_word(0x00, 1, 0, p1),
            _encode_word(0x00, 2, 0, p2),
            _encode_word(0x00, 3, 0, p3),
            _encode_word(0x00, 4, 0, p4),
            _encode_word(0x02, 1, 2, merge_cost),
            _encode_word(0x02, 5, 3, merge_cost),
            _encode_word(0x02, 6, 4, merge_cost),
            _encode_word(0x01, 7, pred_odd, split_cost),
            _encode_word(0xFF, 0, 0, 0),
        ]

        # Python module IDs match RTL/extracted in strict isomorphism mode.
        program_text = [
            ("PNEW", f"{{1}} {p1}"),
            ("PNEW", f"{{2}} {p2}"),
            ("PNEW", f"{{3}} {p3}"),
            ("PNEW", f"{{4}} {p4}"),
            ("PMERGE", f"1 2 {merge_cost}"),
            ("PMERGE", f"5 3 {merge_cost}"),
            ("PMERGE", f"6 4 {merge_cost}"),
            ("PSPLIT", f"7 {pred_odd} {split_cost}"),
            ("HALT", "0"),
        ]

        # Extracted runner uses the same 1-based ModuleIDs as RTL for test harnesses.
        # PNEW {1..4} => 1..4, merges => 5,6,7, then PSPLIT 7 into {1,3} and {2,4}.
        trace_lines = [
            f"PNEW {{1}} {p1}",
            f"PNEW {{2}} {p2}",
            f"PNEW {{3}} {p3}",
            f"PNEW {{4}} {p4}",
            f"PMERGE 1 2 {merge_cost}",
            f"PMERGE 5 3 {merge_cost}",
            f"PMERGE 6 4 {merge_cost}",
            f"PSPLIT 7 {{1,3}} {{2,4}} {split_cost}",
            "HALT 0",
        ]

    elif scenario == "oracle_halts":
        # Special-case: ORACLE_HALTS charges a very large μ (1_000_000). The
        # extracted runner cannot safely execute that delta in strict mode; tests
        # may set SKIP_EXTRACTED_RUNNER=1 to avoid invoking the extracted binary.
        oracle_cost = 1_000_000

        program_words = [
            _encode_word(0x00, 1, 0, pnew_mu),         # PNEW {1}
            _encode_word(0x10, 0, 0, 0),               # ORACLE_HALTS (RTL applies fixed charge)
            _encode_word(0xFF, 0, 0, 0),               # HALT
        ]

        # Use explicit-cost mode for Python so the VM charges oracle_cost deterministically.
        program_text = [
            ("PNEW", f"{{1}} {pnew_mu}"),
            ("ORACLE_HALTS", f"oracle-demo {oracle_cost}"),
            ("HALT", "0"),
        ]

        trace_lines = [
            f"PNEW {{1}} {pnew_mu}",
            f"ORACLE_HALTS oracle-demo {oracle_cost}",
            "HALT 0",
        ]

    else:
        # Highest-risk “magic ops” gate: explicitly exercise the three opcodes
        # that can leak free insight if priced inconsistently.
        #
        # - MDLACC: RTL computes mdl_cost = (bit_length(max+1)*size) << 16.
        #   For singleton {1}: bit_length(2)=1, size=1 => 1<<16.
        # - PDISCOVER: RTL computes INFO_GAIN in Q16.16 via μ-ALU.
        #   Use before=4, after=2 => log2(2)=1.0 => 1<<16.
        # NOTE: ORACLE_HALTS is intentionally excluded from strict cross-layer
        # runs because RTL hardcodes a 1,000,000 μ charge which overflows the
        # extracted runner's Peano-nat stack (Stack_overflow). Keeping this
        # gate strict requires restricting to operations whose μ deltas are
        # tractable under extraction.
        mdl_cost = 1 << 16
        # μ-ALU INFO_GAIN is simplified in RTL to operand_a - operand_b (not Q16.16).
        # Use the same integer delta to match RTL behavior for cross-layer isomorphism.
        info_gain_cost = 4 - 2  # before=4, after=2 => 2

        program_words = [
            _encode_word(0x00, 1, 0, pnew_mu),      # PNEW {1}
            _encode_word(0x05, 0, 0, 0),            # MDLACC current module (μ-ALU adds mdl_cost)
            _encode_word(0x06, 4, 2, 0),            # PDISCOVER before=4 after=2 (μ-ALU adds info_gain)
            _encode_word(0xFF, 0, 0, 0),            # HALT
        ]

        # Python uses explicit-cost mode for MDLACC/PDISCOVER/ORACLE_HALTS to
        # avoid dynamic/file-based behavior. Costs are raw Q16.16 integers.
        program_text = [
            ("PNEW", f"{{1}} {pnew_mu}"),
            ("MDLACC", f"1 {mdl_cost}"),
            ("PDISCOVER", f"1 4 2 {info_gain_cost}"),
            ("HALT", "0"),
        ]

        # Extracted runner uses 0-based ModuleIDs and accepts explicit costs.
        trace_lines = [
            f"PNEW {{1}} {pnew_mu}",
            f"MDLACC 1 {mdl_cost}",
            f"PDISCOVER 1 {{}} {info_gain_cost}",
            "HALT 0",
        ]

    if EVIDENCE_STRICT and ALLOW_MU_NORMALIZE:
        raise AssertionError(
            "EVIDENCE_STRICT forbids μ normalization; unset ALLOW_MU_NORMALIZE for evidence runs."
        )

    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        py_out = _run_python_vm(init_mem, init_regs, program_text, td_path / "python")

    coq_out = _run_extracted(init_mem, init_regs, trace_lines)
    rtl_out = _run_rtl(program_words, init_mem)

    # Normalize μ totals only when explicitly allowed. By default, treat missing
    # or zero μ from Coq/RTL as a failure once the Python VM produces μ > 0.
    mu_expected = py_out.get("mu")
    if not mu_expected:
        raise AssertionError("Deterministic trace produced μ=0; expected non-zero μ to exercise ledger alignment.")

    for name, target in ("extracted", coq_out), ("rtl", rtl_out):
        target["mu_raw"] = target.get("mu")
        target["mu_normalized"] = False
        target["mu_normalize_reason"] = None
        if target.get("mu") in {None, 0}:
            if EVIDENCE_STRICT:
                raise AssertionError(
                    f"{name} runner returned μ={target.get('mu')} under EVIDENCE_STRICT; normalization is forbidden."
                )
            if not ALLOW_MU_NORMALIZE:
                raise AssertionError(
                    f"{name} runner returned μ={target.get('mu')} while Python produced {mu_expected}. "
                    "Set ALLOW_MU_NORMALIZE=1 to fallback to the Python total if μ is not implemented, or set EVIDENCE_STRICT=1"
                    " to force non-normalized runs."
                )
            target["mu"] = mu_expected
            target["mu_normalized"] = True
            target["mu_normalize_reason"] = f"{name}_missing_mu"

    bundle = {
        "program": {
            "scenario": scenario,
            "words": program_words,
            "text": program_text,
            "trace_lines": trace_lines,
        },
        "python": py_out,
        "extracted": coq_out,
        "rtl": rtl_out,
        "evidence_strict": EVIDENCE_STRICT,
        "allow_mu_normalize": ALLOW_MU_NORMALIZE,
        "aligned": py_out["regs"] == coq_out["regs"] == rtl_out["regs"]
        and py_out["mem"] == coq_out["mem"] == rtl_out["mem"]
        and py_out.get("mu") == coq_out.get("mu") == rtl_out.get("mu"),
        "partition": {
            "python": _canonical_regions(_safe_modules_list(py_out)),
            "extracted": _canonical_regions(_safe_modules_list(coq_out)),
            "rtl": _canonical_regions(_safe_modules_list(rtl_out)),
        },
        "no_free_insight": _no_free_insight_cases(),
    }

    if scenario == "psplit_odd":
        expected_regions = [(1, 3), (2, 4)]
        bundle["partition"]["expected"] = expected_regions
        bundle["partition"]["aligned"] = (
            bundle["partition"]["python"]
            == bundle["partition"]["extracted"]
            == bundle["partition"]["rtl"]
            == expected_regions
        )
        bundle["partition"]["zombie_parent_present"] = any(
            r == (1, 2, 3, 4)
            for r in (
                bundle["partition"]["python"]
                + bundle["partition"]["extracted"]
                + bundle["partition"]["rtl"]
            )
        )

    out_path: Path = args.out
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(bundle, indent=2), encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
