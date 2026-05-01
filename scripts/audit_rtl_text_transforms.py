#!/usr/bin/env python3
"""Audit the project-local BSV/Verilog text transforms.

This is a provenance and transform-scope check, not a compiler correctness
proof. It replays the project-specific text processing around the BSC boundary
and records the storage-only rewrites that are intentionally allowed:

  Coq/Kami BSV -> wrapper/import/vec preprocessing -> RegFile BSV
  BSC Verilog  -> synthesis-friendly storage arrays

The audit fails if the current generated artifacts are not byte-for-byte
reproducible from the checked transform scripts.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import importlib.util
import io
import json
import re
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = ROOT / "artifacts" / "rtl_text_transform_audit.json"

RAW_BSV = ROOT / "build" / "kami_hw" / "thiele_hw.bsv"
CLEAN_BSV = ROOT / "build" / "kami_hw" / "thiele_hw_clean.bsv"
RAW_VERILOG = ROOT / "build" / "kami_hw" / "mkModule1.v"
SYNTH_VERILOG = ROOT / "build" / "kami_hw" / "mkModule1_synth.v"
TRACKED_RTL = ROOT / "thielecpu" / "hardware" / "rtl" / "thiele_cpu_kami.v"


def _rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _file_record(path: Path) -> dict[str, Any]:
    data = path.read_bytes()
    return {
        "path": _rel(path),
        "sha256": _sha256(data),
        "bytes": len(data),
        "lines": data.count(b"\n"),
    }


def _load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _preprocess_bsv(raw: str, top_module: str = "ThieleCPU") -> str:
    """Replay the wrapper stripping, Vector import, and vec rewrite in kami_extract.sh."""
    lines = raw.split("\n")
    clean: list[str] = []
    skip = False
    wrapper_prefixes = ("module mkThieleCPU", "module mkTop", f"module mk{top_module}")

    for line in lines:
        if line.startswith(wrapper_prefixes):
            skip = True
        if not skip:
            clean.append(line)
        if skip and line.strip() == "endmodule":
            skip = False

    text = "import Vector::*;\n" + "\n".join(clean)
    return re.sub(r"vec\(([^()]*)\)", r"unpack({\1})", text)


def _bsv_large_vector_decls(text: str) -> list[dict[str, Any]]:
    pattern = re.compile(
        r"Reg#\(Vector#\((\d+),\s*(Bit#\(\d+\))\)\)\s+(\w+)\s+<-\s+mkReg\(unpack\(0\)\);"
    )
    decls = []
    for match in pattern.finditer(text):
        n_elems = int(match.group(1))
        # Threshold tracks MemSize: any backing vector at or above the data/imem
        # size is treated as a "large" vector that gets the RegFile rewrite.
        if n_elems >= 128:
            decls.append(
                {
                    "name": match.group(3),
                    "elements": n_elems,
                    "element_type": match.group(2),
                    "address_bits": (n_elems - 1).bit_length(),
                }
            )
    return sorted(decls, key=lambda item: item["name"])


def _bsv_regfile_decls(text: str) -> list[dict[str, Any]]:
    pattern = re.compile(
        r"RegFile#\(Bit#\((\d+)\),\s*(Bit#\(\d+\))\)\s+(\w+)\s+<-\s+mkRegFileFullZero\(\);"
    )
    return sorted(
        (
            {
                "name": match.group(3),
                "address_bits": int(match.group(1)),
                "element_type": match.group(2),
            }
            for match in pattern.finditer(text)
        ),
        key=lambda item: item["name"],
    )


def _count_regex(text: str, pattern: str) -> int:
    return len(re.findall(pattern, text, flags=re.MULTILINE))


def _module_names(text: str) -> list[str]:
    return sorted(set(re.findall(r"^\s*module\s+(\w+)\b", text, flags=re.MULTILINE)))


def build_audit() -> dict[str, Any]:
    for path in (RAW_BSV, CLEAN_BSV, RAW_VERILOG, SYNTH_VERILOG, TRACKED_RTL):
        if not path.exists():
            raise FileNotFoundError(path)

    bsv_transform = _load_module("bsv_regfile_transform", ROOT / "scripts" / "bsv_regfile_transform.py")
    verilog_transform = _load_module(
        "verilog_synth_transform", ROOT / "scripts" / "verilog_synth_transform.py"
    )

    raw_bsv = RAW_BSV.read_text(encoding="utf-8")
    clean_bsv = CLEAN_BSV.read_text(encoding="utf-8")
    preprocessed_bsv = _preprocess_bsv(raw_bsv)
    with contextlib.redirect_stderr(io.StringIO()):
        regenerated_clean_bsv = bsv_transform.transform_bsv(preprocessed_bsv)

    raw_verilog = RAW_VERILOG.read_text(encoding="utf-8")
    synth_verilog = SYNTH_VERILOG.read_text(encoding="utf-8")
    with contextlib.redirect_stdout(io.StringIO()):
        regenerated_synth_verilog = verilog_transform.transform(raw_verilog)

    tracked_rtl = TRACKED_RTL.read_text(encoding="utf-8")

    bsv_raw_vectors = _bsv_large_vector_decls(preprocessed_bsv)
    bsv_regfiles = _bsv_regfile_decls(clean_bsv)

    expected_regfiles = {
        # MemAddrSz=7 (128 words) — silicon-side bound on imem/mem.
        # lassert_cbuf/lassert_fbuf are 64-entry RegFiles (addr_width=6) per
        # ThieleTypes.LassertCbufIdxSz/LassertFbufIdxSz=6.
        "imem": {"address_bits": 7, "element_type": "Bit#(128)"},
        "mem": {"address_bits": 7, "element_type": "Bit#(32)"},
        "lassert_cbuf": {"address_bits": 6, "element_type": "Bit#(32)"},
        "lassert_fbuf": {"address_bits": 6, "element_type": "Bit#(32)"},
    }
    observed_regfiles = {
        item["name"]: {
            "address_bits": item["address_bits"],
            "element_type": item["element_type"],
        }
        for item in bsv_regfiles
    }

    invariants = {
        "bsv_preprocessed_then_regfile_transform_reproduces_clean_bsv": (
            regenerated_clean_bsv == clean_bsv
        ),
        "verilog_synth_transform_reproduces_synth_verilog": (
            regenerated_synth_verilog == synth_verilog
        ),
        "tracked_rtl_matches_synth_verilog": tracked_rtl == synth_verilog,
        "bsv_expected_regfiles_present": all(
            observed_regfiles.get(name) == spec for name, spec in expected_regfiles.items()
        ),
        "bsv_no_large_vector_mkreg_remains": not _bsv_large_vector_decls(clean_bsv),
        "bsv_wrapper_removed": "module mkThieleCPU" not in clean_bsv,
        "bsv_no_vec_constructor_remains": "vec(" not in clean_bsv,
        "verilog_top_module_preserved": _module_names(raw_verilog) == _module_names(synth_verilog) == ["mkModule1"],
        "verilog_mu_tensor_array_present": "reg [31:0] mt_arr [0:15];" in synth_verilog,
        "verilog_bsc_regfile_submodules_preserved": all(
            snippet in synth_verilog
            for snippet in (
                "// ports of submodule imem",
                "// ports of submodule mem",
                ".D_OUT_1(imem$D_OUT_1)",
                ".D_OUT_1(mem$D_OUT_1)",
            )
        ),
        "verilog_flat_storage_removed": all(
            snippet not in synth_verilog
            for snippet in (
                "reg [8191 : 0] imem;",
                "reg [8191:0] imem;",
                "reg [511 : 0] mu_tensor;",
                "reg [511:0] mu_tensor;",
            )
        ),
    }

    return {
        "manifest_kind": "rtl_text_transform_audit",
        "boundary_statement": (
            "This manifest replays and pins project-local BSV/Verilog text transforms. "
            "It proves byte-for-byte transform reproducibility and allowed storage-shape "
            "rewrites, but it does not prove PP.ml or BSC semantic correctness."
        ),
        "files": {
            "raw_bsv": _file_record(RAW_BSV),
            "clean_bsv": _file_record(CLEAN_BSV),
            "raw_verilog": _file_record(RAW_VERILOG),
            "synth_verilog": _file_record(SYNTH_VERILOG),
            "tracked_rtl": _file_record(TRACKED_RTL),
            "bsv_transform_script": _file_record(ROOT / "scripts" / "bsv_regfile_transform.py"),
            "verilog_transform_script": _file_record(ROOT / "scripts" / "verilog_synth_transform.py"),
        },
        "bsv_transform": {
            "preprocess_steps": [
                "strip generated top wrapper modules mkThieleCPU/mkTop/mk<TOP>",
                "prepend Vector import required by generated vector code",
                "rewrite vec(...) constructors to unpack({...})",
            ],
            "large_vector_sources": bsv_raw_vectors,
            "regfile_targets": bsv_regfiles,
            "sub_reads": clean_bsv.count(".sub("),
            "upd_writes": clean_bsv.count(".upd("),
        },
        "verilog_transform": {
            "raw_modules": _module_names(raw_verilog),
            "synth_modules": _module_names(synth_verilog),
            "storage_rewrites": {
                "imem_arr_refs": synth_verilog.count("imem_arr["),
                "mt_arr_refs": synth_verilog.count("mt_arr["),
                "dm_refs": synth_verilog.count("dm["),
                "rf_refs": synth_verilog.count("rf["),
                "pt_tbl_refs": synth_verilog.count("pt_tbl["),
            },
            "raw_flat_storage_counts": {
                "imem_8192": _count_regex(raw_verilog, r"reg\s+\[8191\s*:\s*0\]\s+imem\s*;"),
                "mu_tensor_512": _count_regex(raw_verilog, r"reg\s+\[511\s*:\s*0\]\s+mu_tensor\s*;"),
                "mem_scalar_regs": _count_regex(raw_verilog, r"reg\s+\[31\s*:\s*0\]\s+mem\d+\s*;"),
                "rf_scalar_regs": _count_regex(raw_verilog, r"reg\s+\[31\s*:\s*0\]\s+reg\d+\s*;"),
                "pt_scalar_regs": _count_regex(raw_verilog, r"reg\s+\[31\s*:\s*0\]\s+pt\d+\s*;"),
            },
        },
        "invariants": invariants,
    }


def write_manifest(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(build_audit(), indent=2, sort_keys=True) + "\n", encoding="utf-8")


def check_manifest(path: Path) -> None:
    expected = json.loads(path.read_text(encoding="utf-8"))
    actual = build_audit()
    if actual != expected:
        print(f"FAIL: {path} is stale or inconsistent", file=sys.stderr)
        print(json.dumps(actual, indent=2, sort_keys=True), file=sys.stderr)
        raise SystemExit(1)
    failing = [name for name, value in actual["invariants"].items() if not value]
    if failing:
        print(f"FAIL: transform audit invariants failed: {', '.join(failing)}", file=sys.stderr)
        raise SystemExit(1)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)

    if args.check:
        check_manifest(args.out)
    else:
        write_manifest(args.out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
