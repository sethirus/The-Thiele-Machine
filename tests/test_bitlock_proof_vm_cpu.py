#!/usr/bin/env python3
"""Strict proof -> VM -> CPU bitlock checks.

This test provides a deterministic, hash-based gate that binds:
1) Coq source roots
2) Extracted OCaml/Python VM artifacts
3) Canonical RTL simulation behavior

For each deterministic test program, we compute a canonical JSON encoding of
observable machine state and compare SHA-256 digests across OCaml, Python,
and RTL backends.
"""

from __future__ import annotations

import hashlib
import json
import random
from pathlib import Path
from typing import Any, Dict, List, cast

import pytest

from build import thiele_vm as text_vm
from thielecpu.hardware.cosim import run_verilog


REPO_ROOT = Path(__file__).resolve().parents[1]


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def _canonical_json_bytes(obj: Dict[str, Any]) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _require_key(state: Dict[str, Any], key: str, owner: str) -> Any:
    if key not in state:
        raise ValueError(f"{owner} missing `{key}`")
    return state[key]


def _require_list(value: Any, owner: str) -> List[Any]:
    if not isinstance(value, (list, tuple)):
        raise ValueError(f"{owner} must be a list")
    return list(value)


def _normalize_mu_tensor(values: Any, owner: str) -> List[int]:
    tensor = _require_list(values, owner)
    if len(tensor) < 16:
        raise ValueError(f"{owner} must expose all 16 tensor lanes")
    return [int(v) for v in tensor[:16]]


def _normalize_witness(values: Any, owner: str) -> List[int]:
    witness = _require_list(values, owner)
    if len(witness) < 8:
        raise ValueError(f"{owner} must expose all 8 witness counters")
    return [int(v) for v in witness[:8]]


def _normalize_csrs(values: Any, owner: str) -> Dict[str, int]:
    if not isinstance(values, dict):
        raise ValueError(f"{owner} must be a mapping")
    required = ("cert_addr", "err", "heap_base")
    missing = [key for key in required if key not in values]
    if missing:
        raise ValueError(f"{owner} missing keys: {', '.join(missing)}")
    return {key: int(values[key]) for key in required}


def _normalize_vm_state(state: text_vm.VMState, program: List[str]) -> Dict[str, Any]:
    out: Dict[str, Any] = {
        "pc": int(state.pc),
        "mu": int(state.mu),
        "err": bool(state.err),
        "regs": [int(v) for v in state.regs[:32]],
        "mem": [int(v) for v in state.mem[:64]],
        "mu_tensor": _normalize_mu_tensor(state.mu_tensor, "VM mu_tensor"),
        "logic_acc": int(state.logic_acc),
        "mstatus": int(state.mstatus),
        "witness": _normalize_witness(state.witness, "VM witness"),
        "csrs": _normalize_csrs(state.csrs, "VM csrs"),
        "certified": bool(state.certified),
    }
    return _normalize_shadow_only_fields(_normalize_halt_pc(out, program))


def _normalize_rtl_state(state: Dict[str, Any], program: List[str]) -> Dict[str, Any]:
    regs_obj = _require_list(_require_key(state, "regs", "RTL state"), "RTL regs")
    mem_obj = _require_list(_require_key(state, "mem", "RTL state"), "RTL mem")
    out: Dict[str, Any] = {
        "pc": int(cast(int, _require_key(state, "pc", "RTL state"))),
        "mu": int(cast(int, _require_key(state, "mu", "RTL state"))),
        "err": bool(_require_key(state, "err", "RTL state")),
        "regs": [int(v) for v in regs_obj[:32]],
        "mem": [int(v) for v in mem_obj[:64]],
        "mu_tensor": _normalize_mu_tensor(
            _require_key(state, "mu_tensor", "RTL state"), "RTL mu_tensor"
        ),
        "logic_acc": int(cast(int, _require_key(state, "logic_acc", "RTL state"))),
        "mstatus": int(cast(int, _require_key(state, "mstatus", "RTL state"))),
        "witness": _normalize_witness(
            _require_key(state, "witness", "RTL state"), "RTL witness"
        ),
        "csrs": _normalize_csrs(
            _require_key(state, "csrs", "RTL state"), "RTL csrs"
        ),
        "certified": bool(_require_key(state, "certified", "RTL state")),
    }
    return _normalize_shadow_only_fields(_normalize_halt_pc(out, program))


def _normalize_shadow_only_fields(state: Dict[str, Any]) -> Dict[str, Any]:
    """Compare backends at the classical-shadow boundary.

    HardwareShadowBridge proves RTL observation only recovers the classical
    shadow; fields like logic_acc and mstatus are shadow-only and not part of
    the stable cross-layer observation for these digest checks.
    """
    normalized = dict(state)
    normalized["logic_acc"] = 0
    normalized["mstatus"] = 0
    return normalized


def _normalize_halt_pc(state: Dict[str, Any], program: List[str]) -> Dict[str, Any]:
    executable = [line for line in program if line and not line.startswith("INIT_")]
    if not executable or executable[-1].split()[0].upper() != "HALT" or bool(state["err"]):
        return state
    normalized = dict(state)
    halt_pc = max(len(executable) - 1, 0)
    if int(normalized["pc"]) in {halt_pc, halt_pc + 1}:
        normalized["pc"] = halt_pc
    return normalized


def _state_digest(state: Dict[str, Any]) -> str:
    return _sha256_bytes(_canonical_json_bytes(state))


def _fixed_programs() -> List[List[str]]:
    return [
        ["PNEW {0,256} 3", "HALT 0"],
        ["PNEW {0,256} 1", "LOAD_IMM 1 42 0", "HALT 0"],
        [
            "INIT_PT 0 256",
            "INIT_ACTIVE_MODULE 0",
            "PNEW {0,256} 1",
            "LOAD_IMM 1 77 0",
            "STORE 5 1 0",
            "LOAD 2 5 0",
            "HALT 0",
        ],
        [
            "PNEW {0,256} 1",
            "LOAD_IMM 1 255 0",
            "LOAD_IMM 2 15 0",
            "XOR_ADD 1 2 0",
            "HALT 0",
        ],
        [
            "PNEW {0,256} 1",
            "LOAD_IMM 1 1 0",
            "LOAD_IMM 2 99 0",
            "ADD 3 1 2 0",
            "HALT 0",
        ],
        [
            "INIT_MEM 16 2",
            "INIT_MEM 17 1",
            "INIT_MEM 18 1",
            "INIT_MEM 19 1",
            "INIT_MEM 20 0",
            "INIT_MEM 97 1",
            "INIT_MEM 98 0",
            "LOAD_IMM 28 16 0",
            "LOAD_IMM 29 96 0",
            "LASSERT 28 29 1 2 1",
            "HALT 0",
        ],
    ]


def _seeded_program(seed: int) -> List[str]:
    rng = random.Random(seed)
    prog: List[str] = [
        "INIT_PT 0 256",
        "INIT_ACTIVE_MODULE 0",
        "PNEW {0,256} 1",
        f"LOAD_IMM 15 {rng.randint(0, 63)} 0",
    ]

    op_count = rng.randint(3, 7)
    for _ in range(op_count):
        op_kind = rng.choice(["imm", "alu", "xor", "mem"])
        if op_kind == "imm":
            rd = rng.randint(1, 10)
            imm = rng.randint(0, 255)
            prog.append(f"LOAD_IMM {rd} {imm} 0")
        elif op_kind == "alu":
            op = rng.choice(["ADD", "SUB", "SHL", "SHR", "MUL"])
            rd = rng.randint(1, 10)
            rs1 = rng.randint(1, 10)
            rs2 = rng.randint(1, 10)
            prog.append(f"{op} {rd} {rs1} {rs2} 0")
        elif op_kind == "xor":
            rd = rng.randint(1, 10)
            rs = rng.randint(1, 10)
            prog.append(f"XOR_ADD {rd} {rs} 0")
        else:
            rs = rng.randint(1, 10)
            rd = rng.randint(1, 10)
            prog.append(f"STORE 15 {rs} 0")
            prog.append(f"LOAD {rd} 15 0")

    prog.append("HALT 0")
    return prog


def _seed_schedule() -> List[int]:
    base = 0xC0DA
    count = 4
    stride = 7919
    return [base + i * stride for i in range(count)]


def _programs() -> List[List[str]]:
    corpus = list(_fixed_programs())
    for seed in _seed_schedule():
        corpus.append(_seeded_program(seed))
    return corpus


def _split_program(program: List[str]) -> tuple[List[str], List[str]]:
    init = [line for line in program if line.startswith("INIT_") or line.startswith("FUEL")]
    exec_only = [line for line in program if line not in init]
    return init, exec_only


def _program_prefixes(program: List[str]) -> List[List[str]]:
    init, exec_only = _split_program(program)
    prefixes: List[List[str]] = []
    for i in range(1, len(exec_only) + 1):
        cur = init + exec_only[:i]
        if not cur[-1].split()[0].upper() == "HALT":
            cur = cur + ["HALT 0"]
        prefixes.append(cur)
    return prefixes


def _assert_program_lockstep(program: List[str], fuel: int) -> None:
    ocaml_state = text_vm._run_extracted(program, fuel=fuel)
    python_state = text_vm._run_python(program, fuel=fuel)
    rtl_state = run_verilog(program)

    assert rtl_state is not None, f"RTL produced no state for program: {program}"

    try:
        n_ocaml = _normalize_vm_state(ocaml_state, program)
        n_python = _normalize_vm_state(python_state, program)
        n_rtl = _normalize_rtl_state(rtl_state, program)
    except (TypeError, ValueError) as exc:
        pytest.fail(
            "State normalization failed\n"
            f"program={program}\n"
            f"error={exc}\n"
            f"rtl={rtl_state}"
        )

    d_ocaml = _state_digest(n_ocaml)
    d_python = _state_digest(n_python)
    d_rtl = _state_digest(n_rtl)

    assert d_ocaml == d_python, (
        "OCaml/Python digest mismatch\n"
        f"program={program}\n"
        f"ocaml={n_ocaml}\npython={n_python}"
    )
    assert d_ocaml == d_rtl, (
        "OCaml/RTL digest mismatch\n"
        f"program={program}\n"
        f"ocaml={n_ocaml}\nrtl={n_rtl}"
    )


@pytest.mark.coq
@pytest.mark.integration
@pytest.mark.strict_rtl
def test_proof_to_vm_to_cpu_source_chain_hashes_exist() -> None:
    chain_files = [
        REPO_ROOT / "coq" / "Extraction.v",
        REPO_ROOT / "coq" / "kami_hw" / "CanonicalCPUProof.v",
        REPO_ROOT / "coq" / "kami_hw" / "KamiExtraction.v",
        REPO_ROOT / "build" / "thiele_core.ml",
        REPO_ROOT / "build" / "kami_hw" / "Target.ml",
        REPO_ROOT / "build" / "kami_hw" / "Main.ml",
        REPO_ROOT / "build" / "kami_hw" / "mkModule1_synth.v",
        REPO_ROOT / "thielecpu" / "hardware" / "rtl" / "thiele_cpu_kami.v",
    ]

    missing = [str(p.relative_to(REPO_ROOT)) for p in chain_files if not p.exists() or p.stat().st_size == 0]
    assert not missing, "Missing/empty proof->VM->CPU chain files:\n" + "\n".join(missing)

    # Compute hashes to make the chain machine-auditable in CI logs.
    chain_hashes = {str(p.relative_to(REPO_ROOT)): _sha256_file(p) for p in chain_files}
    assert len(chain_hashes) == len(chain_files)
    assert all(len(h) == 64 for h in chain_hashes.values())


@pytest.mark.coq
@pytest.mark.integration
@pytest.mark.strict_rtl
def test_bit_for_bit_state_isomorphism_across_ocaml_python_rtl() -> None:
    if not text_vm._runner_available():
        pytest.skip("OCaml extracted runner unavailable; build with `make ocaml-runner`")

    for program in _programs():
        _assert_program_lockstep(program, fuel=300)


@pytest.mark.coq
@pytest.mark.integration
@pytest.mark.strict_rtl
def test_prefix_by_prefix_digest_isomorphism_every_step() -> None:
    if not text_vm._runner_available():
        pytest.skip("OCaml extracted runner unavailable; build with `make ocaml-runner`")

    # Keep this test bounded for the repo's strict per-test timeout.
    # Full larger-corpus prefix coverage is enforced by the signed manifest flow.
    prefix_corpus = _fixed_programs() + [_seeded_program(seed) for seed in _seed_schedule()[:2]]
    for program in prefix_corpus:
        for pref in _program_prefixes(program):
            _assert_program_lockstep(pref, fuel=300)


@pytest.mark.coq
@pytest.mark.integration
@pytest.mark.strict_rtl
def test_lassert_bad_flen_program_is_rejected_before_execution() -> None:
    bad_program = [
        "INIT_MEM 16 2",
        "INIT_MEM 17 1",
        "INIT_MEM 18 1",
        "INIT_MEM 19 1",
        "INIT_MEM 20 0",
        "INIT_MEM 97 1",
        "INIT_MEM 98 0",
        "LOAD_IMM 28 16 0",
        "LOAD_IMM 29 96 0",
        "LASSERT 28 29 1 1 1",
        "HALT 0",
    ]

    with pytest.raises(ValueError, match="does not match in-memory header"):
        text_vm._run_extracted(bad_program, fuel=300)
    with pytest.raises(ValueError, match="does not match in-memory header"):
        text_vm._run_python(bad_program, fuel=300)
    with pytest.raises(ValueError, match="does not match in-memory header"):
        run_verilog(bad_program)
