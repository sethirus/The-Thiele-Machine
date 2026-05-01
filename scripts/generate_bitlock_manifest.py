#!/usr/bin/env python3
"""Generate a deterministic proof->VM->CPU bitlock manifest.

Outputs JSON with:
- SHA-256 hashes of source-of-truth and extracted artifacts
- Per-program normalized state digests for OCaml, Python, RTL
- Aggregate manifest hash for reproducible attestation
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
from pathlib import Path
from typing import Any, Dict, List, cast

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import (
    Ed25519PrivateKey,
    Ed25519PublicKey,
)

from build import thiele_vm as text_vm
from thielecpu.hardware.cosim import run_verilog


REPO_ROOT = Path(__file__).resolve().parents[1]


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def canonical_json_bytes(obj: Dict[str, Any]) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")


def normalize_halt_pc(state: Dict[str, Any], program: List[str]) -> Dict[str, Any]:
    executable = [line for line in program if line and not line.startswith("INIT_")]
    if not executable or executable[-1].split()[0].upper() != "HALT" or bool(state["err"]):
        return state
    normalized = dict(state)
    halt_pc = max(len(executable) - 1, 0)
    if int(normalized["pc"]) in {halt_pc, halt_pc + 1}:
        normalized["pc"] = halt_pc
    return normalized


def normalize_vm_state(state: text_vm.VMState, program: List[str]) -> Dict[str, Any]:
    return normalize_halt_pc(
        {
            "pc": int(state.pc),
            "mu": int(state.mu),
            "err": bool(state.err),
            "regs": [int(v) for v in state.regs[:32]],
            "mem": [int(v) for v in state.mem[:64]],
            "logic_acc": int(state.logic_acc),
            "mstatus": int(state.mstatus),
            "certified": bool(state.certified),
        },
        program,
    )


def normalize_rtl_state(state: Dict[str, Any], program: List[str]) -> Dict[str, Any]:
    regs_obj = cast(List[Any], state.get("regs", []))
    mem_obj = cast(List[Any], state.get("mem", []))
    return normalize_halt_pc(
        {
            "pc": int(cast(int, state.get("pc", 0))),
            "mu": int(cast(int, state.get("mu", 0))),
            "err": bool(state.get("err", False)),
            "regs": [int(v) for v in regs_obj[:32]],
            "mem": [int(v) for v in mem_obj[:64]],
            "logic_acc": int(cast(int, state.get("logic_acc", 0))),
            "mstatus": int(cast(int, state.get("mstatus", 0))),
            "certified": bool(state.get("certified", False)),
        },
        program,
    )


def state_digest(state: Dict[str, Any]) -> str:
    return sha256_bytes(canonical_json_bytes(state))


def fixed_programs() -> List[List[str]]:
    return [
        ["PNEW {0,256} 3", "HALT 0"],
        ["PNEW {0,256} 1", "LOAD_IMM 1 42 0", "HALT 0"],
        [
            "INIT_PT 0 128",
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
    ]


def seeded_program(seed: int) -> List[str]:
    rng = random.Random(seed)
    prog: List[str] = [
        "INIT_PT 0 128",
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


def seed_schedule(base: int, count: int, stride: int) -> List[int]:
    return [base + i * stride for i in range(count)]


def programs(base: int, count: int, stride: int) -> List[List[str]]:
    corpus = list(fixed_programs())
    for seed in seed_schedule(base, count, stride):
        corpus.append(seeded_program(seed))
    return corpus


def split_program(program: List[str]) -> tuple[List[str], List[str]]:
    init = [line for line in program if line.startswith("INIT_") or line.startswith("FUEL")]
    exec_only = [line for line in program if line not in init]
    return init, exec_only


def program_prefixes(program: List[str]) -> List[List[str]]:
    init, exec_only = split_program(program)
    prefixes: List[List[str]] = []
    for i in range(1, len(exec_only) + 1):
        cur = init + exec_only[:i]
        if not cur[-1].split()[0].upper() == "HALT":
            cur = cur + ["HALT 0"]
        prefixes.append(cur)
    return prefixes


def lockstep_digest(program: List[str], fuel: int) -> str:
    ocaml = text_vm._run_extracted(program, fuel=fuel)
    py = text_vm._run_python(program, fuel=fuel)
    rtl = run_verilog(program)
    if rtl is None:
        raise RuntimeError(f"RTL produced no state for program: {program}")

    n_ocaml = normalize_vm_state(ocaml, program)
    n_py = normalize_vm_state(py, program)
    n_rtl = normalize_rtl_state(rtl, program)

    d_ocaml = state_digest(n_ocaml)
    d_py = state_digest(n_py)
    d_rtl = state_digest(n_rtl)

    if not (d_ocaml == d_py == d_rtl):
        raise RuntimeError(
            "Cross-layer digest mismatch\n"
            f"program={program}\n"
            f"ocaml={d_ocaml}\npython={d_py}\nrtl={d_rtl}"
        )
    return d_ocaml


def load_or_create_signing_key(key_path: Path) -> Ed25519PrivateKey:
    if key_path.exists() and key_path.stat().st_size > 0:
        return cast(
            Ed25519PrivateKey,
            serialization.load_pem_private_key(key_path.read_bytes(), password=None),
        )

    key_path.parent.mkdir(parents=True, exist_ok=True)
    private_key = Ed25519PrivateKey.generate()
    key_path.write_bytes(
        private_key.private_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PrivateFormat.PKCS8,
            encryption_algorithm=serialization.NoEncryption(),
        )
    )
    pub_path = key_path.with_suffix(".pub.pem")
    pub_path.write_bytes(
        private_key.public_key().public_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PublicFormat.SubjectPublicKeyInfo,
        )
    )
    return private_key


def public_key_hex(pub: Ed25519PublicKey) -> str:
    return pub.public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    ).hex()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        default="artifacts/isomorphism_bitlock_manifest.json",
        help="Output manifest path",
    )
    parser.add_argument("--seed-base", type=int, default=0xC0DA, help="Deterministic seed base")
    parser.add_argument("--seed-count", type=int, default=16, help="Number of generated seeds")
    parser.add_argument("--seed-stride", type=int, default=7919, help="Deterministic seed stride")
    parser.add_argument(
        "--signing-key-file",
        default="artifacts/keys/bitlock_ed25519_private.pem",
        help="Ed25519 private key path (created if missing)",
    )
    args = parser.parse_args()

    if not text_vm._runner_available():
        raise RuntimeError("OCaml extracted runner unavailable; run `make ocaml-runner`")

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
    if missing:
        raise RuntimeError("Missing/empty chain files:\n" + "\n".join(missing))

    chain_hashes = {str(p.relative_to(REPO_ROOT)): sha256_file(p) for p in chain_files}

    seeds = seed_schedule(args.seed_base, args.seed_count, args.seed_stride)
    program_entries: List[Dict[str, Any]] = []
    corpus = programs(args.seed_base, args.seed_count, args.seed_stride)
    for idx, program in enumerate(corpus):
        final_digest = lockstep_digest(program, fuel=500)
        prefix_digests = [lockstep_digest(pref, fuel=500) for pref in program_prefixes(program)]

        entry: Dict[str, Any] = {
            "id": idx,
            "program": program,
            "final_digest": final_digest,
            "prefix_digests": prefix_digests,
        }
        if idx >= len(fixed_programs()):
            entry["seed"] = seeds[idx - len(fixed_programs())]
        program_entries.append(entry)

    manifest_unsigned: Dict[str, Any] = {
        "schema": "thiele.bitlock.v2",
        "seed_schedule": {
            "base": args.seed_base,
            "count": args.seed_count,
            "stride": args.seed_stride,
            "seeds": seeds,
        },
        "chain_hashes": chain_hashes,
        "programs": program_entries,
    }

    unsigned_bytes = canonical_json_bytes(manifest_unsigned)
    aggregate_digest = sha256_bytes(unsigned_bytes)

    signing_key = load_or_create_signing_key(Path(args.signing_key_file))
    signature = signing_key.sign(unsigned_bytes)
    pub = signing_key.public_key()

    manifest: Dict[str, Any] = dict(manifest_unsigned)
    manifest["aggregate_digest"] = aggregate_digest
    manifest["signature"] = {
        "algorithm": "ed25519",
        "public_key_hex": public_key_hex(pub),
        "signature_hex": signature.hex(),
        "signed_over": "canonical_json(manifest_without_signature_and_aggregate_digest)",
    }

    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Wrote {out_path}")
    print(f"aggregate_digest={manifest['aggregate_digest']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
