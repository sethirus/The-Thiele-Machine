from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import (
    Ed25519PrivateKey,
    Ed25519PublicKey,
)


TRS10_VERSION = "TRS-1.0"
SIG_SCHEME = "ed25519"
EXECUTION_STATE_MODEL = "thiele.vmstate.v1"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_json_bytes(obj: dict[str, Any]) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def _json_canonical_value(value: Any) -> Any:
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if isinstance(value, Path):
        return str(value)
    if isinstance(value, dict):
        return {str(key): _json_canonical_value(val) for key, val in sorted(value.items(), key=lambda item: str(item[0]))}
    if isinstance(value, (list, tuple)):
        return [_json_canonical_value(item) for item in value]
    return repr(value)


def normalize_file_entries(files: list[Path]) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    seen_paths: set[str] = set()
    for file_path in sorted(files, key=lambda item: item.name):
        path = Path(file_path)
        if not path.exists() or not path.is_file():
            raise FileNotFoundError(f"Input file does not exist or is not a file: {path}")
        display_path = path.name
        if display_path in seen_paths:
            raise ValueError(f"Duplicate file basename in receipt set: {display_path}")
        seen_paths.add(display_path)
        entries.append(
            {
                "path": display_path,
                "sha256": sha256_file(path),
                "size": path.stat().st_size,
            }
        )
    return entries


def build_receipt_payload(
    files: list[Path],
    *,
    metadata: Any = ...,
    key_id: str | None = None,
) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "version": TRS10_VERSION,
        "kind": "fileset",
        "files": normalize_file_entries(files),
    }
    if metadata is not ...:
        payload["metadata"] = metadata
    if key_id:
        payload["key_id"] = key_id
    return payload


def payload_digest(payload: dict[str, Any]) -> str:
    return sha256_bytes(canonical_json_bytes(payload))


def sign_receipt_payload(
    payload: dict[str, Any],
    *,
    private_key: Ed25519PrivateKey,
    include_public_key: bool = False,
) -> dict[str, Any]:
    digest = payload_digest(payload)
    receipt = dict(payload)
    receipt["global_digest"] = digest
    receipt["sig_scheme"] = SIG_SCHEME
    receipt["signature"] = private_key.sign(digest.encode("utf-8")).hex()
    if include_public_key:
        receipt["public_key"] = private_key.public_key().public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw,
        ).hex()
    return receipt


def _extract_fuel(source_text: str, default: int = 256) -> int:
    for raw in source_text.splitlines():
        line = raw.strip()
        if not line:
            continue
        for comment_char in ("#", ";", "//"):
            index = line.find(comment_char)
            if index >= 0:
                line = line[:index].strip()
        if not line:
            continue
        parts = line.split()
        if parts and parts[0].upper() == "FUEL" and len(parts) > 1:
            return int(parts[1], 0)
    return default


def canonicalize_program_source(source_path: Path) -> dict[str, Any]:
    from scripts.thiele_asm import _preprocess_source

    source_text = source_path.read_text(encoding="utf-8")
    preprocessed_lines, _ = _preprocess_source(source_text)
    trace_lines: list[str] = [f"FUEL {_extract_fuel(source_text)}"]
    for line in preprocessed_lines:
        parts = line.split()
        if not parts:
            continue
        if parts[0].upper() == ".DATA" and len(parts) >= 3:
            trace_lines.append(f"INIT_MEM {parts[1]} {parts[2]}")
        else:
            trace_lines.append(line)

    canonical_program = {
        "format": "thiele.trace.v1",
        "lines": trace_lines,
    }
    return {
        "source_path": source_path.name,
        "source_sha256": sha256_file(source_path),
        "canonical_lines": trace_lines,
        "canonical_sha256": sha256_bytes(canonical_json_bytes(canonical_program)),
        "fuel": _extract_fuel(source_text),
        "line_count": len(trace_lines),
    }


def split_init_lines(canonical_lines: list[str]) -> list[str]:
    init_lines: list[str] = []
    for line in canonical_lines:
        parts = line.split()
        if not parts:
            continue
        op = parts[0].upper()
        if op == "FUEL" or op.startswith("INIT_"):
            init_lines.append(line)
    return init_lines


def _strip_trailing_zeros(lst: list[int]) -> list[int]:
    """Return list with trailing zero elements removed (canonical compact form)."""
    i = len(lst)
    while i > 0 and lst[i - 1] == 0:
        i -= 1
    return lst[:i]


def normalize_vm_state(state: Any) -> dict[str, Any]:
    modules = []
    for module in getattr(state, "modules", []):
        modules.append(
            {
                "id": int(getattr(module, "id", 0)),
                "region": [int(item) for item in getattr(module, "region", [])],
                "axioms": _json_canonical_value(getattr(module, "axioms", [])),
            }
        )
    modules.sort(key=lambda item: item["id"])

    return {
        "pc": int(getattr(state, "pc", 0)),
        "mu": int(getattr(state, "mu", 0)),
        "err": bool(getattr(state, "err", False)),
        "regs": [int(value) for value in getattr(state, "regs", [])[:32]],
        "mem": _strip_trailing_zeros([int(value) for value in getattr(state, "mem", [])]),
        "csrs": _json_canonical_value(getattr(state, "csrs", {})),
        "modules": modules,
        "mu_tensor": [int(value) for value in getattr(state, "mu_tensor", [])],
        "logic_acc": int(getattr(state, "logic_acc", 0)),
        "mstatus": int(getattr(state, "mstatus", 0)),
        "certified": bool(getattr(state, "certified", False)),
        "witness": [int(value) for value in getattr(state, "witness", [])],
    }


def digest_vm_state(state: Any) -> str:
    return sha256_bytes(canonical_json_bytes(normalize_vm_state(state)))


def build_execution_receipt_payload(
    *,
    program_path: Path,
    pre_state: Any,
    post_state: Any,
    metadata: Any = ...,
    key_id: str | None = None,
) -> dict[str, Any]:
    program = canonicalize_program_source(program_path)
    mu_start = int(getattr(pre_state, "mu", 0))
    mu_end = int(getattr(post_state, "mu", 0))
    payload: dict[str, Any] = {
        "version": TRS10_VERSION,
        "kind": "execution",
        "program": {
            "path": program["source_path"],
            "source_sha256": program["source_sha256"],
            "canonical_sha256": program["canonical_sha256"],
            "fuel": program["fuel"],
            "line_count": program["line_count"],
        },
        "execution": {
            "state_model": EXECUTION_STATE_MODEL,
            "pre_state_digest": digest_vm_state(pre_state),
            "post_state_digest": digest_vm_state(post_state),
            "mu_start": mu_start,
            "mu_end": mu_end,
            "mu_delta": mu_end - mu_start,
        },
    }
    if metadata is not ...:
        payload["metadata"] = metadata
    if key_id:
        payload["key_id"] = key_id
    return payload


def load_private_key_from_hex_file(path: Path) -> Ed25519PrivateKey:
    text = path.read_text(encoding="utf-8").strip()
    raw = bytes.fromhex(text)
    if len(raw) != 32:
        raise ValueError("Ed25519 private key hex must encode exactly 32 bytes")
    return Ed25519PrivateKey.from_private_bytes(raw)


def load_public_key_from_hex(hex_text: str) -> Ed25519PublicKey:
    raw = bytes.fromhex(hex_text.strip())
    if len(raw) != 32:
        raise ValueError("Ed25519 public key hex must encode exactly 32 bytes")
    return Ed25519PublicKey.from_public_bytes(raw)


def verify_receipt_structure(receipt: dict[str, Any]) -> dict[str, Any]:
    if receipt.get("version") != TRS10_VERSION:
        raise ValueError(f"Unsupported receipt version: {receipt.get('version')!r}")
    kind = receipt.get("kind", "fileset")
    if kind == "fileset":
        files = receipt.get("files")
        if not isinstance(files, list) or not files:
            raise ValueError("Receipt must contain a non-empty files list")
        for entry in files:
            if not isinstance(entry, dict):
                raise ValueError("Receipt file entries must be objects")
            for field in ("path", "sha256", "size"):
                if field not in entry:
                    raise ValueError(f"Receipt file entry missing field: {field}")
    elif kind == "execution":
        program = receipt.get("program")
        execution = receipt.get("execution")
        if not isinstance(program, dict):
            raise ValueError("Execution receipt missing program object")
        if not isinstance(execution, dict):
            raise ValueError("Execution receipt missing execution object")
        for field in ("path", "source_sha256", "canonical_sha256", "fuel", "line_count"):
            if field not in program:
                raise ValueError(f"Execution receipt program missing field: {field}")
        for field in ("state_model", "pre_state_digest", "post_state_digest", "mu_start", "mu_end", "mu_delta"):
            if field not in execution:
                raise ValueError(f"Execution receipt execution missing field: {field}")
    else:
        raise ValueError(f"Unsupported receipt kind: {kind!r}")
    if "global_digest" not in receipt:
        raise ValueError("Receipt missing global_digest")
    if receipt.get("sig_scheme") != SIG_SCHEME:
        raise ValueError(f"Unsupported signature scheme: {receipt.get('sig_scheme')!r}")
    if "signature" not in receipt:
        raise ValueError("Receipt missing signature")
    payload = {"version": receipt["version"], "kind": kind}
    if kind == "fileset":
        payload["files"] = receipt["files"]
    else:
        payload["program"] = receipt["program"]
        payload["execution"] = receipt["execution"]
    if "metadata" in receipt:
        payload["metadata"] = receipt["metadata"]
    if "key_id" in receipt:
        payload["key_id"] = receipt["key_id"]
    return payload


def verify_receipt(receipt: dict[str, Any], *, trusted_public_key_hex: str, base_dir: Path | None = None) -> None:
    payload = verify_receipt_structure(receipt)
    expected_digest = payload_digest(payload)
    if receipt["global_digest"] != expected_digest:
        raise ValueError("Receipt global_digest does not match canonical payload digest")

    public_key = load_public_key_from_hex(trusted_public_key_hex)
    public_key.verify(bytes.fromhex(receipt["signature"]), expected_digest.encode("utf-8"))

    if payload["kind"] == "fileset" and base_dir is not None:
        for entry in receipt["files"]:
            path = base_dir / entry["path"]
            if not path.exists() or not path.is_file():
                raise FileNotFoundError(f"Receipt file missing during verification: {path}")
            actual_sha = sha256_file(path)
            if actual_sha != entry["sha256"]:
                raise ValueError(f"Digest mismatch for {entry['path']}")
            actual_size = path.stat().st_size
            if actual_size != entry["size"]:
                raise ValueError(f"Size mismatch for {entry['path']}")
    elif payload["kind"] == "execution":
        if base_dir is None:
            raise ValueError("Execution receipt verification requires a base_dir")
        from build.thiele_vm import run_vm_trace

        program_path = base_dir / receipt["program"]["path"]
        if not program_path.exists() or not program_path.is_file():
            raise FileNotFoundError(f"Execution receipt program missing during verification: {program_path}")

        canonical_program = canonicalize_program_source(program_path)
        if canonical_program["source_sha256"] != receipt["program"]["source_sha256"]:
            raise ValueError("Execution receipt source_sha256 does not match program file")
        if canonical_program["canonical_sha256"] != receipt["program"]["canonical_sha256"]:
            raise ValueError("Execution receipt canonical_sha256 does not match canonicalized program")
        if canonical_program["fuel"] != receipt["program"]["fuel"]:
            raise ValueError("Execution receipt fuel does not match canonicalized program")

        canonical_lines = canonical_program["canonical_lines"]
        init_lines = split_init_lines(canonical_lines)
        pre_state = run_vm_trace(init_lines, fuel=canonical_program["fuel"])
        post_state = run_vm_trace(canonical_lines, fuel=canonical_program["fuel"])

        execution = receipt["execution"]
        if execution["state_model"] != EXECUTION_STATE_MODEL:
            raise ValueError(f"Unsupported execution state model: {execution['state_model']!r}")
        if digest_vm_state(pre_state) != execution["pre_state_digest"]:
            raise ValueError("Execution receipt pre_state_digest mismatch")
        if digest_vm_state(post_state) != execution["post_state_digest"]:
            raise ValueError("Execution receipt post_state_digest mismatch")

        mu_start = int(getattr(pre_state, "mu", 0))
        mu_end = int(getattr(post_state, "mu", 0))
        mu_delta = mu_end - mu_start
        if execution["mu_start"] != mu_start:
            raise ValueError("Execution receipt mu_start mismatch")
        if execution["mu_end"] != mu_end:
            raise ValueError("Execution receipt mu_end mismatch")
        if execution["mu_delta"] != mu_delta:
            raise ValueError("Execution receipt mu_delta mismatch")