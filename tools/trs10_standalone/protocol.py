from __future__ import annotations

import hashlib
import json
from pathlib import PurePath
from typing import Any


TRS10_VERSION = "TRS-1.0"
SIG_SCHEME = "ed25519"
EXECUTION_STATE_MODEL = "thiele.vmstate.v1"


def canonical_json_bytes(obj: dict[str, Any]) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def payload_digest(payload: dict[str, Any]) -> str:
    return hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def validate_receipt_path(path_value: Any, *, field_name: str) -> str:
    if not isinstance(path_value, str) or not path_value:
        raise ValueError(f"{field_name} must be a non-empty string")

    pure_path = PurePath(path_value)
    if pure_path.is_absolute() or pure_path.name != path_value or any(part == ".." for part in pure_path.parts):
        raise ValueError(f"{field_name} uses unsupported path form: {path_value!r}")

    if "\\" in path_value or "/" in path_value:
        raise ValueError(f"{field_name} uses unsupported path form: {path_value!r}")

    return path_value


def validate_hex_string(value: Any, *, field_name: str, expected_length: int) -> str:
    if not isinstance(value, str) or len(value) != expected_length:
        raise ValueError(f"{field_name} must be a {expected_length}-character hex string")
    try:
        bytes.fromhex(value)
    except ValueError as exc:
        raise ValueError(f"{field_name} must be a {expected_length}-character hex string") from exc
    return value


def validate_int_field(value: Any, *, field_name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(f"{field_name} must be an integer")
    return value


def validate_str_field(value: Any, *, field_name: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{field_name} must be a non-empty string")
    return value


def extract_signed_payload(receipt: dict[str, Any]) -> dict[str, Any]:
    if receipt.get("version") != TRS10_VERSION:
        raise ValueError(f"Unsupported receipt version: {receipt.get('version')!r}")

    kind = receipt.get("kind", "fileset")
    payload: dict[str, Any] = {"version": receipt["version"], "kind": kind}

    if kind == "fileset":
        if "program" in receipt or "execution" in receipt:
            raise ValueError("Hybrid fileset receipt must not include execution fields")
        files = receipt.get("files")
        if not isinstance(files, list) or not files:
            raise ValueError("Receipt must contain a non-empty files list")
        for entry in files:
            if not isinstance(entry, dict):
                raise ValueError("Receipt file entries must be objects")
            for field in ("path", "sha256", "size"):
                if field not in entry:
                    raise ValueError(f"Receipt file entry missing field: {field}")
            validate_receipt_path(entry["path"], field_name="fileset.path")
            validate_hex_string(entry["sha256"], field_name="fileset.sha256", expected_length=64)
            validate_int_field(entry["size"], field_name="fileset.size")
        payload["files"] = files
    elif kind == "execution":
        if "files" in receipt:
            raise ValueError("Hybrid execution receipt must not include fileset fields")
        program = receipt.get("program")
        execution = receipt.get("execution")
        if not isinstance(program, dict):
            raise ValueError("Execution receipt missing program object")
        if not isinstance(execution, dict):
            raise ValueError("Execution receipt missing execution object")
        for field in ("path", "source_sha256", "canonical_sha256", "fuel", "line_count"):
            if field not in program:
                raise ValueError(f"Execution receipt program missing field: {field}")
        validate_receipt_path(program["path"], field_name="program.path")
        validate_hex_string(program["source_sha256"], field_name="program.source_sha256", expected_length=64)
        validate_hex_string(program["canonical_sha256"], field_name="program.canonical_sha256", expected_length=64)
        validate_int_field(program["fuel"], field_name="program.fuel")
        validate_int_field(program["line_count"], field_name="program.line_count")
        for field in ("state_model", "pre_state_digest", "post_state_digest", "mu_start", "mu_end", "mu_delta"):
            if field not in execution:
                raise ValueError(f"Execution receipt execution missing field: {field}")
        validate_str_field(execution["state_model"], field_name="execution.state_model")
        validate_hex_string(execution["pre_state_digest"], field_name="execution.pre_state_digest", expected_length=64)
        validate_hex_string(execution["post_state_digest"], field_name="execution.post_state_digest", expected_length=64)
        validate_int_field(execution["mu_start"], field_name="execution.mu_start")
        validate_int_field(execution["mu_end"], field_name="execution.mu_end")
        validate_int_field(execution["mu_delta"], field_name="execution.mu_delta")
        payload["program"] = program
        payload["execution"] = execution
    else:
        raise ValueError(f"Unsupported receipt kind: {kind!r}")

    if "metadata" in receipt:
        payload["metadata"] = receipt["metadata"]
    if "key_id" in receipt:
        validate_str_field(receipt["key_id"], field_name="key_id")
        payload["key_id"] = receipt["key_id"]

    if "global_digest" not in receipt:
        raise ValueError("Receipt missing global_digest")
    validate_hex_string(receipt["global_digest"], field_name="global_digest", expected_length=64)
    if receipt.get("sig_scheme") != SIG_SCHEME:
        raise ValueError(f"Unsupported signature scheme: {receipt.get('sig_scheme')!r}")
    if "signature" not in receipt:
        raise ValueError("Receipt missing signature")
    validate_hex_string(receipt["signature"], field_name="signature", expected_length=128)

    return payload