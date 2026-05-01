from __future__ import annotations

import hashlib
from json import dumps
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Protocol

from build.thiele_vm import run_vm_trace
from scripts.thiele_asm import _preprocess_source

from .protocol import EXECUTION_STATE_MODEL, canonical_json_bytes, validate_receipt_path


@dataclass(frozen=True)
class CanonicalProgram:
    source_sha256: str
    canonical_sha256: str
    fuel: int
    line_count: int
    canonical_lines: list[str]


@dataclass(frozen=True)
class ReplayResult:
    pre_state: Any
    post_state: Any


@dataclass(frozen=True)
class StateFacts:
    state_model: str
    pre_state_digest: str
    post_state_digest: str
    mu_start: int
    mu_end: int
    mu_delta: int


class ProgramCanonicalizer(Protocol):
    def canonicalize(self, program_path: Path) -> CanonicalProgram:
        ...


class ExecutionReplayer(Protocol):
    def replay(self, canonical_program: CanonicalProgram, program_path: Path) -> ReplayResult:
        ...


class NormalizedStateDigester(Protocol):
    def collect(self, replay_result: ReplayResult) -> StateFacts:
        ...


@dataclass(frozen=True)
class ExecutionVerifierAdapters:
    canonicalizer: ProgramCanonicalizer
    replayer: ExecutionReplayer
    digester: NormalizedStateDigester


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


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


def _json_canonical_value(value: Any) -> Any:
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if isinstance(value, Path):
        return str(value)
    if isinstance(value, dict):
        return {
            str(key): _json_canonical_value(val)
            for key, val in sorted(value.items(), key=lambda item: str(item[0]))
        }
    if isinstance(value, (list, tuple)):
        return [_json_canonical_value(item) for item in value]
    return repr(value)


def _strip_trailing_zeros(lst: list[int]) -> list[int]:
    """Return list with trailing zero elements removed (canonical compact form)."""
    i = len(lst)
    while i > 0 and lst[i - 1] == 0:
        i -= 1
    return lst[:i]


def _split_init_lines(canonical_lines: list[str]) -> list[str]:
    init_lines: list[str] = []
    for line in canonical_lines:
        parts = line.split()
        if not parts:
            continue
        op = parts[0].upper()
        if op == "FUEL" or op.startswith("INIT_"):
            init_lines.append(line)
    return init_lines


def _normalize_vm_state(state: Any) -> dict[str, Any]:
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
        "regs": [int(value) for value in getattr(state, "regs", [])[:16]],
        "mem": _strip_trailing_zeros([int(value) for value in getattr(state, "mem", [])]),
        "csrs": _json_canonical_value(getattr(state, "csrs", {})),
        "modules": modules,
        "mu_tensor": [int(value) for value in getattr(state, "mu_tensor", [])],
        "logic_acc": int(getattr(state, "logic_acc", 0)),
        "mstatus": int(getattr(state, "mstatus", 0)),
        "certified": bool(getattr(state, "certified", False)),
        "witness": [int(value) for value in getattr(state, "witness", [])],
    }


def _digest_vm_state(state: Any) -> str:
    return _sha256_bytes(canonical_json_bytes(_normalize_vm_state(state)))


class StandaloneProgramCanonicalizer:
    def canonicalize(self, program_path: Path) -> CanonicalProgram:
        source_text = program_path.read_text(encoding="utf-8")
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
        return CanonicalProgram(
            source_sha256=_sha256_file(program_path),
            canonical_sha256=_sha256_bytes(canonical_json_bytes(canonical_program)),
            fuel=_extract_fuel(source_text),
            line_count=len(trace_lines),
            canonical_lines=trace_lines,
        )


class StandaloneExecutionReplayer:
    def replay(self, canonical_program: CanonicalProgram, program_path: Path) -> ReplayResult:
        del program_path
        init_lines = _split_init_lines(canonical_program.canonical_lines)
        pre_state = run_vm_trace(init_lines, fuel=canonical_program.fuel)
        post_state = run_vm_trace(canonical_program.canonical_lines, fuel=canonical_program.fuel)
        return ReplayResult(pre_state=pre_state, post_state=post_state)


class StandaloneNormalizedStateDigester:
    def collect(self, replay_result: ReplayResult) -> StateFacts:
        mu_start = int(getattr(replay_result.pre_state, "mu", 0))
        mu_end = int(getattr(replay_result.post_state, "mu", 0))
        return StateFacts(
            state_model=EXECUTION_STATE_MODEL,
            pre_state_digest=_digest_vm_state(replay_result.pre_state),
            post_state_digest=_digest_vm_state(replay_result.post_state),
            mu_start=mu_start,
            mu_end=mu_end,
            mu_delta=mu_end - mu_start,
        )


def default_execution_adapters() -> ExecutionVerifierAdapters:
    return ExecutionVerifierAdapters(
        canonicalizer=StandaloneProgramCanonicalizer(),
        replayer=StandaloneExecutionReplayer(),
        digester=StandaloneNormalizedStateDigester(),
    )


def verify_execution_receipt(receipt: dict, *, base_dir: Path, adapters: ExecutionVerifierAdapters) -> None:
    program_path = base_dir / validate_receipt_path(receipt["program"]["path"], field_name="program.path")
    if not program_path.exists() or not program_path.is_file():
        raise FileNotFoundError(f"Execution receipt program missing during verification: {program_path}")

    canonical_program = adapters.canonicalizer.canonicalize(program_path)
    replay_result = adapters.replayer.replay(canonical_program, program_path)
    state_facts = adapters.digester.collect(replay_result)

    program = receipt["program"]
    execution = receipt["execution"]

    if canonical_program.source_sha256 != program["source_sha256"]:
        raise ValueError("Execution receipt source_sha256 does not match program file")
    if canonical_program.canonical_sha256 != program["canonical_sha256"]:
        raise ValueError("Execution receipt canonical_sha256 does not match canonicalized program")
    if canonical_program.fuel != program["fuel"]:
        raise ValueError("Execution receipt fuel does not match canonicalized program")
    if canonical_program.line_count != program["line_count"]:
        raise ValueError("Execution receipt line_count does not match canonicalized program")

    if state_facts.state_model != execution["state_model"]:
        raise ValueError(f"Unsupported execution state model: {execution['state_model']!r}")
    if state_facts.pre_state_digest != execution["pre_state_digest"]:
        raise ValueError("Execution receipt pre_state_digest mismatch")
    if state_facts.post_state_digest != execution["post_state_digest"]:
        raise ValueError("Execution receipt post_state_digest mismatch")
    if state_facts.mu_start != execution["mu_start"]:
        raise ValueError("Execution receipt mu_start mismatch")
    if state_facts.mu_end != execution["mu_end"]:
        raise ValueError("Execution receipt mu_end mismatch")
    if state_facts.mu_delta != execution["mu_delta"]:
        raise ValueError("Execution receipt mu_delta mismatch")