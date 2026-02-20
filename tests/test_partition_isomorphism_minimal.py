import json
import os
import random
import subprocess
import tempfile
from pathlib import Path

import pytest

from thielecpu.state import State
from thielecpu.vm import VM


REPO_ROOT = Path(__file__).parent.parent
HARDWARE_DIR = REPO_ROOT / "thielecpu" / "hardware"
RTL_DIR = HARDWARE_DIR / "rtl"
TESTBENCH_DIR = HARDWARE_DIR / "testbench"
BUILD_DIR = REPO_ROOT / "build"


def _encode_word(opcode: int, a: int = 0, b: int = 0, cost: int = 0) -> int:
    return ((opcode & 0xFF) << 24) | ((a & 0xFF) << 16) | ((b & 0xFF) << 8) | (cost & 0xFF)


def _write_hex_words(path: Path, words: list[int]) -> None:
    path.write_text("\n".join(f"{w & 0xFFFFFFFF:08x}" for w in words) + "\n", encoding="utf-8")


def _region_token(indices: set[int]) -> str:
    # Match the extracted-runner region parser: "{0,2,3}" (no spaces).
    return "{" + ",".join(str(i) for i in sorted(indices)) + "}"


def _predicate_matches(pred_byte: int, x: int) -> bool:
    # Keep this exactly aligned with the predicate-byte split logic in:
    # - thielecpu/vm.py (PSPLIT predicate-byte mode)
    # - thielecpu/hardware/thiele_cpu.v (execute_psplit)
    predicate = pred_byte & 0xFF
    pred_mode = (predicate >> 6) & 0x3
    pred_param = predicate & 0x3F
    element_value = int(x) & 0xFFFFFFFF

    if pred_mode == 0b00:
        return (element_value & 1) == (pred_param & 1)
    if pred_mode == 0b01:
        return element_value >= pred_param
    if pred_mode == 0b10:
        return (element_value & (1 << pred_param)) != 0
    divisor = pred_param + 1
    if (divisor & pred_param) != 0:
        return False
    return (element_value & pred_param) == 0


def _find_nondegenerate_predicate(parent_region: set[int]) -> tuple[int, set[int], set[int]]:
    """Return a predicate byte that splits parent_region into two non-empty parts."""
    if not parent_region:
        raise ValueError("parent_region must be non-empty")

    def try_pred(pred: int) -> tuple[set[int], set[int]]:
        left = {x for x in parent_region if _predicate_matches(pred, x)}
        right = parent_region - left
        return left, right

    # 00=even/odd: try even then odd.
    for pred in (0x00, 0x01):
        left, right = try_pred(pred)
        if left and right:
            return pred, left, right

    # 10=bitwise: test each bit position.
    for bit in range(0, 6):
        pred = (0b10 << 6) | bit
        left, right = try_pred(pred)
        if left and right:
            return pred, left, right

    # 01=threshold: choose a threshold between min+1 and max.
    mn = min(parent_region)
    mx = max(parent_region)
    for thr in range(mn + 1, mx + 1):
        pred = (0b01 << 6) | (thr & 0x3F)
        left, right = try_pred(pred)
        if left and right:
            return pred, left, right

    raise AssertionError(f"failed to find non-degenerate predicate for parent_region={sorted(parent_region)}")


def _python_regions_after_program(program: list[tuple[str, str]]) -> list[list[int]]:
    state = State()
    vm = VM(state)

    with tempfile.TemporaryDirectory() as td:
        vm.run(program, Path(td), write_artifacts=False)

    regions = [sorted(region) for region in state.regions.modules.values() if region]
    return sorted(regions)


def _coq_regions_after_trace(trace_lines: list[str]) -> list[list[int]]:
    runner = BUILD_DIR / "extracted_vm_runner"
    if not runner.exists():
        raise RuntimeError("missing extracted runner; run bash scripts/forge_artifact.sh")

    with tempfile.TemporaryDirectory() as td:
        trace_path = Path(td) / "trace.txt"
        trace_path.write_text("\n".join(trace_lines) + "\n", encoding="utf-8")
        result = subprocess.run(
            [str(runner), str(trace_path)], capture_output=True, text=True, check=True,
            env={**os.environ, "OCAMLRUNPARAM": os.environ.get("OCAMLRUNPARAM", "l=64M")},
        )

        out = result.stdout
        start = out.find("{")
        if start == -1:
            raise AssertionError(
                "No JSON found in extracted runner stdout.\n"
                f"STDOUT:\n{out}\n\nSTDERR:\n{result.stderr}"
            )
        decoder = json.JSONDecoder()
        payload, _end = decoder.raw_decode(out[start:])

    modules = payload["graph"]["modules"]
    regions = [sorted(m["region"]) for m in modules if m.get("region")]
    return sorted(regions)


def _rtl_regions_after_words(program_words: list[int]) -> list[list[int]]:
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        sim_out = td_path / "tb.out"
        program_hex = td_path / "prog.hex"
        data_hex = td_path / "data.hex"

        _write_hex_words(program_hex, program_words)
        _write_hex_words(data_hex, [0] * 256)

        subprocess.run(
            [
                "iverilog",
                "-g2012",
                "-Irtl",
                "-o",
                str(sim_out),
                str(RTL_DIR / "thiele_cpu_unified.v"),
                str(TESTBENCH_DIR / "thiele_cpu_tb.v"),
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

    regions = []
    for m in payload["modules"]:
        if m.get("id") == -1:
            continue
        region = [int(x) for x in m.get("region", [])]
        if region:
            regions.append(sorted(region))
    return sorted(regions)


def _python_regions_after_pnew(indices: list[int]) -> list[list[int]]:
    state = State()
    vm = VM(state)

    program = [("PNEW", "{0}")]
    for idx in indices:
        program.append(("PNEW", f"{{{idx}}}"))
    program.append(("HALT", ""))

    with tempfile.TemporaryDirectory() as td:
        vm.run(program, Path(td), write_artifacts=False)

    regions = []
    for _mid, mask in state.partition_masks.items():
        # Convert to sorted indices
        region = [i for i in range(64) if (mask >> i) & 1]
        regions.append(region)

    # Compare as multiset (sorted list of lists)
    return sorted(regions)


def _coq_regions_after_pnew(indices: list[int]) -> list[list[int]]:
    runner = BUILD_DIR / "extracted_vm_runner"
    if not runner.exists():
        raise RuntimeError("missing extracted runner; run bash scripts/forge_artifact.sh")

    trace_lines = []
    trace_lines.append("PNEW {0} 0")
    for idx in indices:
        trace_lines.append(f"PNEW {{{idx}}} 0")
    trace_lines.append("HALT 0")

    with tempfile.TemporaryDirectory() as td:
        trace_path = Path(td) / "trace.txt"
        trace_path.write_text("\n".join(trace_lines) + "\n", encoding="utf-8")
        result = subprocess.run(
            [str(runner), str(trace_path)], capture_output=True, text=True, check=True,
            env={**os.environ, "OCAMLRUNPARAM": os.environ.get("OCAMLRUNPARAM", "l=64M")},
        )

        out = result.stdout
        start = out.find("{")
        if start == -1:
            raise AssertionError(
                "No JSON found in extracted runner stdout.\n"
                f"STDOUT:\n{out}\n\nSTDERR:\n{result.stderr}"
            )
        decoder = json.JSONDecoder()
        payload, _end = decoder.raw_decode(out[start:])

    modules = payload["graph"]["modules"]
    if not modules:
        raise AssertionError(
            "Extracted runner returned empty graph.modules; expected at least the base module {0}.\n"
            f"Payload:\n{json.dumps(payload, indent=2, sort_keys=True)}"
        )
    regions = [sorted(m["region"]) for m in modules]
    return sorted(regions)


def _rtl_regions_after_pnew(indices: list[int]) -> list[list[int]]:
    program_words = [_encode_word(0x00, 0, 0)]  # PNEW {0}
    for idx in indices:
        program_words.append(_encode_word(0x00, idx, 0))
    program_words.append(_encode_word(0xFF, 0, 0))

    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        sim_out = td_path / "tb.out"
        program_hex = td_path / "prog.hex"
        data_hex = td_path / "data.hex"

        _write_hex_words(program_hex, program_words)
        _write_hex_words(data_hex, [0] * 256)

        subprocess.run(
            [
                "iverilog",
                "-g2012",
                "-Irtl",
                "-o",
                str(sim_out),
                str(RTL_DIR / "thiele_cpu_unified.v"),
                str(TESTBENCH_DIR / "thiele_cpu_tb.v"),
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
        # Find JSON object start (has newline and spaces after opening brace)
        # The RTL output may start with "status" or "partition_ops" field
        start = out.find('{\n  "status":')
        if start == -1:
            start = out.find('{\n  "partition_ops":')
        if start == -1:
            # Try without newline
            start = out.find('{ "status":')
        if start == -1:
            start = out.find('{ "partition_ops":')
        if start == -1:
            start = out.find('{"status":')
        if start == -1:
            start = out.find('{"partition_ops":')
        decoder = json.JSONDecoder()
        payload, _end = decoder.raw_decode(out[start:])

    # Filter out the sentinel object id=-1
    regions = []
    for m in payload["modules"]:
        if m.get("id") == -1:
            continue
        regions.append(sorted([int(x) for x in m.get("region", [])]))

    return sorted(regions)


@pytest.mark.skipif(
    not subprocess.call(["bash", "-lc", "command -v iverilog >/dev/null"]) == 0,
    reason="iverilog not available",
)
def test_partition_ops_pmerge_psplit_isomorphic() -> None:
    # Build a 3-element module via merges, then PSPLIT with a predicate-byte.
    # Predicate byte 0x00 => even/odd mode, "even".
    pred = 0x00

    # Identical *module-id schedule* across Python, extracted runner, and RTL:
    # All three boot with an empty graph and reserve module 0; IDs start at 1.
    #   PNEW {0} -> 1
    #   PNEW {1} -> 2
    #   PMERGE 1 2 -> 3
    #   PNEW {2} -> 4
    #   PMERGE 3 4 -> 5  (region {0,1,2})
    #   PSPLIT 5 pred -> children at 6 and 7
    program = [
        ("PNEW", "{0}"),
        ("PNEW", "{1}"),
        ("PMERGE", "1 2"),
        ("PNEW", "{2}"),
        ("PMERGE", "3 4"),
        ("PSPLIT", f"5 {pred}"),
        ("HALT", ""),
    ]

    # For the extracted runner, encode PSPLIT with explicit left/right regions.
    parent_region = {0, 1, 2}
    left = {x for x in parent_region if _predicate_matches(pred, x)}
    right = parent_region - left
    assert left and right, "test requires non-degenerate split"

    trace_lines = [
        "PNEW {0} 0",
        "PNEW {1} 0",
        "PMERGE 1 2 0",
        "PNEW {2} 0",
        "PMERGE 3 4 0",
        f"PSPLIT 5 {_region_token(left)} {_region_token(right)} 0",
        "HALT 0",
    ]

    program_words = [
        _encode_word(0x00, 0, 0),
        _encode_word(0x00, 1, 0),
        _encode_word(0x02, 1, 2),
        _encode_word(0x00, 2, 0),
        _encode_word(0x02, 3, 4),
        _encode_word(0x01, 5, pred),
        _encode_word(0xFF, 0, 0),
    ]

    py = _python_regions_after_program(program)
    coq = _coq_regions_after_trace(trace_lines)
    rtl = _rtl_regions_after_words(program_words)

    assert py == coq == rtl


@pytest.mark.skipif(
    not subprocess.call(["bash", "-lc", "command -v iverilog >/dev/null"]) == 0,
    reason="iverilog not available",
)
def test_partition_ops_randomized_merge_split_isomorphic() -> None:
    """Run 100 deterministic merge+split programs across Python ↔ Coq(extracted) ↔ RTL.

    Program shape (kept within NUM_MODULES=8 constraints of the RTL TB):
      - create three singleton modules
      - merge into a 3-element module
      - psplit with a predicate-byte that yields a non-degenerate split

    Coq runner PSPLIT is encoded using explicit regions computed from the predicate.
    """

    import os
    rng = random.Random(0xB16B00B5)

    trials = 100 if os.environ.get("THIELE_EXHAUSTIVE") else 5
    for _ in range(trials):
        # Choose 3 distinct small indices so RTL can represent them directly.
        elems = set(rng.sample(list(range(0, 16)), k=3))
        a, b, c = sorted(elems)
        parent_region = {a, b, c}

        pred, left, right = _find_nondegenerate_predicate(parent_region)

        program = [
            ("PNEW", f"{{{a}}}"),
            ("PNEW", f"{{{b}}}"),
            ("PNEW", f"{{{c}}}"),
            ("PMERGE", "1 2"),
            ("PMERGE", "4 3"),
            ("PSPLIT", f"5 {pred}"),
            ("HALT", ""),
        ]

        trace_lines = [
            f"PNEW {{{a}}} 0",
            f"PNEW {{{b}}} 0",
            f"PNEW {{{c}}} 0",
            "PMERGE 1 2 0",
            "PMERGE 4 3 0",
            f"PSPLIT 5 {_region_token(left)} {_region_token(right)} 0",
            "HALT 0",
        ]

        program_words = [
            _encode_word(0x00, a, 0),
            _encode_word(0x00, b, 0),
            _encode_word(0x00, c, 0),
            _encode_word(0x02, 1, 2),
            _encode_word(0x02, 4, 3),
            _encode_word(0x01, 5, pred),
            _encode_word(0xFF, 0, 0),
        ]

        py = _python_regions_after_program(program)
        coq = _coq_regions_after_trace(trace_lines)
        rtl = _rtl_regions_after_words(program_words)

        assert py == coq == rtl


@pytest.mark.skipif(not subprocess.call(["bash", "-lc", "command -v iverilog >/dev/null"]) == 0, reason="iverilog not available")
def test_pnew_dedup_singletons_isomorphic() -> None:
    # Same singleton regions requested multiple times; canonical semantics dedup.
    indices = [3, 3, 7, 3]

    py = _python_regions_after_pnew(indices)
    coq = _coq_regions_after_pnew(indices)
    rtl = _rtl_regions_after_pnew(indices)

    assert py == coq == rtl


@pytest.mark.skipif(not subprocess.call(["bash", "-lc", "command -v iverilog >/dev/null"]) == 0, reason="iverilog not available")
def test_pnew_randomized_sequences_isomorphic() -> None:
    """Run 100 randomized PNEW-only programs across Python ↔ Coq(extracted) ↔ RTL.

    This is a deliberately small shared opcode subset that is supported by all
    three layers and yields a crisp state-projection comparison (regions).
    """

    import os
    rng = random.Random(0xC0FFEE)

    trials = 100 if os.environ.get("THIELE_EXHAUSTIVE") else 5
    for _ in range(trials):
        # Keep the number of distinct singleton regions within MAX_MODULES.
        # (The base module {0} is included by the helper.)
        pool_size = rng.randint(1, 7)
        pool = rng.sample(list(range(0, 16)), k=pool_size)

        # Random length, with duplicates to stress canonicalization/dedup.
        length = rng.randint(1, 20)
        indices = [rng.choice(pool) for _ in range(length)]

        py = _python_regions_after_pnew(indices)
        coq = _coq_regions_after_pnew(indices)
        rtl = _rtl_regions_after_pnew(indices)

        assert py == coq == rtl
