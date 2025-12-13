import json
import subprocess
import tempfile
from pathlib import Path

import pytest

from thielecpu.state import State
from thielecpu.vm import VM


REPO_ROOT = Path(__file__).parent.parent
HARDWARE_DIR = REPO_ROOT / "thielecpu" / "hardware"
BUILD_DIR = REPO_ROOT / "build"


def _encode_word(opcode: int, a: int = 0, b: int = 0, cost: int = 0) -> int:
    return ((opcode & 0xFF) << 24) | ((a & 0xFF) << 16) | ((b & 0xFF) << 8) | (cost & 0xFF)


def _write_hex_words(path: Path, words: list[int]) -> None:
    path.write_text("\n".join(f"{w & 0xFFFFFFFF:08x}" for w in words) + "\n", encoding="utf-8")


def _python_regions_after_pnew(indices: list[int]) -> list[list[int]]:
    state = State()
    vm = VM(state)

    program = [("PNEW", "{0}")]
    for idx in indices:
        program.append(("PNEW", f"{{{idx}}}"))
    program.append(("HALT", ""))

    with tempfile.TemporaryDirectory() as td:
        vm.run(program, Path(td))

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
        result = subprocess.run([str(runner), str(trace_path)], capture_output=True, text=True, check=True)

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
                "-o",
                str(sim_out),
                "thiele_cpu.v",
                "thiele_cpu_tb.v",
                "mu_alu.v",
                "mu_core.v",
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
        start = out.find("{")
        decoder = json.JSONDecoder()
        payload, _end = decoder.raw_decode(out[start:])

    # Filter out the sentinel object id=-1
    regions = []
    for m in payload["modules"]:
        if m.get("id") == -1:
            continue
        regions.append(sorted([int(x) for x in m.get("region", [])]))

    return sorted(regions)


@pytest.mark.skipif(not subprocess.call(["bash", "-lc", "command -v iverilog >/dev/null"]) == 0, reason="iverilog not available")
def test_pnew_dedup_singletons_isomorphic() -> None:
    # Same singleton regions requested multiple times; canonical semantics dedup.
    indices = [3, 3, 7, 3]

    py = _python_regions_after_pnew(indices)
    coq = _coq_regions_after_pnew(indices)
    rtl = _rtl_regions_after_pnew(indices)

    assert py == coq == rtl
