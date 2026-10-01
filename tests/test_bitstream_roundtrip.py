"""The bitstream round-trip check compares configuration bits exactly."""
from __future__ import annotations

import importlib.util
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "fpga" / "bitstream_roundtrip.py"
SPEC = importlib.util.spec_from_file_location("bitstream_roundtrip", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def test_frames_and_bitread_formats_name_the_same_bits(tmp_path):
    words = ["0x00000000"] * 101
    words[3] = "0x00000005"   # bits 0 and 2 of word 3
    words[50] = "0x00000001"  # the ECC word
    frames = tmp_path / "design.frames"
    frames.write_text("0x00400100 " + ",".join(words) + "\n")
    bits = tmp_path / "design.bits"
    bits.write_text("bit_00400100_003_00\nbit_00400100_003_02\nbit_00400100_050_00\n")
    assert MODULE.frames_bits(frames) == MODULE.bitread_bits(bits) == {
        (0x00400100, 3, 0), (0x00400100, 3, 2), (0x00400100, 50, 0)}


def test_ecc_word_is_excluded_from_the_encoding_comparison():
    assert MODULE.without_ecc({(1, 50, 0), (1, 3, 0)}) == {(1, 3, 0)}


def test_any_differing_bit_is_a_mismatch(capsys):
    assert MODULE.report("same", {(1, 2, 3)}, {(1, 2, 3)})
    assert not MODULE.report("missing", {(1, 2, 3)}, set())
    assert not MODULE.report("extra", set(), {(1, 2, 3)})
    assert "MISMATCH" in capsys.readouterr().err
