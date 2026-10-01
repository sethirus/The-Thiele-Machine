#!/usr/bin/env python3
"""Check that the bitstream holds exactly the routed design's configuration.

Two comparisons, both on the Kintex-7 bitstream that run_synthesis_xc7.sh
writes:

1. Encoding. bitread decodes the .bit file to the set of configuration bits
   it sets. Those must be exactly the bits of the frames file that
   xc7frames2bit encoded, outside the per-frame ECC word, which xc7frames2bit
   computes itself. This needs no device database.

2. Meaning. bit2fasm decodes the bitstream through the Project X-Ray
   database into FASM features, and fasm2frames re-encodes those features.
   The re-encoded frames must equal the frames produced from nextpnr's FASM.
   bit2fasm drops any bit the database cannot name, so an unexplained bit
   shows up here as a mismatch.

Exit status 0 means both comparisons hold; any difference is printed and
fails the run.
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ECC_WORD = 50  # 7-series frames carry their ECC in word 50.
BIT_LINE = re.compile(r"^bit_([0-9a-fA-F]{8})_(\d{3})_(\d{2})$")


def frames_bits(path: Path) -> set[tuple[int, int, int]]:
    """Set bits of a fasm2frames frames file, as (frame, word, bit)."""
    bits: set[tuple[int, int, int]] = set()
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        addr_text, words_text = line.split(None, 1)
        addr = int(addr_text, 16)
        for word_index, word_text in enumerate(words_text.split(",")):
            word = int(word_text, 16)
            for bit in range(32):
                if word >> bit & 1:
                    bits.add((addr, word_index, bit))
    return bits


def bitread_bits(path: Path) -> set[tuple[int, int, int]]:
    """Set bits listed by `bitread -z -y`, as (frame, word, bit)."""
    bits: set[tuple[int, int, int]] = set()
    for line in path.read_text().splitlines():
        match = BIT_LINE.match(line.strip())
        if match:
            bits.add((int(match.group(1), 16), int(match.group(2)), int(match.group(3))))
    return bits


def without_ecc(bits: set[tuple[int, int, int]]) -> set[tuple[int, int, int]]:
    return {b for b in bits if b[1] != ECC_WORD}


def report(name: str, expected: set, actual: set) -> bool:
    missing, extra = expected - actual, actual - expected
    if not missing and not extra:
        print(f"[bitstream-roundtrip] {name}: {len(expected)} configuration bits match")
        return True
    print(f"[bitstream-roundtrip] {name}: MISMATCH, {len(missing)} bits missing, "
          f"{len(extra)} unexpected", file=sys.stderr)
    for label, group in (("missing", missing), ("unexpected", extra)):
        for frame, word, bit in sorted(group)[:20]:
            print(f"  {label}: frame 0x{frame:08X} word {word} bit {bit}", file=sys.stderr)
    return False


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bit", required=True, type=Path)
    parser.add_argument("--frames", required=True, type=Path)
    parser.add_argument("--part", required=True)
    parser.add_argument("--db-root", required=True, type=Path)
    parser.add_argument("--prjxray", required=True, type=Path)
    parser.add_argument("--bitread", default="bitread")
    args = parser.parse_args()

    part_yaml = args.db_root / args.part / "part.yaml"
    env = dict(os.environ)
    env["PYTHONPATH"] = f"{args.prjxray}{os.pathsep}{env.get('PYTHONPATH', '')}"

    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        bits_file = work / "design.bits"
        subprocess.run([args.bitread, "--part_file", str(part_yaml), "-o", str(bits_file),
                        "-z", "-y", str(args.bit)], check=True)
        encoded = report("encoding (bitread vs frames)",
                         without_ecc(frames_bits(args.frames)),
                         without_ecc(bitread_bits(bits_file)))

        fasm_file = work / "roundtrip.fasm"
        with fasm_file.open("w") as out:
            subprocess.run([sys.executable, str(args.prjxray / "utils/bit2fasm.py"),
                            "--db-root", str(args.db_root), "--part", args.part,
                            "--bitread", args.bitread, str(args.bit)],
                           check=True, stdout=out, env=env)
        frames_file = work / "roundtrip.frames"
        with frames_file.open("w") as out:
            subprocess.run([sys.executable, str(args.prjxray / "utils/fasm2frames.py"),
                            "--part", args.part, "--db-root", str(args.db_root),
                            str(fasm_file)],
                           check=True, stdout=out, env=env)
        meaning = report("meaning (bit2fasm then fasm2frames vs frames)",
                         frames_bits(args.frames), frames_bits(frames_file))

    return 0 if encoded and meaning else 1


if __name__ == "__main__":
    sys.exit(main())
