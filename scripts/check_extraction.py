#!/usr/bin/env python3
"""Re-extract both Coq roots in isolation and compare every generated ML file."""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SOURCES = ("Extraction.v", "ThieleMachineComplete.v")
OUTPUTS = tuple(
    f"build/{stem}.{suffix}"
    for stem in ("thiele_core", "thiele_core_complete",
                 "kami_hw/Target", "kami_hw/Target_complete")
    for suffix in ("ml", "mli")
)
DIRECTIVE = re.compile(r'(?m)^Extraction\s+"([^"\n]+\.ml)"')


def load_paths(root: Path) -> list[str]:
    flags: list[str] = []
    for line in (root / "coq/_CoqProject").read_text().splitlines():
        if line.startswith(("-R ", "-Q ", "-I ")):
            tokens = shlex.split(line)
            tokens[1] = str((root / "coq" / tokens[1]).resolve())
            flags.extend(tokens)
    return flags


def extract(root: Path = ROOT) -> dict[str, bytes]:
    flags = load_paths(root)
    with tempfile.TemporaryDirectory(prefix="thiele-extraction-") as temp:
        scratch = Path(temp)
        for name in SOURCES:
            source = root / "coq" / name

            def redirect(match: re.Match[str]) -> str:
                original = (root / "coq" / match.group(1)).resolve()
                relative = original.relative_to(root)
                if str(relative) not in OUTPUTS:
                    raise ValueError(f"Unexpected extraction target: {relative}")
                destination = scratch / relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                return f'Extraction "{destination}"'

            rewritten, count = DIRECTIVE.subn(redirect, source.read_text())
            if count != 2:
                raise ValueError(f"Expected two extraction directives in {name}, got {count}")
            isolated_source = scratch / name
            isolated_source.write_text(rewritten)
            result = subprocess.run(
                ["coqc", *flags, str(isolated_source)], cwd=root / "coq",
                text=True, capture_output=True, timeout=300,
            )
            if result.returncode:
                raise RuntimeError(f"{name} extraction failed:\n{result.stdout}\n{result.stderr}")
        outputs: dict[str, bytes] = {}
        for relative in OUTPUTS:
            path = scratch / relative
            if not path.is_file() or not path.stat().st_size:
                raise ValueError(f"Extraction did not produce {relative}")
            outputs[relative] = path.read_bytes()
        for stem in ("thiele_core",):
            for suffix in ("ml", "mli"):
                if outputs[f"build/{stem}.{suffix}"] != outputs[f"build/{stem}_complete.{suffix}"]:
                    raise ValueError(f"Modular and complete extraction differ: {stem}.{suffix}")
        return outputs


def reference_bytes(reference: str, root: Path = ROOT) -> dict[str, bytes]:
    if reference == "working-tree":
        return {relative: (root / relative).read_bytes() for relative in OUTPUTS}
    return {
        relative: subprocess.run(
            ["git", "show", f"HEAD:{relative}"], cwd=root,
            capture_output=True, check=True,
        ).stdout
        for relative in OUTPUTS
    }


def compare(actual: dict[str, bytes], expected: dict[str, bytes]) -> None:
    changed = [relative for relative in OUTPUTS
               if relative not in actual or relative not in expected
               or actual[relative] != expected[relative]]
    if changed:
        raise ValueError("Coq extraction differs from the reference:\n" + "\n".join(changed))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--reference", choices=("working-tree", "HEAD"), default="working-tree")
    mode.add_argument("--write", action="store_true", help="Write freshly extracted artifacts")
    args = parser.parse_args()
    try:
        expected = None if args.write else reference_bytes(args.reference)
        actual = extract()
        if args.write:
            for relative, contents in actual.items():
                (ROOT / relative).write_bytes(contents)
            print(f"Extracted {len(actual)} artifacts from Coq source.")
        else:
            compare(actual, expected)
            print(f"All {len(actual)} artifacts match fresh Coq extraction.")
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        parser.exit(1, f"Extraction check failed: {error}\n")


if __name__ == "__main__":
    main()
