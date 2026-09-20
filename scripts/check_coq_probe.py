#!/usr/bin/env python3
"""Run a current Coq probe with the repository's project load path."""

import argparse
import os
from pathlib import Path
import shlex
import subprocess


ROOT = Path(__file__).resolve().parents[1]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--probe",
        default="tests/coq_probes/contract_probe.v",
        help="Repository-relative or absolute Coq probe file",
    )
    options = parser.parse_args()
    probe = (ROOT / options.probe).resolve()
    args = []
    for line in (ROOT / "coq/_CoqProject").read_text().splitlines():
        if line.startswith(("-R ", "-Q ", "-I ")):
            args.extend(shlex.split(line))
    env = os.environ.copy()
    paths = [str(ROOT / "vendor/bbv/src"), str(ROOT / "vendor/kami")]
    if env.get("COQPATH"):
        paths.append(env["COQPATH"])
    env["COQPATH"] = os.pathsep.join(paths)
    return subprocess.run(
        ["coqtop", "-batch", *args, "-l", str(probe)],
        cwd=ROOT / "coq",
        env=env,
        check=False,
    ).returncode


if __name__ == "__main__":
    raise SystemExit(main())
