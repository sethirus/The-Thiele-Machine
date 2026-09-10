#!/usr/bin/env python3
"""Rebuild the selected proof closure and review checks in a fresh directory.

Run from any directory with Coq 8.18 and make available. Bundled vendor .vo
files are reused; all project .vo files are excluded from the copied tree.
The working tree and the saved assessment receipt are not modified.
"""
from pathlib import Path
import json
import shlex
import shutil
import subprocess
import tempfile


def main():
    evidence = Path(__file__).resolve().parent
    repo = evidence.parents[1]
    scratch = Path(tempfile.mkdtemp(prefix="thiele-assessment-reproduction-"))
    print(f"Build and logs: {scratch}", flush=True)
    shutil.copytree(
        repo / "coq", scratch / "coq",
        ignore=shutil.ignore_patterns("*.vo", "*.vos", "*.vok", "*.glob"),
    )
    shutil.copytree(repo / "vendor", scratch / "vendor")
    project = scratch / "coq"

    def run(arguments, logfile):
        with (scratch / logfile).open("w") as log:
            subprocess.run(arguments, cwd=project, stdout=log,
                           stderr=subprocess.STDOUT, check=True)

    run(["coq_makefile", "-f", "_CoqProject", "-o", "Makefile.review"],
        "makefile.log")
    targets = json.loads((evidence / "verification.json").read_text())["build_targets"]
    run(["make", "-f", "Makefile.review", "-j2", *targets], "build.log")
    flags = []
    for line in (project / "_CoqProject").read_text().splitlines():
        if line.startswith(("-R ", "-Q ")):
            flags.extend(shlex.split(line))
    for name in ("ReviewChecks", "ReviewHardware", "ReviewAssumptions"):
        source = scratch / f"{name}.v"
        shutil.copy2(evidence / source.name, source)
        run(["coqc", *flags, str(source)], f"{name}.log")
        print(f"{name}: passed", flush=True)
    print("Selected source rebuild and review checks passed.")


if __name__ == "__main__":
    main()
