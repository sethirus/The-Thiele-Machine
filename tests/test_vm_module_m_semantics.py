from __future__ import annotations

import os
from pathlib import Path

from thielecpu.state import State
from thielecpu.vm import VM


def test_pyexec_module_m_runs_and_flushes_artifacts(tmp_path: Path) -> None:
    # Create a tiny package in a temp cwd so python -m semantics (cwd on sys.path)
    # behave like CPython.
    pkg = tmp_path / "mypkg"
    pkg.mkdir()
    (pkg / "__init__.py").write_text("", encoding="utf-8")
    (pkg / "mod.py").write_text(
        """
import argparse
import sys

p = argparse.ArgumentParser()
p.add_argument('--x', type=int, required=True)
args = p.parse_args()

print('X=' + str(args.x))
print('ARGV0=' + sys.argv[0])

sys.exit(7)
""".lstrip(),
        encoding="utf-8",
    )

    old_cwd = os.getcwd()
    try:
        os.chdir(tmp_path)

        outdir = tmp_path / "out"
        vm = VM(State())
        vm.python_globals["_vm_script_args"] = ["--x", "123"]
        vm.run([("PYEXEC", "module:mypkg.mod"), ("HALT", "")], outdir)

        trace = (outdir / "trace.log").read_text(encoding="utf-8")
        assert "PYEXEC output: X=123" in trace
        assert "SystemExit: 7" in trace
        assert vm.last_exit_code == 7

        # Still flush artifacts.
        assert (outdir / "mu_ledger.json").exists()
        assert (outdir / "summary.json").exists()
        assert (outdir / "step_receipts.json").exists()
    finally:
        os.chdir(old_cwd)
