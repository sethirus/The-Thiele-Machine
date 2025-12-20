from __future__ import annotations

from pathlib import Path
import subprocess
import sys


def test_vm_cli_c_mode_exit_code_and_output(tmp_path) -> None:
    outdir = tmp_path / "out_c"
    repo_root = Path(__file__).resolve().parents[1]
    vm_py = repo_root / "thielecpu" / "vm.py"
    cmd = [
        sys.executable,
        str(vm_py),
        "--outdir",
        str(outdir),
        "-c",
        "import sys; print('HELLO'); sys.exit(4)",
    ]
    p = subprocess.run(cmd, cwd=str(repo_root), capture_output=True, text=True)
    assert p.returncode == 4
    trace = (outdir / "trace.log").read_text(encoding="utf-8")
    assert "PYEXEC output: HELLO" in trace
    assert "SystemExit: 4" in trace


def test_vm_cli_stdin_mode_exit_code_and_output(tmp_path) -> None:
    outdir = tmp_path / "out_stdin"
    repo_root = Path(__file__).resolve().parents[1]
    vm_py = repo_root / "thielecpu" / "vm.py"
    program = "import sys\nprint('FROMSTDIN')\nsys.exit(5)\n"
    cmd = [
        sys.executable,
        str(vm_py),
        "--outdir",
        str(outdir),
        "-",
    ]
    p = subprocess.run(cmd, cwd=str(repo_root), input=program, capture_output=True, text=True)
    assert p.returncode == 5
    trace = (outdir / "trace.log").read_text(encoding="utf-8")
    assert "PYEXEC output: FROMSTDIN" in trace
    assert "SystemExit: 5" in trace
