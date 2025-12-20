from __future__ import annotations

from pathlib import Path

from thielecpu.vm import VM
from thielecpu.state import State


def test_pyexec_file_semantics_sysargv_file_and_systemexit(tmp_path: Path) -> None:
    # Script reads a sibling file relative to __file__, parses args, prints, then sys.exit(3).
    script_dir = tmp_path / "script_pkg"
    script_dir.mkdir()

    data_path = script_dir / "data.txt"
    data_path.write_text("payload123", encoding="utf-8")

    script_path = script_dir / "demo_script.py"
    script_path.write_text(
        """
import argparse
import sys
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--msg', required=True)
args = p.parse_args()

payload = (Path(__file__).parent / 'data.txt').read_text(encoding='utf-8')
print('MSG=' + args.msg)
print('PAYLOAD=' + payload)
print('ARGV0=' + sys.argv[0])

sys.exit(3)
""".lstrip(),
        encoding="utf-8",
    )

    outdir = tmp_path / "out"

    vm = VM(State())
    vm.python_globals["_vm_script_args"] = ["--msg", "hello"]
    vm.run([("PYEXEC", str(script_path)), ("HALT", "")], outdir)

    trace = (outdir / "trace.log").read_text(encoding="utf-8")
    assert "PYEXEC output: MSG=hello" in trace
    assert "PYEXEC output: PAYLOAD=payload123" in trace
    assert f"PYEXEC output: ARGV0={script_path}" in trace
    assert "SystemExit: 3" in trace

    # VM must still flush artifacts.
    assert (outdir / "mu_ledger.json").exists()
    assert (outdir / "summary.json").exists()
    assert (outdir / "step_receipts.json").exists()

    # Exit code is preserved on the VM instance.
    assert vm.last_exit_code == 3
