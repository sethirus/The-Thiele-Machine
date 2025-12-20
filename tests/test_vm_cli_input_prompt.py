from __future__ import annotations

from pathlib import Path
import subprocess
import sys


def test_vm_cli_tee_stdout_shows_input_prompt(tmp_path: Path) -> None:
    # Script that prompts without newline, then prints the answer.
    repo_root = Path(__file__).resolve().parents[1]
    vm_py = repo_root / "thielecpu" / "vm.py"

    script = tmp_path / "prompt.py"
    script.write_text(
        """
ans = input('PROMPT>')
print('ANSWER=' + ans)
""".lstrip(),
        encoding="utf-8",
    )

    outdir = tmp_path / "out"
    p = subprocess.run(
        [
            sys.executable,
            str(vm_py),
            str(script),
            "--outdir",
            str(outdir),
            "--tee-stdout",
        ],
        cwd=str(repo_root),
        input="xyz\n",
        capture_output=True,
        text=True,
        check=False,
    )

    # Script should succeed.
    assert p.returncode == 0

    # Tee mode should show the prompt on process stdout.
    assert "PROMPT>" in p.stdout

    # VM trace should also capture it.
    trace = (outdir / "trace.log").read_text(encoding="utf-8")
    assert "PYEXEC output: PROMPT>" in trace
    assert "PYEXEC output: PROMPT>ANSWER=xyz" in trace
