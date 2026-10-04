"""Formal input paths must resolve from the directory containing thiele.sby."""
from __future__ import annotations

import importlib.util
from pathlib import Path
from types import SimpleNamespace

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "formal_prepare.py"
SPEC = importlib.util.spec_from_file_location("formal_prepare", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def test_sby_resolves_inputs_from_its_configuration_directory(tmp_path, monkeypatch):
    formal = tmp_path / "formal"
    formal.mkdir()
    out = tmp_path / "build" / "formal"
    out.mkdir(parents=True)
    (formal / "thiele.sby").write_text("[files]\n../build/formal/RegFile.v\n")
    (out / "RegFile.v").write_text("module RegFile; endmodule\n")
    monkeypatch.setattr(MODULE, "FORMAL", formal)
    monkeypatch.setattr(MODULE, "OUT", out)

    def fake_sby(args, *, cwd, capture_output, text):
        assert not capture_output, "solver progress must reach the CI log while running"
        # Model sby's resolution of [files] against its process working directory.
        config = Path(args[-2]).read_text()
        for name in config.split("[files]\n", 1)[1].splitlines():
            assert (Path(cwd) / name).is_file()
        work = Path(args[args.index("-d") + 1])
        work.mkdir()
        (work / "status").write_text("PASS\n")
        return SimpleNamespace(returncode=0, stdout="checked\n", stderr="")

    monkeypatch.setattr(MODULE.subprocess, "run", fake_sby)
    assert MODULE.run_task("cpu_prove_pt")
