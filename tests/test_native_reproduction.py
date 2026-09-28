"""Check source-only copying and failure accounting without compiling Coq."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

import pytest

SPEC = importlib.util.spec_from_file_location(
    'native_reproduction', Path(__file__).resolve().parents[1] / 'scripts/reproduce_coq.py')
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)


@pytest.fixture
def source_repo(tmp_path, monkeypatch):
    root = tmp_path / 'repo'
    for name in (*runner.CONFIGS, *runner.DEFAULT_PROBES):
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text('')
    for folder in runner.FOLDERS:
        path = root / folder
        path.mkdir(parents=True, exist_ok=True)
        (path / 'Proof.v').write_text('Goal True. exact I. Qed.\n')
        (path / 'Proof.vo').write_bytes(b'must not copy')
        (path / 'Makefile.coq').write_text('must not copy')
    monkeypatch.setattr(runner, 'ROOT', root)
    return root


def test_preparation_copies_dependency_sources_without_compiled_objects(source_repo, monkeypatch):
    output = source_repo / 'artifacts/reproduction/check'
    monkeypatch.setattr(sys, 'argv', ['reproduce_coq.py', '--output', str(output), '--prepare-only'])
    assert runner.main() == 0
    assert not list((output / 'source').rglob('*.vo'))
    assert not list((output / 'source').rglob('Makefile.coq'))
    assert (output / 'source/vendor/coq-undecidability/theories/Proof.v').is_file()
    report = json.loads((output / 'reproduction.json').read_text())
    assert report['status'] == 'prepared'
    assert all(c['exit_code'] is None for c in report['commands'])
    assert not (output / 'result.txt').exists()


@pytest.mark.parametrize('failure', [2, OSError('executable unavailable')])
def test_failed_build_is_recorded_and_stops_later_checks(source_repo, monkeypatch, failure):
    output = source_repo / 'artifacts/reproduction/failure'
    monkeypatch.setattr(sys, 'argv', ['reproduce_coq.py', '--output', str(output)])
    monkeypatch.setattr(runner.shutil, 'which', lambda _: sys.executable)
    calls = []

    def run(cmd, **kwargs):
        calls.append(cmd)
        if '-C' in cmd:
            if isinstance(failure, OSError):
                raise failure
            return subprocess.CompletedProcess(cmd, failure)
        return subprocess.CompletedProcess(cmd, 0)

    monkeypatch.setattr(runner.subprocess, 'run', run)
    assert runner.main() != 0
    report = json.loads((output / 'reproduction.json').read_text())
    assert report['status'] == 'failed'
    assert report['exit_code'] != 0
    assert report['commands'][1]['exit_code'] is None
    assert not (output / 'result.txt').exists()
    assert sum('-C' in cmd for cmd in calls) == 1


def test_resume_rejects_modified_captured_sources(source_repo, monkeypatch):
    output = source_repo / 'artifacts/reproduction/resume'
    monkeypatch.setattr(sys, 'argv', ['reproduce_coq.py', '--output', str(output), '--prepare-only'])
    assert runner.main() == 0
    (output / 'source/coq/Proof.v').write_text('changed')
    monkeypatch.setattr(sys, 'argv', ['reproduce_coq.py', '--output', str(output), '--resume'])
    with pytest.raises(SystemExit) as error:
        runner.main()
    assert error.value.code != 0
    assert not (output / 'result.txt').exists()


def test_resume_keeps_completed_build_and_preserves_failed_log(source_repo, monkeypatch):
    output = source_repo / 'artifacts/reproduction/resume'
    monkeypatch.setattr(sys, 'argv', ['reproduce_coq.py', '--output', str(output)])
    monkeypatch.setattr(runner.shutil, 'which', lambda _: sys.executable)

    def first_run(cmd, **kwargs):
        return subprocess.CompletedProcess(cmd, 2 if 'vendor/kami' in cmd else 0)

    monkeypatch.setattr(runner.subprocess, 'run', first_run)
    assert runner.main() == 2
    calls = []

    def resumed_run(cmd, **kwargs):
        calls.append(cmd)
        return subprocess.CompletedProcess(cmd, 0)

    monkeypatch.setattr(runner.subprocess, 'run', resumed_run)
    monkeypatch.setattr(sys, 'argv', ['reproduce_coq.py', '--output', str(output), '--resume'])
    assert runner.main() == 0
    assert not any('vendor/bbv' in cmd for cmd in calls)
    assert any('vendor/kami' in cmd for cmd in calls)
    assert list(output.glob('kami-build.*.log'))
    assert (output / 'result.txt').read_text() == 'passed\n'
