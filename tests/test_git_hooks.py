"""Exercise the installed hook in disposable repos, with expensive tools stubbed.

Git/index operations and the worktree guard are real. Compiler/test stubs let
us inject failures and verify hook ordering without recursively running pytest.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

import pytest

from scripts.coq_proof_scope import FULL_ASSUMPTION_PROBE

ROOT = Path(__file__).resolve().parents[1]


def command(repo, *args, **kwargs):
    env = os.environ.copy()
    # Hook tests may themselves run from a git commit's inherited environment.
    for key in tuple(env):
        if key.startswith("GIT_"):
            env.pop(key)
    env.update(kwargs.pop("env", {}))
    return subprocess.run(args, cwd=repo, env=env, text=True, capture_output=True,
                          timeout=30, **kwargs)


def git(repo, *args):
    return command(repo, "git", *args, check=True).stdout


@pytest.fixture
def repo(tmp_path):
    git(tmp_path, "init", "-q")
    git(tmp_path, "config", "user.email", "hook-test@example.invalid")
    git(tmp_path, "config", "user.name", "Hook test")
    for name in (".githooks/pre-commit", "scripts/install-git-hooks.sh", "scripts/check_hook_worktree.py"):
        destination = tmp_path / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes((ROOT / name).read_bytes())
        destination.chmod((ROOT / name).stat().st_mode & 0o777)
    (tmp_path / "source with spaces.v").write_text("original\n")
    (tmp_path / ".gitignore").write_text("*.vo\n__pycache__/\n")
    git(tmp_path, "add", ".")
    git(tmp_path, "-c", "core.hooksPath=/dev/null", "commit", "-qm", "fixture")
    return tmp_path


def test_installer_repairs_executable_bit_and_supports_worktrees(repo, tmp_path):
    installer = "scripts/install-git-hooks.sh"
    assert command(repo, "bash", installer).returncode == 0
    hook = repo / ".githooks/pre-commit"
    hook.chmod(0o644)
    assert command(repo, "bash", installer).returncode == 0
    assert os.access(hook, os.X_OK)
    worktree = tmp_path / "linked"
    git(repo, "worktree", "add", "-qb", "linked", str(worktree))
    assert (worktree / ".git").is_file()
    result = command(worktree, "bash", installer)
    assert result.returncode == 0, result.stderr
    assert git(worktree, "config", "--get", "core.hooksPath").strip() == ".githooks"


@pytest.mark.parametrize("change", ["partial", "unstaged", "deleted", "untracked", "renamed"])
def test_guard_rejects_worktree_only_inputs_without_staging(repo, change):
    source = repo / "source with spaces.v"
    if change == "partial":
        source.write_text("staged\n")
        git(repo, "add", str(source))
        source.write_text("unstaged\n")
    elif change == "unstaged":
        source.write_text("unstaged\n")
    elif change == "deleted":
        source.unlink()
    elif change == "renamed":
        source.rename(repo / "renamed.v")
    else:
        (repo / "new\nsource.v").write_text("untracked\n")
    before = git(repo, "write-tree")
    result = command(repo, sys.executable, "scripts/check_hook_worktree.py")
    assert result.returncode == 1
    assert "working tree differs" in result.stderr
    assert git(repo, "write-tree") == before


def test_guard_accepts_staged_changes_and_ignored_build_cache(repo):
    (repo / "source with spaces.v").write_text("staged\n")
    (repo / "cached.vo").write_text("compiled")
    git(repo, "add", "source with spaces.v")
    assert command(repo, sys.executable, "scripts/check_hook_worktree.py").returncode == 0


@pytest.fixture
def pipeline(repo, tmp_path):
    outputs = [
        "build/kami_hw/Target.ml", "build/kami_hw/Target.mli",
        "build/kami_hw/Target_complete.ml", "build/kami_hw/Target_complete.mli",
        "build/thiele_core.ml", "build/thiele_core.mli",
        "build/thiele_core_complete.ml", "build/thiele_core_complete.mli",
        "build/extracted_vm_runner", "build/extracted_vm_runner.ml", "thielecpu/vm.py",
        "build/extracted_vm_runner.cmi", "build/extracted_vm_runner.cmo",
        "build/thiele_core.cmi", "build/thiele_core.cmo",
        "artifacts/proof_dependency_dag.json", "artifacts/proof_dependency_connectivity.json",
        "artifacts/proof_dependency_file_graph.mmd", "artifacts/PROOF_FOUNDATION_AUDIT.md",
        "artifacts/final_claim_audit/example.json", "artifacts/rtl_pipeline_manifest.json",
        "artifacts/rtl_text_transform_audit.json", "INQUISITOR_REPORT.md",
    ]
    for name in outputs:
        path = repo / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("original\n")
    (repo / "coq").mkdir()
    (repo / "scripts/coq_proof_scope.py").write_text("def validate_alignment(): return []\n")
    (repo / "scripts/vacuity_targets.json").write_text('{"targets": []}')
    (repo / "artifacts/vacuity_audit.json").write_text(json.dumps({
        "summary": {"vacuous_true": 0, "vacuous_hyp": 0, "error": 0}
    }))
    git(repo, "add", ".")
    git(repo, "-c", "core.hooksPath=/dev/null", "commit", "-qm", "pipeline fixture")
    binaries = tmp_path / ".git" / "test-bin"
    binaries.mkdir()
    stub = binaries / "stub"
    stub.write_text(f"#!{sys.executable}\n" + r'''
import hashlib, json, os, pathlib, subprocess, sys
name = pathlib.Path(sys.argv[0]).name
args = sys.argv[1:]
with open(pathlib.Path(__file__).resolve().parents[1] / "tool-log", "a") as log:
    log.write(json.dumps([name, args, os.environ.get("CI")]) + "\n")
failure = os.environ.get("HOOK_TEST_FAIL")
if failure and any(failure in arg for arg in [name, *args]):
    sys.stderr.write("injected failure: " + failure + "\n")
    sys.exit(7)
if name == "python3":
    if args[0] == "-c" or args[0] == "scripts/check_hook_worktree.py":
        sys.exit(subprocess.call([sys.executable, *args]))
    # check_assumption_consistency.py is not present in this fixture repo; the
    # hook's invocation of it must succeed here (the real check is exercised by
    # tests/test_assumption_consistency.py). Failure injection above still fires.
    if args and args[0] == "build/probe/build_full_probe.py":
        # The hook regenerates the probe before checking receipt/probe coherence.
        for name in (os.environ["HOOK_TEST_ASSUMPTION_PROBE"],
                     "build/probe/probe_inventory.json"):
            path = pathlib.Path(name)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("regenerated probe\n")
    if args[:2] == ["-m", "pytest"]:
        if os.environ.get("HOOK_TEST_MUTATE"):
            pathlib.Path("source with spaces.v").write_text("changed during tests\n")
    elif args[0] == "scripts/generate_rtl_pipeline_manifest.py":
        path = pathlib.Path("artifacts/rtl_pipeline_manifest.json")
        fresh = hashlib.sha256(pathlib.Path("source with spaces.v").read_bytes()).hexdigest()
        if "--check" in args:
            sys.exit(0 if path.read_text() == fresh else 1)
        path.write_text(fresh)
elif name == "bash" and args == ["scripts/generate_assumption_receipt.sh"]:
    for name in (os.environ["HOOK_TEST_ASSUMPTION_PROBE"], "artifacts/print_assumptions_all_proofs.json",
                 "artifacts/print_assumptions_all_proofs.txt", "build/probe/probe_inventory.json",
                 "build/probe/probe_all_output.txt", "build/probe/probe_all_err.txt",
                 "build/probe/probe_batches.json"):
        path = pathlib.Path(name)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("fresh receipt\n")
''')
    stub.chmod(0o755)
    for name in ("python3", "make", "bash", "coqc", "coqtop", "coq_makefile", "ocamlfind",
                 "ocamlc", "iverilog", "vvp", "verilator", "yosys", "node"):
        (binaries / name).symlink_to(stub)
    return repo, {"PATH": str(binaries) + os.pathsep + os.environ["PATH"],
                  "HOOK_TEST_ASSUMPTION_PROBE": FULL_ASSUMPTION_PROBE}


def run_hook(pipeline, **env):
    repo, base_env = pipeline
    return command(repo, "/bin/sh", ".githooks/pre-commit", env={**base_env, **env})


def test_hook_refreshes_manifest_and_tests_in_ci_mode(pipeline):
    repo, _ = pipeline
    (repo / "source with spaces.v").write_text("staged update\n")
    git(repo, "add", "source with spaces.v")
    result = run_hook(pipeline)
    assert result.returncode == 0, result.stdout + result.stderr
    assert git(repo, "show", ":artifacts/rtl_pipeline_manifest.json") == (
        repo / "artifacts/rtl_pipeline_manifest.json").read_text()
    calls = [json.loads(line) for line in (repo / ".git/tool-log").read_text().splitlines()]
    pytest_call = next(call for call in calls if call[1][:2] == ["-m", "pytest"])
    assert "--strict-backends" in pytest_call[1]
    assert pytest_call[2] == "true"
    if "-n" in pytest_call[1]:
        assert pytest_call[1][pytest_call[1].index("-n") + 1] == "0"
    extraction = next(i for i, call in enumerate(calls) if "-W" in call[1])
    manifest = next(i for i, call in enumerate(calls)
                    if "scripts/generate_rtl_pipeline_manifest.py" in call[1])
    assert extraction < manifest


@pytest.mark.parametrize("failure", ["make", "forge_vm.py", "generate_proof_dependency_dag.py",
                                    "generate_master_summary_artifacts.py", "audit_rtl_text_transforms.py",
                                    "generate_rtl_pipeline_manifest.py", "pytest", "inquisitor.py"])
def test_hook_blocks_tool_and_generator_failures(pipeline, failure):
    result = run_hook(pipeline, HOOK_TEST_FAIL=failure)
    assert result.returncode != 0
    assert "injected failure: " + failure in result.stderr
    assert "[pre-commit] PASS:" not in result.stdout


@pytest.mark.parametrize("verdict", ["error", "vacuous_true", "vacuous_hyp"])
def test_hook_blocks_bad_vacuity_verdicts(pipeline, verdict):
    repo, _ = pipeline
    path = repo / "artifacts/vacuity_audit.json"
    data = json.loads(path.read_text())
    data["summary"][verdict] = 1
    path.write_text(json.dumps(data))
    git(repo, "add", str(path))
    result = run_hook(pipeline)
    assert result.returncode != 0
    assert "FAIL: vacuity audit" in result.stderr


def test_hook_detects_source_mutated_by_test_suite(pipeline):
    result = run_hook(pipeline, HOOK_TEST_MUTATE="1")
    assert result.returncode != 0
    assert "[pre-commit] PASS:" not in result.stdout


def test_hook_refuses_partial_staging_before_running_generators(pipeline):
    repo, _ = pipeline
    (repo / "source with spaces.v").write_text("unstaged update\n")
    before = git(repo, "write-tree")
    result = run_hook(pipeline)
    assert result.returncode != 0
    calls = [json.loads(line) for line in (repo / ".git/tool-log").read_text().splitlines()]
    assert len(calls) == 1
    assert git(repo, "write-tree") == before


def test_hook_regenerates_probe_but_defers_receipt_to_ci(pipeline):
    """A proof change refreshes the probe locally; the receipt is CI's job.

    Re-deriving the receipt means executing every Print Assumptions query in the
    corpus (~12k over 421 modules), which is CPU-bound and cannot finish inside
    this sandbox's pre-commit hook. The hook regenerates the probe and checks
    receipt/probe coherence; CI's `make assumption-receipt-check` re-derives and
    diffs the receipt with a 6-hour budget and no reaper.
    """
    repo, _ = pipeline
    (repo / "coq/Proof.v").write_text("proof change\n")
    git(repo, "add", "coq/Proof.v")
    result = run_hook(pipeline)
    assert result.returncode == 0, result.stdout + result.stderr
    calls = [json.loads(line) for line in (repo / ".git/tool-log").read_text().splitlines()]
    assert not any("generate_assumption_receipt.sh" in call[1] for call in calls), (
        "the hook must not re-derive the receipt; CI owns that step"
    )


def test_hook_runs_assumption_consistency_check(pipeline):
    """The hook always checks receipt/probe coherence, and fails when it is stale."""
    repo, _ = pipeline
    (repo / "coq/Proof.v").write_text("proof change\n")
    git(repo, "add", "coq/Proof.v")
    result = run_hook(pipeline)
    assert result.returncode == 0, result.stdout + result.stderr
    calls = [json.loads(line) for line in (repo / ".git/tool-log").read_text().splitlines()]
    assert any("scripts/check_assumption_consistency.py" in call[1] for call in calls)


def test_hook_blocks_stale_assumption_receipt(pipeline):
    """A receipt that is not a coherent snapshot of the probe blocks the commit."""
    repo, _ = pipeline
    (repo / "coq/Proof.v").write_text("proof change\n")
    git(repo, "add", "coq/Proof.v")
    result = run_hook(pipeline, HOOK_TEST_FAIL="check_assumption_consistency.py")
    assert result.returncode != 0
    assert "injected failure" in result.stderr


@pytest.mark.parametrize("state", ["deleted", "corrupt"])
def test_hook_repairs_missing_or_corrupt_manifest(pipeline, state):
    repo, _ = pipeline
    path = repo / "artifacts/rtl_pipeline_manifest.json"
    if state == "deleted":
        git(repo, "rm", str(path))
    else:
        path.write_text("{broken json")
        git(repo, "add", str(path))
    result = run_hook(pipeline)
    assert result.returncode == 0, result.stdout + result.stderr
    assert git(repo, "show", ":artifacts/rtl_pipeline_manifest.json") == path.read_text()


def test_hook_blocks_missing_backend(pipeline):
    repo, base_env = pipeline
    binaries = repo / ".git/test-bin"
    (binaries / "node").unlink()
    (binaries / "git").symlink_to(shutil.which("git"))
    result = command(repo, "/bin/sh", ".githooks/pre-commit", env={"PATH": str(binaries)})
    assert result.returncode != 0
    assert "required tool missing: node" in result.stderr


def test_guard_allows_only_reproducible_kami_compatibility_patch(repo, tmp_path):
    vendor = tmp_path / ".git/vendor-source"
    vendor.mkdir()
    git(vendor, "init", "-q")
    git(vendor, "config", "user.email", "hook-test@example.invalid")
    git(vendor, "config", "user.name", "Hook test")
    for width in (32, 64):
        path = vendor / f"Kami/Ex/Multiplier{width}.v"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text('Notation "w ~ 0" := (BWS BZero w): bword_scope.\n')
    git(vendor, "add", ".")
    git(vendor, "-c", "core.hooksPath=/dev/null", "commit", "-qm", "vendor fixture")
    git(repo, "-c", "protocol.file.allow=always", "submodule", "add", str(vendor), "vendor/kami")
    (repo / "scripts/fix_kami_coq18.sh").write_bytes((ROOT / "scripts/fix_kami_coq18.sh").read_bytes())
    git(repo, "add", ".")
    git(repo, "-c", "core.hooksPath=/dev/null", "commit", "-qm", "pin vendor")
    command(repo, "bash", "scripts/fix_kami_coq18.sh", check=True)
    result = command(repo, sys.executable, "scripts/check_hook_worktree.py",
                     env={"GIT_INDEX_FILE": ".git/index"})
    assert result.returncode == 0, result.stderr
    path = repo / "vendor/kami/Kami/Ex/Multiplier32.v"
    path.write_text(path.read_text() + "unexpected change\n")
    result = command(repo, sys.executable, "scripts/check_hook_worktree.py")
    assert result.returncode != 0
    assert "vendor/kami/Kami/Ex/Multiplier32.v" in result.stderr
