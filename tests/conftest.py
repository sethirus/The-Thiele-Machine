from __future__ import annotations

import importlib.util
import os
import shutil
import signal
import sys
from pathlib import Path

import pytest

# Fix Windows console encoding for Unicode characters (mu, check marks, etc.)
if sys.platform == "win32":
    if hasattr(sys.stdout, "reconfigure"):
        try:
            sys.stdout.reconfigure(encoding="utf-8", errors="replace")
            sys.stderr.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass
    os.environ.setdefault("PYTHONIOENCODING", "utf-8")

ROOT = Path(__file__).resolve().parent
REPO_ROOT = ROOT.parent


def pytest_configure(config):
    """Enable pytest-xdist parallel execution when available and not running
    under VS Code's test adapter. VS Code manages its own parallelism by
    spawning separate processes per test; injecting xdist there adds overhead."""
    if not importlib.util.find_spec("xdist"):
        return
    if config.getoption("numprocesses", default=None) is not None:
        return
    config.option.numprocesses = "auto"
    config.option.dist = "load"


# Guarantee the tests directory is importable even when pytest adjusts sys.path.
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


def pytest_addoption(parser):
    parser.addini("per_test_timeout", "Per-test timeout in seconds", default="60")
    parser.addoption(
        "--per-test-timeout",
        action="store",
        type=int,
        default=None,
        help="Override per-test timeout in seconds (CLI)",
    )
    parser.addoption(
        "--strict-backends",
        action="store_true",
        default=False,
        help="Fail (instead of skip) coq-marked tests when coqc is missing.",
    )


def _alarm_handler(signum, frame):
    raise TimeoutError("Test exceeded per-test timeout")


def _get_timeout(item) -> int:
    cfg = item.config
    cli = cfg.getoption("--per-test-timeout")
    if cli is not None:
        return int(cli)
    # coq-marked tests may trigger Coq compilation which can take minutes.
    if item.get_closest_marker("coq") is not None:
        return 600
    ini = cfg.getini("per_test_timeout")
    try:
        return int(ini)
    except Exception:
        return 60


def pytest_runtest_setup(item):
    strict_mode = item.config.getoption("--strict-backends") or (
        os.getenv("THIELE_STRICT_BACKENDS", "0").strip().lower() in {"1", "true", "yes", "on"}
    )
    if item.get_closest_marker("coq") is not None and shutil.which("coqc") is None:
        msg = "coq marker requires coqc on PATH"
        if strict_mode:
            pytest.fail(msg)
        pytest.skip(msg)

    # SIGALRM is available on Unix and is reliable for per-test timeouts.
    # Windows has no SIGALRM; there the caller's outer timeout applies.
    if hasattr(signal, "SIGALRM"):
        signal.signal(signal.SIGALRM, _alarm_handler)
        signal.alarm(_get_timeout(item))


def pytest_runtest_teardown(item, nextitem):
    if hasattr(signal, "alarm"):
        signal.alarm(0)


# In CI the freshness gates must be able to fail: a stale committed artifact is
# a real defect and the build should say so. Locally we regenerate first so a
# routine source edit doesn't bounce the suite; `git diff` still shows what
# changed, so the developer can stage it.
IN_CI = bool(os.environ.get("CI") or os.environ.get("GITHUB_ACTIONS"))


@pytest.fixture(scope="session", autouse=True)
def refresh_proof_dependency_artifacts():
    """Regenerate the proof dependency DAG once per test session **when
    running locally**, so freshness checks don't fail on derived files the
    developer didn't hand-edit.

    In CI this is a no-op: the freshness tests then compare the committed
    artifacts against a fresh regeneration and hard-fail on drift.
    """
    import subprocess

    if IN_CI:
        return

    script = REPO_ROOT / "scripts" / "generate_proof_dependency_dag.py"
    if not script.exists():
        return
    try:
        subprocess.run(
            [sys.executable, str(script)],
            cwd=str(REPO_ROOT),
            capture_output=True,
            timeout=120,
        )
    except Exception:
        pass
