from __future__ import annotations

import importlib.util
import sys
import os
from pathlib import Path
import signal
from typing import Optional

# Fix Windows console encoding for Unicode characters (μ, ✓, etc.)
if sys.platform == "win32":
    # Force UTF-8 for stdout/stderr to handle Unicode in test output
    if hasattr(sys.stdout, 'reconfigure'):
        try:
            sys.stdout.reconfigure(encoding='utf-8', errors='replace')
            sys.stderr.reconfigure(encoding='utf-8', errors='replace')
        except Exception:
            pass
    # Set environment variable for subprocesses
    os.environ.setdefault('PYTHONIOENCODING', 'utf-8')

ROOT = Path(__file__).resolve().parent

# Guarantee the repository root is importable even when pytest adjusts sys.path.
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


def _ensure_module(name: str, path: Path) -> None:
    if name in sys.modules:
        return
    if not path.exists():
        return
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover
        return
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)  # type: ignore[attr-defined]


_ensure_module("demonstrate_isomorphism", ROOT / "demonstrate_isomorphism.py")


def pytest_addoption(parser):
    parser.addini("per_test_timeout", "Per-test timeout in seconds", default="60")
    parser.addoption(
        "--per-test-timeout",
        action="store",
        type=int,
        default=None,
        help="Override per-test timeout in seconds (CLI)",
    )


def _alarm_handler(signum, frame):
    raise TimeoutError("Test exceeded per-test timeout")


def _get_timeout(item) -> int:
    cfg = item.config
    cli = cfg.getoption("--per-test-timeout")
    if cli is not None:
        return int(cli)
    ini = cfg.getini("per_test_timeout")
    try:
        return int(ini)
    except Exception:
        return 60


def pytest_runtest_setup(item):
    timeout = _get_timeout(item)
    # SIGALRM is available on Unix and is reliable for per-test timeouts
    signal.signal(signal.SIGALRM, _alarm_handler)
    signal.alarm(timeout)


def pytest_runtest_teardown(item, nextitem):
    # Cancel any pending alarm
    signal.alarm(0)


# Hypothesis: relax per-test deadlines on slower/dev Windows machines so
# timing-sensitive property tests don't fail spuriously. We register and
# load a local profile with deadline=None (no per-test timeouts).
try:
    from hypothesis import settings as _hyp_settings

    _hyp_settings.register_profile("thiele_local", deadline=None)
    _hyp_settings.load_profile("thiele_local")
except Exception:
    # If hypothesis isn't available or profile registration fails, continue
    # without altering test behavior.
    pass
