from __future__ import annotations

import importlib.util
import sys
import os
import types
from pathlib import Path
import signal
from typing import Optional
import shutil
import pytest

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
REPO_ROOT = ROOT.parent


def pytest_configure(config):
    """Enable pytest-xdist parallel execution when available and not running
    under VS Code's test adapter. VS Code manages its own parallelism by
    spawning separate processes per test; injecting xdist there adds overhead."""
    # Suppress pytest-benchmark warning when xdist is active (only if installed)
    if importlib.util.find_spec("pytest_benchmark"):
        config.addinivalue_line(
            "filterwarnings",
            "ignore::pytest_benchmark.logger.PytestBenchmarkWarning",
        )

    # Skip if xdist isn't installed
    if not importlib.util.find_spec("xdist"):
        return
    # Skip if the user already specified -n on the CLI
    if config.getoption("numprocesses", default=None) is not None:
        return
    # Inject -n auto for terminal runs
    config.option.numprocesses = "auto"
    config.option.dist = "load"


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


def _install_rtl_harness_compat() -> None:
    cosim_path = REPO_ROOT / "rtl_harness" / "cosim.py"
    accel_path = REPO_ROOT / "rtl_harness" / "accel_cosim.py"
    if not cosim_path.exists() or not accel_path.exists():
        return

    hardware_pkg = sys.modules.get("thielecpu.hardware")
    if hardware_pkg is None:
        hardware_pkg = types.ModuleType("thielecpu.hardware")
        hardware_pkg.__path__ = []  # type: ignore[attr-defined]
        sys.modules["thielecpu.hardware"] = hardware_pkg

    _ensure_module("rtl_harness.cosim", cosim_path)
    _ensure_module("rtl_harness.accel_cosim", accel_path)

    cosim_module = sys.modules.get("rtl_harness.cosim")
    accel_module = sys.modules.get("rtl_harness.accel_cosim")
    if cosim_module is not None:
        sys.modules["thielecpu.hardware.cosim"] = cosim_module
        setattr(hardware_pkg, "cosim", cosim_module)
    if accel_module is not None:
        sys.modules["thielecpu.hardware.accel_cosim"] = accel_module
        setattr(hardware_pkg, "accel_cosim", accel_module)


_install_rtl_harness_compat()


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
        help="Fail (instead of skip) strict backend-marked tests when required backends are missing.",
    )


def _alarm_handler(signum, frame):
    raise TimeoutError("Test exceeded per-test timeout")


def _get_timeout(item) -> int:
    cfg = item.config
    cli = cfg.getoption("--per-test-timeout")
    if cli is not None:
        return int(cli)
    # strict_rtl tests (e.g. prefix-by-prefix lockstep) need ~240s for
    # many subprocess invocations; use a higher default when no CLI override.
    if item.get_closest_marker("strict_rtl") is not None:
        return 240
    ini = cfg.getini("per_test_timeout")
    try:
        return int(ini)
    except Exception:
        return 60


def pytest_runtest_setup(item):
    # Shared strict backend policy for no-shortcuts TDD runs.
    strict_mode = item.config.getoption("--strict-backends") or (
        os.getenv("THIELE_STRICT_BACKENDS", "0").strip().lower() in {"1", "true", "yes", "on"}
    )
    need_extracted = item.get_closest_marker("strict_extracted") is not None
    need_rtl = item.get_closest_marker("strict_rtl") is not None

    if need_extracted:
        runner = REPO_ROOT / "build" / "extracted_vm_runner"
        if not runner.exists():
            msg = f"strict_extracted requires {runner}"
            if strict_mode:
                pytest.fail(msg)
            pytest.skip(msg)

    if need_rtl:
        has_iverilog = shutil.which("iverilog") is not None
        has_verilator = shutil.which("verilator") is not None
        if not (has_iverilog or has_verilator):
            msg = "strict_rtl requires iverilog or verilator"
            if strict_mode:
                pytest.fail(msg)
            pytest.skip(msg)

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
