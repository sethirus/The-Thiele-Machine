#!/usr/bin/env python3
"""Simple smoke tests for thielecpu logging (standalone runner).

This script performs a few quick checks to ensure the structured
security logging works end-to-end without running the full pytest
collection (which may import problematic test-time modules).
"""
import json
import os
import sys
import tempfile
from pathlib import Path

# Ensure local repository root is preferred on sys.path so local
# thielecpu package files are imported during smoke tests rather than
# an installed namespace package.
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))


def smoke_vm_logging():
    with tempfile.TemporaryDirectory() as td:
        td = Path(td)
        log_path = td / "security_log.json"
        os.environ["THIELE_SECURITY_LOGGING"] = "1"
        os.environ["THIELE_SECURITY_LOG_PATH"] = str(log_path)
        os.environ["THIELE_SECURITY_LOG_REDACT"] = "0"

        # Configure in-process monitor instance to point at our tmp file
        import thielecpu.security_monitor as sm
        sm._monitor.enabled = True
        sm._monitor.redact = False
        sm._monitor.log_file = log_path

        from thielecpu.vm import VM
        from thielecpu.state import State

        vm = VM(State())
        program = [("PNEW", "{1}"), ("EMIT", "smoke-emit")]
        outdir = td / "out"
        vm.run(program, outdir)

        if not log_path.exists():
            raise RuntimeError("security log was not created")
        logs = json.loads(log_path.read_text(encoding='utf-8'))
        activities = [e.get("activity") for e in logs]
        if "vm.run.start" not in activities:
            raise RuntimeError("vm.run.start not recorded")
        if "vm.run.finish" not in activities:
            raise RuntimeError("vm.run.finish not recorded")
        if "vm.emit" not in activities:
            raise RuntimeError("vm.emit not recorded")


def smoke_disabled():
    with tempfile.TemporaryDirectory() as td:
        td = Path(td)
        log_path = td / "security_log_disabled.json"
        os.environ["THIELE_SECURITY_LOGGING"] = "0"
        os.environ["THIELE_SECURITY_LOG_PATH"] = str(log_path)

        import thielecpu.security_monitor as sm
        sm._monitor.enabled = False
        sm._monitor.log_file = log_path

        from thielecpu.vm import VM
        from thielecpu.state import State

        vm = VM(State())
        program = [("PNEW", "{1}"), ("EMIT", "no-log")]
        outdir = td / "out2"
        vm.run(program, outdir)

        if log_path.exists():
            raise RuntimeError("security log should not be created when disabled")


def smoke_redaction():
    with tempfile.TemporaryDirectory() as td:
        td = Path(td)
        log_path = td / "security_log_redacted.json"
        os.environ["THIELE_SECURITY_LOGGING"] = "1"
        os.environ["THIELE_SECURITY_LOG_PATH"] = str(log_path)
        os.environ["THIELE_SECURITY_LOG_REDACT"] = "1"

        import thielecpu.security_monitor as sm
        sm._monitor.enabled = True
        sm._monitor.redact = True
        sm._monitor.log_file = log_path

        from thielecpu import log_usage
        log_usage("smoke.redact", {"p": "SECRET_P", "q": 42, "ok": "fine"})

        if not log_path.exists():
            raise RuntimeError("security log was not created for redaction test")
        logs = json.loads(log_path.read_text(encoding='utf-8'))
        details = logs[0]["details"]
        if details.get("p") != "<<REDACTED>>":
            raise RuntimeError("p was not redacted")
        if details.get("q") != "<<REDACTED>>":
            raise RuntimeError("q was not redacted")
        if details.get("ok") != "fine":
            raise RuntimeError("non-sensitive field mutated")


def main():
    try:
        smoke_vm_logging()
        smoke_disabled()
        smoke_redaction()
    except Exception as exc:
        print("SMOKE-TEST FAILED:", exc)
        sys.exit(2)
    print("SMOKE-TESTS: ALL OK")


if __name__ == "__main__":
    main()
