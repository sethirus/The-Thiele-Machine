# Licensed under the Apache License, Version 2.0
"""Tests for thielecpu security monitoring and logging integration."""
import json
from pathlib import Path


def test_vm_logging_creates_log(monkeypatch, tmp_path):
    # Ensure logging enabled and point the monitor at a temp path
    log_path = tmp_path / "security_log.json"
    monkeypatch.setenv("THIELE_SECURITY_LOGGING", "1")
    monkeypatch.setenv("THIELE_SECURITY_LOG_PATH", str(log_path))
    monkeypatch.setenv("THIELE_SECURITY_LOG_REDACT", "0")

    # Import late so the monitor picks up monkeypatched env vars for any
    # reinitialised monitors. We force configuration below on the module
    # instance to be robust against test ordering.
    from thielecpu.vm import VM
    from thielecpu.state import State
    import thielecpu.security_monitor as sm

    # Ensure the in-process monitor is configured for the test
    sm._monitor.enabled = True
    sm._monitor.redact = False
    sm._monitor.log_file = log_path

    vm = VM(State())
    program = [("PNEW", "{1}"), ("EMIT", "hello-world")]
    outdir = tmp_path / "out"
    vm.run(program, outdir)

    assert log_path.exists(), "security log was not created"
    logs = json.loads(log_path.read_text(encoding='utf-8'))
    assert isinstance(logs, list) and logs, "security log must be a non-empty list"
    activities = [e.get("activity") for e in logs]
    assert "vm.run.start" in activities
    assert "vm.run.finish" in activities
    assert "vm.emit" in activities


def test_logging_disabled_no_file(monkeypatch, tmp_path):
    log_path = tmp_path / "security_log_disabled.json"
    monkeypatch.setenv("THIELE_SECURITY_LOGGING", "0")
    monkeypatch.setenv("THIELE_SECURITY_LOG_PATH", str(log_path))

    from thielecpu.vm import VM
    from thielecpu.state import State
    import thielecpu.security_monitor as sm

    # Explicitly disable the already-instantiated monitor object.
    sm._monitor.enabled = False
    sm._monitor.log_file = log_path

    vm = VM(State())
    program = [("PNEW", "{1}"), ("EMIT", "no-log")]
    outdir = tmp_path / "out2"
    vm.run(program, outdir)

    assert not log_path.exists(), "security log should not be created when disabled"


def test_redaction_replaces_sensitive_keys(monkeypatch, tmp_path):
    log_path = tmp_path / "security_log_redacted.json"
    monkeypatch.setenv("THIELE_SECURITY_LOGGING", "1")
    monkeypatch.setenv("THIELE_SECURITY_LOG_PATH", str(log_path))
    monkeypatch.setenv("THIELE_SECURITY_LOG_REDACT", "1")

    import thielecpu.security_monitor as sm
    # Force the monitor state for this test
    sm._monitor.enabled = True
    sm._monitor.redact = True
    sm._monitor.log_file = log_path

    # Emit a sensitive key and a normal key
    from thielecpu import log_usage
    log_usage("test.redaction", {"p": "SECRET_P", "q": 12345, "ok": "fine"})

    assert log_path.exists()
    logs = json.loads(log_path.read_text(encoding='utf-8'))
    assert logs and logs[0]["activity"] == "test.redaction"
    details = logs[0]["details"]
    assert details.get("p") == "<<REDACTED>>"
    assert details.get("q") == "<<REDACTED>>"
    assert details.get("ok") == "fine"
