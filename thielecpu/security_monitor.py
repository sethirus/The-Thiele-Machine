# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
"""thielecpu.security_monitor

Configurable, structured security monitoring for the Thiele CPU.

This module provides a lightweight SecurityMonitor which records
machine-readable events (JSON) about notable Thiele CPU activity.

Design goals:
- Configurable: monitoring can be disabled/enabled via environment
  variables.
- Safe by default: the monitor avoids noisy side-effects on import and
  will not print large guidance blocks unless explicitly requested.
- Robust: writes JSON arrays to a log file while attempting to guard
  against concurrent writers on POSIX systems.

Environment variables:
- THIELE_SECURITY_LOGGING=0|1 (default: 1) -- enable/disable logging
- THIELE_SECURITY_LOG_PATH=PATH (default: ./security_log.json)
- THIELE_SECURITY_LOG_REDACT=0|1 (default: 0) -- replace sensitive
  values with a REDACTED marker

Usage:
>>> from thielecpu.security_monitor import log_usage
>>> log_usage("vm.run.start", program_len=42)

"""

from __future__ import annotations

import json
import hashlib
import datetime
import os
import warnings
import threading
import tempfile
import multiprocessing
from pathlib import Path
from typing import Dict, Any, Optional

try:
    import fcntl  # POSIX advisory locks for concurrent writers
except Exception:
    fcntl = None


def _env_bool(name: str, default: bool) -> bool:
    v = os.environ.get(name)
    if v is None:
        return default
    return v.lower() in ("1", "true", "yes", "on")


class SecurityMonitor:
    """Monitor and log Thiele CPU usage.

    The monitor writes a JSON array to a file (default: ``security_log.json``).
    It is intentionally conservative about side-effects on import: nothing
    is printed automatically and logging can be turned off entirely.
    """

    def __init__(self, log_file: Optional[Path] = None):
        self.log_file = Path(log_file or os.environ.get("THIELE_SECURITY_LOG_PATH", "security_log.json"))
        self.enabled = _env_bool("THIELE_SECURITY_LOGGING", True)
        self.redact = _env_bool("THIELE_SECURITY_LOG_REDACT", False)
        self.session_id = hashlib.sha256(str(datetime.datetime.utcnow().timestamp()).encode()).hexdigest()[:16]
        # In-process lock for thread-safety; for multi-process coordination we use fcntl (POSIX) when available
        self._inproc_lock = threading.Lock()

    def is_enabled(self) -> bool:
        return bool(self.enabled)

    def log_activity(self, activity: str, details: Optional[Dict[str, Any]] = None) -> None:
        """Record an event into the JSON log file.

        The function attempts to keep the on-disk file as a JSON array to
        preserve compatibility with existing examples. If the monitor is
        disabled this is a no-op.
        """
        if not self.enabled:
            return

        details = details or {}
        safe_details = self._sanitize(details)
        if self.redact:
            safe_details = self._redact(safe_details)

        entry = {
            "timestamp": datetime.datetime.utcnow().isoformat() + "Z",
            "session_id": self.session_id,
            "pid": os.getpid(),
            "process": multiprocessing.current_process().name,
            "thread": threading.get_ident(),
            "activity": activity,
            "details": safe_details,
        }

        try:
            # Ensure parent directory exists
            try:
                self.log_file.parent.mkdir(parents=True, exist_ok=True)
            except Exception:
                # ignore directory creation failures; file writes below may fail
                pass

            # Fast path: file does not exist yet
            if not self.log_file.exists():
                try:
                    with open(self.log_file, "w", encoding="utf-8") as f:
                        json.dump([entry], f, indent=2)
                        f.flush()
                    return
                except Exception:
                    # Fall through to robust append behaviour
                    pass

            # Prefer advisory locking on POSIX systems
            if fcntl is not None:
                with self._inproc_lock:
                    with open(self.log_file, "r+", encoding="utf-8") as f:
                        try:
                            fcntl.flock(f.fileno(), fcntl.LOCK_EX)
                        except Exception:
                            # Can't lock, continue but be conservative
                            pass
                        try:
                            try:
                                logs = json.load(f)
                                if not isinstance(logs, list):
                                    logs = []
                            except Exception:
                                logs = []
                            logs.append(entry)
                            f.seek(0)
                            json.dump(logs, f, indent=2)
                            f.truncate()
                            f.flush()
                        finally:
                            try:
                                fcntl.flock(f.fileno(), fcntl.LOCK_UN)
                            except Exception:
                                pass
                return

            # Portable fallback: read/modify/replace using a temp file.
            with self._inproc_lock:
                try:
                    with open(self.log_file, "r", encoding="utf-8") as f:
                        try:
                            logs = json.load(f)
                            if not isinstance(logs, list):
                                logs = []
                        except Exception:
                            logs = []
                except FileNotFoundError:
                    logs = []

                logs.append(entry)
                tmp = Path(tempfile.mktemp(prefix="security_log_", dir=str(self.log_file.parent)))
                with open(tmp, "w", encoding="utf-8") as ftmp:
                    json.dump(logs, ftmp, indent=2)
                    ftmp.flush()
                try:
                    os.replace(str(tmp), str(self.log_file))
                except Exception:
                    # Last resort: try writing directly
                    with open(self.log_file, "w", encoding="utf-8") as f:
                        json.dump(logs, f, indent=2)
                        f.flush()
        except Exception as exc:
            warnings.warn(f"Failed to log security activity: {exc}", UserWarning)

    def check_responsible_use(self) -> None:
        """Print a short responsible-use notice and record that the notice
        was shown. This DOES NOT print the long guidance block by default;
        that is intentionally left for interactive use via this explicit
        call.
        """
        guidelines = (
            "*** THIELE CPU RESPONSIBLE USE NOTICE ***\n\n"
            "This package contains tools that can be used for cryptanalysis and\n"
            "other sensitive tasks. Use only for defensive security research\n"
            "or formal verification.\n\n"
            "To view a longer responsible-use guidance block call\n"
            "thielecpu.security_monitor.display_security_warning().\n"
        )
        print(guidelines)
        # record that the notice was displayed
        try:
            self.log_activity("responsible_use_check_displayed")
        except Exception:
            # best-effort logging only
            pass

    def _sanitize(self, obj: Any) -> Any:
        """Convert objects to JSON-serializable representations where
        necessary. This keeps log writes robust when arbitrary Python
        objects are present in ``details``.
        """
        try:
            json.dumps(obj)
            return obj
        except Exception:
            # For dict-like objects walk the structure shallowly
            if isinstance(obj, dict):
                return {k: self._sanitize(v) for k, v in obj.items()}
            if isinstance(obj, (list, tuple)):
                return [self._sanitize(v) for v in obj]
            # Fallback: represent as string
            try:
                return repr(obj)
            except Exception:
                return "<unserializable>"

    def _redact(self, details: Any) -> Any:
        """Redact likely-sensitive fields from the details structure.

        This is intentionally conservative: common secret-like keys are
        replaced with an explicit marker. Large blobs are truncated.
        """
        SENSITIVE_KEYS = {"p", "q", "private", "secret", "password", "key", "secret_key", "result"}

        def redact_value(v: Any) -> Any:
            if isinstance(v, dict):
                return {k: ("<<REDACTED>>" if k in SENSITIVE_KEYS else redact_value(vv)) for k, vv in v.items()}
            if isinstance(v, (list, tuple)):
                return [redact_value(x) for x in v]
            s = str(v)
            if len(s) > 256:
                return s[:256] + "...<<TRUNCATED>>"
            return ("<<REDACTED>>" if any(k in s.lower() for k in ("private", "secret", "password")) else s)

        return redact_value(details)


# Global monitor instance used by the package
_monitor = SecurityMonitor()


def log_usage(activity: str, details: Optional[Dict[str, Any]] = None, **kwargs) -> None:
    """Package-level convenience function for logging usage events.

    Accepts either a single ``details`` dict or arbitrary keyword
    arguments which will be merged into the details dictionary. This makes
    it convenient to call from multiple call-sites without needing to build
    an explicit dict.
    """
    merged = {} if details is None else dict(details)
    if kwargs:
        merged.update(kwargs)
    _monitor.log_activity(activity, merged)


def display_security_warning() -> None:
    """Explicitly print the longer responsible-use guidance and record
    that it was displayed.
    """
    _monitor.check_responsible_use()


__all__ = ["SecurityMonitor", "log_usage", "display_security_warning"]