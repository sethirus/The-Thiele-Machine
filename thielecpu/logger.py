"""Lightweight structured logger for thielecpu.

This module exposes a small facade that integrates the existing
thielecpu.security_monitor backend with the standard logging module.
It intentionally keeps the surface area tiny so call-sites can emit
structured events without depending directly on the monitor.
"""
from __future__ import annotations

import logging
from typing import Any, Dict, Optional

# Defer importing security_monitor to call time to avoid circular imports


class _ThieleLogger:
    def __init__(self, name: str):
        self._logger = logging.getLogger(name)
        if not self._logger.handlers:
            h = logging.StreamHandler()
            fmt = logging.Formatter("%(asctime)s %(levelname)s %(name)s: %(message)s")
            h.setFormatter(fmt)
            self._logger.addHandler(h)
            # Respect an explicitly configured log level.
            # Only default to INFO when the logger is still NOTSET.
            if self._logger.level == logging.NOTSET:
                self._logger.setLevel(logging.INFO)

    def info(self, activity: str, details: Optional[Dict[str, Any]] = None, **kwargs) -> None:
        # Prefer an explicit details dict; if kwargs are present merge them
        merged = {} if details is None else dict(details)
        if kwargs:
            merged.update(kwargs)
        try:
            # Import at call time to avoid circular import problems during
            # package initialisation. The security monitor is lightweight and
            # import-time cost is negligible for logging.
            from . import security_monitor
            security_monitor.log_usage(activity, merged)
        except Exception:
            # Never raise from a logging call
            pass
        # Also emit a human-friendly informational log
        try:
            self._logger.info(f"%s", {"activity": activity, "details": merged})
        except Exception:
            pass

    def warning(self, msg: str, **kwargs) -> None:
        self._logger.warning(msg)

    def error(self, msg: str, **kwargs) -> None:
        self._logger.error(msg)


def get_thiele_logger(name: str = "thielecpu") -> _ThieleLogger:
    return _ThieleLogger(name)
