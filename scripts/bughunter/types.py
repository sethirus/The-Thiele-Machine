# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Shared dataclasses for the bug hunter framework."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Optional


@dataclass
class LogEntry:
    """Structured log emitted by the bug hunter via the Thiele VM."""

    timestamp: str
    message: str
    severity: str = "INFO"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "timestamp": self.timestamp,
            "severity": self.severity,
            "message": self.message,
        }


@dataclass
class Finding:
    """Represents a security finding uncovered during analysis."""

    rule: str
    severity: str
    file: Path
    line: int
    message: str
    remediation: str
    evidence: Optional[str] = None

    def to_dict(self, repo_root: Path) -> Dict[str, Any]:
        try:
            rel_path = str(self.file.relative_to(repo_root))
        except ValueError:
            rel_path = str(self.file)
        payload: Dict[str, Any] = {
            "rule": self.rule,
            "severity": self.severity,
            "file": rel_path,
            "line": self.line,
            "message": self.message,
            "remediation": self.remediation,
        }
        if self.evidence is not None:
            payload["evidence"] = self.evidence
        return payload
