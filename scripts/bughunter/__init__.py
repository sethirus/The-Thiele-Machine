# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Automated bug hunting framework built on the Thiele VM."""

from .framework import BugHunter, BugHunterReport
from .rules import DEFAULT_RULES, SubprocessShellRule, EvalExecRule, YamlUnsafeLoadRule
from .types import Finding, LogEntry

__all__ = [
    "BugHunter",
    "BugHunterReport",
    "Finding",
    "LogEntry",
    "DEFAULT_RULES",
    "SubprocessShellRule",
    "EvalExecRule",
    "YamlUnsafeLoadRule",
]
