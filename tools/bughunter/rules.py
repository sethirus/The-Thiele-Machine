"""Security rules enforced by the Thiele bug hunter."""

from __future__ import annotations

from dataclasses import dataclass
import ast
from pathlib import Path
from typing import Iterable, List

from .types import Finding


@dataclass
class Rule:
    """Base class for bug hunting rules."""

    name: str
    description: str
    severity: str

    def analyze(self, tree: ast.AST, path: Path, source: str) -> List[Finding]:
        raise NotImplementedError


def _call_name(node: ast.Call) -> str | None:
    target = node.func
    if isinstance(target, ast.Name):
        return target.id
    if isinstance(target, ast.Attribute):
        parts: List[str] = []
        while isinstance(target, ast.Attribute):
            parts.append(target.attr)
            target = target.value
        if isinstance(target, ast.Name):
            parts.append(target.id)
            return ".".join(reversed(parts))
    return None


class SubprocessShellRule(Rule):
    """Detect shell-based command execution that enables injection."""

    def __init__(self) -> None:
        super().__init__(
            name="subprocess-shell",
            description="Detects subprocess calls that enable shell injection via shell=True or os.system.",
            severity="critical",
        )

    def analyze(self, tree: ast.AST, path: Path, source: str) -> List[Finding]:
        findings: List[Finding] = []
        lines = source.splitlines()
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            call_name = _call_name(node)
            if call_name in {"os.system", "os.popen", "os.popen2", "os.popen3", "os.popen4"}:
                findings.append(
                    Finding(
                        rule=self.name,
                        severity=self.severity,
                        file=path,
                        line=getattr(node, "lineno", 1),
                        message=f"Call to {call_name} executes a shell command without sanitisation.",
                        remediation="Use subprocess.run with an argument list and shell=False, or sanitise the input command.",
                        evidence=lines[getattr(node, "lineno", 1) - 1].strip() if lines else None,
                    )
                )
                continue
            if call_name and call_name.startswith("subprocess."):
                for kw in node.keywords:
                    if kw.arg == "shell" and isinstance(kw.value, ast.Constant) and kw.value.value is True:
                        findings.append(
                            Finding(
                                rule=self.name,
                                severity=self.severity,
                                file=path,
                                line=getattr(node, "lineno", 1),
                                message=f"{call_name} invoked with shell=True enables shell injection.",
                                remediation="Invoke subprocess with shell=False and pass arguments as a list, or escape user input strictly.",
                                evidence=lines[getattr(node, "lineno", 1) - 1].strip() if lines else None,
                            )
                        )
        return findings


class EvalExecRule(Rule):
    """Detect use of eval/exec on potentially attacker-controlled data."""

    def __init__(self) -> None:
        super().__init__(
            name="eval-exec",
            description="Detects use of eval/exec which can lead to arbitrary code execution.",
            severity="critical",
        )

    def analyze(self, tree: ast.AST, path: Path, source: str) -> List[Finding]:
        findings: List[Finding] = []
        lines = source.splitlines()
        for node in ast.walk(tree):
            if isinstance(node, ast.Call):
                call_name = _call_name(node)
                if call_name in {"eval", "exec"}:
                    findings.append(
                        Finding(
                            rule=self.name,
                            severity=self.severity,
                            file=path,
                            line=getattr(node, "lineno", 1),
                            message=f"Use of {call_name} executes dynamically supplied Python code.",
                            remediation="Avoid eval/exec. For expressions use ast.literal_eval; otherwise implement explicit parsing or allow-listed operations.",
                            evidence=lines[getattr(node, "lineno", 1) - 1].strip() if lines else None,
                        )
                    )
        return findings


class YamlUnsafeLoadRule(Rule):
    """Detect unsafe yaml.load usages without a safe Loader."""

    _SAFE_LOADERS = {
        "SafeLoader",
        "CSafeLoader",
        "FullLoader",
        "SafeConstructor",
    }

    def __init__(self) -> None:
        super().__init__(
            name="yaml-unsafe-load",
            description="Detects yaml.load without an explicit safe Loader.",
            severity="high",
        )

    def analyze(self, tree: ast.AST, path: Path, source: str) -> List[Finding]:
        findings: List[Finding] = []
        lines = source.splitlines()
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            call_name = _call_name(node)
            if call_name != "yaml.load":
                continue
            safe = False
            for kw in node.keywords:
                if kw.arg == "Loader":
                    if isinstance(kw.value, ast.Attribute):
                        loader_name = f"{getattr(kw.value.value, 'id', '')}.{kw.value.attr}" if isinstance(kw.value.value, ast.Name) else kw.value.attr
                    elif isinstance(kw.value, ast.Name):
                        loader_name = kw.value.id
                    elif isinstance(kw.value, ast.Constant):
                        loader_name = str(kw.value.value)
                    else:
                        loader_name = None
                    if loader_name and any(loader_name.endswith(loader) for loader in self._SAFE_LOADERS):
                        safe = True
                        break
            if not safe:
                findings.append(
                    Finding(
                        rule=self.name,
                        severity=self.severity,
                        file=path,
                        line=getattr(node, "lineno", 1),
                        message="yaml.load without a safe Loader deserialises arbitrary objects.",
                        remediation="Switch to yaml.safe_load or pass Loader=yaml.SafeLoader explicitly.",
                        evidence=lines[getattr(node, "lineno", 1) - 1].strip() if lines else None,
                    )
                )
        return findings


DEFAULT_RULES: List[Rule] = [
    SubprocessShellRule(),
    EvalExecRule(),
    YamlUnsafeLoadRule(),
]

__all__ = [
    "Rule",
    "SubprocessShellRule",
    "EvalExecRule",
    "YamlUnsafeLoadRule",
    "DEFAULT_RULES",
]
