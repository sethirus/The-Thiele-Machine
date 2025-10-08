"""Static analysis helpers used by the regression tests.

The historical repository promised an automated "Bug Hunter" that would
scan code bases for dangerous constructs such as ``subprocess`` calls with
``shell=True`` or unguarded ``yaml.load`` usage.  The test-suite imported a
non-existent ``tools.bughunter`` module, so the code was impossible to
exercise.  This module provides a compact, well-tested implementation that
focuses on the concrete patterns referenced in the documentation.

The analyser operates on Python source files using the ``ast`` module and
emits :class:`Finding` objects describing the rule that was triggered, the
location, a human-readable explanation, and a remediation hint.  Results are
collected in a :class:`Report` that can be saved to JSON for auditors.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import ast
from pathlib import Path
from typing import Callable, Iterable, Iterator, List, Optional
import json


@dataclass(frozen=True)
class Finding:
    """Result reported by a rule."""

    rule: str
    message: str
    path: Path
    line: int
    severity: str
    remediation: str


@dataclass(frozen=True)
class Rule:
    """Static analysis rule.

    The callable must yield ``Finding`` instances when the pattern is
    detected in a parsed :class:`ast.AST` tree.
    """

    name: str
    description: str
    severity: str
    remediation: str
    detector: Callable[[ast.AST, Path], Iterable[Finding]]


@dataclass
class Report:
    """Summary produced by :class:`BugHunter`."""

    scanned_files: int
    executed_rules: List[str]
    findings: List[Finding] = field(default_factory=list)

    def to_dict(self) -> dict:
        return {
            "scanned_files": self.scanned_files,
            "executed_rules": self.executed_rules,
            "findings": [
                {
                    "rule": f.rule,
                    "message": f.message,
                    "path": str(f.path),
                    "line": f.line,
                    "severity": f.severity,
                    "remediation": f.remediation,
                }
                for f in self.findings
            ],
        }


def _iter_python_files(root: Path) -> Iterator[Path]:
    for path in root.rglob("*.py"):
        if path.is_file():
            yield path


def _detect_subprocess_shell(tree: ast.AST, path: Path) -> Iterable[Finding]:
    for node in ast.walk(tree):
        if isinstance(node, ast.Call):
            func = node.func
            if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
                # subprocess.run(..., shell=True)
                if func.value.id == "subprocess" and func.attr in {"run", "Popen", "call", "check_call", "check_output"}:
                    for kw in node.keywords:
                        if kw.arg == "shell" and isinstance(kw.value, ast.Constant) and kw.value.value is True:
                            yield Finding(
                                rule="subprocess-shell",
                                message=f"subprocess.{func.attr} called with shell=True",
                                path=path,
                                line=getattr(node, "lineno", 0),
                                severity="high",
                                remediation="Pass a list of arguments and set shell=False.",
                            )
            elif isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
                if func.value.id == "os" and func.attr in {"system", "popen"}:
                    yield Finding(
                        rule="subprocess-shell",
                        message=f"os.{func.attr} invokes the system shell",
                        path=path,
                        line=getattr(node, "lineno", 0),
                        severity="high",
                        remediation="Use the subprocess module with explicit argument lists.",
                    )


def _detect_eval_exec(tree: ast.AST, path: Path) -> Iterable[Finding]:
    dangerous_names = {"eval", "exec"}
    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in dangerous_names:
            yield Finding(
                rule="eval-exec",
                message=f"dynamic {node.func.id} call",
                path=path,
                line=getattr(node, "lineno", 0),
                severity="critical",
                remediation="Avoid executing user-supplied code; use safe parsers or dispatch tables.",
            )


def _detect_yaml_load(tree: ast.AST, path: Path) -> Iterable[Finding]:
    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
            attr = node.func
            if isinstance(attr.value, ast.Name) and attr.value.id == "yaml" and attr.attr == "load":
                safe = False
                for kw in node.keywords:
                    if kw.arg == "Loader":
                        if isinstance(kw.value, ast.Attribute) and kw.value.attr in {"SafeLoader", "CSafeLoader"}:
                            safe = True
                        elif isinstance(kw.value, ast.Name) and kw.value.id.endswith("SafeLoader"):
                            safe = True
                if not safe:
                    yield Finding(
                        rule="yaml-unsafe-load",
                        message="yaml.load without a safe Loader",
                        path=path,
                        line=getattr(node, "lineno", 0),
                        severity="high",
                        remediation="Call yaml.safe_load or provide Loader=yaml.SafeLoader.",
                    )


DEFAULT_RULES: List[Rule] = [
    Rule(
        name="subprocess-shell",
        description="Detect subprocess and os calls that spawn a shell.",
        severity="high",
        remediation="Use subprocess.run([...], shell=False) or shlex.split().",
        detector=_detect_subprocess_shell,
    ),
    Rule(
        name="eval-exec",
        description="Detect use of eval/exec which enables arbitrary code execution.",
        severity="critical",
        remediation="Replace eval/exec with safe parsers or vetted dispatch tables.",
        detector=_detect_eval_exec,
    ),
    Rule(
        name="yaml-unsafe-load",
        description="Detect yaml.load without a SafeLoader.",
        severity="high",
        remediation="Switch to yaml.safe_load or specify Loader=yaml.SafeLoader.",
        detector=_detect_yaml_load,
    ),
]


class BugHunter:
    """Static analyser that scans Python files for dangerous patterns."""

    def __init__(self, root: Path, rules: Optional[Iterable[Rule]] = None):
        self.root = Path(root)
        self.rules = list(rules) if rules is not None else list(DEFAULT_RULES)
        self._last_report: Optional[Report] = None

    def run(self) -> Report:
        scanned = 0
        findings: List[Finding] = []
        executed_rules = [rule.name for rule in self.rules]

        for file_path in _iter_python_files(self.root):
            scanned += 1
            try:
                source = file_path.read_text(encoding="utf-8")
            except OSError:
                continue
            try:
                tree = ast.parse(source, filename=str(file_path))
            except SyntaxError:
                continue

            for rule in self.rules:
                findings.extend(rule.detector(tree, file_path))

        report = Report(scanned_files=scanned, executed_rules=executed_rules, findings=findings)
        self._last_report = report
        return report

    def save_report(self, destination: Path) -> None:
        if self._last_report is None:
            raise RuntimeError("BugHunter.save_report called before run().")
        destination.write_text(json.dumps(self._last_report.to_dict(), indent=2, sort_keys=True), encoding="utf-8")


__all__ = ["BugHunter", "DEFAULT_RULES", "Rule", "Finding", "Report"]

