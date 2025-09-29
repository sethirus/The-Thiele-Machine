"""Automation harness for running bug hunts inside the Thiele VM."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, List, Optional, Sequence
import json
import ast

from thielecpu.vm import VM
from thielecpu.state import State

from .rules import DEFAULT_RULES, Rule
from .types import Finding, LogEntry


class _MinimalSession:
    """A small proxy object exposed to the VM to reduce attack surface.

    The VM can only call the methods defined on this proxy. It does not
    expose the full BugHunter instance or internal state. All operations
    that mutate host state are routed through tightly-controlled callables
    provided at construction time.
    """

    def __init__(self, run_cb, read_cb, report_cb, log_cb):
        # Only store carefully curated callables; avoid exposing the
        # original BugHunter instance to the VM.
        self._run_cb = run_cb
        self._read_cb = read_cb
        self._report_cb = report_cb
        self._log_cb = log_cb

    def _run_analysis(self) -> None:
        """Entry point invoked from inside the VM to start analysis.

        The actual analysis execution happens on the host via the provided
        callback; the VM only triggers the action.
        """
        # This is intentionally a thin trampoline back into the host.
        self._run_cb()

    def read_file(self, path: str) -> str | None:
        """Read a file via the host in a controlled manner.

        Returns the file contents or None (if unreadable). The VM will not
        gain any other filesystem access.
        """
        return self._read_cb(path)

    def report_finding(self, payload: dict) -> None:
        """Accept a finding payload (serializable dict) from VM code and
        hand it to the host for validation and recording.
        """
        self._report_cb(payload)

    def log(self, message: str, severity: str = "INFO") -> None:
        self._log_cb(message, severity=severity)


@dataclass
class BugHunterReport:
    """Aggregated results from a bug hunt."""

    repo: Path
    findings: List[Finding]
    logs: List[LogEntry]
    scanned_files: int
    executed_rules: Sequence[str]
    timestamp: str

    def to_dict(self) -> dict:
        return {
            "repo": str(self.repo),
            "timestamp": self.timestamp,
            "scanned_files": self.scanned_files,
            "executed_rules": list(self.executed_rules),
            "findings": [f.to_dict(self.repo) for f in self.findings],
            "logs": [log.to_dict() for log in self.logs],
        }

    def to_json(self, *, indent: int = 2) -> str:
        return json.dumps(self.to_dict(), indent=indent)


class BugHunter:
    """Coordinates rule execution and logging through the Thiele VM."""

    _EXCLUDED_DIRS = {".git", "__pycache__", "venv", ".venv", "node_modules", "dist", "build"}

    def __init__(
        self,
        repo: Path,
        *,
        rules: Optional[Sequence[Rule]] = None,
        vm: Optional[VM] = None,
    ) -> None:
        self.repo = repo.resolve()
        self.rules: Sequence[Rule] = rules if rules is not None else DEFAULT_RULES
        self.vm = vm or VM(State())
        self.vm.state.log = self._log  # type: ignore[attr-defined]
        # Provide the VM with a minimal proxy rather than the entire
        # BugHunter object. This reduces the surface area available to
        # sandboxed code while keeping the same top-level workflow.
        proxy = _MinimalSession(
            run_cb=self._run_analysis,
            read_cb=lambda p: self._safe_read(Path(p)),
            report_cb=lambda payload: self._record_finding_from_vm(payload),
            log_cb=self._log,
        )
        self.vm.python_globals["SESSION"] = proxy
        self._logs: List[LogEntry] = []
        self._findings: List[Finding] = []
        self._latest_report: Optional[BugHunterReport] = None

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------
    def run(self) -> BugHunterReport:
        """Execute all rules and return a structured report."""

        if not self.repo.exists():
            raise FileNotFoundError(f"Repository path {self.repo} does not exist")

        self._reset()
        self.vm.execute_python("self.state.log('PNEW: Initialising Thiele bug hunter session')")
        self.vm.execute_python("SESSION._run_analysis()")
        if self._latest_report is None:
            raise RuntimeError("Bug hunt did not produce a report")
        return self._latest_report

    def save_report(self, destination: Path, *, indent: int = 2) -> Path:
        """Persist the most recent report to ``destination``."""

        if self._latest_report is None:
            raise RuntimeError("No report available; run the bug hunter first")
        destination = destination.resolve()
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(self._latest_report.to_json(indent=indent))
        return destination

    # ------------------------------------------------------------------
    # Internal execution helpers (invoked inside the VM sandbox)
    # ------------------------------------------------------------------
    def _run_analysis(self) -> None:
        files = list(self._collect_python_files())
        self.vm.state.log(f"LINFER: Scanning {len(files)} Python files")
        for path in files:
            rel = self._relative(path)
            self.vm.state.log(f"PEXAMINE: {rel}")
            source = self._safe_read(path)
            if source is None:
                continue
            try:
                tree = ast.parse(source, filename=str(path))
            except SyntaxError as exc:
                self._log(
                    f"LASSERT: Failed to parse {rel}: {exc}",
                    severity="warning",
                )
                continue
            for rule in self.rules:
                try:
                    for finding in rule.analyze(tree, path, source):
                        self._record_finding(finding)
                except Exception as exc:  # pragma: no cover - defensive
                    self._log(
                        f"LASSERT: Rule {rule.name} crashed on {rel}: {exc}",
                        severity="error",
                    )
        timestamp = self._now().isoformat()
        self._latest_report = BugHunterReport(
            repo=self.repo,
            findings=list(self._findings),
            logs=list(self._logs),
            scanned_files=len(files),
            executed_rules=[rule.name for rule in self.rules],
            timestamp=timestamp,
        )
        self.vm.state.log(
            f"LDEDUCE: Analysis complete with {len(self._findings)} findings",
        )

    # ------------------------------------------------------------------
    # VM-safe recording helpers (used by the _MinimalSession proxy)
    # ------------------------------------------------------------------
    def _record_finding_from_vm(self, payload: dict) -> None:
        """Validate and record a finding reported from VM-executed code.

        Only accepts a restricted set of fields and converts them into a
        Finding instance on the host side. This prevents the VM from
        constructing arbitrary Python objects and keeps recorded data
        strictly serialisable payloads.
        """
        allowed_keys = {"rule", "severity", "file", "line", "message", "remediation", "evidence"}
        if not isinstance(payload, dict):
            self._log("LASSERT: VM attempted to report non-dict finding", severity="error")
            return
        filtered = {k: payload.get(k) for k in allowed_keys}
        try:
            finding = Finding(
                rule=str(filtered.get("rule", "unknown")),
                severity=str(filtered.get("severity", "info")),
                file=Path(filtered.get("file", "")),
                line=int(filtered.get("line", 1) or 1),
                message=str(filtered.get("message", "")),
                remediation=str(filtered.get("remediation", "")),
                evidence=filtered.get("evidence"),
            )
        except Exception as exc:  # defensive
            self._log(f"LASSERT: Invalid finding payload from VM: {exc}", severity="error")
            return
        self._record_finding(finding)

    # ------------------------------------------------------------------
    # Utility methods
    # ------------------------------------------------------------------
    def _reset(self) -> None:
        self._logs.clear()
        self._findings.clear()
        self._latest_report = None

    def _log(self, message: str, *, severity: str = "INFO") -> None:
        entry = LogEntry(
            timestamp=self._now().isoformat(),
            message=message,
            severity=severity.upper(),
        )
        self._logs.append(entry)

    def _record_finding(self, finding: Finding) -> None:
        self._findings.append(finding)
        rel = self._relative(finding.file)
        self._log(
            f"LDEDUCE: {finding.rule} -> {rel}:{finding.line}",
        )

    def _collect_python_files(self) -> Iterable[Path]:
        for path in self.repo.rglob("*.py"):
            if any(part in self._EXCLUDED_DIRS for part in path.parts):
                continue
            if path.is_file():
                yield path

    def _safe_read(self, path: Path) -> Optional[str]:
        try:
            return path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            self._log(
                f"LASSERT: Skipping non-UTF8 file {self._relative(path)}",
                severity="warning",
            )
        except OSError as exc:
            self._log(
                f"LASSERT: Failed to read {self._relative(path)}: {exc}",
                severity="error",
            )
        return None

    def _relative(self, path: Path) -> str:
        try:
            return str(path.relative_to(self.repo))
        except ValueError:
            return str(path)

    def _now(self) -> datetime:
        """Return a timezone-aware timestamp for logging."""

        return datetime.now(timezone.utc).replace(microsecond=0)


__all__ = ["BugHunter", "BugHunterReport"]
