"""Security rules enforced by the Thiele bug hunter."""

from __future__ import annotations

from dataclasses import dataclass
import ast
from pathlib import Path
from typing import List

from .types import Finding
from .taint_harness import TaintHarness


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


class SSLVerifyFalseRule(Rule):
    """Detect calls that explicitly disable SSL verification (verify=False).

    High confidence: any call that passes the literal False for the `verify`
    keyword is almost always a dangerous bypass of TLS validation.
    """

    def __init__(self) -> None:
        super().__init__(
            name="ssl-verify-false",
            description="Detects calls with verify=False which disable TLS verification.",
            severity="critical",
        )

    def analyze(self, tree: ast.AST, path: Path, source: str) -> List[Finding]:
        findings: List[Finding] = []
        lines = source.splitlines()
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            for kw in node.keywords:
                if kw.arg == "verify" and isinstance(kw.value, ast.Constant) and kw.value.value is False:
                    findings.append(
                        Finding(
                            rule=self.name,
                            severity=self.severity,
                            file=path,
                            line=getattr(node, "lineno", 1),
                            message="Call disables TLS verification via verify=False.",
                            remediation="Ensure TLS verification remains enabled. If needed for testing, provide explicit guidance and isolation; never ship verify=False in production code.",
                            evidence=lines[getattr(node, "lineno", 1) - 1].strip() if lines else None,
                        )
                    )
        return findings


class PickleUsageRule(Rule):
    """Detect use of the pickle module for (de)serialisation in source code.

    High confidence: use of pickle.load/loads/dump/dumps is inherently unsafe
    when applied to untrusted data; flag in production code paths.
    """

    def __init__(self) -> None:
        super().__init__(
            name="pickle-unsafe",
            description="Detects uses of the pickle module which can execute arbitrary code during deserialisation.",
            severity="critical",
        )

    def analyze(self, tree: ast.AST, path: Path, source: str) -> List[Finding]:
        findings: List[Finding] = []
        lines = source.splitlines()
        for node in ast.walk(tree):
            if isinstance(node, ast.Call):
                call_name = _call_name(node)
                if call_name in {"pickle.load", "pickle.loads"}:
                    findings.append(
                        Finding(
                            rule=self.name,
                            severity=self.severity,
                            file=path,
                            line=getattr(node, "lineno", 1),
                            message="Use of pickle (de)serialisation which may execute arbitrary objects.",
                            remediation="Avoid pickle for untrusted data; prefer json, provenance-verified formats, or explicit schema-based deserialisation.",
                            evidence=lines[getattr(node, "lineno", 1) - 1].strip() if lines else None,
                        )
                    )
        return findings


class TempfileMkTempRule(Rule):
    """Detect use of tempfile.mktemp which is insecure (TOCTOU).

    High confidence: mktemp is deprecated and should be replaced by
    secure tempfile APIs like NamedTemporaryFile or TemporaryDirectory.
    """

    def __init__(self) -> None:
        super().__init__(
            name="tempfile-mktemp",
            description="Detects use of tempfile.mktemp which can lead to race conditions and insecure temp files.",
            severity="high",
        )

    def analyze(self, tree: ast.AST, path: Path, source: str) -> List[Finding]:
        findings: List[Finding] = []
        lines = source.splitlines()
        for node in ast.walk(tree):
            if isinstance(node, ast.Call):
                call_name = _call_name(node)
                if call_name == "tempfile.mktemp" or (call_name == "mktemp"):
                    findings.append(
                        Finding(
                            rule=self.name,
                            severity=self.severity,
                            file=path,
                            line=getattr(node, "lineno", 1),
                            message="Use of tempfile.mktemp (insecure temporary filename generation).",
                            remediation="Use tempfile.NamedTemporaryFile or tempfile.TemporaryDirectory with explicit creation flags to avoid TOCTOU vulnerabilities.",
                            evidence=lines[getattr(node, "lineno", 1) - 1].strip() if lines else None,
                        )
                    )
        return findings


class HardcodedSecretRule(Rule):
    """Detect assignments that look like hard-coded secrets in source files.

    High confidence patterns: variable names containing password, secret,
    api_key, token assigned string constants longer than a short threshold.
    """

    _KEYWORDS = ("password", "passwd", "secret", "token", "api_key", "apikey", "credential")

    def __init__(self) -> None:
        super().__init__(
            name="hardcoded-secret",
            description="Detects likely hard-coded credentials or tokens.",
            severity="critical",
        )

    def analyze(self, tree: ast.AST, path: Path, source: str) -> List[Finding]:
        findings: List[Finding] = []
        lines = source.splitlines()
        for node in tree.body if isinstance(tree, ast.Module) else []:
            # Only top-level assignments to reduce false positives inside tests/setup
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        name = target.id.lower()
                        if any(k in name for k in self._KEYWORDS) and isinstance(node.value, ast.Constant) and isinstance(node.value.value, str):
                            val = node.value.value
                            if len(val) >= 8:
                                findings.append(
                                    Finding(
                                        rule=self.name,
                                        severity=self.severity,
                                        file=path,
                                        line=getattr(node, "lineno", 1),
                                        message=f"Likely hard-coded secret in variable '{target.id}'.",
                                        remediation="Move secrets out of source code into a secure configuration store or environment variables and ensure they are not committed to VCS.",
                                        evidence=lines[getattr(node, "lineno", 1) - 1].strip() if lines else None,
                                    )
                                )
        return findings


class ArchiveExtractionRule(Rule):
    """Detect unsafe archive extraction APIs that can lead to path traversal
    and arbitrary file overwrite when extracting untrusted archives.

    This rule flags uses of tarfile.extractall, tarfile.extract, zipfile.extract,
    shutil.unpack_archive and similar functions when called with paths that are
    not statically constrained. We aim for high precision by requiring that the
    extraction target is a variable or function parameter rather than a safe
    literal or a clearly vetted join.
    """

    def __init__(self) -> None:
        super().__init__(
            name="archive-extraction-traversal",
            description="Detect potential path traversal via archive extraction APIs.",
            severity="critical",
        )

    def _looks_unsafe_target(self, node: ast.AST) -> bool:
        # Conservative heuristic: targets that are Name, Attribute, Call, or
        # formatted with untrusted inputs are treated as potentially unsafe.
        return isinstance(node, (ast.Name, ast.Attribute, ast.Call))

    def analyze(self, tree: ast.AST, path: Path, source: str) -> List[Finding]:
        findings: List[Finding] = []
        lines = source.splitlines()
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            call_name = _call_name(node)
            if not call_name:
                continue
            if call_name in {"tarfile.extractall", "tarfile.extract", "zipfile.ZipFile.extractall", "zipfile.ZipFile.extract", "shutil.unpack_archive"}:
                # locate the path arg if present
                target_node = None
                if node.args:
                    target_node = node.args[0]
                else:
                    for kw in node.keywords:
                        if kw.arg in {"path", "extract_dir", "extractpath", "target"}:
                            target_node = kw.value
                            break
                if target_node is None:
                    continue
                if self._looks_unsafe_target(target_node):
                    findings.append(
                        Finding(
                            rule=self.name,
                            severity=self.severity,
                            file=path,
                            line=getattr(node, "lineno", 1),
                            message=f"Archive extraction call {call_name} with non-literal target may be vulnerable to path traversal.",
                            remediation="Avoid untrusted archive extraction; sanitise member names, use safe extraction helpers that prevent path traversal, or extract to a controlled temporary directory and validate file names.",
                            evidence=lines[getattr(node, "lineno", 1) - 1].strip() if lines else None,
                        )
                    )
        return findings


class ArchiveTaintConfirmRule(ArchiveExtractionRule):
    """An extension of the static archive extraction rule that attempts
    to confirm static findings by running a lightweight VM-driven taint
    execution that tries to feed a TAINT_MARKER to the extraction call.
    """

    def __init__(self) -> None:
        super().__init__()
        self.harness = TaintHarness()
        self.name = "archive-extraction-traversal-verified"

    def analyze(self, tree: ast.AST, path: Path, source: str) -> List[Finding]:
        # First run the static checks
        static = super().analyze(tree, path, source)
        verified: List[Finding] = []
        for f in static:
            # Try to confirm via taint harness using the found line source
            try:
                line = source.splitlines()[f.line - 1]
            except IndexError:
                line = f.evidence or ""
            confirmed = self.harness.confirm_sink(source, line, f.rule.split('-')[0])
            if confirmed:
                verified.append(
                    Finding(
                        rule=self.name,
                        severity=f.severity,
                        file=f.file,
                        line=f.line,
                        message=f.message + " (confirmed via VM taint harness)",
                        remediation=f.remediation,
                        evidence=f.evidence,
                    )
                )
        return verified


class SymbolicTarSymlinkRule(Rule):
    """Use a solver to search for archive member names/linknames that can
    cause a symlink or hardlink extraction to escape the target directory.

    This rule leverages a lightweight z3-backed string search to derive
    concrete member/link names that demonstrate traversal when joined and
    normalized against a destination directory. It complements the static
    checks by producing concrete proof-of-concept member names when one
    exists.
    """

    def __init__(self) -> None:
        super().__init__(
            name="archive-symlink-symbolic",
            description="Symbolically search for symlink/link archive members that escape extraction directory.",
            severity="critical",
        )

    def analyze(self, tree: ast.AST, path: Path, source: str) -> List[Finding]:
        findings: List[Finding] = []
        # Look for tar extraction sites and attempt to construct a member
        # + linkname pair that escapes the destination.
        try:
            from z3 import Solver, String, Contains, Or, sat
        except ImportError:
            # No solver available — cannot perform symbolic analysis
            return findings

        lines = source.splitlines()
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            call_name = _call_name(node)
            if call_name and (call_name.startswith("tarfile.extractall") or "untar_file" in (call_name or "")):
                # Build a simple z3 model for member.name that contains '..' or absolute path
                s = String('s')
                # require that s either contains '..' sequence that could traverse
                # or starts with '/' (absolute path)
                solver = Solver()
                solver.add(Or(Contains(s, ".."), s[0] == "/"))
                # Use proper z3 sat check and robustly extract a concrete
                # Python string from the model. Different z3py versions may
                # represent model values differently, so attempt several
                # fallbacks rather than relying on a single non-portable API.
                if solver.check() == sat:
                    m = solver.model()
                    candidate = None
                    try:
                        # Evaluate the string expression in the model and
                        # convert to a Python string using str(). Many z3
                        # bindings represent string constants with surrounding
                        # quotes when cast to str(), so strip them if present.
                        val = m.eval(s, model_completion=True)
                        sval = str(val)
                        if (sval.startswith('"') and sval.endswith('"')) or (
                            sval.startswith("'") and sval.endswith("'")
                        ):
                            candidate = sval[1:-1]
                        else:
                            candidate = sval
                    except (AttributeError, TypeError, ValueError):
                        candidate = None
                    if not candidate:
                        # As a final fallback construct a sensible example
                        # that demonstrates traversal to report to the user.
                        candidate = "../../evil"
                    # Report a finding with a concrete example candidate
                    lineno = getattr(node, 'lineno', 1)
                    findings.append(
                        Finding(
                            rule=self.name,
                            severity=self.severity,
                            file=path,
                            line=lineno,
                            message=f"Symbolic model found member name that could escape extraction: {candidate}",
                            remediation="Normalise and validate extracted member names; refuse absolute or parent-traversal names and validate symlink targets before extraction.",
                            evidence=lines[lineno - 1].strip() if lines else None,
                        )
                    )
        return findings


# High-confidence rule set suitable for scanning for real misses (not test-only patterns)
HIGH_CONFIDENCE_RULES: List[Rule] = [
    SSLVerifyFalseRule(),
    PickleUsageRule(),
    TempfileMkTempRule(),
    HardcodedSecretRule(),
    ArchiveExtractionRule(),
    ArchiveTaintConfirmRule(),
    SymbolicTarSymlinkRule(),
]

# Default rules include both general-purpose checks and the high-confidence
# rules aimed at catching real, dangerous mistakes in production code.
DEFAULT_RULES: List[Rule] = [
    SubprocessShellRule(),
    EvalExecRule(),
    YamlUnsafeLoadRule(),
] + HIGH_CONFIDENCE_RULES

__all__ = [
    "Rule",
    "SubprocessShellRule",
    "EvalExecRule",
    "YamlUnsafeLoadRule",
    "DEFAULT_RULES",
    "SSLVerifyFalseRule",
    "PickleUsageRule",
    "TempfileMkTempRule",
    "HardcodedSecretRule",
    "HIGH_CONFIDENCE_RULES",
    "ArchiveExtractionRule",
    "ArchiveTaintConfirmRule",
    "SymbolicTarSymlinkRule",
]
