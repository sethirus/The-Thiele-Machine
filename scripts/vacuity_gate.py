#!/usr/bin/env python3
"""Kernel-conversion vacuity gate.

For every `Theorem`/`Lemma`/`Corollary` in a target `.v` file, ask Coq's
kernel whether the conclusion is convertible (after δ/ι/ζ/β reduction)
to either:

  (probe a) the proposition `True`, or
  (probe b) one of the theorem's own hypotheses.

A positive probe is conclusive: Coq's own kernel accepts a trivial
proof of the theorem, so the theorem is vacuous. False positives are
impossible by construction. False negatives — existentials behind
layered unification, polymorphism that defeats lazy reduction — slip
through silently. Those get caught by reading the proof, not the gate.

Usage::

    python3 scripts/vacuity_gate.py \
        --target coq/test_fixtures/VacuitySmoke.v \
        --logical TestFixtures.VacuitySmoke \
        --output artifacts/vacuity_audit.json

Multiple ``--target``/``--logical`` pairs are accepted. Output is a
single JSON file aggregating verdicts for every theorem in every
target.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field, asdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_PROBE_DIR = REPO_ROOT / "build" / "vacuity_probes"
COQ_ROOT = REPO_ROOT / "coq"
COQ_PROJECT = COQ_ROOT / "_CoqProject"


# ---------------------------------------------------------------------------
# Coq source parsing
# ---------------------------------------------------------------------------


def strip_coq_comments(text: str) -> str:
    """Remove (nested) ``(* ... *)`` comments, preserving offsets with spaces."""
    out: list[str] = []
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        if i + 1 < n and text[i] == "(" and text[i + 1] == "*":
            depth += 1
            out.append("  ")
            i += 2
            continue
        if i + 1 < n and text[i] == "*" and text[i + 1] == ")" and depth > 0:
            depth -= 1
            out.append("  ")
            i += 2
            continue
        if depth > 0:
            out.append(" " if text[i] != "\n" else "\n")
            i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


@dataclass(frozen=True)
class TheoremDecl:
    name: str
    kind: str            # Theorem | Lemma | Corollary | ...
    statement: str       # text between `:` and terminating `.`
    line: int            # 1-based start line


def _find_sentence_end(text: str, start: int) -> int | None:
    """Find the offset of the `.` that terminates the Coq sentence beginning at *start*."""
    paren = 0
    i = start
    n = len(text)
    while i < n:
        c = text[i]
        if c == "(":
            paren += 1
        elif c == ")":
            paren = max(0, paren - 1)
        elif c == "." and paren == 0:
            if i + 1 == n or text[i + 1] in " \t\n\r":
                return i
        i += 1
    return None


_KINDS = ("Theorem", "Lemma", "Corollary", "Proposition", "Fact", "Remark")

# Pre-compiled: matches a theorem-like header at start-of-line. Captures kind + name.
_HEADER_RE = __import__("re").compile(
    r"(?m)^[ \t]*(Theorem|Lemma|Corollary|Proposition|Fact|Remark)[ \t]+([A-Za-z0-9_']+)"
)


def parse_theorems(source_text: str) -> list[TheoremDecl]:
    """Extract Theorem/Lemma declarations from *source_text*.

    Linear-time: regex-finds every header in one pass, then for each match
    advances past the colon to find the sentence-terminating `.`.
    """
    text = strip_coq_comments(source_text)
    decls: list[TheoremDecl] = []
    for m in _HEADER_RE.finditer(text):
        kind = m.group(1)
        name = m.group(2)
        # Walk forward from the end of the name token to find the top-level `:`.
        j = m.end()
        paren = 0
        n = len(text)
        colon_idx: int | None = None
        while j < n:
            c = text[j]
            if c == "(":
                paren += 1
            elif c == ")":
                paren = max(0, paren - 1)
            elif c == ":" and paren == 0:
                # Skip `::` (notation) and `:=` (definition syntax sneaking in).
                if text[j : j + 2] != ":=" and text[j - 1 : j + 1] != "::":
                    colon_idx = j
                    break
            elif c == "." and paren == 0:
                # No `:` before the sentence terminator → not a real theorem header
                # (e.g. `Theorem name := body.` style, or aborted declaration).
                break
            j += 1
        if colon_idx is None:
            continue
        end_idx = _find_sentence_end(text, colon_idx + 1)
        if end_idx is None:
            continue
        raw_stmt = text[colon_idx + 1 : end_idx].strip()
        stmt = " ".join(raw_stmt.split())
        line = text[: m.start()].count("\n") + 1
        decls.append(TheoremDecl(name=name, kind=kind, statement=stmt, line=line))
    return decls


# ---------------------------------------------------------------------------
# Probe synthesis + execution
# ---------------------------------------------------------------------------


@dataclass
class ProbeRun:
    probe_name: str           # "a" or "b"
    succeeded: bool           # coqc exit code == 0
    coq_stderr_tail: str = ""
    probe_path: str = ""


@dataclass
class TheoremVerdict:
    name: str
    file: str
    line: int
    kind: str
    statement: str
    probe_a: ProbeRun | None = None
    probe_b: ProbeRun | None = None
    status: str = "ok"        # ok | vacuous-true | vacuous-hyp | error

    def to_dict(self) -> dict:
        d = asdict(self)
        return d


# Probe (a): the theorem's conclusion is convertible (after lazy reduction) to True.
PROBE_A_TACTIC = "Proof. intros; lazy; exact I. Qed."
# Probe (b): the theorem's conclusion is convertible to one of its hypotheses.
PROBE_B_TACTIC = "Proof. intros; lazy in *; assumption. Qed."


def synthesise_probe(
    *,
    probe_kind: str,                # "a" | "b"
    source_logical_name: str,       # e.g. "TestFixtures.VacuitySmoke" or "Kernel.MuChaitin"
    theorem: TheoremDecl,
    probe_dir: Path,
) -> Path:
    """Write a probe .v file to *probe_dir* and return its path."""
    tactic = PROBE_A_TACTIC if probe_kind == "a" else PROBE_B_TACTIC
    safe_name = theorem.name.replace("'", "_q")
    probe_path = probe_dir / f"{source_logical_name.replace('.', '__')}__{safe_name}__{probe_kind}.v"
    # If the logical name is dotted (e.g. "TestFixtures.VacuitySmoke"), use
    # `From <prefix> Require Import <suffix>.`; otherwise (top-level coq/ files
    # with no -R prefix in _CoqProject) use the unqualified form.
    if "." in source_logical_name:
        prefix, suffix = source_logical_name.rsplit(".", 1)
        require_line = f"From {prefix} Require Import {suffix}."
    else:
        require_line = f"Require Import {source_logical_name}."
    body = (
        f"(* Auto-generated by scripts/vacuity_gate.py — DO NOT EDIT. *)\n"
        f"{require_line}\n"
        f"Theorem _vacuity_probe_{probe_kind}_{safe_name} : {theorem.statement}.\n"
        f"{tactic}\n"
    )
    probe_path.write_text(body, encoding="utf-8")
    return probe_path


def _coq_flags_from_project(coqproject: Path) -> list[str]:
    """Extract -R / -Q flags from a `_CoqProject` file as a flat list usable on
    the coqc command line.

    Also adds `-Q <project_dir> ""` whenever the project directory itself
    contains .v files at its top level (i.e. files listed in _CoqProject with
    no explicit -R/-Q prefix). Without this, probes that `Require Import` a
    top-level file like [ReceiptTheorem] or [VerifierModel] cannot find the
    .vo because no -R/-Q line in _CoqProject binds the project root to a
    logical prefix. With the empty-prefix binding, top-level imports resolve.
    """
    if not coqproject.exists():
        return []
    root = coqproject.parent.resolve()
    explicit_flags: list[str] = []
    has_top_level_v_listing = False
    for raw in coqproject.read_text(encoding="utf-8", errors="replace").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("-R ") or line.startswith("-Q "):
            parts = line.split()
            if len(parts) >= 3:
                mapping = parts[1]
                logical = parts[2]
                mapping_path = Path(mapping)
                if not mapping_path.is_absolute():
                    mapping_path = (root / mapping_path).resolve()
                explicit_flags.extend([parts[0], str(mapping_path), logical])
        elif line.endswith(".v") and "/" not in line:
            has_top_level_v_listing = True

    # Coq's -Q binding is recursive — `-Q coq ""` would override the more
    # specific `-Q coq/kernel/foundation Kernel` bindings if it came later
    # on the command line. coqc resolves later flags as taking precedence
    # over earlier ones for the same directory, so the empty-prefix
    # binding must come FIRST and the explicit kernel mappings AFTER, so
    # the explicit ones win for their subdirectories.
    flags: list[str] = []
    if has_top_level_v_listing:
        # Empty-prefix binding so `Require Import <stem>` resolves for
        # top-level files. Pass an actual empty string as the logical name
        # — not the literal characters `""`, which coqc treats as a
        # malformed identifier.
        flags.extend(["-Q", str(root), ""])
    flags.extend(explicit_flags)
    return flags


def run_probe(probe_path: Path, coq_flags: list[str], timeout: int = 30) -> ProbeRun:
    """Run `coqc` on *probe_path* and report whether it accepted the proof."""
    cmd = ["coqc", *coq_flags, str(probe_path)]
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        succeeded = proc.returncode == 0
        tail = ((proc.stderr or "") + (proc.stdout or ""))[-400:].strip()
        return ProbeRun(
            probe_name=probe_path.stem.rsplit("__", 1)[-1],
            succeeded=succeeded,
            coq_stderr_tail=tail if not succeeded else "",
            probe_path=str(probe_path.relative_to(REPO_ROOT)),
        )
    except subprocess.TimeoutExpired:
        return ProbeRun(
            probe_name=probe_path.stem.rsplit("__", 1)[-1],
            succeeded=False,
            coq_stderr_tail=f"<timeout after {timeout}s>",
            probe_path=str(probe_path.relative_to(REPO_ROOT)),
        )


# ---------------------------------------------------------------------------
# Top-level orchestration
# ---------------------------------------------------------------------------


def _new_verdict(target_path: Path, decl: TheoremDecl) -> TheoremVerdict:
    return TheoremVerdict(
        name=decl.name,
        file=str(target_path.relative_to(REPO_ROOT)),
        line=decl.line,
        kind=decl.kind,
        statement=decl.statement,
    )


def _probe_theorem_serial(
    verdict: TheoremVerdict,
    decl: TheoremDecl,
    *,
    logical_module: str,
    probe_dir: Path,
    coq_flags: list[str],
    timeout: int,
) -> None:
    """Fill *verdict* by spawning one coqc per probe — the reference path.

    Probe (a) first; probe (b) only if (a) didn't already flag. This is the
    original, deliberately-simple implementation; the batched path below must
    produce identical verdicts (pinned by tests/test_vacuity_gate.py).
    """
    a_path = synthesise_probe(
        probe_kind="a",
        source_logical_name=logical_module,
        theorem=decl,
        probe_dir=probe_dir,
    )
    verdict.probe_a = run_probe(a_path, coq_flags, timeout=timeout)
    if verdict.probe_a.succeeded:
        verdict.status = "vacuous-true"
    else:
        # Probe (b) — only worth running if (a) didn't already flag
        b_path = synthesise_probe(
            probe_kind="b",
            source_logical_name=logical_module,
            theorem=decl,
            probe_dir=probe_dir,
        )
        verdict.probe_b = run_probe(b_path, coq_flags, timeout=timeout)
        if verdict.probe_b.succeeded:
            verdict.status = "vacuous-hyp"


def gate_one_target(
    *,
    target_path: Path,
    logical_module: str,
    probe_dir: Path,
    coq_flags: list[str],
    timeout: int,
) -> list[TheoremVerdict]:
    """Serial reference path: one coqc per probe (see module docstring).

    Kept as the correctness oracle for the batched path and as the explicit
    ``--engine serial`` escape hatch. For real corpora prefer
    ``gate_one_target_batched`` — it loads each target's .vo closure once
    instead of once per probe.
    """
    text = target_path.read_text(encoding="utf-8", errors="replace")
    decls = parse_theorems(text)
    verdicts: list[TheoremVerdict] = []
    for decl in decls:
        verdict = _new_verdict(target_path, decl)
        _probe_theorem_serial(
            verdict,
            decl,
            logical_module=logical_module,
            probe_dir=probe_dir,
            coq_flags=coq_flags,
            timeout=timeout,
        )
        verdicts.append(verdict)
    return verdicts


# ---------------------------------------------------------------------------
# Batched per-target probing — the fast path.
#
# The serial path above spawns one coqc per probe, and EVERY probe re-loads
# the target module's entire .vo closure. That deserialisation (seconds of
# kernel work) dwarfs the millisecond convertibility check it then performs;
# for a target with N theorems it is up to 2N cold loads of the SAME closure.
#
# The batched path loads the closure ONCE. It synthesises a single .v that
# `Require Import`s the target a single time, then emits two convertibility
# probes per theorem, each wrapped in `tryif (...) then idtac "...VACUOUS"
# else idtac "...OK"` so that NEITHER outcome aborts the batch. The probes
# use non-closing tests (`change`) so every block ends with the goal still
# open and a plain `Abort` returns to a known state. Verdicts are read back
# from the idtac markers on coqc's stdout.
#
# Faithfulness to the serial probes (pinned by the equivalence test in
# tests/test_vacuity_gate.py):
#   probe a  serial `intros; lazy; exact I`  →  batch `intros; lazy; change True`
#   probe b  serial `intros; lazy in *; assumption`
#                                            →  batch `intros; lazy in *;
#                                                match goal with H : ?T |- _ => change T end`
# `change`, `exact I` and `assumption` all defer to the same kernel
# convertibility test; `change` merely leaves the goal open instead of closing
# it, which is what lets every probe end from a known proof state.
#
# Safety net: if a theorem's markers are missing from stdout — e.g. a
# statement that fails to elaborate aborts the batch at that sentence — that
# theorem falls back to `_probe_theorem_serial`. Correctness never depends on
# the batch surviving to the end.
# ---------------------------------------------------------------------------

_BATCH_PROBE_A = "intros; lazy; change True"
_BATCH_PROBE_B = "intros; lazy in *; match goal with H : ?T |- _ => change T end"
_MARKER_RE = re.compile(r"VPROBE\s+(\d+)\s+([ab])\s+(VACUOUS|OK)")


def _require_line(source_logical_name: str) -> str:
    if "." in source_logical_name:
        prefix, suffix = source_logical_name.rsplit(".", 1)
        return f"From {prefix} Require Import {suffix}."
    return f"Require Import {source_logical_name}."


def synthesise_batched_probe(
    *,
    source_logical_name: str,
    decls: list[TheoremDecl],
    probe_dir: Path,
) -> Path:
    """Write ONE probe .v covering every theorem in a target; return its path."""
    parts = [
        "(* Auto-generated by scripts/vacuity_gate.py (batched) — DO NOT EDIT. *)",
        _require_line(source_logical_name),
    ]
    for i, decl in enumerate(decls):
        for probe, tac in (("a", _BATCH_PROBE_A), ("b", _BATCH_PROBE_B)):
            parts.append(f"Goal {decl.statement}.")
            parts.append(
                f'  tryif ({tac}) then idtac "VPROBE {i} {probe} VACUOUS"'
                f' else idtac "VPROBE {i} {probe} OK".'
            )
            parts.append("Abort.")
    probe_path = probe_dir / f"{source_logical_name.replace('.', '__')}__BATCH.v"
    probe_path.write_text("\n".join(parts) + "\n", encoding="utf-8")
    return probe_path


def run_batched_target(
    probe_path: Path, coq_flags: list[str], timeout: int
) -> dict[int, dict[str, bool]]:
    """Run the batched probe; return {theorem_index: {"a": bool, "b": bool}}.

    True means that probe's convertibility test SUCCEEDED (theorem vacuous
    under that probe). Indices/probes absent from the result (batch aborted
    early, or timed out) are left for the caller's per-theorem fallback.
    """
    cmd = ["coqc", *coq_flags, str(probe_path)]
    try:
        proc = subprocess.run(
            cmd, cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=timeout
        )
    except subprocess.TimeoutExpired:
        return {}
    out: dict[int, dict[str, bool]] = {}
    for m in _MARKER_RE.finditer((proc.stdout or "") + "\n" + (proc.stderr or "")):
        out.setdefault(int(m.group(1)), {})[m.group(2)] = m.group(3) == "VACUOUS"
    return out


def gate_one_target_batched(
    *,
    target_path: Path,
    logical_module: str,
    probe_dir: Path,
    coq_flags: list[str],
    timeout: int,
) -> list[TheoremVerdict]:
    """Fast path: one coqc per target (see comment above).

    Verdicts are identical to ``gate_one_target``; any theorem the batch fails
    to report falls back to the serial per-probe path.
    """
    text = target_path.read_text(encoding="utf-8", errors="replace")
    decls = parse_theorems(text)
    if not decls:
        return []

    batch_path = synthesise_batched_probe(
        source_logical_name=logical_module, decls=decls, probe_dir=probe_dir
    )
    # The batch does one closure load then 2N millisecond checks, so it needs
    # roughly one probe's worth of time, not 2N. Be generous but bounded.
    batch_timeout = max(180, timeout * 3)
    seen = run_batched_target(batch_path, coq_flags, batch_timeout)
    batch_rel = str(batch_path.relative_to(REPO_ROOT))

    verdicts: list[TheoremVerdict] = []
    for i, decl in enumerate(decls):
        verdict = _new_verdict(target_path, decl)
        marks = seen.get(i)
        if marks is None or "a" not in marks or "b" not in marks:
            # Batch didn't reach/report this theorem → exact serial fallback.
            _probe_theorem_serial(
                verdict,
                decl,
                logical_module=logical_module,
                probe_dir=probe_dir,
                coq_flags=coq_flags,
                timeout=timeout,
            )
        elif marks["a"]:
            verdict.status = "vacuous-true"
            verdict.probe_a = ProbeRun(probe_name="a", succeeded=True, probe_path=batch_rel)
        elif marks["b"]:
            verdict.status = "vacuous-hyp"
            verdict.probe_b = ProbeRun(probe_name="b", succeeded=True, probe_path=batch_rel)
        verdicts.append(verdict)
    return verdicts


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--target",
        action="append",
        default=[],
        metavar="PATH",
        help="Coq .v source to scan (repeatable). Pair each with --logical.",
    )
    p.add_argument(
        "--logical",
        action="append",
        default=[],
        metavar="MODULE",
        help="Logical module name for the corresponding --target (e.g. TestFixtures.VacuitySmoke).",
    )
    p.add_argument(
        "--manifest",
        type=Path,
        default=None,
        metavar="PATH",
        help=(
            "JSON manifest listing targets — schema "
            '{"targets":[{"path":"...","logical":"..."}, ...]}. '
            "An empty manifest is valid: the gate produces an empty audit report."
        ),
    )
    p.add_argument(
        "--output",
        type=Path,
        default=REPO_ROOT / "artifacts" / "vacuity_audit.json",
        help="Path for the JSON verdict report.",
    )
    p.add_argument(
        "--probe-dir",
        type=Path,
        default=DEFAULT_PROBE_DIR,
        help="Directory to write synthesised probe .v files into.",
    )
    p.add_argument(
        "--coqproject",
        type=Path,
        default=COQ_PROJECT,
        help="Path to _CoqProject for -R/-Q flag inference.",
    )
    p.add_argument(
        "--timeout",
        type=int,
        default=30,
        help="Per-probe coqc timeout in seconds.",
    )
    p.add_argument(
        "--engine",
        choices=("batched", "serial"),
        default="batched",
        help=(
            "batched (default): one coqc per target — loads each .vo closure "
            "once. serial: one coqc per probe — the reference oracle, much "
            "slower, kept for equivalence testing and debugging."
        ),
    )
    p.add_argument(
        "--jobs",
        type=int,
        default=0,
        metavar="N",
        help=(
            "Number of targets to probe concurrently. 0 (default) = "
            "min(4, CPU count - 1). Each worker holds one coqc's closure in "
            "memory, so lower this under memory pressure."
        ),
    )
    p.add_argument(
        "--merge",
        action="store_true",
        help=(
            "Merge into an existing --output audit instead of replacing it: "
            "verdicts for the files probed in THIS run replace their old "
            "entries; every other file's verdicts are kept; the summary is "
            "recomputed over the union. Lets an incremental caller (the "
            "pre-commit hook) re-probe only changed files without shrinking "
            "the committed audit."
        ),
    )
    args = p.parse_args()

    if shutil.which("coqc") is None:
        print("vacuity_gate: coqc not found in PATH — cannot run.", file=sys.stderr)
        return 2

    if len(args.target) != len(args.logical):
        print(
            "vacuity_gate: --target and --logical must be paired (same count).",
            file=sys.stderr,
        )
        return 2

    # Merge manifest-supplied targets with CLI targets.
    pairs: list[tuple[str, str]] = list(zip(args.target, args.logical))
    if args.manifest is not None:
        if not args.manifest.exists():
            print(
                f"vacuity_gate: manifest not found: {args.manifest}",
                file=sys.stderr,
            )
            return 2
        try:
            manifest_data = json.loads(args.manifest.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            print(f"vacuity_gate: manifest JSON invalid: {exc}", file=sys.stderr)
            return 2
        for entry in manifest_data.get("targets", []):
            pairs.append((entry["path"], entry["logical"]))

    args.probe_dir.mkdir(parents=True, exist_ok=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)

    coq_flags = _coq_flags_from_project(args.coqproject)

    # Resolve + validate every target up front (fail fast before spawning coqc).
    resolved: list[tuple[Path, str]] = []
    for target_str, logical in pairs:
        target_path = Path(target_str)
        if not target_path.is_absolute():
            target_path = (REPO_ROOT / target_path).resolve()
        if not target_path.is_file():
            print(f"vacuity_gate: target not found: {target_path}", file=sys.stderr)
            return 2
        resolved.append((target_path, logical))

    gate_fn = gate_one_target_batched if args.engine == "batched" else gate_one_target

    def _probe(item: tuple[Path, str]) -> list[TheoremVerdict]:
        target_path, logical = item
        return gate_fn(
            target_path=target_path,
            logical_module=logical,
            probe_dir=args.probe_dir,
            coq_flags=coq_flags,
            timeout=args.timeout,
        )

    jobs = args.jobs if args.jobs > 0 else min(4, max(1, (os.cpu_count() or 2) - 1))

    all_verdicts: list[TheoremVerdict] = []
    if jobs <= 1 or len(resolved) <= 1:
        for item in resolved:
            all_verdicts.extend(_probe(item))
    else:
        # The heavy work is in coqc subprocesses, so threads (which release the
        # GIL across subprocess.run) parallelise fine and avoid pickling state.
        # pool.map preserves input order → the audit is deterministic.
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            for verdicts in pool.map(_probe, resolved):
                all_verdicts.extend(verdicts)

    verdict_dicts = [v.to_dict() for v in all_verdicts]

    if args.merge and args.output.exists():
        probed_files = set()
        for target_str, _logical in pairs:
            target_path = Path(target_str)
            if not target_path.is_absolute():
                target_path = (REPO_ROOT / target_str).resolve()
            try:
                probed_files.add(str(target_path.relative_to(REPO_ROOT)))
            except ValueError:
                probed_files.add(str(target_path))
        try:
            prior = json.loads(args.output.read_text(encoding="utf-8"))
            kept = [
                v for v in prior.get("verdicts", [])
                if v.get("file") not in probed_files
            ]
        except (json.JSONDecodeError, OSError) as exc:
            print(
                f"vacuity_gate: --merge could not read prior audit ({exc}); "
                "writing this run's verdicts only.",
                file=sys.stderr,
            )
            kept = []
        verdict_dicts = kept + verdict_dicts

    report = {
        "schema": "vacuity_audit.v1",
        "verdicts": verdict_dicts,
        "summary": {
            "total": len(verdict_dicts),
            "ok": sum(1 for v in verdict_dicts if v["status"] == "ok"),
            "vacuous_true": sum(1 for v in verdict_dicts if v["status"] == "vacuous-true"),
            "vacuous_hyp": sum(1 for v in verdict_dicts if v["status"] == "vacuous-hyp"),
            "error": sum(1 for v in verdict_dicts if v["status"] == "error"),
        },
    }
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    try:
        display_path = args.output.resolve().relative_to(REPO_ROOT)
    except ValueError:
        display_path = args.output
    print(
        f"vacuity_gate: wrote {display_path} "
        f"({report['summary']['total']} theorems, "
        f"{report['summary']['vacuous_true']} vacuous-true, "
        f"{report['summary']['vacuous_hyp']} vacuous-hyp)"
    )

    # Exit code policy: any vacuous-true / vacuous-hyp result is a finding,
    # but the gate itself does not error out — that is the consumer's choice.
    # For CI integration, the wrapping pytest test decides whether to fail.
    return 0


if __name__ == "__main__":
    sys.exit(main())
