#!/usr/bin/env python3
"""Generate a single, deep cross-layer integration atlas.

Outputs exactly one canonical artifact:
  - artifacts/ATLAS.md

Design intent:
- Help integration, not blind deletion.
- Never recommend proofs for removal.
- Only classify `remove_safe` when confidence is extremely high:
  stale/legacy path markers + zero incoming/outgoing edges + non-proof symbols.
- Provide rich, thesis-friendly diagrams and detailed tables.
"""

from __future__ import annotations

import ast
import csv
import json
import os
import re
import shutil
import subprocess
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import DefaultDict, Dict, Iterable, List, Mapping, Optional, Sequence, Set, Tuple

REPO_ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = REPO_ROOT / "artifacts"
OUT_PATH = ARTIFACTS / "ATLAS.md"
ATLAS_EXPORT_DIR = ARTIFACTS / "atlas"
STATE_DIR = REPO_ROOT / ".atlas_state"
HISTORY_PATH = STATE_DIR / "atlas_history.json"

COQ_ROOT = REPO_ROOT / "coq"
PYTHON_ROOTS = [
    REPO_ROOT / "thielecpu",
    REPO_ROOT / "scripts",
    REPO_ROOT / "verifier",
    REPO_ROOT / "tools",
    REPO_ROOT / "demos" / "scripts",
    REPO_ROOT / "build",
    REPO_ROOT / "experiments",
]
TEST_ROOTS = [REPO_ROOT / "tests", REPO_ROOT / "scripts"]
RTL_ROOTS = [REPO_ROOT / "thielecpu" / "hardware", REPO_ROOT / "fpga"]

STALE_MARKERS = {"archive", "disabled", "exploratory", "unused", "deprecated", "legacy", "old", "patches"}

# Synthesis output / generated netlists — these are build artifacts, not source RTL.
# Including them inflates the symbol table with thousands of auto-generated wire names
# that can never participate in cross-layer isomorphism.
RTL_GENERATED_SUFFIXES = {"_out.v", "_netlist.v", "_synth.v"}
RTL_GENERATED_STEMS = {"synth_lite_out", "synth_full_out"}
REMOVE_SAFE_MARKERS = {"unused", "deprecated", "legacy", "dead", "tmp", "disabled"}
PROD_LAYERS = {"coq", "python", "rtl"}

DOD_THRESHOLDS: Dict[str, float] = {
    # ── Priority 1: Core isomorphism gates ──
    # All proofs connected across Coq↔Python↔RTL, full triad closure
    "min_isomorphism_score": 100.0,
    "min_triad_completion_ratio": 1.0,
    "min_core_bridge_ratio": 1.0,
    # ── Priority 2: Test verification gates ──
    # Every production symbol and file exercised by tests
    "min_test_prod_symbol_coverage_ratio": 1.0,
    "min_test_prod_file_coverage_ratio": 1.0,
    "max_isolated_test_files": 0.0,
    # ── Priority 3: Per-proof documentation gates ──
    # Every theorem/lemma has a (** doc comment, every directory has README
    "min_per_proof_doc_ratio": 1.0,
    "min_proof_files_with_readme_ratio": 1.0,
    "min_kernel_proof_latex_coverage_ratio": 1.0,
    # ── Priority 4: Toolchain gates — real compilation/synthesis checks ──
    "min_coq_compile_pass": 1.0,
    "min_extraction_freshness_pass": 1.0,
    "min_rtl_synthesis_pass": 1.0,
}

COQ_DECL_RE = re.compile(
    r"^\s*(?:Local\s+|Global\s+|#\[.*?\]\s*)?"
    r"(Theorem|Lemma|Corollary|Proposition|Fact|Remark|Definition|Fixpoint|"
    r"CoFixpoint|Inductive|CoInductive|Record|Class|Instance|Axiom|"
    r"Hypothesis|Parameter|Variable|Conjecture)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)",
    re.MULTILINE,
)
COQ_REQUIRE_RE = re.compile(
    r"^\s*(?:From\s+\S+\s+)?Require\s+(?:Import\s+|Export\s+)?([A-Za-z0-9_.]+)",
    re.MULTILINE,
)
COQ_REF_TOKEN_RE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_']*)\b")
COQ_END_RE = re.compile(r"^\s*(Qed\.|Defined\.|Admitted\.|Save\.|Abort\.)\s*$")

RTL_MODULE_RE = re.compile(r"^\s*module\s+([A-Za-z_][A-Za-z0-9_]*)\s*[#(;]", re.MULTILINE)
RTL_LOCALPARAM_RE = re.compile(r"^\s*localparam\s+(?:\[[^\]]+\]\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*=", re.MULTILINE)
RTL_PORT_RE = re.compile(r"^\s*(?:input|output|inout)\s+(?:wire\s+|reg\s+)?(?:\[[^\]]+\]\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*[,;)]", re.MULTILINE)
RTL_WIRE_REG_RE = re.compile(r"^\s*(?:wire|reg)\s+(?:\[[^\]]+\]\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*[;,=[]", re.MULTILINE)
RTL_INSTANCE_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s+(?:#\([^)]*\)\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*\(", re.MULTILINE)
PY_CONST_RE = re.compile(r"^[ \t]*([A-Z][A-Z0-9_]{2,})\s*[=:]\s*", re.MULTILINE)
VERILOG_NUM_RE = re.compile(r"^\s*(\d+)'([dDhHbBoO])([0-9a-fA-F_xXzZ]+)\s*$")
COQ_RAT_RE = re.compile(r"(-?\d+)\s*#\s*(-?\d+)")

# Typed normalization rules for deep cross-layer constant comparison.
# Without this, the audit can report false mismatches from representation changes
# (e.g. raw Q16 carrier int vs scaled real).
NORM_COMPARE_RULES: List[Tuple[re.Pattern[str], str]] = [
    (re.compile(r"^q16_"), "int32_raw"),
    (re.compile(r"^(tsirelson_bound|tau_mu|classical_bound|quantum_bound)$"), "q16_real"),
    (re.compile(r"^tsirelson_(alice|bob)_(setting|outcome)$"), "enum_b01"),
]
NORM_SKIP_RULES: Set[str] = {
    # Known semantic collision: Coq real-valued measure vs RTL width-like constant.
    "variation_of_information",
    # Generic names currently collide across unrelated constants.
    "mask",
    "modulus",
}
INT_EXPR_NAMES: Dict[str, int] = {
    "Q16_SHIFT": 16,
    "q16_shift": 16,
}


@dataclass
class Symbol:
    id: str
    name: str
    norm: str
    kind: str
    layer: str
    file: str
    line: int
    raw_refs: List[str] = field(default_factory=list)
    value: Optional[str] = None  # Extracted value for constants/localparams


@dataclass
class Edge:
    src_id: str
    dst_id: str
    kind: str


def _read(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def _rel(path: Path) -> str:
    try:
        return path.relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def _norm(name: str) -> str:
    return re.sub(r"[_' ]+", "_", name.lower()).strip("_")


def _safe_id(raw: str) -> str:
    return re.sub(r"[^a-zA-Z0-9_]", "_", raw)


def _as_int(value: object, default: int = 0) -> int:
    if isinstance(value, bool):
        return int(value)
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return int(value)
    if isinstance(value, str):
        try:
            return int(value)
        except ValueError:
            return default
    return default


def _as_float(value: object, default: float = 0.0) -> float:
    if isinstance(value, bool):
        return float(int(value))
    if isinstance(value, (int, float)):
        return float(value)
    if isinstance(value, str):
        try:
            return float(value)
        except ValueError:
            return default
    return default


def _is_stale(path: Path) -> bool:
    return any(part.lower() in STALE_MARKERS for part in path.parts)


def _has_remove_marker(rel_path: str) -> bool:
    parts = Path(rel_path).parts
    return any(part.lower() in REMOVE_SAFE_MARKERS for part in parts)


def _sym_id(layer: str, file: str, line: int, name: str, kind: str) -> str:
    return f"{layer}:{file}:{line}:{kind}:{name}"


def _coq_kind_is_proof(kind: str) -> bool:
    return kind in {
        "theorem",
        "lemma",
        "corollary",
        "proposition",
        "fact",
        "remark",
        "conjecture",
    }


def _norm_compare_mode(norm: str) -> str:
    for patt, mode in NORM_COMPARE_RULES:
        if patt.match(norm):
            return mode
    return "auto"


def _safe_eval_int_expr(expr: str, names: Mapping[str, int]) -> Optional[int]:
    """Evaluate a constrained integer expression safely (no calls/attributes)."""
    try:
        node = ast.parse(expr, mode="eval")
    except SyntaxError:
        return None

    def eval_node(n: ast.AST) -> int:
        if isinstance(n, ast.Expression):
            return eval_node(n.body)
        if isinstance(n, ast.Constant) and isinstance(n.value, int):
            return int(n.value)
        if isinstance(n, ast.Name):
            if n.id in names:
                return int(names[n.id])
            raise ValueError(f"unknown name {n.id}")
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, (ast.UAdd, ast.USub, ast.Invert)):
            v = eval_node(n.operand)
            if isinstance(n.op, ast.UAdd):
                return +v
            if isinstance(n.op, ast.USub):
                return -v
            return ~v
        if isinstance(n, ast.BinOp):
            l = eval_node(n.left)
            r = eval_node(n.right)
            if isinstance(n.op, ast.Add):
                return l + r
            if isinstance(n.op, ast.Sub):
                return l - r
            if isinstance(n.op, ast.Mult):
                return l * r
            if isinstance(n.op, ast.FloorDiv):
                return l // r
            if isinstance(n.op, ast.LShift):
                return l << r
            if isinstance(n.op, ast.RShift):
                return l >> r
            if isinstance(n.op, ast.BitOr):
                return l | r
            if isinstance(n.op, ast.BitAnd):
                return l & r
            if isinstance(n.op, ast.Pow):
                return l ** r
        raise ValueError("unsupported expression")

    try:
        return eval_node(node)
    except ValueError:
        return None


def _iter_unique(paths: Iterable[Path]) -> List[Path]:
    seen: Set[str] = set()
    out: List[Path] = []
    for path in paths:
        rel = _rel(path)
        if rel in seen:
            continue
        seen.add(rel)
        out.append(path)
    return sorted(out)


def _parse_coq_file(path: Path) -> List[Symbol]:
    text = _read(path)
    rel = _rel(path)
    
    if _is_stale(path):
        layer = "stale"
    elif "tests" in path.parts:
        layer = "test"
    else:
        layer = "coq"
        
    symbols: List[Symbol] = []

    for m in COQ_REQUIRE_RE.finditer(text):
        line = text[: m.start()].count("\n") + 1
        name = f"require::{m.group(1)}"
        symbols.append(
            Symbol(
                id=_sym_id(layer, rel, line, name, "import"),
                name=name,
                norm=_norm(name),
                kind="import",
                layer=layer,
                file=rel,
                line=line,
            )
        )

    lines = text.splitlines()
    i = 0
    while i < len(lines):
        m = COQ_DECL_RE.match(lines[i])
        if not m:
            i += 1
            continue
        kind = m.group(1).lower()
        name = m.group(2)
        line_no = i + 1
        decl_line = lines[i]  # Save the declaration line for value extraction
        i += 1
        
        # Check if this is a one-liner (declaration line contains '.' before any comment or at end)
        # Remove inline comments and check for period
        line_without_comment = re.sub(r'\(\*.*?\*\)', '', decl_line)
        is_one_liner = '.' in line_without_comment
        
        body_lines: List[str] = []
        if not is_one_liner:
            while i < len(lines):
                # Check if we hit a proof end marker
                if COQ_END_RE.match(lines[i]):
                    body_lines.append(lines[i])
                    i += 1
                    break
                # Check if we hit the next declaration (don't consume it)
                if COQ_DECL_RE.match(lines[i]):
                    break
                # Add this line to body
                body_lines.append(lines[i])
                # Check if this line ends the definition (ends with '.' and not a comment line)
                line_stripped = lines[i].strip()
                if line_stripped.endswith('.') and not line_stripped.startswith('(*'):
                    i += 1
                    break
                i += 1
        body = "\n".join(body_lines)
        refs = sorted({tok for tok in COQ_REF_TOKEN_RE.findall(body) if tok != name and len(tok) > 1})
        
        # Extract value for definitions
        value_str = None
        if kind == "definition":
            # First check the declaration line itself (for one-liners like "Definition x := 5.")
            if ":=" in decl_line:
                value_str = decl_line.split(":=", 1)[-1].split(".")[0].strip()
            # Otherwise check body_lines
            elif not value_str:
                for line in body_lines[:5]:
                    if ":=" in line:
                        value_str = line.split(":=", 1)[-1].split(".")[0].strip()
                        break
        
        symbols.append(
            Symbol(
                id=_sym_id(layer, rel, line_no, name, kind),
                name=name,
                norm=_norm(name),
                kind=kind,
                layer=layer,
                file=rel,
                line=line_no,
                raw_refs=refs,
                value=value_str,
            )
        )

    return symbols


def _attach_parents(tree: ast.AST) -> None:
    for node in ast.walk(tree):
        for child in ast.iter_child_nodes(node):
            setattr(child, "_parent", node)


def _node_refs(node: ast.AST) -> List[str]:
    refs: Set[str] = set()
    for sub in ast.walk(node):
        if isinstance(sub, ast.Name):
            refs.add(sub.id)
        elif isinstance(sub, ast.Attribute):
            refs.add(sub.attr)
        elif isinstance(sub, ast.Call):
            if isinstance(sub.func, ast.Name):
                refs.add(sub.func.id)
            elif isinstance(sub.func, ast.Attribute):
                refs.add(sub.func.attr)
    return sorted(refs)


def _parse_python_file(path: Path, is_test: bool = False) -> List[Symbol]:
    text = _read(path)
    rel = _rel(path)
    layer = "stale" if _is_stale(path) else ("test" if is_test else "python")
    symbols: List[Symbol] = []

    try:
        tree = ast.parse(text, filename=str(path))
    except SyntaxError:
        return symbols

    _attach_parents(tree)

    for node in ast.walk(tree):
        if isinstance(node, ast.ClassDef):
            symbols.append(
                Symbol(
                    id=_sym_id(layer, rel, node.lineno, node.name, "class"),
                    name=node.name,
                    norm=_norm(node.name),
                    kind="class",
                    layer=layer,
                    file=rel,
                    line=node.lineno,
                    raw_refs=_node_refs(node),
                )
            )
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            kind = "method" if isinstance(getattr(node, "_parent", None), ast.ClassDef) else "function"
            symbols.append(
                Symbol(
                    id=_sym_id(layer, rel, node.lineno, node.name, kind),
                    name=node.name,
                    norm=_norm(node.name),
                    kind=kind,
                    layer=layer,
                    file=rel,
                    line=node.lineno,
                    raw_refs=_node_refs(node),
                )
            )
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            if isinstance(node, ast.ImportFrom):
                module = node.module or ""
                for alias in node.names:
                    symname = alias.asname or alias.name
                    ref = f"{module}.{alias.name}" if module else alias.name
                    nm = f"import::{symname}"
                    symbols.append(
                        Symbol(
                            id=_sym_id(layer, rel, node.lineno, nm, "import"),
                            name=nm,
                            norm=_norm(nm),
                            kind="import",
                            layer=layer,
                            file=rel,
                            line=node.lineno,
                            raw_refs=[ref, alias.name],
                        )
                    )
            else:
                for alias in node.names:
                    symname = alias.asname or alias.name
                    nm = f"import::{symname}"
                    symbols.append(
                        Symbol(
                            id=_sym_id(layer, rel, node.lineno, nm, "import"),
                            name=nm,
                            norm=_norm(nm),
                            kind="import",
                            layer=layer,
                            file=rel,
                            line=node.lineno,
                            raw_refs=[alias.name],
                        )
                    )
        elif isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and re.match(r"^[A-Z][A-Z0-9_]{2,}$", target.id):
                    # Extract value string
                    value_str = None
                    try:
                        value_str = ast.get_source_segment(text, node.value)
                    except:
                        pass
                    symbols.append(
                        Symbol(
                            id=_sym_id(layer, rel, node.lineno, target.id, "constant"),
                            name=target.id,
                            norm=_norm(target.id),
                            kind="constant",
                            layer=layer,
                            file=rel,
                            line=node.lineno,
                            raw_refs=_node_refs(node.value),
                            value=value_str,
                        )
                    )

    for m in PY_CONST_RE.finditer(text):
        name = m.group(1)
        line = text[: m.start()].count("\n") + 1
        if not any(s.name == name and s.file == rel for s in symbols):
            # Extract value
            value_start = m.end()
            value_line = text[m.start():text.find('\n', value_start) if text.find('\n', value_start) != -1 else len(text)]
            value = value_line.split('=', 1)[-1].split('#')[0].strip() if '=' in value_line else None
            
            symbols.append(
                Symbol(
                    id=_sym_id(layer, rel, line, name, "constant"),
                    name=name,
                    norm=_norm(name),
                    kind="constant",
                    layer=layer,
                    file=rel,
                    line=line,
                    value=value,
                )
            )

    return symbols


def _parse_rtl_file(path: Path, is_tb: bool = False) -> List[Symbol]:
    text = _read(path)
    rel = _rel(path)
    layer = "stale" if _is_stale(path) else ("rtl_tb" if is_tb else "rtl")
    symbols: List[Symbol] = []

    def ln(match: re.Match) -> int:
        return text[: match.start()].count("\n") + 1

    for m in RTL_MODULE_RE.finditer(text):
        name = m.group(1)
        symbols.append(
            Symbol(
                id=_sym_id(layer, rel, ln(m), name, "module"),
                name=name,
                norm=_norm(name),
                kind="module",
                layer=layer,
                file=rel,
                line=ln(m),
            )
        )

    # Improved localparam parser - handle multiple on one line: localparam A=1, B=2;
    for m in re.finditer(r"localparam\s+(?:\[[^\]]+\]\s+)?(.*?);", text, re.DOTALL):
        line_no = ln(m)
        content = m.group(1)
        # Remove comments from content
        content = re.sub(r'//.*', '', content)
        content = re.sub(r'/\*.*?\*/', '', content, flags=re.DOTALL)
        
        parts = content.split(",")
        for part in parts:
            if "=" in part:
                p_name_val = part.split("=", 1)
                p_name = p_name_val[0].strip().split()[-1]
                p_val = p_name_val[1].strip()
                # De-duplicate: if multiple definitions in same file (e.g. ifdef), 
                # keep first one for simplicity.
                if any(s.name == p_name and s.file == rel for s in symbols):
                    continue
                symbols.append(
                    Symbol(
                        id=_sym_id(layer, rel, line_no, p_name, "localparam"),
                        name=p_name,
                        norm=_norm(p_name),
                        kind="localparam",
                        layer=layer,
                        file=rel,
                        line=line_no,
                        value=p_val,
                    )
                )

    for m in RTL_PORT_RE.finditer(text):
        name = m.group(1)
        if any(s.name == name and s.file == rel for s in symbols):
            continue
        symbols.append(
            Symbol(
                id=_sym_id(layer, rel, ln(m), name, "port"),
                name=name,
                norm=_norm(name),
                kind="port",
                layer=layer,
                file=rel,
                line=ln(m),
            )
        )

    for m in RTL_WIRE_REG_RE.finditer(text):
        name = m.group(1)
        if any(s.name == name and s.file == rel for s in symbols):
            continue
        symbols.append(
            Symbol(
                id=_sym_id(layer, rel, ln(m), name, "wire"),
                name=name,
                norm=_norm(name),
                kind="wire",
                layer=layer,
                file=rel,
                line=ln(m),
            )
        )

    for m in RTL_INSTANCE_RE.finditer(text):
        inst_type = m.group(1)
        inst_name = m.group(2)
        if inst_type in {"input", "output", "wire", "reg", "module", "always", "if", "else", "begin", "end", "case", "assign"}:
            continue
        sym_name = f"inst::{inst_name}"
        symbols.append(
            Symbol(
                id=_sym_id(layer, rel, ln(m), sym_name, "instance"),
                name=sym_name,
                norm=_norm(sym_name),
                kind="instance",
                layer=layer,
                file=rel,
                line=ln(m),
                raw_refs=[inst_type],
            )
        )

    return symbols


def _discover_all() -> Tuple[List[Path], List[Path], List[Path], List[Path], List[Path]]:
    coq_files = _iter_unique(p for p in COQ_ROOT.rglob("*.v") if p.is_file())

    py_src_files = _iter_unique(
        p
        for root in PYTHON_ROOTS
        if root.exists()
        for p in root.rglob("*.py")
        if p.is_file() and "__pycache__" not in p.parts and not p.name.startswith("test_")
    )

    py_test_files = _iter_unique(
        p
        for root in TEST_ROOTS
        if root.exists()
        for p in root.rglob("test_*.py")
        if p.is_file() and "__pycache__" not in p.parts
    )

    rtl_files = _iter_unique(
        p
        for root in RTL_ROOTS
        if root.exists()
        for pattern in ("*.v", "*.sv", "*.vh")
        for p in root.rglob(pattern)
        if p.is_file()
        and p.stem not in RTL_GENERATED_STEMS
        and not any(p.name.endswith(suffix) for suffix in RTL_GENERATED_SUFFIXES)
    )

    rtl_tb_files = [
        p
        for p in rtl_files
        if "testbench" in p.parts or p.name.endswith("_tb.v") or "tb" in p.stem.lower()
    ]
    rtl_src_files = [p for p in rtl_files if p not in rtl_tb_files]

    return coq_files, py_src_files, py_test_files, rtl_src_files, rtl_tb_files


def _build_symbol_table(
    coq_files: List[Path],
    py_src_files: List[Path],
    py_test_files: List[Path],
    rtl_src_files: List[Path],
    rtl_tb_files: List[Path],
) -> List[Symbol]:
    symbols: List[Symbol] = []
    for path in coq_files:
        symbols.extend(_parse_coq_file(path))
    for path in py_src_files:
        symbols.extend(_parse_python_file(path, is_test=False))
    for path in py_test_files:
        symbols.extend(_parse_python_file(path, is_test=True))
    for path in rtl_src_files:
        symbols.extend(_parse_rtl_file(path, is_tb=False))
    for path in rtl_tb_files:
        symbols.extend(_parse_rtl_file(path, is_tb=True))
    return symbols


def _add_edge(
    edges: List[Edge],
    seen: Set[Tuple[str, str, str]],
    src_id: str,
    dst_id: str,
    kind: str,
) -> None:
    if src_id == dst_id:
        return
    key = (src_id, dst_id, kind)
    if key in seen:
        return
    seen.add(key)
    edges.append(Edge(src_id=src_id, dst_id=dst_id, kind=kind))


def _build_edges(symbols: List[Symbol]) -> List[Edge]:
    sym_by_id: Dict[str, Symbol] = {s.id: s for s in symbols}
    by_name: DefaultDict[str, List[str]] = defaultdict(list)
    by_norm: DefaultDict[str, List[str]] = defaultdict(list)

    for s in symbols:
        by_name[s.name].append(s.id)
        if len(s.norm) >= 2:
            by_norm[s.norm].append(s.id)

    edges: List[Edge] = []
    seen: Set[Tuple[str, str, str]] = set()

    for s in symbols:
        for ref in s.raw_refs:
            token = ref.split(".")[-1]
            candidates = by_name.get(token, [])[:20]
            for cid in candidates:
                other = sym_by_id[cid]
                if s.layer == "coq" and other.layer == "coq":
                    _add_edge(edges, seen, s.id, other.id, "coq_ref")
                elif s.layer in {"python", "test", "stale"} and other.layer in {"python", "test", "stale"}:
                    _add_edge(edges, seen, s.id, other.id, "py_ref")
                elif s.layer in {"rtl", "rtl_tb", "stale"} and other.layer in {"rtl", "rtl_tb", "stale"}:
                    _add_edge(edges, seen, s.id, other.id, "rtl_ref")

    for name, ids in by_name.items():
        if len(ids) < 2:
            continue
        for i, src_id in enumerate(ids):
            for dst_id in ids[i + 1 :]:
                src = sym_by_id[src_id]
                dst = sym_by_id[dst_id]
                if src.layer == dst.layer:
                    continue
                if src.layer in PROD_LAYERS and dst.layer in PROD_LAYERS:
                    _add_edge(edges, seen, src_id, dst_id, "cross_name")
                    _add_edge(edges, seen, dst_id, src_id, "cross_name")

    for norm, ids in by_norm.items():
        if len(norm) < 4 or len(ids) < 2:
            continue
        for i, src_id in enumerate(ids):
            for dst_id in ids[i + 1 :]:
                src = sym_by_id[src_id]
                dst = sym_by_id[dst_id]
                if src.layer == dst.layer:
                    continue
                if src.name == dst.name:
                    continue
                if src.layer in PROD_LAYERS and dst.layer in PROD_LAYERS:
                    _add_edge(edges, seen, src_id, dst_id, "cross_norm")
                    _add_edge(edges, seen, dst_id, src_id, "cross_norm")

    py_consts = [s for s in symbols if s.layer == "python" and s.kind == "constant"]
    rtl_consts = [s for s in symbols if s.layer == "rtl" and s.kind == "localparam"]
    py_const_by = {s.name: s.id for s in py_consts}
    rtl_const_by = {s.name: s.id for s in rtl_consts}
    for k in sorted(set(py_const_by) & set(rtl_const_by)):
        _add_edge(edges, seen, py_const_by[k], rtl_const_by[k], "cross_opcode")
        _add_edge(edges, seen, rtl_const_by[k], py_const_by[k], "cross_opcode")

    # Stem matching: connect symbols whose norm starts with another symbol's norm
    # as a prefix, separated by underscore.  E.g. Coq 'mu_cost_nonneg' → Python 'mu_cost'.
    # The stem pool uses implementation symbols (definitions, functions, etc.) as stems.
    # Any production symbol (including theorems/lemmas) can match a stem.
    _STEM_ANCHOR_KINDS = {
        "function", "class", "method", "constant", "localparam", "port", "wire",
        "module", "definition", "fixpoint", "inductive", "coinductive", "record",
    }
    stem_pool: Dict[str, List[str]] = defaultdict(list)
    for s in symbols:
        if s.layer in PROD_LAYERS and len(s.norm) >= 4 and s.kind in _STEM_ANCHOR_KINDS:
            stem_pool[s.norm].append(s.id)

    stem_norms = sorted(stem_pool.keys())
    for s in symbols:
        if s.layer not in PROD_LAYERS or len(s.norm) < 5:
            continue
        # Check if this symbol's norm starts with any stem-pool norm + underscore
        for stem in stem_norms:
            if len(stem) >= len(s.norm):
                continue
            if not s.norm.startswith(stem + "_"):
                continue
            for target_id in stem_pool[stem]:
                target = sym_by_id[target_id]
                if target.layer == s.layer:
                    continue
                _add_edge(edges, seen, s.id, target_id, "cross_stem")
                _add_edge(edges, seen, target_id, s.id, "cross_stem")

    # Test coverage edges: test symbols → prod symbols via raw_refs
    for s in symbols:
        if s.layer != "test":
            continue
        refs = set(s.raw_refs)
        for ref in refs:
            token = ref.split(".")[-1]
            for other_id in by_name.get(token, []):
                other = sym_by_id[other_id]
                if other.layer in PROD_LAYERS:
                    _add_edge(edges, seen, s.id, other.id, "test_covers")

    # Cross-layer reference edges: any prod symbol whose raw_refs mention a symbol
    # name from a *different* prod layer gets a cross_ref edge.
    for s in symbols:
        if s.layer not in PROD_LAYERS:
            continue
        refs = set(s.raw_refs)
        for ref in refs:
            token = ref.split(".")[-1]
            for other_id in by_name.get(token, [])[:10]:
                other = sym_by_id[other_id]
                if other.layer in PROD_LAYERS and other.layer != s.layer:
                    _add_edge(edges, seen, s.id, other.id, "cross_ref")
                    _add_edge(edges, seen, other_id, s.id, "cross_ref")

    # Transitive cross-layer propagation (1-hop):
    # If symbol A has a within-layer reference edge to symbol B, and B has a
    # cross-layer edge to symbol C in a different prod layer, then A is
    # transitively connected to that layer.  This captures the common pattern
    # where a Coq lemma 'mu_cost_nonneg_step' references 'mu_cost' (within Coq),
    # and 'mu_cost' connects cross-layer to Python's 'mu_cost'.
    cross_connected: Dict[str, Set[str]] = defaultdict(set)
    for e in edges:
        if e.kind.startswith("cross_") or e.kind == "test_covers":
            src = sym_by_id.get(e.src_id)
            dst = sym_by_id.get(e.dst_id)
            if src and dst and src.layer in PROD_LAYERS and dst.layer in PROD_LAYERS and src.layer != dst.layer:
                cross_connected[src.id].add(dst.layer)

    within_edges: DefaultDict[str, Set[str]] = defaultdict(set)
    for e in edges:
        src = sym_by_id.get(e.src_id)
        dst = sym_by_id.get(e.dst_id)
        if src and dst and src.layer == dst.layer and src.layer in PROD_LAYERS:
            within_edges[src.id].add(dst.id)

    for src_id, neighbors in within_edges.items():
        src = sym_by_id[src_id]
        if src_id in cross_connected:
            continue  # already cross-connected
        for neighbor_id in neighbors:
            if neighbor_id in cross_connected:
                for target_layer in cross_connected[neighbor_id]:
                    if target_layer != src.layer:
                        # Pick any symbol from the connected neighbor's cross targets
                        # to form the edge (we just need the layer connection)
                        for e2 in edges:
                            dst2 = sym_by_id.get(e2.dst_id)
                            if e2.src_id == neighbor_id and dst2 and dst2.layer == target_layer:
                                _add_edge(edges, seen, src_id, e2.dst_id, "cross_transitive")
                                break

    return edges


def _classify(symbols: List[Symbol], edges: List[Edge]) -> Tuple[Dict[str, str], Dict[str, int], Dict[str, Set[str]]]:
    sym_by_id: Dict[str, Symbol] = {s.id: s for s in symbols}
    incident: Dict[str, int] = defaultdict(int)
    connected_prod_layers: Dict[str, Set[str]] = defaultdict(set)

    for edge in edges:
        src = sym_by_id[edge.src_id]
        dst = sym_by_id[edge.dst_id]
        incident[src.id] += 1
        incident[dst.id] += 1
        if dst.layer in PROD_LAYERS:
            connected_prod_layers[src.id].add(dst.layer)
        if src.layer in PROD_LAYERS:
            connected_prod_layers[dst.id].add(src.layer)

    norm_layer_files: DefaultDict[Tuple[str, str], Set[str]] = defaultdict(set)
    for s in symbols:
        norm_layer_files[(s.norm, s.layer)].add(s.file)

    cls: Dict[str, str] = {}
    for s in symbols:
        if s.layer == "stale":
            cls[s.id] = "stale"
            continue
        if s.layer in {"test", "rtl_tb"}:
            cls[s.id] = "test_only"
            continue

        is_duplicate = len(norm_layer_files.get((s.norm, s.layer), set())) > 1

        prod = set(connected_prod_layers.get(s.id, set()))
        own = {s.layer} if s.layer in PROD_LAYERS else set()
        cross = prod - own

        # Cross-layer connection takes priority over duplicate status:
        # a symbol that connects to 2+ other layers is "core" even if duplicated,
        # and one connecting to 1 other layer is "bridge" even if duplicated.
        if len(cross) >= 2:
            cls[s.id] = "core"
        elif len(cross) == 1:
            cls[s.id] = "bridge"
        elif is_duplicate:
            cls[s.id] = "duplicate"
        elif incident.get(s.id, 0) > 0:
            cls[s.id] = "island"
        else:
            cls[s.id] = "orphan"

    return cls, incident, connected_prod_layers


def _strict_remove_safe(file_path: str, file_syms: List[Symbol], cls: Dict[str, str], incident: Dict[str, int]) -> bool:
    if not _has_remove_marker(file_path):
        return False
    if any(s.layer == "coq" for s in file_syms):
        return False
    for s in file_syms:
        if s.layer == "coq" and _coq_kind_is_proof(s.kind):
            return False
        if incident.get(s.id, 0) > 0:
            return False
        if cls.get(s.id) not in {"orphan", "stale", "test_only"}:
            return False
        if s.kind in {"theorem", "lemma", "corollary", "proposition", "fact", "remark", "conjecture"}:
            return False
    return len(file_syms) > 0


def _file_metrics(symbols: List[Symbol], cls: Dict[str, str], incident: Dict[str, int]) -> List[Dict[str, object]]:
    by_file: DefaultDict[str, List[Symbol]] = defaultdict(list)
    for s in symbols:
        by_file[s.file].append(s)

    rows: List[Dict[str, object]] = []
    for file_path, file_syms in sorted(by_file.items()):
        layer_counter = Counter(s.layer for s in file_syms)
        layer = max(layer_counter, key=lambda k: layer_counter[k])
        counts = Counter(cls.get(s.id, "unknown") for s in file_syms)

        total_prod = sum(counts[k] for k in ("core", "bridge", "island", "orphan", "duplicate"))
        connected = counts["core"] + counts["bridge"]
        ratio = round((connected / total_prod), 3) if total_prod else 0.0

        action = "keep"
        if layer == "stale":
            action = "archive"
        elif counts["duplicate"] > 0:
            action = "deduplicate"
        elif _strict_remove_safe(file_path, file_syms, cls, incident):
            action = "remove_safe"
        elif layer == "coq":
            action = "integrate" if ratio < 0.25 else "keep"
        elif layer in {"python", "rtl"}:
            action = "integrate" if ratio < 0.35 else "keep"

        rows.append(
            {
                "file": file_path,
                "layer": layer,
                "symbol_count": len(file_syms),
                "core": counts["core"],
                "bridge": counts["bridge"],
                "island": counts["island"],
                "orphan": counts["orphan"],
                "duplicate": counts["duplicate"],
                "stale": counts["stale"],
                "test_only": counts["test_only"],
                "connectivity_ratio": ratio,
                "action": action,
            }
        )

    rows.sort(key=lambda r: (str(r["action"]), _as_float(r["connectivity_ratio"]), str(r["file"])))
    return rows


def _find_triads(symbols: List[Symbol]) -> List[Dict[str, object]]:
    clusters: DefaultDict[str, Dict[str, List[Symbol]]] = defaultdict(lambda: defaultdict(list))
    for s in symbols:
        if s.layer in PROD_LAYERS and len(s.norm) >= 4:
            clusters[s.norm][s.layer].append(s)

    triads: List[Dict[str, object]] = []
    for norm in sorted(clusters):
        if not all(layer in clusters[norm] for layer in ("coq", "python", "rtl")):
            continue
        triads.append(
            {
                "norm": norm,
                "coq": clusters[norm]["coq"][0].name,
                "python": clusters[norm]["python"][0].name,
                "rtl": clusters[norm]["rtl"][0].name,
                "coq_count": len(clusters[norm]["coq"]),
                "python_count": len(clusters[norm]["python"]),
                "rtl_count": len(clusters[norm]["rtl"]),
            }
        )

    triads.sort(
        key=lambda t: (
            -(
                _as_int(t["coq_count"])
                + _as_int(t["python_count"])
                + _as_int(t["rtl_count"])
            ),
            str(t["norm"]),
        )
    )
    return triads


def _validate_triad_isomorphism(symbols: List[Symbol], triads: List[Dict[str, object]]) -> List[Dict[str, object]]:
    """Deep isomorphism check: verify VALUES match across Coq↔Python↔RTL, not just names."""
    violations: List[Dict[str, object]] = []
    
    sym_by_id = {s.id: s for s in symbols}
    clusters: DefaultDict[str, Dict[str, List[Symbol]]] = defaultdict(lambda: defaultdict(list))
    for s in symbols:
        if s.layer in PROD_LAYERS and len(s.norm) >= 4:
            clusters[s.norm][s.layer].append(s)
    
    def normalize_value(value: str, layer: str, norm: str = "", mode: str = "auto") -> Optional[float]:
        """Convert Coq/Python/RTL numeric surface syntax into comparable values."""
        if not value:
            return None

        cleaned = value.strip()
        cleaned = cleaned.split("//", 1)[0].strip()
        cleaned = cleaned.split("/*", 1)[0].strip()
        cleaned = cleaned.replace("_", "")

        # Enums encoded as constructors in Coq and bits in impl layers.
        if mode == "enum_b01":
            token = cleaned.strip("()%;,").upper()
            enum_map = {
                "B0": 0.0,
                "B1": 1.0,
                "0": 0.0,
                "1": 1.0,
            }
            return enum_map.get(token)

        # Python Fraction: Fraction(2828, 1000)
        frac_match = re.search(r"Fraction\(\s*(-?\d+)\s*,\s*(-?\d+)\s*\)", cleaned)
        if frac_match:
            den = int(frac_match.group(2))
            if den != 0:
                return int(frac_match.group(1)) / den

        # Coq rational: (5657 # 2000)%Q
        rat_match = COQ_RAT_RE.search(cleaned)
        if rat_match:
            den = int(rat_match.group(2))
            if den != 0:
                return int(rat_match.group(1)) / den

        # Verilog sized constants: 32'h0002D3CE / 16'd42 / 8'b1010
        vnum = VERILOG_NUM_RE.match(cleaned.rstrip(";,"))
        if vnum:
            width = int(vnum.group(1))
            base = vnum.group(2).lower()
            digits = vnum.group(3).replace("x", "0").replace("z", "0")
            base_map = {"d": 10, "h": 16, "b": 2, "o": 8}
            intval = int(digits, base_map[base])

            # Int carrier view for fixed-point constants (e.g. Q16_ONE = 65536).
            if mode == "int32_raw":
                if width == 32 and intval >= (1 << 31):
                    intval -= (1 << 32)
                return float(intval)

            # Semantic fixed-point view (Q16.16).
            if mode == "q16_real":
                if width == 32 and intval >= (1 << 31):
                    intval -= (1 << 32)
                return float(intval) / 65536.0

            # Backward-compatible heuristic scaling in auto mode.
            norm_l = norm.lower()
            fixed_hint = any(token in norm_l for token in ("fixed", "tau_mu", "classical_bound", "quantum_bound"))
            if mode == "auto" and fixed_hint and width >= 24:
                if intval >= (1 << 31):
                    intval -= (1 << 32)
                return intval / 65536.0
            return float(intval)

        # Trim wrappers like parentheses and Coq %suffixes
        scalar = cleaned.strip("()")
        scalar = re.sub(r"%[A-Za-z0-9_']+", "", scalar)

        # Coq often uses '^' for arithmetic exponentiation.
        if layer == "coq" and "^" in scalar and "**" not in scalar:
            scalar = scalar.replace("^", "**")

        # Plain integer literals (supports 0x... and signs)
        try:
            return float(int(scalar, 0))
        except ValueError:
            pass

        # Safe integer expression subset, e.g. 1 << Q16_SHIFT or 2 ** 256.
        int_expr = _safe_eval_int_expr(scalar, INT_EXPR_NAMES)
        if int_expr is not None:
            if mode == "q16_real":
                return float(int_expr) / 65536.0
            return float(int_expr)

        try:
            return float(scalar)
        except ValueError:
            return None
    
    for triad in triads:
        norm = triad["norm"]
        if norm not in clusters:
            continue
        if norm in NORM_SKIP_RULES:
            continue

        compare_mode = _norm_compare_mode(norm)
        
        coq_syms = clusters[norm].get("coq", [])
        python_syms = clusters[norm].get("python", [])
        rtl_syms = clusters[norm].get("rtl", [])

        coq_value_syms = [s for s in coq_syms if s.value]
        python_value_syms = [s for s in python_syms if s.value]
        rtl_value_syms = [s for s in rtl_syms if s.value]

        # Ambiguous norms (multiple value symbols in a layer) are often name-collisions,
        # not true constant-contract mismatches. Skip until a typed manifest disambiguates.
        if any(len(vs) > 1 for vs in (coq_value_syms, python_value_syms, rtl_value_syms)):
            continue
        
        # Extract values
        coq_vals = [normalize_value(s.value, "coq", norm, compare_mode) for s in coq_value_syms]
        python_vals = [normalize_value(s.value, "python", norm, compare_mode) for s in python_value_syms]
        rtl_vals = [normalize_value(s.value, "rtl", norm, compare_mode) for s in rtl_value_syms]
        
        coq_vals = [v for v in coq_vals if v is not None]
        python_vals = [v for v in python_vals if v is not None]
        rtl_vals = [v for v in rtl_vals if v is not None]
        
        if not coq_vals and not python_vals and not rtl_vals:
            continue  # No values to compare
        
        # Check for mismatches (tolerance 0.1% for floating point)
        all_vals = coq_vals + python_vals + rtl_vals
        if len(all_vals) < 2:
            continue
        
        min_val, max_val = min(all_vals), max(all_vals)
        tolerance = max(abs(min_val), abs(max_val)) * 0.001 if max_val != 0 else 0.001
        
        if abs(max_val - min_val) > tolerance:
            violations.append({
                "norm": norm,
                "compare_mode": compare_mode,
                "coq_value": coq_vals[0] if coq_vals else None,
                "python_value": python_vals[0] if python_vals else None,
                "rtl_value": rtl_vals[0] if rtl_vals else None,
                "coq_raw": coq_syms[0].value if coq_syms and coq_syms[0].value else "",
                "python_raw": python_syms[0].value if python_syms and python_syms[0].value else "",
                "rtl_raw": rtl_syms[0].value if rtl_syms and rtl_syms[0].value else "",
                "delta": max_val - min_val,
                "severity": "CRITICAL" if abs(max_val - min_val) > tolerance * 10 else "WARNING"
            })
    
    return violations


def _cross_layer_matrix(symbols: List[Symbol], edges: List[Edge]) -> Dict[Tuple[str, str], int]:
    sym_by_id = {s.id: s for s in symbols}
    matrix: DefaultDict[Tuple[str, str], int] = defaultdict(int)
    for e in edges:
        src = sym_by_id[e.src_id]
        dst = sym_by_id[e.dst_id]
        if src.layer == dst.layer:
            continue
        if src.layer in PROD_LAYERS and dst.layer in PROD_LAYERS:
            matrix[(src.layer, dst.layer)] += 1
    return dict(matrix)


def _top_cross_file_links(symbols: List[Symbol], edges: List[Edge], limit: int = 30) -> List[Tuple[str, str, int]]:
    sym_by_id = {s.id: s for s in symbols}
    pair_count: DefaultDict[Tuple[str, str], int] = defaultdict(int)
    for e in edges:
        src = sym_by_id[e.src_id]
        dst = sym_by_id[e.dst_id]
        if src.layer == dst.layer:
            continue
        if src.layer not in PROD_LAYERS or dst.layer not in PROD_LAYERS:
            continue
        if src.file == dst.file:
            continue
        pair_count[(src.file, dst.file)] += 1
    ranked = sorted(pair_count.items(), key=lambda kv: (-kv[1], kv[0][0], kv[0][1]))
    return [(a, b, c) for (a, b), c in ranked[:limit]]


def _find_partial_triads(symbols: List[Symbol]) -> List[Dict[str, object]]:
    clusters: DefaultDict[str, Dict[str, List[Symbol]]] = defaultdict(lambda: defaultdict(list))
    for s in symbols:
        if s.layer in PROD_LAYERS and len(s.norm) >= 4:
            clusters[s.norm][s.layer].append(s)

    partial: List[Dict[str, object]] = []
    for norm in sorted(clusters):
        layers = set(clusters[norm].keys())
        if len(layers) != 2:
            continue
        missing = sorted(PROD_LAYERS - layers)
        partial.append(
            {
                "norm": norm,
                "present_layers": ",".join(sorted(layers)),
                "missing_layers": ",".join(missing),
                "coq_count": len(clusters[norm].get("coq", [])),
                "python_count": len(clusters[norm].get("python", [])),
                "rtl_count": len(clusters[norm].get("rtl", [])),
                "weight": sum(len(v) for v in clusters[norm].values()),
            }
        )

    partial.sort(key=lambda r: (-_as_int(r["weight"]), str(r["norm"])))
    return partial


def _compute_isomorphism_metrics(
    symbols: List[Symbol],
    edges: List[Edge],
    cls: Dict[str, str],
    triads: List[Dict[str, object]],
    partial_triads: List[Dict[str, object]],
    file_metrics: List[Dict[str, object]],
) -> Dict[str, object]:
    # Exclude imports from the core_bridge denominator: 'import::os' and similar
    # are dependency declarations, not project-specific symbols that should require
    # cross-layer counterparts.  Also exclude symbols with very short norms (< 3 chars)
    # which are too generic for meaningful cross-layer matching (e.g. 'n', 'x', 'eq').
    prod_symbols = [
        s for s in symbols
        if s.layer in PROD_LAYERS
        and s.kind != "import"
        and len(s.norm) >= 3
    ]
    prod_symbol_count = len(prod_symbols)
    class_counts = Counter(cls.get(s.id, "unknown") for s in prod_symbols)
    core_bridge_count = class_counts.get("core", 0) + class_counts.get("bridge", 0)
    core_bridge_ratio = (core_bridge_count / prod_symbol_count) if prod_symbol_count else 0.0

    triad_count = len(triads)
    partial_count = len(partial_triads)
    triad_completion_ratio = triad_count / (triad_count + partial_count) if (triad_count + partial_count) else 0.0

    matrix = _cross_layer_matrix(symbols, edges)
    directions = [
        ("coq", "python"),
        ("python", "coq"),
        ("coq", "rtl"),
        ("rtl", "coq"),
        ("python", "rtl"),
        ("rtl", "python"),
    ]
    active_directions = sum(1 for pair in directions if matrix.get(pair, 0) > 0)
    directional_coverage = active_directions / len(directions)

    integrate_files = [r for r in file_metrics if str(r.get("action")) == "integrate"]
    prod_files = [r for r in file_metrics if str(r.get("layer")) in PROD_LAYERS]
    integrate_ratio = (len(integrate_files) / len(prod_files)) if prod_files else 0.0

    score = (
        0.35 * core_bridge_ratio
        + 0.35 * triad_completion_ratio
        + 0.20 * directional_coverage
        + 0.10 * (1.0 - integrate_ratio)
    ) * 100.0

    return {
        "isomorphism_score": round(score, 2),
        "core_bridge_ratio": round(core_bridge_ratio, 4),
        "triad_completion_ratio": round(triad_completion_ratio, 4),
        "directional_coverage_ratio": round(directional_coverage, 4),
        "integrate_file_ratio": round(integrate_ratio, 4),
        "prod_symbol_count": prod_symbol_count,
        "core_bridge_count": core_bridge_count,
        "triad_count": triad_count,
        "partial_triad_count": partial_count,
        "active_direction_count": active_directions,
        "direction_count": len(directions),
        "integrate_file_count": len(integrate_files),
        "prod_file_count": len(prod_files),
    }


def _load_history() -> List[Dict[str, object]]:
    if not HISTORY_PATH.exists():
        return []
    try:
        loaded = json.loads(_read(HISTORY_PATH))
    except json.JSONDecodeError:
        return []
    if not isinstance(loaded, list):
        return []
    return [row for row in loaded if isinstance(row, dict)]


def _update_history(generated_at: str, metrics: Dict[str, object]) -> Tuple[List[Dict[str, object]], Optional[Dict[str, object]]]:
    history = _load_history()
    prev = history[-1] if history else None

    history.append(
        {
            "generated_at": generated_at,
            "isomorphism_score": _as_float(metrics.get("isomorphism_score")),
            "core_bridge_ratio": _as_float(metrics.get("core_bridge_ratio")),
            "triad_completion_ratio": _as_float(metrics.get("triad_completion_ratio")),
            "directional_coverage_ratio": _as_float(metrics.get("directional_coverage_ratio")),
            "integrate_file_count": _as_int(metrics.get("integrate_file_count")),
            "triad_count": _as_int(metrics.get("triad_count")),
            "partial_triad_count": _as_int(metrics.get("partial_triad_count")),
            "prod_symbol_count": _as_int(metrics.get("prod_symbol_count")),
        }
    )

    history = history[-120:]
    HISTORY_PATH.parent.mkdir(parents=True, exist_ok=True)
    HISTORY_PATH.write_text(json.dumps(history, indent=2), encoding="utf-8")
    return history, prev


def _history_delta(current: Dict[str, object], prev: Optional[Dict[str, object]]) -> Dict[str, object]:
    if not prev:
        return {
            "has_previous": False,
            "score_delta": 0.0,
            "triad_delta": 0,
            "partial_triad_delta": 0,
            "integrate_file_delta": 0,
            "core_bridge_ratio_delta": 0.0,
        }
    return {
        "has_previous": True,
        "score_delta": round(_as_float(current.get("isomorphism_score")) - _as_float(prev.get("isomorphism_score")), 2),
        "triad_delta": _as_int(current.get("triad_count")) - _as_int(prev.get("triad_count")),
        "partial_triad_delta": _as_int(current.get("partial_triad_count")) - _as_int(prev.get("partial_triad_count")),
        "integrate_file_delta": _as_int(current.get("integrate_file_count")) - _as_int(prev.get("integrate_file_count")),
        "core_bridge_ratio_delta": round(
            _as_float(current.get("core_bridge_ratio")) - _as_float(prev.get("core_bridge_ratio")), 4
        ),
    }


def _parse_inquisitor_report(report_path: Path) -> Dict[str, object]:
    if not report_path.exists():
        return {
            "report_found": False,
            "scanned_files": 0,
            "high": 0,
            "medium": 0,
            "low": 0,
            "top_rules": [],
        }

    text = _read(report_path)
    scanned_match = re.search(r"Scanned:\s*(\d+)\s+Coq files", text)
    high_match = re.search(r"-\s*HIGH:\s*(\d+)", text)
    medium_match = re.search(r"-\s*MEDIUM:\s*(\d+)", text)
    low_match = re.search(r"-\s*LOW:\s*(\d+)", text)

    rule_hits = Counter(re.findall(r"\*\*([A-Z0-9_]+)\*\*", text))
    top_rules = [{"rule": rule, "count": count} for rule, count in rule_hits.most_common(20)]

    return {
        "report_found": True,
        "scanned_files": _as_int(scanned_match.group(1) if scanned_match else 0),
        "high": _as_int(high_match.group(1) if high_match else 0),
        "medium": _as_int(medium_match.group(1) if medium_match else 0),
        "low": _as_int(low_match.group(1) if low_match else 0),
        "top_rules": top_rules,
    }


def _run_inquisitor() -> Dict[str, object]:
    """Run Inquisitor proof analyzer with 120 second timeout."""
    report_path = REPO_ROOT / "INQUISITOR_REPORT.md"
    cmd = ["python3", "scripts/inquisitor.py", "--report", "INQUISITOR_REPORT.md"]
    timeout_sec = int(os.environ.get("INQUISITOR_TIMEOUT", "120"))  # 120s timeout to allow full Coq compilation
    
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            check=False,
            timeout=timeout_sec,
        )
    except subprocess.TimeoutExpired:
        return {
            "ran": True,
            "timed_out": True,
            "returncode": 124,
            "status": "TIMEOUT",
            "strict_pass": False,
            "report": _parse_inquisitor_report(report_path),
            "stdout_tail": "",
            "stderr_tail": f"Inquisitor timed out after {timeout_sec} seconds.",
            "command": " ".join(cmd),
            "report_path": _rel(report_path),
        }
    except OSError as exc:
        return {
            "ran": False,
            "timed_out": False,
            "returncode": 127,
            "status": "ERROR",
            "strict_pass": False,
            "report": _parse_inquisitor_report(report_path),
            "stdout_tail": "",
            "stderr_tail": str(exc),
            "command": " ".join(cmd),
            "report_path": _rel(report_path),
        }

    parsed = _parse_inquisitor_report(report_path)
    high = _as_int(parsed.get("high"))
    medium = _as_int(parsed.get("medium"))
    strict_pass = proc.returncode == 0 and high == 0 and medium == 0
    status = "PASS" if strict_pass else "FAIL"

    return {
        "ran": True,
        "timed_out": False,
        "returncode": proc.returncode,
        "status": status,
        "strict_pass": strict_pass,
        "report": parsed,
        "stdout_tail": "\n".join(proc.stdout.splitlines()[-40:]),
        "stderr_tail": "\n".join(proc.stderr.splitlines()[-40:]),
        "command": " ".join(cmd),
        "report_path": _rel(report_path),
    }


def _compute_proof_quality_metrics(inquisitor_result: Dict[str, object]) -> Dict[str, object]:
    report = inquisitor_result.get("report")
    if not isinstance(report, dict):
        report = {}
    scanned = max(_as_int(report.get("scanned_files")), 1)
    high = _as_int(report.get("high"))
    medium = _as_int(report.get("medium"))
    low = _as_int(report.get("low"))

    weighted_penalty = (1.0 * high) + (0.35 * medium) + (0.1 * low)
    raw_accuracy = max(0.0, min(100.0, (1.0 - (weighted_penalty / scanned)) * 100.0))

    if _as_int(inquisitor_result.get("returncode")) == 0 and high == 0 and medium == 0:
        gate_rating = "PASS"
    else:
        gate_rating = "FAIL"

    if raw_accuracy >= 97.0:
        grade = "A+"
    elif raw_accuracy >= 93.0:
        grade = "A"
    elif raw_accuracy >= 85.0:
        grade = "B"
    elif raw_accuracy >= 70.0:
        grade = "C"
    else:
        grade = "D"

    return {
        "proof_accuracy": round(raw_accuracy, 2),
        "proof_quality_grade": grade,
        "gate_rating": gate_rating,
        "high": high,
        "medium": medium,
        "low": low,
        "scanned_files": _as_int(report.get("scanned_files")),
        "weighted_penalty": round(weighted_penalty, 3),
        "strict_pass": bool(inquisitor_result.get("strict_pass", False)),
    }


# ---------------------------------------------------------------------------
# Real-toolchain gate functions
# ---------------------------------------------------------------------------

def _run_coq_compile_gate() -> Dict[str, object]:
    """Run ``make -C coq`` and report compile pass/fail and .vo coverage."""
    coq_dir = str(REPO_ROOT / "coq")
    try:
        result = subprocess.run(
            ["make", "-j4"],
            cwd=coq_dir,
            capture_output=True,
            text=True,
            check=False,
            timeout=3600,
        )
    except FileNotFoundError:
        return {"ran": False, "pass": False, "error": "make not found"}
    except subprocess.TimeoutExpired:
        return {"ran": True, "pass": False, "error": "make -C coq timed out"}

    # Count .v files vs .vo files to get compile ratio
    coq_path = REPO_ROOT / "coq"
    v_files = [f for f in coq_path.rglob("*.v") if "patches" not in f.parts]
    vo_files = [f for f in coq_path.rglob("*.vo") if "patches" not in f.parts]
    total_v = len(v_files)
    total_vo = len(vo_files)
    compile_ratio = (total_vo / total_v) if total_v else 0.0

    # Scan sources for any Admitted. (gate integrity check)
    admitted_count = 0
    for vf in v_files:
        txt = vf.read_text(encoding="utf-8", errors="replace")
        admitted_count += txt.count("Admitted.")

    passed = result.returncode == 0 and admitted_count == 0
    return {
        "ran": True,
        "pass": passed,
        "returncode": result.returncode,
        "stderr_tail": result.stderr[-500:] if result.stderr else "",
        "total_v_files": total_v,
        "total_vo_files": total_vo,
        "compile_ratio": round(compile_ratio, 4),
        "admitted_count": admitted_count,
    }


def _run_extraction_freshness_gate() -> Dict[str, object]:
    """Verify extraction artefacts are present, non-empty, and export the right symbols."""
    build_dir = REPO_ROOT / "build"
    coq_dir = REPO_ROOT / "coq"

    pairs = [
        (coq_dir / "Extraction.v",        build_dir / "thiele_core.ml"),
        (coq_dir / "MinimalExtraction.v", build_dir / "thiele_core_minimal.ml"),
    ]
    required_symbols = ["vm_instruction", "vm_apply", "vMState"]

    checks: Dict[str, object] = {}
    all_pass = True
    for v_src, ml_out in pairs:
        name = v_src.name
        if not ml_out.exists():
            checks[name] = {"exists": False, "nonempty": False, "symbols": False}
            all_pass = False
            continue
        content = ml_out.read_text(encoding="utf-8", errors="replace")
        nonempty = len(content.strip()) > 0
        # Check symbol presence
        missing_syms = [s for s in required_symbols if s not in content]
        symbols_ok = not missing_syms
        # Check staleness by comparing mtime (skip if mtimes identical — fresh clone)
        fresh = True
        if v_src.exists():
            ml_mtime = ml_out.stat().st_mtime
            v_mtime = v_src.stat().st_mtime
            # Only flag if there's a meaningful difference (>1s)
            if ml_mtime < v_mtime - 1.0:
                fresh = False
        ok = nonempty and symbols_ok and fresh
        checks[name] = {
            "exists": True,
            "nonempty": nonempty,
            "symbols_ok": symbols_ok,
            "missing_symbols": missing_syms,
            "fresh": fresh,
            "pass": ok,
        }
        if not ok:
            all_pass = False

    return {
        "ran": True,
        "pass": all_pass,
        "files": checks,
    }


def _run_rtl_synthesis_gate() -> Dict[str, object]:
    """Run Yosys lite synthesis and report pass/fail, module count, and cell count."""
    rtl_dir = REPO_ROOT / "thielecpu" / "hardware" / "rtl"
    synth_script = rtl_dir / "synth_lite.ys"
    unified_v = rtl_dir / "thiele_cpu_unified.v"

    if not shutil.which("yosys"):
        return {"ran": False, "pass": False, "error": "yosys not found on PATH"}
    if not unified_v.exists():
        return {"ran": False, "pass": False, "error": f"RTL source not found: {unified_v}"}
    if not synth_script.exists():
        return {"ran": False, "pass": False, "error": f"synth_lite.ys not found: {synth_script}"}

    try:
        result = subprocess.run(
            ["yosys", "-s", str(synth_script)],
            cwd=str(rtl_dir),
            capture_output=True,
            text=True,
            check=False,
            timeout=300,
        )
    except FileNotFoundError:
        return {"ran": False, "pass": False, "error": "yosys binary not found"}
    except subprocess.TimeoutExpired:
        return {"ran": True, "pass": False, "error": "yosys timed out after 300s"}

    stdout = result.stdout or ""
    import re as _re
    cell_match = _re.search(r"Number of cells:\s+(\d+)", stdout)
    cell_count = int(cell_match.group(1)) if cell_match else 0
    module_match = _re.findall(r"^===\s+([A-Za-z_]\w*)\s+===$", stdout, _re.MULTILINE)
    top_present = "thiele_cpu" in module_match

    passed = result.returncode == 0 and cell_count > 0 and top_present
    return {
        "ran": True,
        "pass": passed,
        "mode": "full_synthesis",
        "returncode": result.returncode,
        "cell_count": cell_count,
        "top_module_present": top_present,
        "modules_found": module_match[:10],
        "stderr_tail": result.stderr[-400:] if result.stderr else "",
    }


def _run_cosim_gate() -> Dict[str, object]:
    """Run the Verilog co-simulation testbench under iverilog/vvp."""
    rtl_dir = REPO_ROOT / "thielecpu" / "hardware" / "rtl"
    tb_dir = REPO_ROOT / "thielecpu" / "hardware" / "testbench"
    unified_v = rtl_dir / "thiele_cpu_unified.v"

    if not shutil.which("iverilog"):
        return {"ran": False, "pass": False, "error": "iverilog not found"}
    if not unified_v.exists():
        return {"ran": False, "pass": False, "error": f"{unified_v} not found"}

    tb_files = list(tb_dir.glob("*.v")) if tb_dir.exists() else []
    if not tb_files:
        return {"ran": False, "pass": False, "error": "no testbench .v files found"}

    tb_main = next((f for f in tb_files if "thiele_cpu_tb" in f.name), tb_files[0])

    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        sim_bin = str(Path(tmp) / "sim_out")
        try:
            compile_result = subprocess.run(
                ["iverilog", "-g2012", "-DSIMULATION",
                 "-o", sim_bin, str(tb_main), str(unified_v)],
                cwd=str(rtl_dir),
                capture_output=True, text=True, check=False, timeout=120,
            )
        except subprocess.TimeoutExpired:
            return {"ran": True, "pass": False, "error": "iverilog timed out"}

        if compile_result.returncode != 0:
            return {
                "ran": True, "pass": False,
                "stage": "compile",
                "stderr_tail": compile_result.stderr[-400:],
            }

        try:
            run_result = subprocess.run(
                ["vvp", sim_bin],
                cwd=str(rtl_dir),
                capture_output=True, text=True, check=False, timeout=60,
            )
        except subprocess.TimeoutExpired:
            return {"ran": True, "pass": False, "error": "vvp timed out"}

        output = run_result.stdout + run_result.stderr
        has_fail = "FAILED" in output.upper() and "0 FAILED" not in output.upper()
        passed = run_result.returncode == 0 and not has_fail
        return {
            "ran": True,
            "pass": passed,
            "returncode": run_result.returncode,
            "has_fail_marker": has_fail,
            "stdout_tail": run_result.stdout[-400:],
        }


def _compute_test_verification_metrics(
    symbols: List[Symbol],
    edges: List[Edge],
    file_metrics: List[Dict[str, object]],
) -> Tuple[Dict[str, object], List[Dict[str, object]]]:
    sym_by_id = {s.id: s for s in symbols}
    prod_symbol_ids = {s.id for s in symbols if s.layer in PROD_LAYERS}
    test_symbols = [s for s in symbols if s.layer in {"test", "rtl_tb"}]

    covered_prod_symbol_ids: Set[str] = set()
    test_file_edge_count: DefaultDict[str, int] = defaultdict(int)
    test_file_prod_files: DefaultDict[str, Set[str]] = defaultdict(set)
    test_file_prod_symbols: DefaultDict[str, Set[str]] = defaultdict(set)

    for edge in edges:
        src = sym_by_id.get(edge.src_id)
        dst = sym_by_id.get(edge.dst_id)
        if not src or not dst:
            continue
        if src.layer in {"test", "rtl_tb"} and dst.layer in PROD_LAYERS:
            covered_prod_symbol_ids.add(dst.id)
            test_file_edge_count[src.file] += 1
            test_file_prod_files[src.file].add(dst.file)
            test_file_prod_symbols[src.file].add(dst.id)

    prod_files = [r for r in file_metrics if str(r.get("layer")) in PROD_LAYERS]
    covered_prod_files = set()
    for files in test_file_prod_files.values():
        covered_prod_files.update(files)
    prod_file_set = {str(r.get("file")) for r in prod_files}
    uncovered_prod_files = sorted(prod_file_set - covered_prod_files)

    test_rows: List[Dict[str, object]] = []
    test_files = sorted({s.file for s in test_symbols})
    for tf in test_files:
        layer = "test"
        syms = [s for s in test_symbols if s.file == tf]
        if any(s.layer == "rtl_tb" for s in syms):
            layer = "rtl_tb"
        edges_count = test_file_edge_count.get(tf, 0)
        covered_files_count = len(test_file_prod_files.get(tf, set()))
        covered_symbols_count = len(test_file_prod_symbols.get(tf, set()))
        status = "covered" if edges_count > 0 else "isolated"
        notes = ""
        if status == "isolated":
            notes = "No discovered edges from this test file to production symbols"
        test_rows.append(
            {
                "test_file": tf,
                "layer": layer,
                "symbol_count": len(syms),
                "coverage_edges": edges_count,
                "covered_prod_files": covered_files_count,
                "covered_prod_symbols": covered_symbols_count,
                "status": status,
                "notes": notes,
            }
        )

    test_rows.sort(key=lambda r: (str(r.get("status")), _as_int(r.get("coverage_edges")), str(r.get("test_file"))))

    prod_symbol_coverage_ratio = (
        len(covered_prod_symbol_ids) / len(prod_symbol_ids) if prod_symbol_ids else 0.0
    )
    prod_file_coverage_ratio = (
        len(covered_prod_files & prod_file_set) / len(prod_file_set) if prod_file_set else 0.0
    )
    isolated_tests = [r for r in test_rows if str(r.get("status")) == "isolated"]

    strict_pass = (
        prod_symbol_coverage_ratio >= 0.60
        and prod_file_coverage_ratio >= 0.75
        and len(isolated_tests) == 0
    )

    metrics: Dict[str, object] = {
        "test_gate": "PASS" if strict_pass else "FAIL",
        "strict_pass": strict_pass,
        "test_file_count": len(test_files),
        "isolated_test_file_count": len(isolated_tests),
        "prod_symbol_coverage_ratio": round(prod_symbol_coverage_ratio, 4),
        "prod_file_coverage_ratio": round(prod_file_coverage_ratio, 4),
        "covered_prod_symbol_count": len(covered_prod_symbol_ids),
        "prod_symbol_count": len(prod_symbol_ids),
        "covered_prod_file_count": len(covered_prod_files & prod_file_set),
        "prod_file_count": len(prod_file_set),
        "uncovered_prod_files_top": uncovered_prod_files[:30],
    }
    return metrics, test_rows


def _build_priority_plan(
    iso_metrics: Dict[str, object],
    file_metrics: List[Dict[str, object]],
    partial_triads: List[Dict[str, object]],
    test_metrics: Dict[str, object],
    limit: int = 10,
) -> List[Dict[str, object]]:
    triad_count = _as_int(iso_metrics.get("triad_count"))
    partial_count = max(_as_int(iso_metrics.get("partial_triad_count")), 1)
    triad_gain = round(35.0 / (triad_count + partial_count), 2)

    opportunities: List[Dict[str, object]] = []

    integrate_rows = sorted(
        [r for r in file_metrics if str(r.get("action")) == "integrate" and str(r.get("layer")) in PROD_LAYERS],
        key=lambda r: (-(_as_int(r.get("orphan")) + _as_int(r.get("island"))), _as_float(r.get("connectivity_ratio"))),
    )
    for row in integrate_rows[:10]:
        pressure = _as_int(row.get("orphan")) + _as_int(row.get("island"))
        gain = round(min(3.0, 0.35 + 0.06 * pressure), 2)
        opportunities.append(
            {
                "type": "integrate_file",
                "priority": 0,
                "task": f"Integrate {row.get('file')} ({row.get('layer')})",
                "details": f"orphan={row.get('orphan')} island={row.get('island')} connectivity={_as_float(row.get('connectivity_ratio')):.0%}",
                "estimated_score_gain": gain,
            }
        )

    for gap in partial_triads[:18]:
        opportunities.append(
            {
                "type": "close_partial_triad",
                "priority": 1,
                "task": f"Complete triad '{gap.get('norm')}'",
                "details": f"missing={gap.get('missing_layers')} present={gap.get('present_layers')}",
                "estimated_score_gain": triad_gain,
            }
        )

    uncovered_raw = test_metrics.get("uncovered_prod_files_top")
    uncovered_files: List[str] = []
    if isinstance(uncovered_raw, list):
        uncovered_files = [str(item) for item in uncovered_raw]

    for file_path in uncovered_files[:12]:
        opportunities.append(
            {
                "type": "test_coverage_gap",
                "priority": 2,
                "task": f"Add strict tests covering {file_path}",
                "details": "No discovered test coverage edges to this production file",
                "estimated_score_gain": 0.8,
            }
        )

    ranked = sorted(
        opportunities,
        key=lambda row: (
            _as_int(row.get("priority")),       # integration first, triads second, tests third
            -_as_float(row.get("estimated_score_gain")),
            str(row.get("task")),
        ),
    )
    return ranked[:limit]


def _fragmented_correctness_flags(
    iso_metrics: Dict[str, object],
    proof_metrics: Dict[str, object],
    test_metrics: Dict[str, object],
    toolchain_gates: Optional[Dict[str, Dict[str, object]]] = None,
) -> List[str]:
    flags: List[str] = []
    proof_pass = bool(proof_metrics.get("strict_pass", False))
    test_pass = bool(test_metrics.get("strict_pass", False))
    bridge_ratio = _as_float(iso_metrics.get("core_bridge_ratio"))
    triad_ratio = _as_float(iso_metrics.get("triad_completion_ratio"))
    
    # Check toolchain gates if provided
    if toolchain_gates:
        coq_pass = toolchain_gates.get("coq_compile", {}).get("pass", False)
        extraction_pass = toolchain_gates.get("extraction_freshness", {}).get("pass", False)
        rtl_pass = toolchain_gates.get("rtl_synthesis", {}).get("pass", False)
        cosim_pass = toolchain_gates.get("cosim", {}).get("pass", False)
        
        if proof_pass and not coq_pass:
            flags.append("Proof analysis PASS but Coq compile FAIL: possible proof bugs or build issues.")
        if coq_pass and not extraction_pass:
            flags.append("Coq compile PASS but extraction FAIL: stale or missing extracted OCaml/Python code.")
        if extraction_pass and not rtl_pass:
            flags.append("Extraction PASS but RTL synthesis FAIL: Verilog may not match extracted semantics.")
        if rtl_pass and not cosim_pass:
            flags.append("RTL synthesis PASS but co-simulation FAIL: testbench errors or runtime bugs.")

    if proof_pass and not test_pass:
        flags.append("Proof gate PASS but test gate FAIL: verified statements are not yet sufficiently exercised against runtime surfaces.")
    if proof_pass and bridge_ratio < 0.15:
        flags.append("Proof hygiene is high while bridge ratio is low: risk of decorative proofs disconnected from implementation layers.")
    if triad_ratio < 0.20:
        flags.append("Triad completion is low: most candidate concepts still lack full Coq↔Python↔RTL closure.")
    if _as_float(test_metrics.get("prod_symbol_coverage_ratio")) < 0.30:
        flags.append("Production symbol coverage by tests is below strict target; dynamic paths are under-verified.")

    if not flags:
        flags.append("No fragmented-correctness red flags detected under current thresholds.")
    return flags


def _compute_latex_coverage(symbols: List[Symbol], triads: List[Dict[str, object]]) -> Dict[str, object]:
    tex_roots = [REPO_ROOT / "thesis", REPO_ROOT / "papers"]
    tex_files = _iter_unique(
        p
        for root in tex_roots
        if root.exists()
        for p in root.rglob("*.tex")
        if p.is_file()
    )

    tex_text_parts: List[str] = []
    for path in tex_files:
        tex_text_parts.append(_read(path).lower())
    corpus = "\n".join(tex_text_parts)

    kernel_proof_names = sorted(
        {
            s.name
            for s in symbols
            if s.layer == "coq"
            and s.file.startswith("coq/kernel/")
            and _coq_kind_is_proof(s.kind)
            and len(s.name) >= 4
        }
    )

    kernel_hits = [name for name in kernel_proof_names if name.lower() in corpus]
    kernel_missing = [name for name in kernel_proof_names if name.lower() not in corpus]

    triad_norms = sorted({str(t.get("norm", "")).strip() for t in triads if str(t.get("norm", "")).strip()})
    triad_hits = [norm for norm in triad_norms if norm.lower() in corpus]

    kernel_ratio = (len(kernel_hits) / len(kernel_proof_names)) if kernel_proof_names else 0.0
    triad_ratio = (len(triad_hits) / len(triad_norms)) if triad_norms else 0.0

    return {
        "tex_file_count": len(tex_files),
        "kernel_proof_symbol_count": len(kernel_proof_names),
        "kernel_proof_symbol_mentioned_count": len(kernel_hits),
        "kernel_proof_latex_coverage_ratio": round(kernel_ratio, 4),
        "kernel_proof_missing_top": kernel_missing[:40],
        "triad_norm_count": len(triad_norms),
        "triad_norm_mentioned_count": len(triad_hits),
        "triad_norm_latex_coverage_ratio": round(triad_ratio, 4),
    }


def _compute_proof_documentation_coverage(symbols: List[Symbol]) -> Tuple[Dict[str, object], List[Dict[str, object]]]:
    """Per-proof documentation quality: every theorem/lemma should have a preceding (** doc comment."""
    DOC_COMMENT_BEFORE_PROOF_RE = re.compile(
        r"\(\*\*[^*].*?\*\)"
        r"\s*\n"
        r"\s*(?:Local\s+|Global\s+|#\[.*?\]\s*)*"
        r"(?:Theorem|Lemma|Corollary|Proposition|Fact|Remark|Conjecture)\s+",
        re.DOTALL,
    )

    by_file: DefaultDict[str, List[Symbol]] = defaultdict(list)
    for s in symbols:
        if s.layer == "coq" and _coq_kind_is_proof(s.kind):
            by_file[s.file].append(s)

    rows: List[Dict[str, object]] = []
    total_proofs = 0
    documented_proofs = 0

    for file_path, file_syms in sorted(by_file.items()):
        abs_path = REPO_ROOT / file_path
        text = _read(abs_path)
        has_comment_blocks = "(*" in text and "*)" in text
        dir_path = abs_path.parent
        readme_exists = any((dir_path / name).exists() for name in ("README.md", "README", "readme.md", "readme"))

        # Count proofs in this file that have a preceding (** doc comment
        file_proof_count = len(file_syms)
        documented_in_file = len(DOC_COMMENT_BEFORE_PROOF_RE.findall(text))
        doc_ratio = (documented_in_file / file_proof_count) if file_proof_count else 0.0

        total_proofs += file_proof_count
        documented_proofs += min(documented_in_file, file_proof_count)

        status = "documented" if (doc_ratio >= 0.9 and readme_exists) else "needs_docs"
        rows.append(
            {
                "proof_file": file_path,
                "proof_count": file_proof_count,
                "documented_proof_count": min(documented_in_file, file_proof_count),
                "per_proof_doc_ratio": round(doc_ratio, 4),
                "has_comment_blocks": has_comment_blocks,
                "has_local_readme": readme_exists,
                "status": status,
            }
        )

    rows.sort(key=lambda r: (_as_float(r.get("per_proof_doc_ratio")), str(r.get("proof_file"))))

    total_files = len(rows)
    with_readme = sum(1 for r in rows if bool(r.get("has_local_readme")))
    with_comments = sum(1 for r in rows if bool(r.get("has_comment_blocks")))
    documented = sum(1 for r in rows if str(r.get("status")) == "documented")
    fully_documented_files = sum(1 for r in rows if _as_float(r.get("per_proof_doc_ratio")) >= 0.9)

    per_proof_doc_ratio = (documented_proofs / total_proofs) if total_proofs else 0.0

    metrics: Dict[str, object] = {
        "proof_file_count": total_files,
        "total_proof_count": total_proofs,
        "documented_proof_count": documented_proofs,
        "per_proof_doc_ratio": round(per_proof_doc_ratio, 4),
        "fully_documented_file_count": fully_documented_files,
        "fully_documented_file_ratio": round((fully_documented_files / total_files), 4) if total_files else 0.0,
        "proof_files_with_readme_count": with_readme,
        "proof_files_with_comment_blocks_count": with_comments,
        "proof_files_documented_count": documented,
        "proof_files_with_readme_ratio": round((with_readme / total_files), 4) if total_files else 0.0,
        "proof_files_with_comment_ratio": round((with_comments / total_files), 4) if total_files else 0.0,
        "proof_files_documented_ratio": round((documented / total_files), 4) if total_files else 0.0,
        "missing_readme_proof_files_top": [str(r.get("proof_file")) for r in rows if not bool(r.get("has_local_readme"))][:40],
        "underdocumented_proof_files_top": [
            str(r.get("proof_file"))
            for r in rows
            if _as_float(r.get("per_proof_doc_ratio")) < 0.9
        ][:40],
    }
    return metrics, rows


def _compute_definition_of_done(
    iso_metrics: Dict[str, object],
    proof_metrics: Dict[str, object],
    test_metrics: Dict[str, object],
    latex_metrics: Dict[str, object],
    proof_doc_metrics: Dict[str, object],
    toolchain_gates: Optional[Dict[str, object]] = None,
) -> Dict[str, object]:
    checks: List[Dict[str, object]] = []

    def add_check(name: str, actual: float, comparator: str, threshold: float) -> None:
        if comparator == ">=":
            passed = actual >= threshold
        else:
            passed = actual <= threshold
        checks.append(
            {
                "name": name,
                "actual": round(actual, 4),
                "comparator": comparator,
                "threshold": threshold,
                "passed": passed,
            }
        )

    add_check("isomorphism_score", _as_float(iso_metrics.get("isomorphism_score")), ">=", DOD_THRESHOLDS["min_isomorphism_score"])
    add_check("triad_completion_ratio", _as_float(iso_metrics.get("triad_completion_ratio")), ">=", DOD_THRESHOLDS["min_triad_completion_ratio"])
    add_check("core_bridge_ratio", _as_float(iso_metrics.get("core_bridge_ratio")), ">=", DOD_THRESHOLDS["min_core_bridge_ratio"])
    add_check("test_prod_symbol_coverage_ratio", _as_float(test_metrics.get("prod_symbol_coverage_ratio")), ">=", DOD_THRESHOLDS["min_test_prod_symbol_coverage_ratio"])
    add_check("test_prod_file_coverage_ratio", _as_float(test_metrics.get("prod_file_coverage_ratio")), ">=", DOD_THRESHOLDS["min_test_prod_file_coverage_ratio"])
    add_check("isolated_test_files", float(_as_int(test_metrics.get("isolated_test_file_count"))), "<=", DOD_THRESHOLDS["max_isolated_test_files"])
    add_check("per_proof_doc_ratio", _as_float(proof_doc_metrics.get("per_proof_doc_ratio")), ">=", DOD_THRESHOLDS["min_per_proof_doc_ratio"])
    add_check("proof_files_with_readme_ratio", _as_float(proof_doc_metrics.get("proof_files_with_readme_ratio")), ">=", DOD_THRESHOLDS["min_proof_files_with_readme_ratio"])
    add_check("kernel_proof_latex_coverage_ratio", _as_float(latex_metrics.get("kernel_proof_latex_coverage_ratio")), ">=", DOD_THRESHOLDS["min_kernel_proof_latex_coverage_ratio"])

    # Real toolchain gates
    if toolchain_gates:
        coq_gate = toolchain_gates.get("coq_compile") or {}
        ext_gate = toolchain_gates.get("extraction_freshness") or {}
        rtl_gate = toolchain_gates.get("rtl_synthesis") or {}
        if coq_gate.get("ran", False):
            add_check("coq_compile_pass", 1.0 if bool(coq_gate.get("pass")) else 0.0, ">=", DOD_THRESHOLDS["min_coq_compile_pass"])
        if ext_gate.get("ran", False):
            add_check("extraction_freshness_pass", 1.0 if bool(ext_gate.get("pass")) else 0.0, ">=", DOD_THRESHOLDS["min_extraction_freshness_pass"])
        if rtl_gate.get("ran", False):
            add_check("rtl_synthesis_pass", 1.0 if bool(rtl_gate.get("pass")) else 0.0, ">=", DOD_THRESHOLDS["min_rtl_synthesis_pass"])

    inquisitor_pass = bool(proof_metrics.get("strict_pass", False))
    checks.append(
        {
            "name": "inquisitor_strict_pass",
            "actual": 1.0 if inquisitor_pass else 0.0,
            "comparator": "==",
            "threshold": 1.0,
            "passed": inquisitor_pass,
        }
    )

    completed = all(bool(c.get("passed")) for c in checks)
    unmet = [c for c in checks if not bool(c.get("passed"))]
    return {
        "status": "COMPLETED" if completed else "NOT_COMPLETED",
        "completed": completed,
        "checks": checks,
        "unmet_check_count": len(unmet),
        "unmet_checks": unmet,
    }


def _mermaid_layer_flow(symbols: List[Symbol], edges: List[Edge]) -> str:
    layer_counts = Counter(s.layer for s in symbols)
    matrix = _cross_layer_matrix(symbols, edges)
    lines = [
        "flowchart LR",
        f"  C[\"Coq\\n{layer_counts['coq']} symbols\"]",
        f"  P[\"Python/VM\\n{layer_counts['python']} symbols\"]",
        f"  R[\"RTL/Verilog\\n{layer_counts['rtl']} symbols\"]",
        f"  T[\"Tests/TB\\n{layer_counts['test'] + layer_counts['rtl_tb']} symbols\"]",
        "  C -->|" + str(matrix.get(("coq", "python"), 0)) + "| P",
        "  P -->|" + str(matrix.get(("python", "coq"), 0)) + "| C",
        "  C -->|" + str(matrix.get(("coq", "rtl"), 0)) + "| R",
        "  R -->|" + str(matrix.get(("rtl", "coq"), 0)) + "| C",
        "  P -->|" + str(matrix.get(("python", "rtl"), 0)) + "| R",
        "  R -->|" + str(matrix.get(("rtl", "python"), 0)) + "| P",
        "  T -. coverage .-> C",
        "  T -. coverage .-> P",
        "  T -. coverage .-> R",
    ]
    return "\n".join(lines)


def _mermaid_top_links(symbols: List[Symbol], edges: List[Edge], limit: int = 22) -> str:
    links = _top_cross_file_links(symbols, edges, limit=limit)
    if not links:
        return "flowchart LR\n  A[\"No cross-file production links found\"]"

    node_map: Dict[str, str] = {}
    lines = ["flowchart LR"]

    def node_id(path: str) -> str:
        if path not in node_map:
            node_map[path] = "N" + _safe_id(str(len(node_map) + 1))
        return node_map[path]

    for src, dst, weight in links:
        sid = node_id(src)
        did = node_id(dst)
        lines.append(f"  {sid}[\"{src}\"]")
        lines.append(f"  {did}[\"{dst}\"]")
        lines.append(f"  {sid} -->|{weight}| {did}")

    return "\n".join(lines)


def _mermaid_triads(triads: List[Dict[str, object]], limit: int = 18) -> str:
    if not triads:
        return "flowchart LR\n  A[\"No 3-layer triads found\"]"

    lines = ["flowchart TB", "  C[\"Coq\"]", "  P[\"Python\"]", "  R[\"RTL\"]"]
    for idx, triad in enumerate(triads[:limit], start=1):
        tid = f"T{idx}"
        lbl = str(triad["norm"]).replace('"', "")
        lines.append(f"  {tid}[\"{lbl}\"]")
        lines.append(f"  C --> {tid}")
        lines.append(f"  {tid} --> P")
        lines.append(f"  {tid} --> R")
    return "\n".join(lines)


def _mermaid_class_breakdown(cls: Dict[str, str]) -> str:
    counts = Counter(cls.values())
    lines = [
        "pie title Symbol Classification Breakdown",
        f'  "core" : {counts["core"]}',
        f'  "bridge" : {counts["bridge"]}',
        f'  "island" : {counts["island"]}',
        f'  "orphan" : {counts["orphan"]}',
        f'  "duplicate" : {counts["duplicate"]}',
        f'  "test_only" : {counts["test_only"]}',
        f'  "stale" : {counts["stale"]}',
    ]
    return "\n".join(lines)


def _mermaid_action_breakdown(file_metrics: List[Dict[str, object]]) -> str:
    counts = Counter(str(r.get("action", "unknown")) for r in file_metrics)
    lines = [
        "pie title File Action Breakdown",
        f'  "keep" : {counts["keep"]}',
        f'  "integrate" : {counts["integrate"]}',
        f'  "deduplicate" : {counts["deduplicate"]}',
        f'  "archive" : {counts["archive"]}',
        f'  "remove_safe" : {counts["remove_safe"]}',
    ]
    return "\n".join(lines)


def _mermaid_python_rtl_focus(symbols: List[Symbol], edges: List[Edge], limit: int = 18) -> str:
    sym_by_id = {s.id: s for s in symbols}
    pair_count: DefaultDict[Tuple[str, str], int] = defaultdict(int)

    for edge in edges:
        src = sym_by_id[edge.src_id]
        dst = sym_by_id[edge.dst_id]
        if src.file == dst.file:
            continue
        if src.layer == "python" and dst.layer == "rtl":
            pair_count[(src.file, dst.file)] += 1
        elif src.layer == "rtl" and dst.layer == "python":
            pair_count[(dst.file, src.file)] += 1

    ranked = sorted(pair_count.items(), key=lambda kv: (-kv[1], kv[0][0], kv[0][1]))[:limit]
    if not ranked:
        return "flowchart LR\n  A[\"No Python↔RTL cross links found\"]"

    node_map: Dict[str, str] = {}
    lines = ["flowchart LR"]

    def nid(path: str) -> str:
        if path not in node_map:
            node_map[path] = "X" + _safe_id(str(len(node_map) + 1))
        return node_map[path]

    for (py_file, rtl_file), weight in ranked:
        py_id = nid(py_file)
        rtl_id = nid(rtl_file)
        lines.append(f'  {py_id}["{py_file}"]')
        lines.append(f'  {rtl_id}["{rtl_file}"]')
        lines.append(f"  {py_id} -->|{weight}| {rtl_id}")

    return "\n".join(lines)


def _write_csv(path: Path, rows: Sequence[Mapping[str, object]], fieldnames: List[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow({k: row.get(k, "") for k in fieldnames})


def _read_csv_rows(path: Path) -> List[Dict[str, str]]:
    if not path.exists():
        return []
    with path.open("r", encoding="utf-8", newline="") as f:
        return list(csv.DictReader(f))


def _terminal_deep_analysis(bundle: Dict[str, List[str]]) -> None:
    summary_path = ATLAS_EXPORT_DIR / "atlas_summary.json"
    metrics_path = ATLAS_EXPORT_DIR / "atlas_file_metrics.csv"
    partial_path = ATLAS_EXPORT_DIR / "atlas_partial_triads.csv"
    inquisitor_path = ATLAS_EXPORT_DIR / "atlas_inquisitor_summary.json"

    summary: Dict[str, object] = {}
    if summary_path.exists():
        try:
            loaded = json.loads(_read(summary_path))
            if isinstance(loaded, dict):
                summary = loaded
        except json.JSONDecodeError:
            summary = {}

    file_rows = _read_csv_rows(metrics_path)
    partial_rows = _read_csv_rows(partial_path)

    inquisitor_payload: Dict[str, object] = {}
    if inquisitor_path.exists():
        try:
            loaded = json.loads(_read(inquisitor_path))
            if isinstance(loaded, dict):
                inquisitor_payload = loaded
        except json.JSONDecodeError:
            inquisitor_payload = {}

    iso = summary.get("isomorphism_metrics")
    if not isinstance(iso, dict):
        iso = {}
    trend = summary.get("trend_delta")
    if not isinstance(trend, dict):
        trend = {}
    proof = summary.get("proof_quality_metrics")
    if not isinstance(proof, dict):
        proof = {}
    test_metrics = summary.get("test_verification_metrics")
    if not isinstance(test_metrics, dict):
        test_metrics = {}
    priority_plan = summary.get("priority_plan")
    if not isinstance(priority_plan, list):
        priority_plan = []
    frag_flags = summary.get("fragmented_correctness_flags")
    if not isinstance(frag_flags, list):
        frag_flags = []
    latex_metrics = summary.get("latex_coverage_metrics")
    if not isinstance(latex_metrics, dict):
        latex_metrics = {}
    proof_doc_metrics = summary.get("proof_documentation_metrics")
    if not isinstance(proof_doc_metrics, dict):
        proof_doc_metrics = {}
    dod_status = summary.get("definition_of_done")
    if not isinstance(dod_status, dict):
        dod_status = {}

    integrate_rows = [r for r in file_rows if str(r.get("action")) == "integrate"]
    worst_integrate = sorted(
        integrate_rows,
        key=lambda r: (-(_as_int(r.get("orphan")) + _as_int(r.get("island"))), _as_float(r.get("connectivity_ratio"))),
    )

    missing_by_layer: Counter[str] = Counter()
    for row in partial_rows:
        missing = str(row.get("missing_layers", "")).strip()
        if not missing:
            continue
        for layer in missing.split(","):
            name = layer.strip()
            if name:
                missing_by_layer[name] += 1

    cross_map = summary.get("cross_layer_matrix")
    if not isinstance(cross_map, dict):
        cross_map = {}

    print("\n=== ATLAS DEEP ANALYSIS (POST-GENERATION) ===")
    print("This analysis is computed from generated files in artifacts/atlas/.")
    print("Proof accuracy below is Inquisitor proof-hygiene accuracy (not project-completion percent).")
    print("\n[1] SYSTEM STATUS")
    print(
        "  "
        f"Isomorphism score={_as_float(iso.get('isomorphism_score')):.2f} "
        f"(delta {_as_float(trend.get('score_delta')):+.2f}) | "
        f"Triads={_as_int(iso.get('triad_count'))} | "
        f"Partial-triads={_as_int(iso.get('partial_triad_count'))}"
    )
    print(
        "  "
        f"Proof gate={proof.get('gate_rating', 'FAIL')} | "
        f"Proof accuracy={_as_float(proof.get('proof_accuracy')):.2f}% | "
        f"HIGH/MEDIUM/LOW={_as_int(proof.get('high'))}/{_as_int(proof.get('medium'))}/{_as_int(proof.get('low'))}"
    )
    print(
        "  "
        f"Test gate={test_metrics.get('test_gate', 'FAIL')} | "
        f"Prod-symbol coverage={_as_float(test_metrics.get('prod_symbol_coverage_ratio')):.0%} | "
        f"Prod-file coverage={_as_float(test_metrics.get('prod_file_coverage_ratio')):.0%} | "
        f"Isolated tests={_as_int(test_metrics.get('isolated_test_file_count'))}"
    )
    print(
        "  "
        f"Core+Bridge ratio={_as_float(iso.get('core_bridge_ratio')):.0%} | "
        f"Triad completion={_as_float(iso.get('triad_completion_ratio')):.0%} | "
        f"Directional coverage={_as_int(iso.get('active_direction_count'))}/{_as_int(iso.get('direction_count'))}"
    )
    print(
        "  "
        f"Definition-of-Done={dod_status.get('status', 'NOT_COMPLETED')} | "
        f"Kernel-proof LaTeX coverage={_as_float(latex_metrics.get('kernel_proof_latex_coverage_ratio')):.0%} | "
        f"Proof-files with README={_as_float(proof_doc_metrics.get('proof_files_with_readme_ratio')):.0%}"
    )

    # Toolchain gates (new section)
    raw_tc = summary.get("toolchain_gates")
    if isinstance(raw_tc, dict) and raw_tc:
        gate_names = [
            ("coq_compile",          "Coq compile"),
            ("extraction_freshness", "Extraction"),
            ("rtl_synthesis",        "RTL synth"),
            ("cosim",                "Co-sim"),
        ]
        parts = []
        for key, label in gate_names:
            g = raw_tc.get(key) or {}
            if bool(g.get("ran")):
                status = "PASS" if bool(g.get("pass")) else "FAIL"
            else:
                status = "skip"
            parts.append(f"{label}={status}")
        print("  " + " | ".join(parts))

    print("\n[2] CRITICAL GAPS TO CLOSE")
    if worst_integrate:
        for row in worst_integrate[:8]:
            print(
                "  - "
                f"{row.get('file')} [{row.get('layer')}] "
                f"orphan={_as_int(row.get('orphan'))}, island={_as_int(row.get('island'))}, "
                f"connectivity={_as_float(row.get('connectivity_ratio')):.0%}"
            )
    else:
        print("  - No integrate backlog entries detected.")

    print("\n[3] PARTIAL TRIAD DEFICIT (MISSING LAYER COUNTS)")
    if missing_by_layer:
        for layer, count in missing_by_layer.most_common():
            print(f"  - missing {layer}: {count}")
    else:
        print("  - No partial triads detected.")

    print("\n[4] CROSS-LAYER DIRECTION HEALTH")
    for key in ["coq->python", "python->coq", "coq->rtl", "rtl->coq", "python->rtl", "rtl->python"]:
        print(f"  - {key}: {_as_int(cross_map.get(key))}")

    top_links = summary.get("top_cross_file_links")
    if isinstance(top_links, list):
        print("\n[5] STRONGEST CROSS-FILE LINKS")
        shown = 0
        for item in top_links[:10]:
            if not isinstance(item, dict):
                continue
            print(
                "  - "
                f"{item.get('src')} -> {item.get('dst')} "
                f"(weight {_as_int(item.get('weight'))})"
            )
            shown += 1
        if shown == 0:
            print("  - No cross-file links available.")

    iq = inquisitor_payload.get("inquisitor")
    if isinstance(iq, dict):
        report = iq.get("report")
        if isinstance(report, dict):
            rules = report.get("top_rules")
            if isinstance(rules, list):
                print("\n[6] INQUISITOR RULE PRESSURE")
                shown = 0
                for entry in rules[:8]:
                    if not isinstance(entry, dict):
                        continue
                    print(f"  - {entry.get('rule', 'UNKNOWN_RULE')}: {_as_int(entry.get('count'))}")
                    shown += 1
                if shown == 0:
                    print("  - No failing rule pressure (strict pass).")

    print("\n[7] ITERATIVE DESIGN GUIDANCE")
    print("  Phase A: eliminate integrate backlog files with highest orphan/island counts.")
    print("  Phase B: close partial triads by implementing missing layer contracts in priority order.")
    print("  Phase C: bind physics/domain Coq statements to kernel semantics via explicit bridge lemmas.")
    print("  Phase D: maintain inquisitor strict PASS while increasing triad completion ratio each run.")
    print("  Success criterion: rising isomorphism score + shrinking partial-triad and integrate backlogs.")

    print("\n[8] FRAGMENTED-CORRECTNESS DIAGNOSTICS")
    if frag_flags:
        for flag in frag_flags:
            print(f"  - {flag}")
    else:
        print("  - No diagnostics available.")

    print("\n[9] DEFINITION-OF-DONE GATE")
    checks = dod_status.get("checks")
    if isinstance(checks, list):
        for check in checks:
            if not isinstance(check, dict):
                continue
            print(
                "  - "
                f"{check.get('name')}: actual={check.get('actual')} "
                f"target {check.get('comparator')} {check.get('threshold')} "
                f"pass={check.get('passed')}"
            )

    print("\n[10] TOP CLOSURE TASKS (ESTIMATED IMPACT)")
    if priority_plan:
        for idx, item in enumerate(priority_plan[:10], start=1):
            if not isinstance(item, dict):
                continue
            print(
                "  "
                f"{idx:02d}. {item.get('task')} "
                f"[{item.get('type')}] gain~{_as_float(item.get('estimated_score_gain')):.2f} "
                f":: {item.get('details')}"
            )
    else:
        print("  - No priority plan items generated.")

    exported = bundle.get("exported", [])
    rendered = bundle.get("rendered_images", [])
    print("\n[11] GENERATED OUTPUTS")
    print(f"  - exported artifacts: {len(exported)}")
    print(f"  - rendered images: {len(rendered)}")
    print("=== END DEEP ANALYSIS ===\n")


def _clean_previous_outputs() -> None:
    if OUT_PATH.exists():
        OUT_PATH.unlink()

    if not ATLAS_EXPORT_DIR.exists():
        return

    for child in ATLAS_EXPORT_DIR.iterdir():
        if child.is_dir():
            shutil.rmtree(child, ignore_errors=True)
        else:
            try:
                child.unlink()
            except OSError:
                pass


def _try_render_mermaid(mmd_path: Path) -> List[str]:
    outputs: List[str] = []
    if shutil.which("mmdc") is None:
        return outputs

    svg_path = mmd_path.with_suffix(".svg")
    png_path = mmd_path.with_suffix(".png")

    subprocess.run(
        ["mmdc", "-i", str(mmd_path), "-o", str(svg_path), "--backgroundColor", "transparent"],
        check=False,
        capture_output=True,
        text=True,
    )
    if svg_path.exists():
        outputs.append(_rel(svg_path))

    subprocess.run(
        ["mmdc", "-i", str(mmd_path), "-o", str(png_path), "--backgroundColor", "transparent"],
        check=False,
        capture_output=True,
        text=True,
    )
    if png_path.exists():
        outputs.append(_rel(png_path))

    return outputs


def _try_render_matplotlib(
    symbols: List[Symbol],
    edges: List[Edge],
    cls: Dict[str, str],
    file_metrics: List[Dict[str, object]],
) -> List[str]:
    try:
        import matplotlib

        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except Exception:
        return []

    out_paths: List[str] = []

    layer_counts = Counter(s.layer for s in symbols)
    layers = ["coq", "python", "rtl", "rtl_tb", "test", "stale"]
    layer_values = [layer_counts.get(layer, 0) for layer in layers]
    fig, ax = plt.subplots(figsize=(10, 4))
    ax.bar(layers, layer_values)
    ax.set_title("Symbol Counts by Layer")
    ax.set_ylabel("symbols")
    fig.tight_layout()
    layer_plot = ATLAS_EXPORT_DIR / "layer_symbol_counts.png"
    fig.savefig(layer_plot, dpi=180)
    plt.close(fig)
    out_paths.append(_rel(layer_plot))

    class_counts = Counter(cls.values())
    class_labels = ["core", "bridge", "island", "orphan", "duplicate", "test_only", "stale"]
    class_values = [class_counts.get(label, 0) for label in class_labels]
    fig, ax = plt.subplots(figsize=(10, 4))
    ax.bar(class_labels, class_values)
    ax.set_title("Symbol Classification Breakdown")
    ax.set_ylabel("count")
    fig.tight_layout()
    class_plot = ATLAS_EXPORT_DIR / "symbol_class_breakdown.png"
    fig.savefig(class_plot, dpi=180)
    plt.close(fig)
    out_paths.append(_rel(class_plot))

    action_counts = Counter(str(r.get("action", "unknown")) for r in file_metrics)
    action_labels = ["keep", "integrate", "deduplicate", "archive", "remove_safe"]
    action_values = [action_counts.get(label, 0) for label in action_labels]
    fig, ax = plt.subplots(figsize=(10, 4))
    ax.bar(action_labels, action_values)
    ax.set_title("File Action Breakdown")
    ax.set_ylabel("files")
    fig.tight_layout()
    action_plot = ATLAS_EXPORT_DIR / "file_action_breakdown.png"
    fig.savefig(action_plot, dpi=180)
    plt.close(fig)
    out_paths.append(_rel(action_plot))

    matrix = _cross_layer_matrix(symbols, edges)
    axes_labels = ["coq", "python", "rtl"]
    data = [[matrix.get((src, dst), 0) for dst in axes_labels] for src in axes_labels]
    fig, ax = plt.subplots(figsize=(6, 5))
    im = ax.imshow(data)
    ax.set_xticks(range(len(axes_labels)), labels=axes_labels)
    ax.set_yticks(range(len(axes_labels)), labels=axes_labels)
    ax.set_title("Cross-Layer Edge Matrix")
    for i, row in enumerate(data):
        for j, val in enumerate(row):
            ax.text(j, i, str(val), ha="center", va="center")
    fig.colorbar(im, ax=ax, shrink=0.85)
    fig.tight_layout()
    matrix_plot = ATLAS_EXPORT_DIR / "cross_layer_matrix.png"
    fig.savefig(matrix_plot, dpi=180)
    plt.close(fig)
    out_paths.append(_rel(matrix_plot))

    return out_paths


def _write_analysis_bundle(
    symbols: List[Symbol],
    edges: List[Edge],
    cls: Dict[str, str],
    file_metrics: List[Dict[str, object]],
    triads: List[Dict[str, object]],
    partial_triads: List[Dict[str, object]],
    iso_metrics: Dict[str, object],
    trend_delta: Dict[str, object],
    history_count: int,
    inquisitor_result: Dict[str, object],
    proof_metrics: Dict[str, object],
    test_metrics: Dict[str, object],
    test_rows: List[Dict[str, object]],
    priority_plan: List[Dict[str, object]],
    frag_flags: List[str],
    latex_metrics: Dict[str, object],
    proof_doc_metrics: Dict[str, object],
    proof_doc_rows: List[Dict[str, object]],
    dod_status: Dict[str, object],
    isomorphism_violations: List[Dict[str, object]],
    generated_at: str,
    toolchain_gates: Optional[Dict[str, object]] = None,
) -> Dict[str, List[str]]:
    ATLAS_EXPORT_DIR.mkdir(parents=True, exist_ok=True)

    sym_by_id = {s.id: s for s in symbols}
    edge_rows = [
        {
            "src_id": e.src_id,
            "src_layer": sym_by_id[e.src_id].layer,
            "src_file": sym_by_id[e.src_id].file,
            "src_name": sym_by_id[e.src_id].name,
            "dst_id": e.dst_id,
            "dst_layer": sym_by_id[e.dst_id].layer,
            "dst_file": sym_by_id[e.dst_id].file,
            "dst_name": sym_by_id[e.dst_id].name,
            "kind": e.kind,
        }
        for e in edges
    ]

    symbol_rows = [
        {
            "id": s.id,
            "layer": s.layer,
            "kind": s.kind,
            "name": s.name,
            "norm": s.norm,
            "file": s.file,
            "line": s.line,
            "class": cls.get(s.id, "unknown"),
            "raw_ref_count": len(s.raw_refs),
        }
        for s in symbols
    ]

    summary_path = ATLAS_EXPORT_DIR / "atlas_summary.json"
    symbols_csv = ATLAS_EXPORT_DIR / "atlas_symbols.csv"
    edges_csv = ATLAS_EXPORT_DIR / "atlas_edges.csv"
    file_metrics_csv = ATLAS_EXPORT_DIR / "atlas_file_metrics.csv"
    triads_csv = ATLAS_EXPORT_DIR / "atlas_triads.csv"
    partial_triads_csv = ATLAS_EXPORT_DIR / "atlas_partial_triads.csv"
    inquisitor_json = ATLAS_EXPORT_DIR / "atlas_inquisitor_summary.json"
    test_csv = ATLAS_EXPORT_DIR / "atlas_test_verification.csv"
    priority_json = ATLAS_EXPORT_DIR / "atlas_priority_plan.json"
    proof_docs_csv = ATLAS_EXPORT_DIR / "atlas_proof_documentation.csv"
    latex_json = ATLAS_EXPORT_DIR / "atlas_latex_coverage.json"
    dod_json = ATLAS_EXPORT_DIR / "atlas_definition_of_done.json"
    violations_json = ATLAS_EXPORT_DIR / "atlas_isomorphism_violations.json"

    summary_payload = {
        "generated_at": generated_at,
        "counts": {
            "symbols": len(symbols),
            "edges": len(edges),
            "triads": len(triads),
            "files": len({s.file for s in symbols}),
        },
        "class_counts": dict(Counter(cls.values())),
        "edge_kind_counts": dict(Counter(e.kind for e in edges)),
        "cross_layer_matrix": {
            f"{src}->{dst}": weight
            for (src, dst), weight in sorted(_cross_layer_matrix(symbols, edges).items())
        },
        "top_cross_file_links": [
            {"src": s, "dst": d, "weight": w}
            for s, d, w in _top_cross_file_links(symbols, edges, limit=80)
        ],
        "isomorphism_metrics": iso_metrics,
        "trend_delta": trend_delta,
        "history_length": history_count,
        "inquisitor": inquisitor_result,
        "proof_quality_metrics": proof_metrics,
        "test_verification_metrics": test_metrics,
        "priority_plan": priority_plan,
        "fragmented_correctness_flags": frag_flags,
        "latex_coverage_metrics": latex_metrics,
        "proof_documentation_metrics": proof_doc_metrics,
        "definition_of_done": dod_status,
        "isomorphism_violations": isomorphism_violations,
        "isomorphism_violation_count": len(isomorphism_violations),
        "toolchain_gates": toolchain_gates or {},
    }
    summary_path.write_text(json.dumps(summary_payload, indent=2), encoding="utf-8")
    inquisitor_json.write_text(
        json.dumps(
            {
                "generated_at": generated_at,
                "inquisitor": inquisitor_result,
                "proof_quality_metrics": proof_metrics,
                "fragmented_correctness_flags": frag_flags,
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    priority_json.write_text(json.dumps(priority_plan, indent=2), encoding="utf-8")
    latex_json.write_text(json.dumps(latex_metrics, indent=2), encoding="utf-8")
    dod_json.write_text(json.dumps(dod_status, indent=2), encoding="utf-8")
    violations_json.write_text(json.dumps(isomorphism_violations, indent=2), encoding="utf-8")

    _write_csv(
        symbols_csv,
        symbol_rows,
        ["id", "layer", "kind", "name", "norm", "file", "line", "class", "raw_ref_count"],
    )
    _write_csv(
        edges_csv,
        edge_rows,
        ["src_id", "src_layer", "src_file", "src_name", "dst_id", "dst_layer", "dst_file", "dst_name", "kind"],
    )
    _write_csv(
        file_metrics_csv,
        file_metrics,
        [
            "file",
            "layer",
            "symbol_count",
            "core",
            "bridge",
            "island",
            "orphan",
            "duplicate",
            "stale",
            "test_only",
            "connectivity_ratio",
            "action",
        ],
    )
    _write_csv(
        triads_csv,
        triads,
        ["norm", "coq", "python", "rtl", "coq_count", "python_count", "rtl_count"],
    )
    _write_csv(
        partial_triads_csv,
        partial_triads,
        ["norm", "present_layers", "missing_layers", "coq_count", "python_count", "rtl_count", "weight"],
    )
    _write_csv(
        test_csv,
        test_rows,
        [
            "test_file",
            "layer",
            "symbol_count",
            "coverage_edges",
            "covered_prod_files",
            "covered_prod_symbols",
            "status",
            "notes",
        ],
    )
    _write_csv(
        proof_docs_csv,
        proof_doc_rows,
        ["proof_file", "proof_count", "has_comment_blocks", "has_local_readme", "status"],
    )

    diagrams: Dict[str, str] = {
        "layer_flow.mmd": _mermaid_layer_flow(symbols, edges),
        "top_file_links.mmd": _mermaid_top_links(symbols, edges),
        "triad_topology.mmd": _mermaid_triads(triads),
        "symbol_class_breakdown.mmd": _mermaid_class_breakdown(cls),
        "file_action_breakdown.mmd": _mermaid_action_breakdown(file_metrics),
        "python_rtl_focus.mmd": _mermaid_python_rtl_focus(symbols, edges),
    }

    exported: List[str] = []
    rendered: List[str] = []

    for filename, body in diagrams.items():
        out = ATLAS_EXPORT_DIR / filename
        out.write_text(body + "\n", encoding="utf-8")
        exported.append(_rel(out))
        rendered.extend(_try_render_mermaid(out))

    rendered.extend(_try_render_matplotlib(symbols, edges, cls, file_metrics))

    exported.extend(
        [
            _rel(summary_path),
            _rel(symbols_csv),
            _rel(edges_csv),
            _rel(file_metrics_csv),
            _rel(triads_csv),
            _rel(partial_triads_csv),
            _rel(inquisitor_json),
            _rel(test_csv),
            _rel(priority_json),
            _rel(proof_docs_csv),
            _rel(latex_json),
            _rel(dod_json),
            _rel(violations_json),
        ]
    )

    return {
        "exported": sorted(exported),
        "rendered_images": sorted(rendered),
    }


def _guidance_actions(
    symbols: List[Symbol],
    file_metrics: List[Dict[str, object]],
    partial_triads: List[Dict[str, object]],
    matrix: Dict[Tuple[str, str], int],
    inquisitor_result: Dict[str, object],
    proof_metrics: Dict[str, object],
    limit: int = 20,
) -> List[str]:
    actions: List[str] = []

    for row in sorted(
        [r for r in file_metrics if str(r.get("action")) == "integrate" and str(r.get("layer")) in PROD_LAYERS],
        key=lambda r: (-(_as_int(r.get("orphan")) + _as_int(r.get("island"))), _as_float(r.get("connectivity_ratio"))),
    )[:8]:
        actions.append(
            "Integrate "
            f"{row['file']} ({row['layer']}) by resolving orphan/island symbols "
            f"[{row['orphan']} orphan, {row['island']} island; connectivity {_as_float(row['connectivity_ratio']):.0%}]"
        )

    for gap in partial_triads[:8]:
        actions.append(
            "Close partial triad "
            f"'{gap['norm']}' by adding missing layer(s): {gap['missing_layers']} "
            f"[present: {gap['present_layers']}]"
        )

    for src, dst in [
        ("coq", "python"),
        ("python", "coq"),
        ("coq", "rtl"),
        ("rtl", "coq"),
        ("python", "rtl"),
        ("rtl", "python"),
    ]:
        if matrix.get((src, dst), 0) == 0:
            actions.append(f"Create at least one explicit bridge from {src} to {dst} (currently zero directional edges)")

    report = inquisitor_result.get("report")
    if isinstance(report, dict):
        top_rules = report.get("top_rules")
        if isinstance(top_rules, list):
            for item in top_rules[:5]:
                if not isinstance(item, dict):
                    continue
                rule = str(item.get("rule", "UNKNOWN_RULE"))
                count = _as_int(item.get("count"))
                actions.append(
                    f"Reduce Inquisitor rule {rule} occurrences (current count: {count}) to raise proof gate accuracy"
                )

    if not bool(proof_metrics.get("strict_pass", False)):
        actions.append("Proof gate is FAIL: eliminate all HIGH and MEDIUM Inquisitor findings before claiming isomorphic completion")

    if not actions:
        actions.append("No critical gaps detected; continue expanding triad density and reducing integrate backlog")
    return actions[:limit]


def _md_report(
    symbols: List[Symbol],
    edges: List[Edge],
    cls: Dict[str, str],
    file_metrics: List[Dict[str, object]],
    triads: List[Dict[str, object]],
    partial_triads: List[Dict[str, object]],
    iso_metrics: Dict[str, object],
    trend_delta: Dict[str, object],
    history_count: int,
    inquisitor_result: Dict[str, object],
    proof_metrics: Dict[str, object],
    test_metrics: Dict[str, object],
    test_rows: List[Dict[str, object]],
    priority_plan: List[Dict[str, object]],
    frag_flags: List[str],
    latex_metrics: Dict[str, object],
    proof_doc_metrics: Dict[str, object],
    proof_doc_rows: List[Dict[str, object]],
    dod_status: Dict[str, object],
    isomorphism_violations: List[Dict[str, object]],
    generated_at: str,
    output_bundle: Dict[str, List[str]],
    toolchain_gates: Optional[Dict[str, object]] = None,
) -> str:
    layer_files: Dict[str, Set[str]] = defaultdict(set)
    for s in symbols:
        layer_files[s.layer].add(s.file)

    cls_counts = Counter(cls.values())
    layer_counts = Counter(s.layer for s in symbols)
    edge_kinds = Counter(e.kind for e in edges)

    remove_safe_files = [r for r in file_metrics if r["action"] == "remove_safe"]
    integrate_files = [r for r in file_metrics if r["action"] == "integrate"]
    dedup_files = [r for r in file_metrics if r["action"] == "deduplicate"]
    archive_files = [r for r in file_metrics if r["action"] == "archive"]

    worst_isolation = sorted(
        [r for r in file_metrics if r["layer"] in PROD_LAYERS and _as_int(r["symbol_count"]) >= 3],
        key=lambda r: (-(_as_int(r["orphan"]) + _as_int(r["island"])), _as_float(r["connectivity_ratio"])),
    )[:35]

    matrix = _cross_layer_matrix(symbols, edges)
    inquisitor_report = inquisitor_result.get("report")
    if not isinstance(inquisitor_report, dict):
        inquisitor_report = {}

    kernel_coq_rows = [
        r for r in file_metrics if str(r.get("layer")) == "coq" and str(r.get("file", "")).startswith("coq/kernel/")
    ]
    non_kernel_coq_rows = [
        r for r in file_metrics if str(r.get("layer")) == "coq" and not str(r.get("file", "")).startswith("coq/kernel/")
    ]

    kernel_connectivity = (
        sum(_as_float(r.get("connectivity_ratio")) for r in kernel_coq_rows) / len(kernel_coq_rows)
        if kernel_coq_rows
        else 0.0
    )
    non_kernel_connectivity = (
        sum(_as_float(r.get("connectivity_ratio")) for r in non_kernel_coq_rows) / len(non_kernel_coq_rows)
        if non_kernel_coq_rows
        else 0.0
    )

    if kernel_connectivity >= non_kernel_connectivity:
        kernel_guidance = (
            "Kernel should remain the minimal canonical semantics layer; keep physics and domain files outside kernel "
            "and prove bridges into kernel invariants."
        )
    else:
        kernel_guidance = (
            "Kernel connectivity is weaker than non-kernel Coq files; prioritize proving bridge lemmas from physics/domain "
            "theorems into kernel VM semantics before moving declarations into kernel."
        )

    guidance_actions = _guidance_actions(
        symbols,
        file_metrics,
        partial_triads,
        matrix,
        inquisitor_result,
        proof_metrics,
        limit=25,
    )

    lines: List[str] = [
        "# Thiele Integration Atlas",
        "",
        f"Generated: {generated_at}",
        "",
        "Single canonical atlas for cross-layer integration planning (Coq + VM/Python + RTL/Verilog + tests).",
        "",
        "## Executive Summary",
        "",
        f"- Total symbols: **{len(symbols)}**",
        f"- Total edges: **{len(edges)}**",
        f"- 3-layer triads: **{len(triads)}**",
        f"- Partial triads (2/3 layers): **{len(partial_triads)}**",
        f"- Integrate candidates: **{len(integrate_files)}**",
        f"- Safe removals (strict): **{len(remove_safe_files)}**",
        f"- Inquisitor gate: **{str(proof_metrics.get('gate_rating', 'FAIL'))}**",
        f"- Proof accuracy: **{_as_float(proof_metrics.get('proof_accuracy')):.2f}%**",
        f"- Test verification gate: **{str(test_metrics.get('test_gate', 'FAIL'))}**",
        f"- Definition of Done: **{str(dod_status.get('status', 'NOT_COMPLETED'))}**",
        f"- Deep isomorphism value mismatches: **{len(isomorphism_violations)}**",
        "",
        "Conservative policy: no Coq proof declarations are ever recommended for removal.",
        "Important: Proof accuracy is Inquisitor proof-hygiene quality, not project completion percentage.",
        "",
        "## Inquisitor Proof Gate",
        "",
        "| Metric | Value |",
        "|---|---:|",
        f"| Gate rating | {proof_metrics.get('gate_rating', 'FAIL')} |",
        f"| Strict pass | {bool(proof_metrics.get('strict_pass', False))} |",
        f"| Proof accuracy | {_as_float(proof_metrics.get('proof_accuracy')):.2f}% |",
        f"| Proof grade | {proof_metrics.get('proof_quality_grade', 'D')} |",
        f"| Scanned Coq files | {_as_int(proof_metrics.get('scanned_files'))} |",
        f"| HIGH findings | {_as_int(proof_metrics.get('high'))} |",
        f"| MEDIUM findings | {_as_int(proof_metrics.get('medium'))} |",
        f"| LOW findings | {_as_int(proof_metrics.get('low'))} |",
        f"| Inquisitor return code | {_as_int(inquisitor_result.get('returncode'))} |",
        "",
        "Top failing rule families from Inquisitor:",
        "",
        "| Rule | Count |",
        "|---|---:|",
    ]

    top_rules = inquisitor_report.get("top_rules")
    if isinstance(top_rules, list) and top_rules:
        for item in top_rules[:15]:
            if not isinstance(item, dict):
                continue
            lines.append(f"| {item.get('rule', 'UNKNOWN_RULE')} | {_as_int(item.get('count'))} |")
    else:
        lines.append("| *(none parsed)* | 0 |")

    lines += [
        "",
        "## Kernel Organization Guidance",
        "",
        f"- Kernel Coq files: **{len(kernel_coq_rows)}**, average connectivity **{kernel_connectivity:.0%}**",
        f"- Non-kernel Coq files: **{len(non_kernel_coq_rows)}**, average connectivity **{non_kernel_connectivity:.0%}**",
        f"- Guidance: {kernel_guidance}",
        "",
        "## Isomorphism Guidance Scorecard",
        "",
        "| Metric | Value |",
        "|---|---:|",
        f"| Isomorphism score (0-100) | {_as_float(iso_metrics.get('isomorphism_score')):.2f} |",
        f"| Core+Bridge production ratio | {_as_float(iso_metrics.get('core_bridge_ratio')):.0%} |",
        f"| Triad completion ratio | {_as_float(iso_metrics.get('triad_completion_ratio')):.0%} |",
        f"| Directional coverage | {_as_int(iso_metrics.get('active_direction_count'))}/{_as_int(iso_metrics.get('direction_count'))} |",
        f"| Integrate-file pressure | {_as_float(iso_metrics.get('integrate_file_ratio')):.0%} |",
        f"| Completion readiness (heuristic) | {max(0.0, min(100.0, 0.7 * _as_float(iso_metrics.get('isomorphism_score')) + 0.3 * _as_float(test_metrics.get('prod_symbol_coverage_ratio')) * 100.0)):.2f} |",
        "",
        "## Test Verification Gate",
        "",
        "| Metric | Value |",
        "|---|---:|",
        f"| Gate rating | {test_metrics.get('test_gate', 'FAIL')} |",
        f"| Production symbol coverage | {_as_float(test_metrics.get('prod_symbol_coverage_ratio')):.0%} |",
        f"| Production file coverage | {_as_float(test_metrics.get('prod_file_coverage_ratio')):.0%} |",
        f"| Isolated test files | {_as_int(test_metrics.get('isolated_test_file_count'))} |",
        f"| Covered prod symbols | {_as_int(test_metrics.get('covered_prod_symbol_count'))}/{_as_int(test_metrics.get('prod_symbol_count'))} |",
        f"| Covered prod files | {_as_int(test_metrics.get('covered_prod_file_count'))}/{_as_int(test_metrics.get('prod_file_count'))} |",
        "",
        "## Definition of Done (Unambiguous Completion Gate)",
        "",
        f"Overall status: **{dod_status.get('status', 'NOT_COMPLETED')}**",
        "",
        "| Check | Actual | Target | Pass |",
        "|---|---:|---:|---|",
    ]

    dod_checks = dod_status.get("checks")
    if isinstance(dod_checks, list):
        for check in dod_checks:
            if not isinstance(check, dict):
                continue
            target = f"{check.get('comparator')} {check.get('threshold')}"
            lines.append(
                f"| {check.get('name')} | {check.get('actual')} | {target} | {check.get('passed')} |"
            )

    unmet = dod_status.get("unmet_checks")
    if isinstance(unmet, list) and unmet:
        lines += [
            "",
            "Unmet checks:",
            "",
        ]
        for check in unmet:
            if not isinstance(check, dict):
                continue
            lines.append(
                f"- {check.get('name')}: actual={check.get('actual')} target {check.get('comparator')} {check.get('threshold')}"
            )

    lines += [
        "",
        "## Toolchain Reality Gates",
        "",
        "These gates verify **actual compilation, extraction, and synthesis** — not just",
        "static graph analysis. All four must PASS for the isomorphism to be mechanically",
        "checkable end-to-end.",
        "",
        "| Gate | Ran | Pass | Detail |",
        "|---|---|---|---|",
    ]

    lines += [
        "",
        "## Deep Isomorphism Value Mismatches",
        "",
        "These are value-level disagreements for triads where constants were parseable across layers.",
        "",
        "| Norm | Coq | Python | RTL | Delta | Severity |",
        "|---|---:|---:|---:|---:|---|",
    ]
    if isomorphism_violations:
        for row in isomorphism_violations[:30]:
            lines.append(
                "| "
                f"{row.get('norm')} | "
                f"{row.get('coq_value')} | "
                f"{row.get('python_value')} | "
                f"{row.get('rtl_value')} | "
                f"{row.get('delta')} | "
                f"{row.get('severity')} |"
            )
    else:
        lines.append("| *(none)* | | | | | |")
    if toolchain_gates:
        gate_defs = [
            ("coq_compile",          "Coq compile (make -C coq, zero Admitted)"),
            ("extraction_freshness", "Extraction freshness (thiele_core.ml ≥ Extraction.v)"),
            ("rtl_synthesis",        "RTL synthesis (Yosys lite, top=thiele_cpu, cells>0)"),
            ("cosim",                "Co-simulation (iverilog/vvp testbench)"),
        ]
        for key, label in gate_defs:
            g = toolchain_gates.get(key) or {}
            ran = "✓" if bool(g.get("ran")) else "—"
            passed = "**PASS**" if bool(g.get("pass")) else ("FAIL" if bool(g.get("ran")) else "not run")
            detail_parts = []
            if key == "coq_compile" and g.get("ran"):
                detail_parts.append(f"{g.get('total_vo_files')}/{g.get('total_v_files')} .vo, admits={g.get('admitted_count')}")
            elif key == "extraction_freshness" and g.get("ran"):
                file_checks = g.get("files") or {}
                for fname, fc in file_checks.items():
                    if isinstance(fc, dict) and not fc.get("pass"):
                        detail_parts.append(f"{fname}: fresh={fc.get('fresh')} symbols={fc.get('symbols_ok')}")
            elif key == "rtl_synthesis" and g.get("ran"):
                detail_parts.append(f"cells={g.get('cell_count')} top={g.get('top_module_present')}")
            elif key == "cosim" and g.get("ran"):
                detail_parts.append(f"rc={g.get('returncode')} fatal={g.get('has_fail_marker')}")
            detail = "; ".join(detail_parts) if detail_parts else "—"
            lines.append(f"| {label} | {ran} | {passed} | {detail} |")
    else:
        lines.append("| *(gates not run — call generate_full_mesh_audit.py)* | — | — | — |")

    lines += [
        "",
        "## Thesis/Math LaTeX Coverage",
        "",
        "| Metric | Value |",
        "|---|---:|",
        f"| TeX files scanned | {_as_int(latex_metrics.get('tex_file_count'))} |",
        f"| Kernel proof symbols mentioned in TeX | {_as_int(latex_metrics.get('kernel_proof_symbol_mentioned_count'))}/{_as_int(latex_metrics.get('kernel_proof_symbol_count'))} |",
        f"| Kernel proof LaTeX coverage ratio | {_as_float(latex_metrics.get('kernel_proof_latex_coverage_ratio')):.0%} |",
        f"| Triad norms mentioned in TeX | {_as_int(latex_metrics.get('triad_norm_mentioned_count'))}/{_as_int(latex_metrics.get('triad_norm_count'))} |",
        f"| Triad norm LaTeX coverage ratio | {_as_float(latex_metrics.get('triad_norm_latex_coverage_ratio')):.0%} |",
        "",
        "Top missing kernel proof symbols in TeX (first 20):",
        "",
        "| Symbol |",
        "|---|",
    ]

    missing_kernel = latex_metrics.get("kernel_proof_missing_top")
    if isinstance(missing_kernel, list) and missing_kernel:
        for sym in missing_kernel[:20]:
            lines.append(f"| {sym} |")
    else:
        lines.append("| *(none)* |")

    lines += [
        "",
        "## Coq Proof Documentation Coverage (Low Priority)",
        "",
        "| Metric | Value |",
        "|---|---:|",
        f"| Proof files | {_as_int(proof_doc_metrics.get('proof_file_count'))} |",
        f"| Proof files with local README | {_as_int(proof_doc_metrics.get('proof_files_with_readme_count'))}/{_as_int(proof_doc_metrics.get('proof_file_count'))} |",
        f"| Proof files with comment blocks | {_as_int(proof_doc_metrics.get('proof_files_with_comment_blocks_count'))}/{_as_int(proof_doc_metrics.get('proof_file_count'))} |",
        f"| Proof files documented (README + comments) | {_as_int(proof_doc_metrics.get('proof_files_documented_count'))}/{_as_int(proof_doc_metrics.get('proof_file_count'))} |",
        "",
        "| Proof file | Proof count | Has comments | Has README | Status |",
        "|---|---:|---|---|---|",
    ]

    for row in proof_doc_rows[:260]:
        lines.append(
            f"| {row.get('proof_file')} | {_as_int(row.get('proof_count'))} | {row.get('has_comment_blocks')} | {row.get('has_local_readme')} | {row.get('status')} |"
        )

    if len(proof_doc_rows) > 260:
        lines.append(f"| ... {len(proof_doc_rows) - 260} more proof-doc rows omitted | | | | |")

    lines += [
        "",
        "Top uncovered production files (first 20):",
        "",
        "| Production file |",
        "|---|",
    ]

    uncovered = test_metrics.get("uncovered_prod_files_top")
    if isinstance(uncovered, list) and uncovered:
        for file_path in uncovered[:20]:
            lines.append(f"| {file_path} |")
    else:
        lines.append("| *(none)* |")

    lines += [
        "",
        "## Fragmented Correctness Diagnostics",
        "",
    ]

    for flag in frag_flags:
        lines.append(f"- {flag}")

    lines += [
        "",
        "## Top 10 Highest-Impact Closure Tasks",
        "",
        "| Rank | Task | Type | Estimated score gain | Details |",
        "|---:|---|---|---:|---|",
    ]

    for idx, item in enumerate(priority_plan[:10], start=1):
        lines.append(
            f"| {idx} | {item.get('task')} | {item.get('type')} | {_as_float(item.get('estimated_score_gain')):.2f} | {item.get('details')} |"
        )

    if not priority_plan:
        lines.append("| 1 | *(none generated)* | n/a | 0.00 | n/a |")

    lines += [
        "",
        "## Test File Verification Detail",
        "",
        "| Test file | Layer | Symbols | Coverage edges | Covered prod files | Covered prod symbols | Status |",
        "|---|---|---:|---:|---:|---:|---|",
    ]

    for row in test_rows[:320]:
        lines.append(
            f"| {row.get('test_file')} | {row.get('layer')} | {_as_int(row.get('symbol_count'))} | {_as_int(row.get('coverage_edges'))} | {_as_int(row.get('covered_prod_files'))} | {_as_int(row.get('covered_prod_symbols'))} | {row.get('status')} |"
        )

    if len(test_rows) > 320:
        lines.append(f"| ... {len(test_rows) - 320} more test rows omitted | | | | | | |")

    lines += [
        "",
        "## Run-to-Run Progress Delta",
        "",
        f"- History snapshots tracked: **{history_count}**",
        f"- Score delta vs previous run: **{_as_float(trend_delta.get('score_delta')):+.2f}**",
        f"- Triad delta vs previous run: **{_as_int(trend_delta.get('triad_delta')):+d}**",
        f"- Partial-triad delta vs previous run: **{_as_int(trend_delta.get('partial_triad_delta')):+d}**",
        f"- Integrate-file delta vs previous run: **{_as_int(trend_delta.get('integrate_file_delta')):+d}**",
        "",
        "## Guided Next Actions (Priority Queue)",
        "",
    ]

    for action in guidance_actions:
        lines.append(f"- {action}")

    lines += [
        "",
        "## Coverage by Layer",
        "",
        "| Layer | Files | Symbols |",
        "|---|---:|---:|",
    ]

    for layer in ["coq", "python", "rtl", "rtl_tb", "test", "stale"]:
        lines.append(f"| {layer} | {len(layer_files[layer])} | {layer_counts[layer]} |")

    lines += [
        "",
        "## Connectivity Legend",
        "",
        "- **core**: connected to all three production layers",
        "- **bridge**: connected to exactly two production layers",
        "- **island**: connected only inside one layer",
        "- **orphan**: no edges",
        "- **duplicate**: same normalized symbol appears in multiple files of same layer",
        "- **stale**: located under archive/disabled/exploratory/legacy markers",
        "- **test_only**: symbol declared in test or testbench layer",
        "",
        "## Symbol Classification",
        "",
        "| Class | Count |",
        "|---|---:|",
        f"| core | {cls_counts['core']} |",
        f"| bridge | {cls_counts['bridge']} |",
        f"| island | {cls_counts['island']} |",
        f"| orphan | {cls_counts['orphan']} |",
        f"| duplicate | {cls_counts['duplicate']} |",
        f"| stale | {cls_counts['stale']} |",
        f"| test_only | {cls_counts['test_only']} |",
        "",
        "## Edge Kinds",
        "",
        "| Edge kind | Count |",
        "|---|---:|",
    ]

    for kind, count in sorted(edge_kinds.items(), key=lambda kv: (-kv[1], kv[0])):
        lines.append(f"| {kind} | {count} |")

    lines += [
        "",
        "## Layer Interaction Diagram",
        "",
        "```mermaid",
        _mermaid_layer_flow(symbols, edges),
        "```",
        "",
        "## File-Level Connection Diagram (Top Links)",
        "",
        "```mermaid",
        _mermaid_top_links(symbols, edges),
        "```",
        "",
        "## Triad Topology Diagram",
        "",
        "```mermaid",
        _mermaid_triads(triads),
        "```",
        "",
        "## Cross-Layer Matrix",
        "",
        "| From \\ To | coq | python | rtl |",
        "|---|---:|---:|---:|",
        f"| coq | 0 | {matrix.get(('coq', 'python'), 0)} | {matrix.get(('coq', 'rtl'), 0)} |",
        f"| python | {matrix.get(('python', 'coq'), 0)} | 0 | {matrix.get(('python', 'rtl'), 0)} |",
        f"| rtl | {matrix.get(('rtl', 'coq'), 0)} | {matrix.get(('rtl', 'python'), 0)} | 0 |",
        "",
        "## Confirmed 3-Layer Triads (Isomorphic Name Clusters)",
        "",
        "| Normalized | Coq | Python/VM | RTL/Verilog | Multiplicity (C/P/R) |",
        "|---|---|---|---|---|",
    ]

    for triad in triads[:220]:
        lines.append(
            f"| {triad['norm']} | {triad['coq']} | {triad['python']} | {triad['rtl']} | "
            f"{triad['coq_count']}/{triad['python_count']}/{triad['rtl_count']} |"
        )

    if len(triads) > 220:
        lines.append(f"| ... {len(triads) - 220} more triads omitted for readability | | | | |")

    lines += [
        "",
        "## Partial Triads (Missing One Layer)",
        "",
        "| Normalized | Present layers | Missing layer(s) | Weight |",
        "|---|---|---|---:|",
    ]

    for gap in partial_triads[:240]:
        lines.append(
            f"| {gap['norm']} | {gap['present_layers']} | {gap['missing_layers']} | {gap['weight']} |"
        )

    if len(partial_triads) > 240:
        lines.append(f"| ... {len(partial_triads) - 240} more partial triads omitted | | | |")

    lines += [
        "",
        "## Integration Backlog (Action = integrate)",
        "",
        "| File | Layer | Symbols | Core | Bridge | Island | Orphan | Connectivity |",
        "|---|---|---:|---:|---:|---:|---:|---:|",
    ]

    for row in integrate_files[:300]:
        lines.append(
            f"| {row['file']} | {row['layer']} | {row['symbol_count']} | {row['core']} | {row['bridge']} | "
            f"{row['island']} | {row['orphan']} | {_as_float(row['connectivity_ratio']):.0%} |"
        )

    if len(integrate_files) > 300:
        lines.append(f"| ... {len(integrate_files) - 300} more integrate rows omitted | | | | | | | |")

    lines += [
        "",
        "## Duplicate Collisions",
        "",
        "| File | Layer | Duplicate symbols |",
        "|---|---|---:|",
    ]

    for row in dedup_files[:200]:
        lines.append(f"| {row['file']} | {row['layer']} | {row['duplicate']} |")

    if len(dedup_files) > 200:
        lines.append(f"| ... {len(dedup_files) - 200} more duplicate rows omitted | | |")

    lines += [
        "",
        "## Strict Safe-Removal Candidates",
        "",
        "A file appears here only if ALL conditions hold:",
        "1) path contains remove-safe markers (unused/deprecated/legacy/dead/tmp/disabled)",
        "2) every symbol has zero incident edges",
        "3) no Coq proof declarations involved",
        "",
        "| File | Layer | Symbols | Reason |",
        "|---|---|---:|---|",
    ]

    for row in remove_safe_files:
        lines.append(
            f"| {row['file']} | {row['layer']} | {row['symbol_count']} | marker+zero-edge+non-proof strict pass |"
        )

    if not remove_safe_files:
        lines.append("| *(none)* | | | strict filter found no safe removals |")

    lines += [
        "",
        "## Archive/Legacy Files",
        "",
        "| File | Symbols |",
        "|---|---:|",
    ]

    for row in archive_files[:240]:
        lines.append(f"| {row['file']} | {row['symbol_count']} |")

    if len(archive_files) > 240:
        lines.append(f"| ... {len(archive_files) - 240} more archive rows omitted | |")

    lines += [
        "",
        "## Highest Isolation Files",
        "",
        "| File | Layer | Symbols | Orphan | Island | Connectivity |",
        "|---|---|---:|---:|---:|---:|",
    ]

    for row in worst_isolation:
        lines.append(
            f"| {row['file']} | {row['layer']} | {row['symbol_count']} | {row['orphan']} | {row['island']} | {_as_float(row['connectivity_ratio']):.0%} |"
        )

    compact_json = {
        "generated_at": generated_at,
        "summary": {
            "symbols": len(symbols),
            "edges": len(edges),
            "triads": len(triads),
            "partial_triads": len(partial_triads),
            "classifications": dict(cls_counts),
            "integrate_files": len(integrate_files),
            "remove_safe_files": len(remove_safe_files),
        },
        "isomorphism_metrics": iso_metrics,
        "trend_delta": trend_delta,
        "proof_quality_metrics": proof_metrics,
        "test_verification_metrics": test_metrics,
        "priority_plan": priority_plan,
        "fragmented_correctness_flags": frag_flags,
        "latex_coverage_metrics": latex_metrics,
        "proof_documentation_metrics": proof_doc_metrics,
        "definition_of_done": dod_status,
        "toolchain_gates": toolchain_gates or {},
        "inquisitor": {
            "status": inquisitor_result.get("status"),
            "returncode": inquisitor_result.get("returncode"),
            "report_path": inquisitor_result.get("report_path"),
        },
        "cross_layer_matrix": {f"{a}->{b}": v for (a, b), v in sorted(matrix.items())},
        "top_cross_file_links": [
            {"src": s, "dst": d, "weight": w}
            for s, d, w in _top_cross_file_links(symbols, edges, limit=50)
        ],
    }

    lines += [
        "",
        "## Embedded Machine Snapshot",
        "",
        "```json",
        json.dumps(compact_json, indent=2),
        "```",
        "",
        "## Companion Outputs",
        "",
        "Atlas run also writes machine-readable analysis and diagram sources under `artifacts/atlas/`.",
        "",
        "| Exported path |",
        "|---|",
    ]

    for path in output_bundle.get("exported", []):
        lines.append(f"| {path} |")

    if output_bundle.get("rendered_images"):
        lines += [
            "",
            "Rendered image files:",
            "",
            "| Image path |",
            "|---|",
        ]
        for path in output_bundle.get("rendered_images", []):
            lines.append(f"| {path} |")
    else:
        lines += [
            "",
            "Rendered image files: *(none — Mermaid CLI `mmdc` not found at runtime; `.mmd` sources exported)*",
        ]

    lines += [
        "",
        "## Notes",
        "",
        "- This atlas is intentionally integration-biased and conservative on removals.",
        "- Use triads + top file links as the primary map for cross-layer completion work.",
        "- Keep Coq-only or proof-heavy files in the pipeline unless independently deprecated.",
        "",
    ]

    return "\n".join(lines)


def main() -> int:
    print("Cleaning previous atlas outputs...")
    _clean_previous_outputs()

    print("Discovering repository files...")
    coq_files, py_src_files, py_test_files, rtl_src_files, rtl_tb_files = _discover_all()
    print(
        "  "
        f"coq={len(coq_files)} "
        f"py_src={len(py_src_files)} "
        f"py_test={len(py_test_files)} "
        f"rtl_src={len(rtl_src_files)} "
        f"rtl_tb={len(rtl_tb_files)}"
    )

    print("Parsing symbols...")
    symbols = _build_symbol_table(coq_files, py_src_files, py_test_files, rtl_src_files, rtl_tb_files)
    print(f"  symbols={len(symbols)}")

    print("Building edges...")
    edges = _build_edges(symbols)
    print(f"  edges={len(edges)}")

    print("Classifying symbols...")
    cls, incident, _connected_prod = _classify(symbols, edges)

    print("Computing file-level metrics and triads...")
    file_metrics = _file_metrics(symbols, cls, incident)
    triads = _find_triads(symbols)
    partial_triads = _find_partial_triads(symbols)
    
    print("Validating deep isomorphism (bit-for-bit value equivalence)...")
    isomorphism_violations = _validate_triad_isomorphism(symbols, triads)
    if isomorphism_violations:
        print(f"  WARNING: {len(isomorphism_violations)} ISOMORPHISM VIOLATIONS DETECTED!")
        for violation in isomorphism_violations[:5]:  # Show first 5
            coq_val = f"{violation['coq_value']:.6f}" if violation['coq_value'] is not None else "N/A"
            py_val = f"{violation['python_value']:.6f}" if violation['python_value'] is not None else "N/A"
            rtl_val = f"{violation['rtl_value']:.6f}" if violation['rtl_value'] is not None else "N/A"
            print(f"    - {violation['norm']}: Coq={coq_val} Python={py_val} RTL={rtl_val} (Δ={violation['delta']:.6f})")
    else:
        print("  ✓ All triads have matching values across layers")

    print("Scoring isomorphism progress and updating run history...")
    iso_metrics = _compute_isomorphism_metrics(symbols, edges, cls, triads, partial_triads, file_metrics)

    print("Auditing test verification coverage and strictness...")
    test_metrics, test_rows = _compute_test_verification_metrics(symbols, edges, file_metrics)
    priority_plan = _build_priority_plan(iso_metrics, file_metrics, partial_triads, test_metrics, limit=10)

    print("Analyzing thesis/math LaTeX coverage and proof documentation coverage...")
    latex_metrics = _compute_latex_coverage(symbols, triads)
    proof_doc_metrics, proof_doc_rows = _compute_proof_documentation_coverage(symbols)

    generated_at = datetime.now(timezone.utc).isoformat()
    history, prev_snapshot = _update_history(generated_at, iso_metrics)
    trend_delta = _history_delta(iso_metrics, prev_snapshot)

    print("Running Inquisitor proof gate and extracting proof-quality metrics...")
    inquisitor_result = _run_inquisitor()
    proof_metrics = _compute_proof_quality_metrics(inquisitor_result)

    print("Running real toolchain gates (Coq compile, extraction freshness, RTL synthesis, co-sim)...")
    coq_gate = _run_coq_compile_gate()
    ext_gate = _run_extraction_freshness_gate()
    rtl_gate = _run_rtl_synthesis_gate()
    cosim_gate = _run_cosim_gate()
    toolchain_gates: Dict[str, object] = {
        "coq_compile": coq_gate,
        "extraction_freshness": ext_gate,
        "rtl_synthesis": rtl_gate,
        "cosim": cosim_gate,
    }
    _gate_summary = " ".join(
        f"{k}={'PASS' if bool(v.get('pass')) else ('FAIL' if bool(v.get('ran')) else 'skip')}"
        for k, v in toolchain_gates.items()
        if isinstance(v, dict)
    )
    print(f"  {_gate_summary}")

    frag_flags = _fragmented_correctness_flags(iso_metrics, proof_metrics, test_metrics, toolchain_gates)
    dod_status = _compute_definition_of_done(
        iso_metrics,
        proof_metrics,
        test_metrics,
        latex_metrics,
        proof_doc_metrics,
        toolchain_gates,
    )

    print("Exporting companion analysis bundle...")
    bundle = _write_analysis_bundle(
        symbols,
        edges,
        cls,
        file_metrics,
        triads,
        partial_triads,
        iso_metrics,
        trend_delta,
        len(history),
        inquisitor_result,
        proof_metrics,
        test_metrics,
        test_rows,
        priority_plan,
        frag_flags,
        latex_metrics,
        proof_doc_metrics,
        proof_doc_rows,
        dod_status,
        isomorphism_violations,
        generated_at,
        toolchain_gates,
    )

    md = _md_report(
        symbols,
        edges,
        cls,
        file_metrics,
        triads,
        partial_triads,
        iso_metrics,
        trend_delta,
        len(history),
        inquisitor_result,
        proof_metrics,
        test_metrics,
        test_rows,
        priority_plan,
        frag_flags,
        latex_metrics,
        proof_doc_metrics,
        proof_doc_rows,
        dod_status,
        isomorphism_violations,
        generated_at,
        bundle,
        toolchain_gates,
    )

    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_text(md, encoding="utf-8")
    print(f"Wrote {OUT_PATH.relative_to(REPO_ROOT)}")
    print(f"Exported companion files: {len(bundle.get('exported', []))}")
    print(f"Rendered images: {len(bundle.get('rendered_images', []))}")
    _terminal_deep_analysis(bundle)

    remove_count = sum(1 for r in file_metrics if r["action"] == "remove_safe")
    integrate_count = sum(1 for r in file_metrics if r["action"] == "integrate")
    print(
        "Summary: "
        f"score={_as_float(iso_metrics.get('isomorphism_score')):.2f} "
        f"gate={proof_metrics.get('gate_rating', 'FAIL')} "
        f"proof_accuracy={_as_float(proof_metrics.get('proof_accuracy')):.2f}% "
        f"test_gate={test_metrics.get('test_gate', 'FAIL')} "
        f"test_symbol_cov={_as_float(test_metrics.get('prod_symbol_coverage_ratio')):.0%} "
        f"coq_compile={'PASS' if bool(coq_gate.get('pass')) else 'FAIL'} "
        f"extraction={'PASS' if bool(ext_gate.get('pass')) else 'FAIL'} "
        f"rtl_synth={'PASS' if bool(rtl_gate.get('pass')) else 'FAIL'} "
        f"dod={dod_status.get('status', 'NOT_COMPLETED')} "
        f"triads={len(triads)} partial_triads={len(partial_triads)} "
        f"integrate={integrate_count} remove_safe={remove_count}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
