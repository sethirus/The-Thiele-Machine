#!/usr/bin/env python3
"""Pre-registered μ→SAT-difficulty experiment scaffold.

This script is designed to be:
- Doable in minutes (small default suite).
- Falsifiable (writes predictions before solver runtimes).
- Solver-free during μ extraction (hard import gate against z3).

Outputs (by default under benchmarks/mu_sat_difficulty/):
- instances/*.cnf
- instances/meta.jsonl
- predictions.jsonl
- z3_results.csv
- analysis.json
- fig_mu_vs_runtime.png (if matplotlib is available)

Usage:
  python tools/mu_sat_difficulty_scale.py generate
  python tools/mu_sat_difficulty_scale.py predict --no-solve
  python tools/mu_sat_difficulty_scale.py solve
  python tools/mu_sat_difficulty_scale.py analyze

Or one-shot:
  python tools/mu_sat_difficulty_scale.py run --no-solve
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib
import importlib.util
import json
import math
import os
import platform
import random
import subprocess
import sys
import time
import contextlib
import io
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ROOT = REPO_ROOT / "benchmarks" / "mu_sat_difficulty"
MANIFEST_NAME = "MANIFEST.json"

_TOOL_MODULE_CACHE: Dict[str, Any] = {}


def _load_tool_module(module_stem: str) -> Any:
    """Load a module from tools/<module_stem>.py without relying on sys.path."""

    cached = _TOOL_MODULE_CACHE.get(module_stem)
    if cached is not None:
        return cached

    module_path = REPO_ROOT / "tools" / f"{module_stem}.py"
    if not module_path.exists():
        raise FileNotFoundError(f"Tool module not found: {module_path}")

    spec = importlib.util.spec_from_file_location(module_stem, module_path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Failed to load module spec for: {module_path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    _TOOL_MODULE_CACHE[module_stem] = module
    return module


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256_file(path: Path) -> str:
    return _sha256_bytes(path.read_bytes())


def _maybe_sha256_file(path: Path) -> Optional[str]:
    return _sha256_file(path) if path.exists() else None


def _write_jsonl(path: Path, rows: Iterable[Dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, sort_keys=True) + "\n")


def _read_jsonl(path: Path) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            rows.append(json.loads(line))
    return rows


def _git_head_sha(root: Path) -> str:
    try:
        out = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=str(root), text=True)
        return out.strip()
    except Exception:
        return "UNKNOWN"


def _read_cpuinfo() -> Dict[str, Any]:
    cpuinfo: Dict[str, Any] = {"model_name": None, "cores": None}
    try:
        text = Path("/proc/cpuinfo").read_text(encoding="utf-8", errors="ignore")
        model = None
        cores = 0
        for line in text.splitlines():
            if line.startswith("model name") and model is None:
                model = line.split(":", 1)[1].strip()
            if line.startswith("processor"):
                cores += 1
        cpuinfo["model_name"] = model
        cpuinfo["cores"] = cores or None
    except Exception:
        pass
    return cpuinfo


def _tool_hashes() -> Dict[str, str]:
    # Hash the prereg + core tools to lock the pipeline definition.
    return {
        "PREREG.md": _sha256_file(REPO_ROOT / "PREREG.md"),
        "tools/mu_sat_difficulty_scale.py": _sha256_file(REPO_ROOT / "tools" / "mu_sat_difficulty_scale.py"),
        "tools/generate_cnf_instances.py": _sha256_file(REPO_ROOT / "tools" / "generate_cnf_instances.py"),
        "tools/cnf_analyzer.py": _sha256_file(REPO_ROOT / "tools" / "cnf_analyzer.py"),
    }


def _manifest_path(root: Path) -> Path:
    return root / MANIFEST_NAME


def _write_manifest(path: Path, payload: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


def _load_manifest(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _init_manifest(root: Path, *, params: Dict[str, Any]) -> Dict[str, Any]:
    created_at = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    manifest = {
        "created_at": created_at,
        "git_head": _git_head_sha(REPO_ROOT),
        "platform": {
            "python": sys.version.split()[0],
            "os": platform.platform(),
            "machine": platform.machine(),
            "cpu": _read_cpuinfo(),
        },
        "params": params,
        "tool_hashes": _tool_hashes(),
        "artifacts": {
            "instances_meta_jsonl": None,
            "predictions_jsonl": None,
            "no_solve_receipt_json": None,
            "z3_results_csv": None,
            "analysis_json": None,
            "fig_mu_vs_runtime_png": None,
        },
        "order": [
            "instances/meta.jsonl",
            "predictions.jsonl",
            "no_solve_receipt.json",
            "z3_results.csv",
            "analysis.json",
            "fig_mu_vs_runtime.png",
        ],
    }
    _write_manifest(_manifest_path(root), manifest)
    return manifest


def _update_manifest_artifacts(root: Path) -> None:
    path = _manifest_path(root)
    if not path.exists():
        raise FileNotFoundError(f"Missing {MANIFEST_NAME}; prereg requires a manifest")
    manifest = _load_manifest(path)
    manifest["artifacts"] = {
        "instances_meta_jsonl": _maybe_sha256_file(root / "instances" / "meta.jsonl"),
        "predictions_jsonl": _maybe_sha256_file(root / "predictions.jsonl"),
        "no_solve_receipt_json": _maybe_sha256_file(root / "no_solve_receipt.json"),
        "z3_results_csv": _maybe_sha256_file(root / "z3_results.csv"),
        "analysis_json": _maybe_sha256_file(root / "analysis.json"),
        "fig_mu_vs_runtime_png": _maybe_sha256_file(root / "fig_mu_vs_runtime.png"),
    }
    _write_manifest(path, manifest)


def _require_manifest(root: Path) -> Dict[str, Any]:
    path = _manifest_path(root)
    if not path.exists():
        raise FileNotFoundError(
            f"Missing {MANIFEST_NAME}. Run via 'run' or create manifest before staged execution."
        )
    return _load_manifest(path)


def _require_manifest_or_fail(root: Path) -> None:
    if not _manifest_path(root).exists():
        raise RuntimeError(
            f"Missing {MANIFEST_NAME}. Run 'run' (recommended) or first run: "
            f"python tools/mu_sat_difficulty_scale.py --root {root} init"
        )


def _require_params_match_manifest(root: Path, *, actual: Dict[str, Any]) -> None:
    """Fail fast if a staged run is attempted with params that diverge from MANIFEST.json."""

    manifest = _require_manifest(root)
    expected = manifest.get("params", {})
    mismatches: List[str] = []
    for k, v in actual.items():
        if k not in expected:
            mismatches.append(f"{k}: missing from manifest")
            continue
        if expected.get(k) != v:
            mismatches.append(f"{k}: manifest={expected.get(k)!r} args={v!r}")
    if mismatches:
        raise RuntimeError(
            "Parameter mismatch vs manifest (prereg invalid; use a new --root/manifest):\n  "
            + "\n  ".join(mismatches)
        )


def _verify_manifest_inputs(root: Path) -> Dict[str, Any]:
    manifest = _require_manifest(root)
    # Verify tool hashes still match the prereg definition.
    expected_tools = manifest.get("tool_hashes", {})
    current_tools = _tool_hashes()
    for k, v in expected_tools.items():
        if current_tools.get(k) != v:
            raise RuntimeError(
                f"Tool hash mismatch for {k}. Expected {v}, got {current_tools.get(k)}. "
                "This invalidates prereg unless you create a new output root/manifest."
            )
    return manifest


def _stable_split(instance_id: str, *, split_seed: int, test_ratio: float) -> str:
    if not (0.0 < test_ratio < 1.0):
        raise ValueError("test_ratio must be in (0,1)")
    h = hashlib.sha256(f"{split_seed}:{instance_id}".encode("utf-8")).digest()
    bucket = int.from_bytes(h[:2], "big") / 65535.0
    return "test" if bucket < test_ratio else "train"


class _BlockZ3Imports:
    """Import hook that forbids importing z3 during μ extraction."""

    def __init__(self) -> None:
        self._enabled = False
        self._orig_import = __import__

    def enable(self) -> None:
        if self._enabled:
            return
        self._enabled = True

        def guarded_import(name, globals=None, locals=None, fromlist=(), level=0):  # type: ignore[no-untyped-def]
            if name == "z3" or name.startswith("z3."):
                raise RuntimeError("NO_SOLVE violation: attempted to import z3 during μ extraction")
            return self._orig_import(name, globals, locals, fromlist, level)

        builtins = importlib.import_module("builtins")
        setattr(builtins, "__import__", guarded_import)

    def disable(self) -> None:
        if not self._enabled:
            return
        builtins = importlib.import_module("builtins")
        setattr(builtins, "__import__", self._orig_import)
        self._enabled = False


class _NoSolveGuards:
    """Guards that forbid external process execution during μ extraction.

    This is intentionally strict: any attempt to spawn a subprocess or exec is treated
    as a NO_SOLVE violation.
    """

    def __init__(self) -> None:
        self._enabled = False
        self._orig = {}
        self.blocked_calls: int = 0

    def enable(self) -> None:
        if self._enabled:
            return
        self._enabled = True

        def deny(*_args: Any, **_kwargs: Any) -> Any:
            self.blocked_calls += 1
            raise RuntimeError("NO_SOLVE violation: attempted external process execution")

        # subprocess
        self._orig["subprocess.Popen"] = subprocess.Popen
        self._orig["subprocess.run"] = subprocess.run
        self._orig["subprocess.call"] = subprocess.call
        self._orig["subprocess.check_call"] = subprocess.check_call
        self._orig["subprocess.check_output"] = subprocess.check_output
        subprocess.Popen = deny  # type: ignore[assignment]
        subprocess.run = deny  # type: ignore[assignment]
        subprocess.call = deny  # type: ignore[assignment]
        subprocess.check_call = deny  # type: ignore[assignment]
        subprocess.check_output = deny  # type: ignore[assignment]

        # os exec/system
        self._orig["os.system"] = os.system
        self._orig["os.execv"] = os.execv
        self._orig["os.execve"] = os.execve
        self._orig["os.execl"] = os.execl
        self._orig["os.execlp"] = os.execlp
        self._orig["os.execvp"] = os.execvp
        self._orig["os.execvpe"] = os.execvpe
        os.system = deny  # type: ignore[assignment]
        os.execv = deny  # type: ignore[assignment]
        os.execve = deny  # type: ignore[assignment]
        os.execl = deny  # type: ignore[assignment]
        os.execlp = deny  # type: ignore[assignment]
        os.execvp = deny  # type: ignore[assignment]
        os.execvpe = deny  # type: ignore[assignment]

    def disable(self) -> None:
        if not self._enabled:
            return
        subprocess.Popen = self._orig["subprocess.Popen"]  # type: ignore[assignment]
        subprocess.run = self._orig["subprocess.run"]  # type: ignore[assignment]
        subprocess.call = self._orig["subprocess.call"]  # type: ignore[assignment]
        subprocess.check_call = self._orig["subprocess.check_call"]  # type: ignore[assignment]
        subprocess.check_output = self._orig["subprocess.check_output"]  # type: ignore[assignment]
        os.system = self._orig["os.system"]  # type: ignore[assignment]
        os.execv = self._orig["os.execv"]  # type: ignore[assignment]
        os.execve = self._orig["os.execve"]  # type: ignore[assignment]
        os.execl = self._orig["os.execl"]  # type: ignore[assignment]
        os.execlp = self._orig["os.execlp"]  # type: ignore[assignment]
        os.execvp = self._orig["os.execvp"]  # type: ignore[assignment]
        os.execvpe = self._orig["os.execvpe"]  # type: ignore[assignment]
        self._enabled = False


@dataclass(frozen=True)
class InstanceSpec:
    family: str
    n_vars: int
    seed: int
    modules: Optional[int] = None


def _call_generate_cnf(
    *,
    family: str,
    n_vars: int,
    seed: int,
    modules: Optional[int],
    out_path: Path,
) -> None:
    # We delegate generation to the existing repo tool so we don't repave.
    cmd = [
        sys.executable,
        str(REPO_ROOT / "tools" / "generate_cnf_instances.py"),
        "--type",
        family,
        "--vars",
        str(n_vars),
        "--seed",
        str(seed),
        "--output",
        str(out_path),
    ]
    if modules is not None:
        cmd.extend(["--modules", str(modules)])

    env = os.environ.copy()
    env["PYTHONHASHSEED"] = str(seed)
    subprocess.run(cmd, cwd=str(REPO_ROOT), env=env, check=True, capture_output=True, text=True)


def _parse_dimacs_counts(path: Path) -> Tuple[int, int]:
    num_vars = 0
    num_clauses = 0
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p cnf"):
                parts = line.split()
                num_vars = int(parts[2])
                num_clauses = int(parts[3])
                break
    return num_vars, num_clauses


def _cheap_dimacs_stats(path: Path) -> Dict[str, Any]:
    """Compute cheap, solver-free structural stats from a DIMACS CNF.

    These are intended as Baseline-B features to avoid the "μ just measures size" failure mode.
    """

    num_vars = 0
    clauses: List[List[int]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p cnf"):
                parts = line.split()
                num_vars = int(parts[2])
                continue
            lits = [int(x) for x in line.split() if x]
            if not lits:
                continue
            if lits[-1] == 0:
                lits = lits[:-1]
            if lits:
                clauses.append(lits)

    clause_lens = [len(c) for c in clauses]
    avg_clause_len = float(sum(clause_lens) / len(clause_lens)) if clause_lens else 0.0
    var_clause_len = (
        float(sum((cl - avg_clause_len) ** 2 for cl in clause_lens) / len(clause_lens))
        if clause_lens
        else 0.0
    )

    is_2sat = int(all(len(c) <= 2 for c in clauses))
    horn_count = sum(1 for c in clauses if sum(1 for lit in c if lit > 0) <= 1)
    horn_fraction = float(horn_count / len(clauses)) if clauses else 0.0

    # Variable degrees in the co-occurrence (interaction) graph.
    adj = [set() for _ in range(num_vars + 1)]
    for clause in clauses:
        vs = [abs(l) for l in clause if abs(l) <= num_vars]
        for i in range(len(vs)):
            for j in range(i + 1, len(vs)):
                a, b = vs[i], vs[j]
                if a == b:
                    continue
                adj[a].add(b)
                adj[b].add(a)

    degs = [len(adj[i]) for i in range(1, num_vars + 1)] if num_vars > 0 else []
    mean_deg = float(sum(degs) / len(degs)) if degs else 0.0
    var_deg = float(sum((d - mean_deg) ** 2 for d in degs) / len(degs)) if degs else 0.0

    # Edge density = 2E / (V(V-1))
    e2 = float(sum(degs))
    edges = e2 / 2.0
    density = float(2.0 * edges / (num_vars * (num_vars - 1))) if num_vars > 1 else 0.0

    return {
        "avg_clause_len": avg_clause_len,
        "var_clause_len": var_clause_len,
        "is_2sat": is_2sat,
        "horn_fraction": horn_fraction,
        "mean_degree": mean_deg,
        "var_degree": var_deg,
        "interaction_density_cheap": density,
    }


def _read_dimacs_clauses(path: Path) -> Tuple[int, List[List[int]]]:
    num_vars = 0
    clauses: List[List[int]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p cnf"):
                parts = line.split()
                num_vars = int(parts[2])
                continue
            lits = [int(x) for x in line.split() if x]
            if not lits:
                continue
            if lits[-1] == 0:
                lits = lits[:-1]
            if lits:
                clauses.append(lits)
    return num_vars, clauses


def _write_dimacs(path: Path, num_vars: int, clauses: List[List[int]], *, comment: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        handle.write(f"c {comment}\n")
        handle.write("c Generated by mu_sat_difficulty_scale.py\n")
        handle.write(f"p cnf {num_vars} {len(clauses)}\n")
        for clause in clauses:
            handle.write(" ".join(str(x) for x in clause) + " 0\n")


def _make_permutation_twin(src: Path, dst: Path, *, seed: int) -> None:
    n, clauses = _read_dimacs_clauses(src)
    rng = random.Random(seed)
    perm = list(range(1, n + 1))
    rng.shuffle(perm)
    mapping = {i + 1: perm[i] for i in range(n)}
    out: List[List[int]] = []
    for clause in clauses:
        out_clause = []
        for lit in clause:
            v = abs(lit)
            nv = mapping.get(v, v)
            out_clause.append(nv if lit > 0 else -nv)
        out.append(out_clause)
    rng.shuffle(out)
    _write_dimacs(dst, n, out, comment=f"Permutation twin of {src.name}")


def _generate_2sat(num_vars: int, *, seed: int, clauses_per_var: int = 2) -> List[List[int]]:
    rng = random.Random(seed)
    m = max(1, num_vars * clauses_per_var)
    clauses: List[List[int]] = []
    for _ in range(m):
        a, b = rng.sample(range(1, num_vars + 1), k=2 if num_vars >= 2 else 1)
        if num_vars < 2:
            b = a
        la = a if rng.random() > 0.5 else -a
        lb = b if rng.random() > 0.5 else -b
        clauses.append([la, lb])
    return clauses


def _generate_horn(num_vars: int, *, seed: int, clauses_per_var: int = 2, clause_size: int = 3) -> List[List[int]]:
    rng = random.Random(seed)
    m = max(1, num_vars * clauses_per_var)
    clauses: List[List[int]] = []
    for _ in range(m):
        k = min(clause_size, num_vars)
        vs = rng.sample(range(1, num_vars + 1), k=k)
        # Horn: at most one positive literal.
        pos_idx = rng.randrange(len(vs))
        clause: List[int] = []
        for i, v in enumerate(vs):
            if i == pos_idx:
                clause.append(v)
            else:
                clause.append(-v if rng.random() > 0.2 else -v)
        clauses.append(clause)
    return clauses


def cmd_generate(args: argparse.Namespace) -> int:
    _require_manifest_or_fail(args.root)
    _verify_manifest_inputs(args.root)
    _require_params_match_manifest(
        args.root,
        actual={
            "sizes": list(args.sizes),
            "per_size": int(args.per_size),
            "seed_base": int(args.seed_base),
            "split_seed": int(args.split_seed),
            "test_ratio": float(args.test_ratio),
            "controls_per_size": int(getattr(args, "controls_per_size", 0)),
            "permute_pairs": int(getattr(args, "permute_pairs", 0)),
        },
    )

    root: Path = args.root
    inst_dir = root / "instances"
    inst_dir.mkdir(parents=True, exist_ok=True)

    # Primary suite: 4 families x 3 sizes x per_size seeds.
    sizes = args.sizes
    seeds = list(range(args.seed_base, args.seed_base + args.per_size))

    specs: List[InstanceSpec] = []
    for family in ("modular", "chain", "tree", "random"):
        for n_vars in sizes:
            for seed in seeds:
                modules = None
                if family == "modular":
                    modules = max(2, n_vars // 10)
                specs.append(InstanceSpec(family=family, n_vars=n_vars, seed=seed, modules=modules))

    meta_rows: List[Dict[str, Any]] = []
    for spec in specs:
        instance_id = f"{spec.family}_{spec.n_vars}_seed{spec.seed}" + (f"_m{spec.modules}" if spec.modules else "")
        out_path = inst_dir / f"{instance_id}.cnf"
        if out_path.exists() and not args.force:
            continue

        _call_generate_cnf(
            family=spec.family,
            n_vars=spec.n_vars,
            seed=spec.seed,
            modules=spec.modules,
            out_path=out_path,
        )

        n_vars, n_clauses = _parse_dimacs_counts(out_path)
        stats = _cheap_dimacs_stats(out_path)
        split = _stable_split(instance_id, split_seed=args.split_seed, test_ratio=args.test_ratio)
        meta_rows.append(
            {
                "id": instance_id,
                "family": spec.family,
                "n_vars": n_vars,
                "n_clauses": n_clauses,
                "seed": spec.seed,
                "split": split,
                "role": "primary",
                "params": {"modules": spec.modules},
                "stats": stats,
                "path": str(out_path.relative_to(root)),
                "sha256": _sha256_file(out_path),
            }
        )

    # Sanity-only controls: 2-SAT + Horn. These are not part of PASS metrics.
    if args.controls_per_size > 0:
        for n_vars in sizes:
            for k in range(args.controls_per_size):
                seed = args.seed_base + 10_000 + (n_vars * 100) + k

                cid = f"control_2sat_{n_vars}_seed{seed}"
                cpath = inst_dir / f"{cid}.cnf"
                _write_dimacs(
                    cpath,
                    n_vars,
                    _generate_2sat(n_vars, seed=seed),
                    comment="2-SAT control (sanity-only)",
                )
                meta_rows.append(
                    {
                        "id": cid,
                        "family": "2sat",
                        "n_vars": n_vars,
                        "n_clauses": _parse_dimacs_counts(cpath)[1],
                        "seed": seed,
                        "split": "control",
                        "role": "control",
                        "params": {},
                        "stats": _cheap_dimacs_stats(cpath),
                        "path": str(cpath.relative_to(root)),
                        "sha256": _sha256_file(cpath),
                    }
                )

                hid = f"control_horn_{n_vars}_seed{seed}"
                hpath = inst_dir / f"{hid}.cnf"
                _write_dimacs(
                    hpath,
                    n_vars,
                    _generate_horn(n_vars, seed=seed),
                    comment="Horn-SAT control (sanity-only)",
                )
                meta_rows.append(
                    {
                        "id": hid,
                        "family": "horn",
                        "n_vars": n_vars,
                        "n_clauses": _parse_dimacs_counts(hpath)[1],
                        "seed": seed,
                        "split": "control",
                        "role": "control",
                        "params": {},
                        "stats": _cheap_dimacs_stats(hpath),
                        "path": str(hpath.relative_to(root)),
                        "sha256": _sha256_file(hpath),
                    }
                )

    # Sanity-only permutation twins: create twins for the first N primary instances.
    if args.permute_pairs > 0:
        primary_rows = [r for r in meta_rows if r.get("role") == "primary"]
        primary_rows.sort(key=lambda r: r["id"])
        for base in primary_rows[: args.permute_pairs]:
            base_id = base["id"]
            twin_id = f"{base_id}__perm"
            src = root / Path(base["path"])
            dst = inst_dir / f"{twin_id}.cnf"
            _make_permutation_twin(src, dst, seed=args.split_seed)
            meta_rows.append(
                {
                    "id": twin_id,
                    "family": base["family"],
                    "n_vars": base["n_vars"],
                    "n_clauses": _parse_dimacs_counts(dst)[1],
                    "seed": base.get("seed"),
                    "split": base.get("split"),
                    "role": "sanity",
                    "twin_of": base_id,
                    "twin_type": "permute",
                    "params": base.get("params", {}),
                    "stats": _cheap_dimacs_stats(dst),
                    "path": str(dst.relative_to(root)),
                    "sha256": _sha256_file(dst),
                }
            )

    meta_path = inst_dir / "meta.jsonl"
    existing = _read_jsonl(meta_path) if meta_path.exists() else []
    by_id = {row["id"]: row for row in existing}
    for row in meta_rows:
        by_id[row["id"]] = row
    _write_jsonl(meta_path, [by_id[k] for k in sorted(by_id)])

    print(f"Wrote {meta_path}")
    _update_manifest_artifacts(root) if _manifest_path(root).exists() else None
    return 0


def _cnf_analyzer_report(cnf_path: Path, *, verbose: bool) -> Dict[str, Any]:
    cnf_analyzer = _load_tool_module("cnf_analyzer")
    CNFAnalyzer = getattr(cnf_analyzer, "CNFAnalyzer")

    analyzer = CNFAnalyzer(cnf_path)
    if verbose:
        analyzer.parse()
        analyzer.analyze_structure()
        analyzer.discover_partitions()
        return analyzer.report(output_path=None)

    # cnf_analyzer is intentionally chatty; keep the prereg harness output clean.
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
        analyzer.parse()
        analyzer.analyze_structure()
        analyzer.discover_partitions()
        return analyzer.report(output_path=None)


def cmd_predict(args: argparse.Namespace) -> int:
    root: Path = args.root
    inst_dir = root / "instances"
    meta_path = inst_dir / "meta.jsonl"
    if not meta_path.exists():
        raise FileNotFoundError(f"Missing instances metadata: {meta_path}")

    _require_manifest_or_fail(root)
    _verify_manifest_inputs(root)
    _require_params_match_manifest(
        root,
        actual={
            "no_solve": bool(args.no_solve),
            "permute_epsilon": float(getattr(args, "permute_epsilon", 0.01)),
        },
    )

    no_solve = bool(args.no_solve)
    blocker = _BlockZ3Imports()
    guards = _NoSolveGuards()
    if no_solve:
        blocker.enable()
        guards.enable()

    try:
        meta = _read_jsonl(meta_path)
        rows: List[Dict[str, Any]] = []
        total = len(meta)
        receipt: Dict[str, Any] = {
            "stage": "predict",
            "no_solve": no_solve,
            "git_head": _git_head_sha(REPO_ROOT),
            "tool_hashes": _tool_hashes(),
            "guards": {
                "block_z3_imports": bool(no_solve),
                "forbid_subprocess_exec": bool(no_solve),
            },
            "blocked_calls": 0,
            "env": {
                "PATH": os.environ.get("PATH"),
                "PYTHONNOUSERSITE": os.environ.get("PYTHONNOUSERSITE"),
            },
        }
        for idx, row in enumerate(meta, start=1):
            cnf_rel = Path(row["path"])
            cnf_path = root / cnf_rel
            report = _cnf_analyzer_report(cnf_path, verbose=bool(args.verbose))
            if not args.verbose:
                print(f"μ-extract {idx:>4}/{total}: {row['id']}")

            partition = report.get("partition", {})
            summary = report.get("summary", {})

            # Receipt: hash of the canonicalized report JSON.
            report_bytes = json.dumps(report, sort_keys=True).encode("utf-8")
            receipt_hash = _sha256_bytes(report_bytes)

            rows.append(
                {
                    "id": row["id"],
                    "family": row["family"],
                    "split": row.get("split"),
                    "role": row.get("role"),
                    "twin_of": row.get("twin_of"),
                    "twin_type": row.get("twin_type"),
                    "n_vars": int(summary.get("variables", row.get("n_vars", 0))),
                    "n_clauses": int(summary.get("clauses", row.get("n_clauses", 0))),
                    "mu_total": float(summary.get("mu_total", 0.0)),
                    "mu_components": {
                        "mu_discovery": float(partition.get("mu_discovery", 0.0)),
                        "mu_operational": float(partition.get("mu_operational", 0.0)),
                        "modules": int(partition.get("num_modules", 0)),
                        "interaction_density": float(partition.get("interaction_density", 0.0)),
                    },
                    "receipt_hash": receipt_hash,
                    "source": {
                        "cnf_sha256": row.get("sha256"),
                        "cnf_analyzer": "tools/cnf_analyzer.py:CNFAnalyzer",
                        "git_head": _git_head_sha(REPO_ROOT),
                        "no_solve": no_solve,
                    },
                }
            )

        out_path = root / "predictions.jsonl"
        _write_jsonl(out_path, rows)
        print(f"Wrote {out_path}")

        # Sanity falsifier 1: permutation invariance.
        if args.permute_epsilon is not None:
            by_id = {r["id"]: r for r in rows}
            for m in meta:
                if m.get("role") != "sanity" or m.get("twin_type") != "permute":
                    continue
                twin_id = m["id"]
                base_id = m.get("twin_of")
                if not base_id or base_id not in by_id or twin_id not in by_id:
                    continue
                a = float(by_id[base_id]["mu_total"])
                b = float(by_id[twin_id]["mu_total"])
                rel = abs(a - b) / max(a, b, 1e-9)
                if rel >= float(args.permute_epsilon):
                    raise RuntimeError(
                        f"Permutation invariance FAILED for {base_id} vs {twin_id}: rel_diff={rel:.6f}"
                    )

        if no_solve:
            receipt["blocked_calls"] = guards.blocked_calls
            receipt_path = root / "no_solve_receipt.json"
            receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True), encoding="utf-8")
            print(f"Wrote {receipt_path}")

        _update_manifest_artifacts(root)
        return 0
    finally:
        if no_solve:
            guards.disable()
            blocker.disable()


def _load_z3() -> Any:
    try:
        import z3  # type: ignore

        return z3
    except Exception as exc:
        raise RuntimeError(
            "z3-solver is required for the solve stage (pip install z3-solver)"
        ) from exc


def _solve_with_z3_dimacs(
    z3: Any, cnf_path: Path, timeout_s: int
) -> Tuple[str, float, float, float, bool]:
    # Minimal DIMACS -> Z3 encoding.
    cnf_analyzer = _load_tool_module("cnf_analyzer")
    DIMACSParser = getattr(cnf_analyzer, "DIMACSParser")

    t0 = time.perf_counter()
    n_vars, _, clauses = DIMACSParser.parse(cnf_path)
    vars_dict = {i: z3.Bool(f"x{i}") for i in range(1, n_vars + 1)}

    solver = z3.Solver()
    threads_set_ok = False
    try:
        # Best-effort single-thread policy (some Z3 builds may ignore or reject this).
        solver.set("threads", 1)
        threads_set_ok = True
    except Exception:
        threads_set_ok = False
    solver.set("timeout", int(timeout_s * 1000))

    for clause in clauses:
        lits = []
        for lit in clause:
            v = vars_dict[abs(lit)]
            lits.append(v if lit > 0 else z3.Not(v))
        solver.add(z3.Or(lits))

    t1 = time.perf_counter()
    res = solver.check()

    t2 = time.perf_counter()
    encode_s = t1 - t0
    check_s = t2 - t1
    total_s = t2 - t0

    if str(res) == "sat":
        status = "sat"
    elif str(res) == "unsat":
        status = "unsat"
    else:
        status = "timeout" if check_s >= timeout_s else "unknown"

    # Return total wall time used for the prereg Y (check_s is what analysis uses).
    return status, encode_s, check_s, total_s, threads_set_ok


def cmd_solve(args: argparse.Namespace) -> int:
    root: Path = args.root
    inst_dir = root / "instances"
    meta_path = inst_dir / "meta.jsonl"
    if not meta_path.exists():
        raise FileNotFoundError(f"Missing instances metadata: {meta_path}")

    _require_manifest_or_fail(root)
    _verify_manifest_inputs(root)
    _require_params_match_manifest(root, actual={"timeout_s": int(args.timeout)})

    preds_path = root / "predictions.jsonl"
    if not preds_path.exists():
        raise FileNotFoundError(
            "Missing predictions.jsonl. Prereg order requires running: "
            "predict (NO_SOLVE) → solve."
        )
    preds_sha = _sha256_file(preds_path)

    z3 = _load_z3()
    z3_version = getattr(z3, "get_version_string", lambda: "unknown")()

    out_path = root / "z3_results.csv"
    meta = _read_jsonl(meta_path)

    with out_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "id",
                "family",
                "split",
                "role",
                "encode_s",
                "check_s",
                "total_s",
                "runtime_s",
                "status",
                "timeout_s",
                "z3_threads_requested",
                "z3_threads_set_ok",
                "z3_version",
                "predictions_sha256",
            ],
        )
        writer.writeheader()
        for row in meta:
            cnf_path = root / Path(row["path"])
            status, encode_s, check_s, total_s, threads_set_ok = _solve_with_z3_dimacs(
                z3, cnf_path, timeout_s=args.timeout
            )
            writer.writerow(
                {
                    "id": row["id"],
                    "family": row["family"],
                    "split": row.get("split"),
                    "role": row.get("role"),
                    "encode_s": f"{encode_s:.6f}",
                    "check_s": f"{check_s:.6f}",
                    "total_s": f"{total_s:.6f}",
                    "runtime_s": f"{check_s:.6f}",
                    "status": status,
                    "timeout_s": str(args.timeout),
                    "z3_threads_requested": "1",
                    "z3_threads_set_ok": "1" if threads_set_ok else "0",
                    "z3_version": z3_version,
                    "predictions_sha256": preds_sha,
                }
            )

    print(f"Wrote {out_path}")
    _update_manifest_artifacts(root)
    return 0


def _ranks(xs: List[float]) -> List[float]:
    # Average ranks for ties.
    sorted_idx = sorted(range(len(xs)), key=lambda i: xs[i])
    ranks = [0.0] * len(xs)
    i = 0
    while i < len(xs):
        j = i
        while j + 1 < len(xs) and xs[sorted_idx[j + 1]] == xs[sorted_idx[i]]:
            j += 1
        avg_rank = (i + j) / 2.0 + 1.0
        for k in range(i, j + 1):
            ranks[sorted_idx[k]] = avg_rank
        i = j + 1
    return ranks


def _pearson(x: List[float], y: List[float]) -> float:
    if len(x) != len(y) or not x:
        return float("nan")
    mx = sum(x) / len(x)
    my = sum(y) / len(y)
    num = sum((a - mx) * (b - my) for a, b in zip(x, y))
    denx = math.sqrt(sum((a - mx) ** 2 for a in x))
    deny = math.sqrt(sum((b - my) ** 2 for b in y))
    if denx == 0 or deny == 0:
        return float("nan")
    return num / (denx * deny)


def _spearman(x: List[float], y: List[float]) -> float:
    return _pearson(_ranks(x), _ranks(y))


def _ols_fit(features: List[List[float]], y: List[float]) -> Tuple[List[float], float]:
    # Simple normal-equation solve via Gaussian elimination for small feature counts.
    # Adds intercept automatically.
    n = len(y)
    if n == 0:
        return [], float("nan")
    p = len(features[0]) + 1
    X = [[1.0] + features[i] for i in range(n)]

    # Build normal equations: (X^T X) beta = X^T y
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for i in range(n):
        for a in range(p):
            xty[a] += X[i][a] * y[i]
            for b in range(p):
                xtx[a][b] += X[i][a] * X[i][b]

    # Solve via Gauss-Jordan.
    aug = [xtx[r] + [xty[r]] for r in range(p)]
    for col in range(p):
        pivot = max(range(col, p), key=lambda r: abs(aug[r][col]))
        if abs(aug[pivot][col]) < 1e-12:
            continue
        aug[col], aug[pivot] = aug[pivot], aug[col]
        scale = aug[col][col]
        aug[col] = [v / scale for v in aug[col]]
        for r in range(p):
            if r == col:
                continue
            factor = aug[r][col]
            aug[r] = [rv - factor * cv for rv, cv in zip(aug[r], aug[col])]

    beta = [aug[r][-1] for r in range(p)]
    # Compute in-sample R^2
    yhat = [sum(beta[j] * X[i][j] for j in range(p)) for i in range(n)]
    my = sum(y) / n
    ss_tot = sum((yi - my) ** 2 for yi in y)
    ss_res = sum((yi - yhi) ** 2 for yi, yhi in zip(y, yhat))
    r2 = 1.0 - (ss_res / ss_tot if ss_tot > 0 else 0.0)
    return beta, r2


def _ols_predict(beta: List[float], features: List[List[float]]) -> List[float]:
    # beta includes intercept.
    if not beta:
        return [0.0 for _ in features]
    yhat: List[float] = []
    for row in features:
        x = [1.0] + row
        yhat.append(sum(beta[j] * x[j] for j in range(min(len(beta), len(x)))))
    return yhat


def _r2_score(y_true: List[float], y_pred: List[float]) -> float:
    if not y_true or len(y_true) != len(y_pred):
        return float("nan")
    my = sum(y_true) / len(y_true)
    ss_tot = sum((yi - my) ** 2 for yi in y_true)
    ss_res = sum((yi - yhi) ** 2 for yi, yhi in zip(y_true, y_pred))
    return 1.0 - (ss_res / ss_tot if ss_tot > 0 else 0.0)


def _auc(scores: List[float], labels: List[int]) -> float:
    # AUC via Mann-Whitney U (equiv to probability a positive has higher score).
    pos = [(s, i) for i, (s, l) in enumerate(zip(scores, labels)) if l == 1]
    neg = [(s, i) for i, (s, l) in enumerate(zip(scores, labels)) if l == 0]
    if not pos or not neg:
        return float("nan")
    ranks = _ranks(scores)
    sum_ranks_pos = sum(ranks[i] for _, i in pos)
    n1 = len(pos)
    n0 = len(neg)
    u1 = sum_ranks_pos - n1 * (n1 + 1) / 2.0
    return u1 / (n1 * n0)


def cmd_analyze(args: argparse.Namespace) -> int:
    root: Path = args.root
    _require_manifest_or_fail(root)
    _verify_manifest_inputs(root)
    manifest = _require_manifest(root)
    _require_params_match_manifest(
        root,
        actual={
            "hard_threshold_s": float(args.hard_threshold),
            "min_holdout_solved": int(args.min_holdout_solved),
            "min_family_holdout_solved": int(args.min_family_holdout_solved),
        },
    )

    preds_path = root / "predictions.jsonl"
    results_path = root / "z3_results.csv"
    meta_path = root / "instances" / "meta.jsonl"
    if not preds_path.exists() or not results_path.exists():
        raise FileNotFoundError("Missing predictions.jsonl or z3_results.csv; run predict and solve first")
    if not meta_path.exists():
        raise FileNotFoundError("Missing instances/meta.jsonl; run generate first")

    # Gate A: analysis must read from saved artifacts only.
    # Also verify artifact hashes match the manifest.
    current_artifacts = {
        "instances_meta_jsonl": _sha256_file(meta_path),
        "predictions_jsonl": _sha256_file(preds_path),
        "no_solve_receipt_json": _maybe_sha256_file(root / "no_solve_receipt.json"),
        "z3_results_csv": _sha256_file(results_path),
    }
    expected_artifacts = manifest.get("artifacts", {})
    for k, cur in current_artifacts.items():
        exp = expected_artifacts.get(k)
        if exp is not None and exp != cur:
            raise RuntimeError(f"Artifact hash mismatch for {k}: expected {exp}, got {cur}")

    preds_sha = current_artifacts["predictions_jsonl"]

    meta = {row["id"]: row for row in _read_jsonl(meta_path)}
    preds = {row["id"]: row for row in _read_jsonl(preds_path)}
    rows: List[Dict[str, Any]] = []
    with results_path.open("r", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        for r in reader:
            rid = r["id"]
            if rid not in preds:
                continue
            if rid not in meta:
                continue
            if r.get("predictions_sha256") and r["predictions_sha256"] != preds_sha:
                raise RuntimeError(
                    "z3_results.csv predictions_sha256 does not match current predictions.jsonl hash"
                )
            p = preds[rid]
            m = meta[rid]
            check_s = float(r.get("check_s") or r["runtime_s"])
            runtime_log = math.log10(max(check_s, 1e-6))
            split = (r.get("split") or p.get("split") or m.get("split") or "unknown")
            role = (r.get("role") or p.get("role") or m.get("role") or "unknown")
            stats = m.get("stats", {})
            rows.append(
                {
                    "id": rid,
                    "family": r["family"],
                    "split": split,
                    "role": role,
                    "mu_total": float(p["mu_total"]),
                    "n_vars": int(p["n_vars"]),
                    "n_clauses": int(p["n_clauses"]),
                    "density": float(p["mu_components"].get("interaction_density", 0.0)),
                    "modules": int(p["mu_components"].get("modules", 0)),
                    "stats": stats,
                    "check_s": check_s,
                    "log10_runtime": runtime_log,
                    "status": r["status"],
                }
            )

    if not rows:
        raise RuntimeError("No aligned rows to analyze")

    def is_solved(r: Dict[str, Any]) -> bool:
        return r.get("status") in ("sat", "unsat")

    primary = [r for r in rows if r.get("role") == "primary"]
    sanity = [r for r in rows if r.get("role") == "sanity"]
    controls = [r for r in rows if r.get("role") == "control"]

    # Gate C: holdout is defined at generation time; primary metrics are on holdout.
    train = [r for r in primary if r.get("split") == "train"]
    test = [r for r in primary if r.get("split") == "test"]
    train_solved = [r for r in train if is_solved(r)]
    test_solved = [r for r in test if is_solved(r)]

    if not test:
        raise RuntimeError("No holdout/test rows found; check split assignment in instances/meta.jsonl")

    # Correlation: solved-only (timeouts are censored data).
    mu_test = [r["mu_total"] for r in test_solved]
    logt_test = [r["log10_runtime"] for r in test_solved]
    rho_holdout_solved = _spearman(mu_test, logt_test) if test_solved else float("nan")

    # Baseline A and A+μ: fit on train_solved, score on test_solved.
    feats_a_train = [[float(r["n_vars"]), float(r["n_clauses"])] for r in train_solved]
    feats_a_test = [[float(r["n_vars"]), float(r["n_clauses"])] for r in test_solved]
    y_train = [r["log10_runtime"] for r in train_solved]
    y_test = [r["log10_runtime"] for r in test_solved]
    beta_a, _ = _ols_fit(feats_a_train, y_train) if train_solved else ([], float("nan"))
    r2_a_holdout = _r2_score(y_test, _ols_predict(beta_a, feats_a_test)) if test_solved else float("nan")

    feats_a_mu_train = [[float(r["n_vars"]), float(r["n_clauses"]), float(r["mu_total"])] for r in train_solved]
    feats_a_mu_test = [[float(r["n_vars"]), float(r["n_clauses"]), float(r["mu_total"])] for r in test_solved]
    beta_a_mu, _ = _ols_fit(feats_a_mu_train, y_train) if train_solved else ([], float("nan"))
    r2_a_mu_holdout = _r2_score(y_test, _ols_predict(beta_a_mu, feats_a_mu_test)) if test_solved else float("nan")

    # Baseline B: cheap structural stats (from meta.jsonl), fit and score like A.
    def feats_b(r: Dict[str, Any]) -> List[float]:
        s = r.get("stats", {})
        return [
            float(r["n_vars"]),
            float(r["n_clauses"]),
            float(s.get("avg_clause_len", 0.0)),
            float(s.get("var_clause_len", 0.0)),
            float(s.get("mean_degree", 0.0)),
            float(s.get("var_degree", 0.0)),
            float(s.get("horn_fraction", 0.0)),
            float(s.get("is_2sat", 0.0)),
            float(s.get("interaction_density_cheap", 0.0)),
        ]

    feats_b_train = [feats_b(r) for r in train_solved]
    feats_b_test = [feats_b(r) for r in test_solved]
    beta_b, _ = _ols_fit(feats_b_train, y_train) if train_solved else ([], float("nan"))
    r2_b_holdout = _r2_score(y_test, _ols_predict(beta_b, feats_b_test)) if test_solved else float("nan")

    feats_b_mu_train = [feats_b(r) + [float(r["mu_total"])] for r in train_solved]
    feats_b_mu_test = [feats_b(r) + [float(r["mu_total"])] for r in test_solved]
    beta_b_mu, _ = _ols_fit(feats_b_mu_train, y_train) if train_solved else ([], float("nan"))
    r2_b_mu_holdout = _r2_score(y_test, _ols_predict(beta_b_mu, feats_b_mu_test)) if test_solved else float("nan")

    # Hard/easy classification on holdout (includes timeouts).
    hard_test = [1 if (r["check_s"] >= args.hard_threshold or r["status"] == "timeout") else 0 for r in test]
    mu_test_all = [r["mu_total"] for r in test]
    auc_mu_holdout = _auc(mu_test_all, hard_test)

    # Minimum solved count gate.
    min_gate_ok = True
    min_gate_reasons: List[str] = []
    if len(test_solved) < args.min_holdout_solved:
        min_gate_ok = False
        min_gate_reasons.append(
            f"holdout_solved={len(test_solved)} < min_holdout_solved={args.min_holdout_solved}"
        )
    fam_counts: Dict[str, int] = {}
    for r in test_solved:
        fam_counts[r["family"]] = fam_counts.get(r["family"], 0) + 1
    for fam in sorted({r["family"] for r in test}):
        if fam_counts.get(fam, 0) < args.min_family_holdout_solved:
            min_gate_ok = False
            min_gate_reasons.append(
                f"family={fam} holdout_solved={fam_counts.get(fam, 0)} < min_family_holdout_solved={args.min_family_holdout_solved}"
            )

    # Sanity falsifier 2: 2-SAT/Horn controls should not be "hard".
    controls_failed: List[str] = []
    for r in controls:
        if r["status"] == "timeout" or r["check_s"] >= args.hard_threshold:
            controls_failed.append(r["id"])

    # Residuals (A+μ), holdout solved.
    residuals: List[Dict[str, Any]] = []
    if test_solved and beta_a_mu:
        pred = _ols_predict(beta_a_mu, feats_a_mu_test)
        for r, yhat in zip(test_solved, pred):
            resid = float(r["log10_runtime"]) - float(yhat)
            residuals.append(
                {
                    "id": r["id"],
                    "family": r["family"],
                    "mu_total": r["mu_total"],
                    "log10_runtime": r["log10_runtime"],
                    "pred_log10_runtime": float(yhat),
                    "residual": resid,
                }
            )
        residuals.sort(key=lambda x: abs(x["residual"]), reverse=True)
        residuals = residuals[:10]

    per_family_holdout: Dict[str, Dict[str, float]] = {}
    for family in sorted({r["family"] for r in test_solved}):
        fam_rows = [r for r in test_solved if r["family"] == family]
        per_family_holdout[family] = {
            "n": float(len(fam_rows)),
            "spearman_rho_solved": float(_spearman([r["mu_total"] for r in fam_rows], [r["log10_runtime"] for r in fam_rows])),
        }

    analysis = {
        "manifest": {
            "path": MANIFEST_NAME,
            "git_head": manifest.get("git_head"),
            "created_at": manifest.get("created_at"),
            "params": manifest.get("params"),
            "tool_hashes": manifest.get("tool_hashes"),
            "artifacts": manifest.get("artifacts"),
        },
        "counts": {
            "all": len(rows),
            "primary": len(primary),
            "sanity": len(sanity),
            "control": len(controls),
            "train": len(train),
            "test": len(test),
            "train_solved": len(train_solved),
            "test_solved": len(test_solved),
        },
        "holdout": {
            "spearman_rho_solved": rho_holdout_solved,
            "r2_baseline_a": r2_a_holdout,
            "r2_a_plus_mu": r2_a_mu_holdout,
            "r2_a_delta": r2_a_mu_holdout - r2_a_holdout,
            "r2_baseline_b": r2_b_holdout,
            "r2_b_plus_mu": r2_b_mu_holdout,
            "r2_b_delta": r2_b_mu_holdout - r2_b_holdout,
            "auc_mu_hard": auc_mu_holdout,
            "hard_threshold_s": args.hard_threshold,
            "per_family": per_family_holdout,
        },
        "gates": {
            "minimum_solved_evaluable": min_gate_ok,
            "minimum_solved_reasons": min_gate_reasons,
            "controls_all_easy": len(controls_failed) == 0,
            "controls_failed": controls_failed,
        },
        "top_residuals_holdout_solved_a_plus_mu": residuals,
        "hard_threshold_s": args.hard_threshold,
    }

    def json_sanitize(value: Any) -> Any:
        if isinstance(value, float) and (math.isnan(value) or math.isinf(value)):
            return None
        if isinstance(value, dict):
            return {k: json_sanitize(v) for k, v in value.items()}
        if isinstance(value, list):
            return [json_sanitize(v) for v in value]
        return value

    analysis = json_sanitize(analysis)

    out_path = root / "analysis.json"
    out_path.write_text(json.dumps(analysis, indent=2), encoding="utf-8")
    print(f"Wrote {out_path}")

    _update_manifest_artifacts(root)

    # Optional plot
    if args.plot:
        try:
            import matplotlib.pyplot as plt  # type: ignore
            from matplotlib.lines import Line2D  # type: ignore

            # Plot solved-only to avoid implying timeouts are exact runtime values.
            fams = sorted({r["family"] for r in test_solved})
            cmap = {fam: i for i, fam in enumerate(fams)}
            colors = [cmap[r["family"]] for r in test_solved]

            plt.figure(figsize=(7.5, 5.5))
            plt.scatter(mu_test, logt_test, c=colors, s=22, alpha=0.8)
            plt.xlabel("μ_total (discovery+operational, μ-spec v2.0)")
            plt.ylabel("log10(runtime_s)")
            plt.title("μ vs Z3 runtime (holdout solved-only)")
            if fams:
                handles = []
                labels = []
                for fam in fams:
                    idx = cmap[fam]
                    h = Line2D([0], [0], marker='o', linestyle='', color=f"C{idx % 10}")
                    handles.append(h)
                    labels.append(fam)
                plt.legend(handles=handles, labels=labels, loc="best", frameon=True, fontsize=8)
            fig_path = root / "fig_mu_vs_runtime.png"
            plt.tight_layout()
            plt.savefig(fig_path, dpi=200)
            plt.close()
            print(f"Wrote {fig_path}")
        except Exception as exc:
            print(f"Plot skipped (matplotlib unavailable): {exc}")

    # Human-readable summary
    print("\n=== μ→SAT Difficulty Summary ===")
    c = analysis["counts"]
    h = analysis["holdout"]
    print(f"Primary={c['primary']}  Holdout={c['test']}  Holdout(solved)={c['test_solved']}  Controls={c['control']}")
    g = analysis.get("gates", {})
    if not g.get("minimum_solved_evaluable", True):
        print("NOT EVALUABLE (minimum solved gate failed)")
    sr = h.get("spearman_rho_solved")
    print(f"Holdout Spearman ρ (solved-only)={sr:.3f}" if sr is not None else "Holdout Spearman ρ: n/a")
    print(
        "Holdout R²: A={:.3f}  A+μ={:.3f}  ΔA={:.3f} | B={:.3f}  B+μ={:.3f}  ΔB={:.3f}".format(
            float(h["r2_baseline_a"]),
            float(h["r2_a_plus_mu"]),
            float(h["r2_a_delta"]),
            float(h["r2_baseline_b"]),
            float(h["r2_b_plus_mu"]),
            float(h["r2_b_delta"]),
        )
    )
    auc_val = h.get("auc_mu_hard")
    if auc_val is None:
        print(f"Holdout AUC(hard) from μ=n/a (need both hard and easy samples; hard if runtime≥{args.hard_threshold}s or timeout)")
    else:
        print(f"Holdout AUC(hard) from μ={float(auc_val):.3f} (hard if runtime≥{args.hard_threshold}s or timeout)")
    if h.get("per_family"):
        print("Holdout per-family ρ (solved-only):")
        for family, payload in h["per_family"].items():
            val = payload.get("spearman_rho_solved")
            if val is None:
                print(f"  {family}: ρ=n/a (n={int(payload['n'])})")
            else:
                print(f"  {family}: ρ={float(val):.3f} (n={int(payload['n'])})")

    if not g.get("controls_all_easy", True):
        print(f"CONTROL FAIL: hard controls={len(g.get('controls_failed', []))}")

    if not g.get("minimum_solved_evaluable", True):
        for reason in g.get("minimum_solved_reasons", []) or []:
            print(f"  gate: {reason}")
        return 1
    if not g.get("controls_all_easy", True):
        return 1

    return 0


def cmd_init(args: argparse.Namespace) -> int:
    """Create a binding MANIFEST.json without running the pipeline."""

    root: Path = args.root
    manifest_path = _manifest_path(root)
    if manifest_path.exists() and not args.overwrite:
        raise RuntimeError(
            f"{MANIFEST_NAME} already exists at {manifest_path}. "
            "Choose a new --root or pass --overwrite to replace the run."
        )

    params = {
        "sizes": list(args.sizes),
        "per_size": int(args.per_size),
        "seed_base": int(args.seed_base),
        "split_seed": int(args.split_seed),
        "test_ratio": float(args.test_ratio),
        "controls_per_size": int(getattr(args, "controls_per_size", 0)),
        "permute_pairs": int(getattr(args, "permute_pairs", 0)),
        "permute_epsilon": float(getattr(args, "permute_epsilon", 0.01)),
        "timeout_s": int(args.timeout),
        "hard_threshold_s": float(args.hard_threshold),
        "min_holdout_solved": int(getattr(args, "min_holdout_solved", 20)),
        "min_family_holdout_solved": int(getattr(args, "min_family_holdout_solved", 5)),
        "no_solve": bool(args.no_solve),
        "isolate_no_solve": bool(args.isolate_no_solve),
    }
    _init_manifest(root, params=params)
    print(f"Wrote {_manifest_path(root)}")
    return 0


def cmd_run(args: argparse.Namespace) -> int:
    # One-shot convenience: manifest → generate → predict → solve → analyze.
    root: Path = args.root
    manifest_path = _manifest_path(root)
    if manifest_path.exists() and not args.overwrite:
        raise RuntimeError(
            f"{MANIFEST_NAME} already exists at {manifest_path}. "
            "Choose a new --root or pass --overwrite to replace the run."
        )

    params = {
        "sizes": list(args.sizes),
        "per_size": int(args.per_size),
        "seed_base": int(args.seed_base),
        "split_seed": int(args.split_seed),
        "test_ratio": float(args.test_ratio),
        "controls_per_size": int(getattr(args, "controls_per_size", 0)),
        "permute_pairs": int(getattr(args, "permute_pairs", 0)),
        "permute_epsilon": float(getattr(args, "permute_epsilon", 0.01)),
        "timeout_s": int(args.timeout),
        "hard_threshold_s": float(args.hard_threshold),
        "min_holdout_solved": int(getattr(args, "min_holdout_solved", 20)),
        "min_family_holdout_solved": int(getattr(args, "min_family_holdout_solved", 5)),
        "no_solve": bool(args.no_solve),
        "isolate_no_solve": bool(args.isolate_no_solve),
    }
    _init_manifest(root, params=params)

    cmd_generate(args)

    if args.no_solve and args.isolate_no_solve:
        # Gate B option (1): run μ extraction in a subprocess with sanitized PATH.
        env = os.environ.copy()
        env["PYTHONNOUSERSITE"] = "1"
        env["PATH"] = ""  # prevent calling external solvers even if code tried
        cmd = [
            sys.executable,
            str(REPO_ROOT / "tools" / "mu_sat_difficulty_scale.py"),
            "--root",
            str(root),
            "predict",
            "--no-solve",
            "--permute-epsilon",
            str(args.permute_epsilon),
        ]
        if args.verbose:
            cmd.append("--verbose")
        subprocess.run(cmd, cwd=str(REPO_ROOT), env=env, check=True)
    else:
        cmd_predict(args)

    cmd_solve(args)
    cmd_analyze(args)
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Pre-registered μ→SAT difficulty experiment")
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT, help="Output root directory")
    parser.add_argument("--overwrite", action="store_true", help="Overwrite an existing run at --root")

    sub = parser.add_subparsers(dest="cmd", required=True)

    p_init = sub.add_parser("init", help="Write binding MANIFEST.json")
    p_init.add_argument("--sizes", type=int, nargs="+", default=[20, 30, 40])
    p_init.add_argument("--per-size", type=int, default=15)
    p_init.add_argument("--seed-base", type=int, default=1000)
    p_init.add_argument("--split-seed", type=int, default=7)
    p_init.add_argument("--test-ratio", type=float, default=0.25)
    p_init.add_argument("--timeout", type=int, default=5)
    p_init.add_argument("--hard-threshold", type=float, default=1.0)
    p_init.add_argument("--controls-per-size", type=int, default=2)
    p_init.add_argument("--permute-pairs", type=int, default=10)
    p_init.add_argument("--permute-epsilon", type=float, default=0.01)
    p_init.add_argument("--min-holdout-solved", type=int, default=20)
    p_init.add_argument("--min-family-holdout-solved", type=int, default=5)
    p_init.add_argument("--no-solve", action="store_true")
    p_init.add_argument("--verbose", action="store_true")
    p_init.add_argument("--isolate-no-solve", action=argparse.BooleanOptionalAction, default=True)
    p_init.set_defaults(func=cmd_init)

    p_gen = sub.add_parser("generate", help="Generate instance families")
    p_gen.add_argument("--sizes", type=int, nargs="+", default=[20, 30, 40], help="Variable counts")
    p_gen.add_argument("--per-size", type=int, default=15, help="Instances per size per family")
    p_gen.add_argument("--seed-base", type=int, default=1000)
    p_gen.add_argument("--split-seed", type=int, default=7)
    p_gen.add_argument("--test-ratio", type=float, default=0.25)
    p_gen.add_argument("--controls-per-size", type=int, default=2)
    p_gen.add_argument("--permute-pairs", type=int, default=10)
    p_gen.add_argument("--force", action="store_true")
    p_gen.set_defaults(func=cmd_generate)

    p_pred = sub.add_parser("predict", help="Compute μ predictions (solver-free)")
    p_pred.add_argument("--no-solve", action="store_true", help="Forbid importing z3 during μ extraction")
    p_pred.add_argument("--verbose", action="store_true", help="Show full cnf_analyzer output")
    p_pred.add_argument("--permute-epsilon", type=float, default=0.01)
    p_pred.set_defaults(func=cmd_predict)

    p_solve = sub.add_parser("solve", help="Run Z3 baseline runtimes")
    p_solve.add_argument("--timeout", type=int, default=5)
    p_solve.set_defaults(func=cmd_solve)

    p_an = sub.add_parser("analyze", help="Analyze μ vs runtime")
    p_an.add_argument("--hard-threshold", type=float, default=1.0)
    p_an.add_argument("--min-holdout-solved", type=int, default=20)
    p_an.add_argument("--min-family-holdout-solved", type=int, default=5)
    p_an.add_argument("--plot", action="store_true", default=True)
    p_an.set_defaults(func=cmd_analyze)

    p_run = sub.add_parser("run", help="generate→predict→solve→analyze")
    p_run.add_argument("--sizes", type=int, nargs="+", default=[20, 30, 40])
    p_run.add_argument("--per-size", type=int, default=15)
    p_run.add_argument("--seed-base", type=int, default=1000)
    p_run.add_argument("--split-seed", type=int, default=7)
    p_run.add_argument("--test-ratio", type=float, default=0.25)
    p_run.add_argument("--controls-per-size", type=int, default=2)
    p_run.add_argument("--permute-pairs", type=int, default=10)
    p_run.add_argument("--force", action="store_true")
    p_run.add_argument("--no-solve", action="store_true")
    p_run.add_argument("--isolate-no-solve", action=argparse.BooleanOptionalAction, default=True)
    p_run.add_argument("--verbose", action="store_true")
    p_run.add_argument("--timeout", type=int, default=5)
    p_run.add_argument("--hard-threshold", type=float, default=1.0)
    p_run.add_argument("--min-holdout-solved", type=int, default=20)
    p_run.add_argument("--min-family-holdout-solved", type=int, default=5)
    p_run.add_argument("--permute-epsilon", type=float, default=0.01)
    p_run.add_argument("--plot", action="store_true", default=True)
    p_run.set_defaults(func=cmd_run)

    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
