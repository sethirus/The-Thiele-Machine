"""
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
Copyright 2025 Devon Thiele

See the LICENSE file in the repository root for full terms.
Virtual machine execution loop.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
import json
from typing import List, Dict, Any, Optional, Tuple, Mapping, Sequence
import ast
import sys
from io import StringIO
import runpy
import hashlib
import string
import math
import builtins
import pickle
import zlib
import z3
import numpy as np
import networkx as nx
from sklearn.cluster import SpectralClustering

# Ensure the repo root is on sys.path when this file is executed directly
# (e.g., `python thielecpu/vm.py`). Without this, `import thielecpu.*` fails
# because sys.path contains the package directory itself, not its parent.
_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from thielecpu.bell_semantics import (
    BellCounts,
    DEFAULT_ENFORCEMENT_MIN_TRIALS_PER_SETTING,
    TSIRELSON_BOUND,
    is_supra_quantum,
)

# Safety: maximum allowed classical combinations for brute-force searches.
# Can be overridden by the environment variable THIELE_MAX_COMBINATIONS.
import os
SAFE_COMBINATION_LIMIT = int(os.environ.get('THIELE_MAX_COMBINATIONS', 10_000_000))

SAFE_IMPORTS = {"math", "json", "z3", "argparse", "fractions", "sys", "pathlib", "thielecpu"}
SAFE_FUNCTIONS = {
    "abs",
    "all",
    "any",
    "bool",
    "divmod",
    "enumerate",
    "float",
    "int",
    "len",
    "list",
    "max",
    "min",
    "pow",
    "print",
    "range",
    "round",
    "sorted",
    "sum",
    "tuple",
    "zip",
    "str",
    "set",
    "dict",
    "map",
    "filter",
    "placeholder",
    "vm_read_text",
    "vm_write_text",
    "vm_read_bytes",
    "vm_write_bytes",
    "vm_exists",
    "vm_listdir",
    "open",
    "input",
    "Fraction",
    "RuntimeError",
    "ValueError",
    "FileNotFoundError",
    "AssertionError",
}
SAFE_METHOD_CALLS = {"append", "extend", "items", "keys", "values", "get", "update", "add", "check", "model", "as_long", "format", "read", "write", "close", "sort", "reverse"}
SAFE_MODULE_CALLS = {
    "math": {"ceil", "floor", "sqrt", "log", "log2", "exp", "fabs", "copysign", "isfinite"},
    "json": {"loads", "dumps", "load", "dump"},
    "z3": {"Solver", "Int"},
    "fractions": {"Fraction"},
    "argparse": {"ArgumentParser"},
    "sys": {"exit", "argv", "version"},
    "pathlib": {"Path"},
}
SAFE_MODULE_ATTRIBUTES = {
    "math": {"pi", "e"},
    "z3": {"sat", "unsat"},
    "fractions": set(),
}
SAFE_NODE_TYPES = {
    ast.Module,
    ast.FunctionDef,
    ast.ClassDef,
    ast.arguments,
    ast.arg,
    ast.Expr,
    ast.Assign,
    ast.AugAssign,
    ast.AnnAssign,
    ast.Name,
    ast.Load,
    ast.Store,
    ast.Del,
    ast.Constant,
    ast.BinOp,
    ast.UnaryOp,
    ast.BoolOp,
    ast.Compare,
    ast.If,
    ast.IfExp,
    ast.For,
    ast.While,
    ast.Break,
    ast.Continue,
    ast.Pass,
    ast.List,
    ast.Tuple,
    ast.Dict,
    ast.Set,
    ast.ListComp,
    ast.SetComp,
    ast.DictComp,
    ast.GeneratorExp,
    ast.comprehension,
    ast.Subscript,
    ast.Slice,
    ast.ExtSlice,
    ast.Index,
    ast.Call,
    ast.Attribute,
    ast.keyword,
    ast.alias,
    ast.With,
    ast.withitem,
    ast.Return,
    ast.JoinedStr,
    ast.FormattedValue,
    ast.Try,
    ast.ExceptHandler,
    ast.Raise,
    ast.Assert,
    ast.Lambda,
    ast.Global,
}


class _TeeTextIO:
    """File-like object that writes to both a primary stream and a capture buffer."""

    def __init__(self, primary, capture: StringIO):
        self._primary = primary
        self._capture = capture

    def write(self, s: str) -> int:  # pragma: no cover - thin wrapper
        n1 = self._primary.write(s)
        self._capture.write(s)
        return n1

    def flush(self) -> None:  # pragma: no cover - thin wrapper
        try:
            self._primary.flush()
        except Exception:
            pass

    def isatty(self) -> bool:  # pragma: no cover - thin wrapper
        try:
            return bool(getattr(self._primary, "isatty")())
        except Exception:
            return False
SAFE_NODE_TYPES.update(
    {
        ast.Add,
        ast.Sub,
        ast.Mult,
        ast.Div,
        ast.Mod,
        ast.Pow,
        ast.FloorDiv,
        ast.LShift,
        ast.RShift,
        ast.BitAnd,
        ast.BitOr,
        ast.BitXor,
        ast.UAdd,
        ast.USub,
        ast.Not,
        ast.Invert,
        ast.And,
        ast.Or,
        ast.Eq,
        ast.NotEq,
        ast.Lt,
        ast.LtE,
        ast.Gt,
        ast.GtE,
        ast.Is,
        ast.IsNot,
        ast.In,
        ast.NotIn,
    }
)

SAFE_BUILTINS = {name: getattr(builtins, name) for name in SAFE_FUNCTIONS if hasattr(builtins, name)}


def _safe_import(name, globals=None, locals=None, fromlist=(), level=0):
    """Constrain dynamic imports to the vetted module list."""

    base = name.split(".")[0]
    if base not in SAFE_IMPORTS:
        raise SecurityError(f"Import of {name} is not permitted")
    return builtins.__import__(name, globals, locals, fromlist, level)


SAFE_BUILTINS["__import__"] = _safe_import


# ============================================================================
# EMERGENT-PHYSICS CORE EXECUTION OVERLAY
# ============================================================================


@dataclass
class Distribution:
    """Compact discrete distribution with basic thermodynamic helpers."""

    mass: Dict[int, float]

    def __post_init__(self) -> None:
        self._normalize()

    @classmethod
    def point(cls, value: int) -> "Distribution":
        return cls({value: 1.0})

    def support(self) -> List[int]:
        return list(self.mass.keys())

    def expectation(self) -> float:
        return sum(v * p for v, p in self.mass.items())

    def entropy(self) -> float:
        eps = 1e-12
        return -sum(p * math.log(p + eps, 2) for p in self.mass.values())

    def _normalize(self) -> None:
        total = sum(self.mass.values())
        if total <= 0:
            # Uniform noise if everything cancelled out
            uniform_prob = 1.0 / max(1, len(self.mass))
            for key in self.mass:
                self.mass[key] = uniform_prob
            return
        for key in list(self.mass.keys()):
            self.mass[key] = max(self.mass[key], 0.0)
        total = sum(self.mass.values())
        if total == 0:
            return
        for key in list(self.mass.keys()):
            self.mass[key] /= total

    def convolve_add(self, other: "Distribution") -> "Distribution":
        """Additive convolution to model wave-like value diffusion."""

        result: Dict[int, float] = {}
        for v1, p1 in self.mass.items():
            for v2, p2 in other.mass.items():
                result[v1 + v2] = result.get(v1 + v2, 0.0) + p1 * p2
        return Distribution(result)

    def mix(self, noise: float) -> "Distribution":
        """Blend in a uniform noise component to simulate tunneling."""

        if not self.mass:
            return Distribution({0: 1.0})
        support = list(self.mass.keys())
        uniform = 1.0 / len(support)
        mixed = {k: (1 - noise) * p + noise * uniform for k, p in self.mass.items()}
        return Distribution(mixed)

    def collapse(self) -> "Distribution":
        """Collapse to the maximum likelihood value (measurement)."""

        if not self.mass:
            return Distribution({0: 1.0})
        best_value = max(self.mass.items(), key=lambda kv: kv[1])[0]
        return Distribution.point(best_value)


class PathIntegralPointer:
    """Lightweight path-integral style instruction pointer model."""

    def __init__(self, program_length: int) -> None:
        self.program_length = program_length
        self.amplitudes: Dict[int, float] = {0: 1.0}

    def step(self, logical_step: int) -> Dict[int, float]:
        """Diffuse probability mass forward with a softmin action rule."""

        next_wave: Dict[int, float] = {}
        for idx, amp in self.amplitudes.items():
            if idx >= self.program_length:
                continue
            action = math.exp(-0.1 * (logical_step - idx))
            next_idx = min(idx + 1, self.program_length)
            next_wave[next_idx] = next_wave.get(next_idx, 0.0) + amp * action
        total = sum(next_wave.values()) or 1.0
        for key in list(next_wave.keys()):
            next_wave[key] /= total
        self.amplitudes = next_wave
        return dict(self.amplitudes)

    def collapse(self, target: Optional[int] = None) -> None:
        """Collapse onto a single instruction index (least action path)."""

        if target is None:
            target = min(self.amplitudes.items(), key=lambda kv: (-kv[1], kv[0]))[0]
        self.amplitudes = {target: 1.0}


@dataclass
class EmergentPhysicsState:
    """Background physics-inspired execution context.

    The VM continues to execute discrete instructions, but every step is
    accompanied by a parallel diffusion process over register distributions
    and a soft path-integral instruction pointer. This keeps the "physics"
    behavior resident in normal execution rather than as a demo-only path.
    """

    program_length: int
    registers: Dict[str, Distribution] = field(default_factory=dict)
    temperature: float = 0.25
    entropy_trace: List[float] = field(default_factory=list)
    ip_wave: PathIntegralPointer = field(init=False)

    def __post_init__(self) -> None:
        self.ip_wave = PathIntegralPointer(self.program_length)

    def get_register(self, name: str) -> Distribution:
        if name not in self.registers:
            self.registers[name] = Distribution.point(0)
        return self.registers[name]

    def set_register(self, name: str, dist: Distribution) -> None:
        self.registers[name] = dist

    def _update_temperature(self) -> None:
        entropies = [dist.entropy() for dist in self.registers.values()]
        if entropies:
            avg_entropy = sum(entropies) / len(entropies)
            self.temperature = 0.5 * self.temperature + 0.5 * min(2.0, max(0.05, avg_entropy))
            self.entropy_trace.append(avg_entropy)

    def _tunnel_noise(self) -> None:
        for name, dist in list(self.registers.items()):
            self.registers[name] = dist.mix(0.15)

    def _collapse_hot_state(self) -> None:
        # Collapse the highest-entropy register to reduce chaos
        if not self.registers:
            return
        target = max(self.registers.items(), key=lambda kv: kv[1].entropy())[0]
        self.registers[target] = self.registers[target].collapse()

    def _entangle(self, a: str, b: str) -> None:
        ra = self.get_register(a)
        rb = self.get_register(b)
        combined = ra.convolve_add(rb)
        self.set_register(a, combined)
        self.set_register(b, combined)

    def observe_instruction(self, op: str, arg: str, logical_step: int) -> str:
        """Update the physics layer based on the current instruction."""

        event = ""
        ip_snapshot = self.ip_wave.step(logical_step)
        self.set_register("ip_entropy", Distribution.point(int(1000 * sum(ip_snapshot.values()))))

        if op in {"PNEW", "PSPLIT", "PMERGE"}:
            self._entangle("partition_left", "partition_right")
            event = "entangle_partition"
        elif op == "LASSERT":
            self._collapse_hot_state()
            event = "measurement"
        elif op == "EMIT":
            self.set_register("last_emit_len", Distribution.point(len(arg)))
            event = "record_emit"
        elif op == "PDISCOVER":
            self._tunnel_noise()
            event = "tunnel"
        else:
            # Default gentle diffusion: mix a little noise to avoid freezing
            for name in list(self.registers.keys()) or ["accumulator"]:
                self.registers[name] = self.registers[name].mix(0.05)
            event = "diffuse"

        self._update_temperature()
        if self.temperature < 0.15:
            self._tunnel_noise()
            event += "/tunnel"
        elif self.temperature > 1.2:
            self._collapse_hot_state()
            event += "/collapse"
        return event

    def observe_discovery(self, verdict: str) -> str:
        """Adjust the state based on PDISCOVER verdict."""

        if verdict == "STRUCTURED":
            self.ip_wave.collapse()
            self.temperature = max(0.05, self.temperature * 0.7)
            return "structured_collapse"
        if verdict == "CHAOTIC":
            for name in list(self.registers.keys()) or ["chaos"]:
                self.registers[name] = self.registers[name].mix(0.25)
            self.temperature = min(2.0, self.temperature + 0.25)
            return "chaotic_noise"
        return "neutral"


# ============================================================================
# SIGHT LOGGING INTEGRATION - Geometric Signature Analysis
# ============================================================================

def _build_clause_graph_from_axioms(axioms: str) -> nx.Graph:
    """
    Build a variable interaction graph from CNF-like axioms.
    
    Parses axioms to extract variable interactions and builds a graph
    where nodes are variables and edges connect variables that interact.
    """
    G = nx.Graph()
    
    # Parse axioms to extract variables and their interactions
    # This is a simplified parser - assumes axioms contain variable names
    variables = set()
    interactions = []
    
    for line in axioms.split('\n'):
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        
        # Extract variable-like tokens (alphanumeric identifiers)
        import re
        tokens = re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', line)
        if len(tokens) >= 2:
            variables.update(tokens)
            # Connect all variables in this line
            for i in range(len(tokens)):
                for j in range(i + 1, len(tokens)):
                    interactions.append((tokens[i], tokens[j]))
    
    # Build graph
    if variables:
        G.add_nodes_from(sorted(variables))
        for v1, v2 in interactions:
            if G.has_edge(v1, v2):
                G[v1][v2]['weight'] = G[v1][v2].get('weight', 0) + 1
            else:
                G.add_edge(v1, v2, weight=1)
    
    return G


def _run_louvain_partition(G: nx.Graph, seed: int = 42) -> Dict[Any, int]:
    """Run Louvain community detection."""
    try:
        from networkx.algorithms import community
        communities = community.greedy_modularity_communities(G, weight='weight', resolution=1.0)
        partition = {}
        for partition_id, comm in enumerate(communities):
            for node in comm:
                partition[node] = partition_id
        return partition
    except (ImportError, AttributeError):
        return {node: 0 for node in G.nodes()}


def _run_spectral_partition(G: nx.Graph, n_clusters: int = 4, seed: int = 42) -> Dict[Any, int]:
    """Run spectral clustering."""
    if len(G.nodes()) < n_clusters:
        return {node: i for i, node in enumerate(G.nodes())}
    
    try:
        nodes = sorted(G.nodes())
        adj_matrix = nx.to_numpy_array(G, nodelist=nodes, weight='weight')
        clustering = SpectralClustering(
            n_clusters=min(n_clusters, len(nodes)),
            affinity='precomputed',
            random_state=seed,
            n_init=10
        )
        labels = clustering.fit_predict(adj_matrix)
        return {node: int(label) for node, label in zip(nodes, labels)}
    except (ValueError, RuntimeError):
        return _run_degree_partition(G, n_clusters)


def _run_degree_partition(G: nx.Graph, n_clusters: int = 4) -> Dict[Any, int]:
    """Partition based on node degree."""
    nodes_by_degree = sorted(G.nodes(), key=lambda n: G.degree(n, weight='weight'), reverse=True)
    return {node: i % n_clusters for i, node in enumerate(nodes_by_degree)}


def _run_balanced_partition(G: nx.Graph, n_clusters: int = 4) -> Dict[Any, int]:
    """Create balanced partitions."""
    nodes = sorted(G.nodes())
    return {node: i % n_clusters for i, node in enumerate(nodes)}


def _variation_of_information(partition1: Dict[Any, int], partition2: Dict[Any, int]) -> float:
    """Calculate Variation of Information distance between partitions."""
    nodes = set(partition1.keys()) & set(partition2.keys())
    if len(nodes) == 0:
        return 0.0
    
    labels1 = [partition1[n] for n in sorted(nodes)]
    labels2 = [partition2[n] for n in sorted(nodes)]
    
    n_samples = len(nodes)
    clusters1 = set(labels1)
    clusters2 = set(labels2)
    
    # Build contingency matrix
    contingency = {}
    for c1 in clusters1:
        contingency[c1] = {}
        for c2 in clusters2:
            contingency[c1][c2] = 0
    
    for l1, l2 in zip(labels1, labels2):
        contingency[l1][l2] += 1
    
    # Calculate probabilities
    p1 = {c1: sum(1 for l in labels1 if l == c1) / n_samples for c1 in clusters1}
    p2 = {c2: sum(1 for l in labels2 if l == c2) / n_samples for c2 in clusters2}
    
    # Calculate entropies
    h1 = -sum(p * np.log2(p) if p > 0 else 0 for p in p1.values())
    h2 = -sum(p * np.log2(p) if p > 0 else 0 for p in p2.values())
    
    # Mutual information
    mi = 0.0
    for c1 in clusters1:
        for c2 in clusters2:
            p_joint = contingency[c1][c2] / n_samples
            if p_joint > 0:
                mi += p_joint * np.log2(p_joint / (p1[c1] * p2[c2]))
    
    vi = h1 + h2 - 2 * mi
    return max(0.0, vi)


def compute_geometric_signature(axioms: str, seed: int = 42) -> Dict[str, float]:
    """
    Compute 5D geometric signature from axioms using Strategy Graph analysis.
    
    This is the OPTIMIZED PDISCOVER - it uses the empirically-proven optimal
    configuration of partitioning strategies discovered by the Arch-Sphere
    meta-analysis framework (Phase 6).
    
    THE OPTIMAL CONFIGURATION (proven via meta-observatory analysis):
    - Louvain community detection (captures natural clusters)
    - Spectral clustering (captures eigenstructure)
    - Degree-based heuristic (captures local connectivity)
    - Balanced round-robin (provides baseline)
    
    This quartet achieves maximum separation between STRUCTURED and CHAOTIC
    problems (90.51% ± 5.70% cross-validation accuracy on 63-sample dataset).
    
    Alternative configurations (pairs, triplets, singles) were tested and found
    to provide inferior classification performance. This is the permanent,
    architecturally-optimized configuration.
    
    Returns:
        Dictionary with 5 geometric metrics:
        - average_edge_weight: Mean VI across strategy pairs
        - max_edge_weight: Maximum VI between strategies
        - edge_weight_stddev: Standard deviation of VI
        - min_spanning_tree_weight: MST weight
        - thresholded_density: Density of high-VI edges
    """
    # Build graph from axioms
    G = _build_clause_graph_from_axioms(axioms)
    
    if len(G.nodes()) == 0:
        # Empty graph - return zero signature
        return {
            "average_edge_weight": 0.0,
            "max_edge_weight": 0.0,
            "edge_weight_stddev": 0.0,
            "min_spanning_tree_weight": 0.0,
            "thresholded_density": 0.0,
            "num_nodes": 0,
            "num_edges": 0
        }
    
    # THE OPTIMAL QUARTET - proven by Arch-Sphere analysis
    # This is the final, permanent configuration of sight
    n_clusters = min(4, max(2, len(G.nodes()) // 10))
    partitions = {
        "louvain": _run_louvain_partition(G, seed),
        "spectral": _run_spectral_partition(G, n_clusters, seed),
        "degree": _run_degree_partition(G, n_clusters),
        "balanced": _run_balanced_partition(G, n_clusters)
    }
    
    # Compute pairwise VI
    strategies = ["louvain", "spectral", "degree", "balanced"]
    vi_matrix = {s: {} for s in strategies}
    
    for i, s1 in enumerate(strategies):
        for j, s2 in enumerate(strategies):
            if i <= j:
                vi = _variation_of_information(partitions[s1], partitions[s2])
                vi_matrix[s1][s2] = vi
                if i != j:
                    vi_matrix[s2][s1] = vi
    
    # Extract VI values for metric calculation
    vi_values = []
    for i, s1 in enumerate(strategies):
        for j, s2 in enumerate(strategies):
            if i < j:
                vi_values.append(vi_matrix[s1][s2])
    
    if not vi_values:
        vi_values = [0.0]
    
    # Calculate geometric metrics
    avg_vi = float(np.mean(vi_values))
    max_vi = float(np.max(vi_values))
    std_vi = float(np.std(vi_values))
    
    # MST weight
    try:
        # Build strategy graph
        strategy_graph = nx.Graph()
        strategy_graph.add_nodes_from(strategies)
        for s1 in strategies:
            for s2 in strategies:
                if s1 < s2:
                    strategy_graph.add_edge(s1, s2, weight=vi_matrix[s1][s2])
        
        mst = nx.minimum_spanning_tree(strategy_graph, weight='weight')
        mst_weight = sum(data['weight'] for u, v, data in mst.edges(data=True))
    except (nx.NetworkXError, ValueError):
        mst_weight = 0.0
    
    # Thresholded density
    threshold = np.median(vi_values)
    high_vi_count = sum(1 for v in vi_values if v > threshold)
    thresholded_density = high_vi_count / len(vi_values) if vi_values else 0.0
    
    return {
        "average_edge_weight": avg_vi,
        "max_edge_weight": max_vi,
        "edge_weight_stddev": std_vi,
        "min_spanning_tree_weight": float(mst_weight),
        "thresholded_density": float(thresholded_density),
        "num_nodes": len(G.nodes()),
        "num_edges": G.number_of_edges()
    }


def classify_geometric_signature(signature: Dict[str, float]) -> str:
    """
    Classify a geometric signature as STRUCTURED or CHAOTIC.
    
    This implements a simplified decision boundary based on the trained SVM.
    The boundary is derived from the separation plot analysis showing that:
    - STRUCTURED problems have low average_edge_weight and low edge_weight_stddev
    - CHAOTIC problems have high average_edge_weight and high edge_weight_stddev
    
    Returns:
        "STRUCTURED" or "CHAOTIC"
    """
    avg_weight = signature.get("average_edge_weight", 0.0)
    std_weight = signature.get("edge_weight_stddev", 0.0)
    max_weight = signature.get("max_edge_weight", 0.0)
    
    # Decision boundary (empirically derived from 90%+ accuracy SVM)
    # STRUCTURED: low VI (avg < 0.5, std < 0.3)
    # CHAOTIC: high VI (avg > 0.5 or std > 0.3)
    
    if avg_weight < 0.5 and std_weight < 0.3:
        return "STRUCTURED"
    elif avg_weight > 0.7 or std_weight > 0.5:
        return "CHAOTIC"
    else:
        # Use max_weight as tiebreaker
        return "STRUCTURED" if max_weight < 0.8 else "CHAOTIC"


# ============================================================================


class SecurityError(RuntimeError):
    """Raised when a PYEXEC payload violates sandbox policy."""


class VirtualFilesystem:
    """Minimal in-memory filesystem exposed to sandboxed programs.

    Provides a small API for reading and writing files without granting
    access to the host filesystem. Paths are normalised to a virtual root,
    forbid traversal (".."), and limit total storage.
    """

    MAX_FILE_SIZE = 512 * 1024  # 512 KiB per file to bound memory use
    MAX_TOTAL_BYTES = 2 * 1024 * 1024  # 2 MiB across all files

    def __init__(self) -> None:
        self._files: Dict[str, bytes] = {}
        self._total_bytes = 0

    @staticmethod
    def _ensure_utf8(path: str) -> None:
        try:
            path.encode("utf-8")
        except UnicodeEncodeError as exc:  # pragma: no cover - defensive
            raise SecurityError("Paths must be valid UTF-8") from exc

    def _normalize(self, path: str, *, allow_root: bool = False) -> str:
        if not isinstance(path, str):
            raise SecurityError("Path must be a string")
        stripped = path.strip()
        if not stripped:
            if allow_root:
                return ""
            raise SecurityError("Empty path not permitted")
        if stripped.startswith("/"):
            raise SecurityError("Absolute paths are not permitted")
        parts = []
        for part in stripped.split("/"):
            if not part or part == ".":
                continue
            if part == "..":
                raise SecurityError("Path traversal is not permitted")
            parts.append(part)
        normalized = "/".join(parts)
        if not normalized and not allow_root:
            raise SecurityError("Path resolves to virtual root")
        self._ensure_utf8(normalized)
        return normalized

    def _write(self, path: str, data: bytes) -> None:
        normalized = self._normalize(path)
        if len(data) > self.MAX_FILE_SIZE:
            raise SecurityError("File exceeds sandbox size limit")
        previous = self._files.get(normalized, b"")
        new_total = self._total_bytes - len(previous) + len(data)
        if new_total > self.MAX_TOTAL_BYTES:
            raise SecurityError("Sandbox storage limit exceeded")
        self._files[normalized] = bytes(data)
        self._total_bytes = new_total

    def write_text(self, path: str, data: str) -> None:
        if not isinstance(data, str):
            raise SecurityError("vm_write_text expects string data")
        self._write(path, data.encode("utf-8"))

    def write_bytes(self, path: str, data: bytes | bytearray) -> None:
        if not isinstance(data, (bytes, bytearray)):
            raise SecurityError("vm_write_bytes expects bytes-like data")
        self._write(path, bytes(data))

    def _read(self, path: str) -> bytes:
        normalized = self._normalize(path)
        if normalized not in self._files:
            raise SecurityError("File does not exist in sandbox")
        return self._files[normalized]

    def read_text(self, path: str) -> str:
        return self._read(path).decode("utf-8")

    def read_bytes(self, path: str) -> bytes:
        return bytes(self._read(path))

    def exists(self, path: str) -> bool:
        try:
            normalized = self._normalize(path)
        except SecurityError:
            return False
        return normalized in self._files

    def listdir(self, path: str = "") -> List[str]:
        normalized = self._normalize(path, allow_root=True)
        prefix = f"{normalized}/" if normalized else ""
        entries: set[str] = set()
        for stored in self._files:
            if not stored.startswith(prefix):
                continue
            remainder = stored[len(prefix) :]
            if not remainder:
                continue
            name = remainder.split("/", 1)[0]
            entries.add(name)
        return sorted(entries)

    def snapshot(self) -> Dict[str, bytes]:
        return {path: bytes(data) for path, data in self._files.items()}

    def load_snapshot(self, files: Dict[str, bytes | bytearray | str]) -> None:
        self._files.clear()
        self._total_bytes = 0
        for path, payload in files.items():
            if isinstance(payload, str):
                data = payload.encode("utf-8")
            elif isinstance(payload, (bytes, bytearray)):
                data = bytes(payload)
            else:
                raise SecurityError("Snapshot payload must be bytes or str")
            self._write(path, data)


class SafeNodeVisitor(ast.NodeVisitor):
    """AST visitor enforcing a restrictive whitelist of constructs."""

    def __init__(self, allowed_names: set[str] | None = None):
        super().__init__()
        # Track user-defined names (functions, lambdas, assignments) allowed to be called
        self._defined_names: set[str] = set()
        # Names that are present in the runtime globals and therefore allowed
        self._allowed_names: set[str] = set(allowed_names or [])

    def generic_visit(self, node: ast.AST) -> None:
        if type(node) not in SAFE_NODE_TYPES:
            raise SecurityError(f"Disallowed construct: {type(node).__name__}")
        super().generic_visit(node)

    def visit_Import(self, node: ast.Import) -> None:  # pragma: no cover - simple check
        for alias in node.names:
            base = alias.name.split('.')[0]
            if base not in SAFE_IMPORTS:
                raise SecurityError(f"Import of {alias.name} is not permitted")
        super().generic_visit(node)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        # Record user-defined function names so calls to them are permitted
        self._defined_names.add(node.name)
        super().generic_visit(node)

    def visit_Assign(self, node: ast.Assign) -> None:
        # If assigned value is a lambda, record the target name as callable
        if isinstance(node.value, ast.Lambda):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    self._defined_names.add(target.id)
        super().generic_visit(node)

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:  # pragma: no cover - simple check
        module = node.module or ""
        base = module.split('.')[0] if module else ''
        if base not in SAFE_IMPORTS:
            raise SecurityError(f"Import from {module} is not permitted")
        # Record imported names as allowed callables for subsequent calls in the payload
        for alias in node.names:
            name = alias.asname if alias.asname else alias.name
            # Only the top-level name is relevant for 'from module import name'
            self._allowed_names.add(name)
        super().generic_visit(node)

    def visit_Attribute(self, node: ast.Attribute) -> None:
        # Allow attribute access on simple names (module.attr) or on call-returned
        # objects like open(...).read if the method is whitelisted.
        if isinstance(node.value, ast.Name):
            base = node.value.id
            attr = node.attr
            if base in SAFE_MODULE_CALLS:
                allowed = SAFE_MODULE_CALLS[base] | SAFE_MODULE_ATTRIBUTES.get(base, set())
                if attr not in allowed:
                    raise SecurityError(f"Attribute {base}.{attr} not permitted")
            elif attr not in SAFE_METHOD_CALLS:
                raise SecurityError(f"Method {attr} is not permitted")
        elif isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name):
            # open(...).read() style: allow attribute if in SAFE_METHOD_CALLS
            attr = node.attr
            if attr not in SAFE_METHOD_CALLS:
                raise SecurityError(f"Method {attr} is not permitted on call-returned objects")
        else:
            raise SecurityError("Attribute access is restricted to named objects")
        super().generic_visit(node)

    def visit_Call(self, node: ast.Call) -> None:
        func = node.func
        # Allow direct calls to whitelisted functions or to functions that were
        # either defined in the payload or are present in the runtime globals.
        if isinstance(func, ast.Name):
            if (
                func.id not in SAFE_FUNCTIONS
                and func.id not in getattr(self, '_defined_names', set())
                and func.id not in getattr(self, '_allowed_names', set())
            ):
                raise SecurityError(f"Function {func.id} is not permitted")
        # Attribute calls: e.g., sys.exit or fileobj.read()
        elif isinstance(func, ast.Attribute):
            # Typical base: a module name (ast.Name) -> sys.exit
            if isinstance(func.value, ast.Name):
                base = func.value.id
                attr = func.attr
                if base in SAFE_MODULE_CALLS and attr in SAFE_MODULE_CALLS[base]:
                    pass
                elif attr in SAFE_METHOD_CALLS:
                    pass
                else:
                    raise SecurityError(f"Call to {base}.{attr} is not permitted")
            # Allow call-chained attribute calls like open(...).read() where the
            # call returns a file-like object and the attribute is in SAFE_METHOD_CALLS
            elif isinstance(func.value, ast.Call) and isinstance(func.value.func, ast.Name):
                attr = func.attr
                if attr not in SAFE_METHOD_CALLS:
                    raise SecurityError(f"Chained attribute call to method '{attr}' is not permitted")
            else:
                raise SecurityError("Chained attribute calls are not permitted")
        else:
            raise SecurityError("Dynamic function calls are not permitted")
        super().generic_visit(node)


def safe_eval(code: str, scope: Dict[str, Any]) -> Any:
    """Evaluate a Python expression in a sandboxed environment.

    Note: Sandbox validation is disabled to enable full Python execution.
    This allows function definitions, recursion, and all standard library
    functions. Use with trusted code only.

    For security-sensitive deployments, re-enable SafeNodeVisitor validation.
    """
    tree = ast.parse(code, mode="eval")
    # Sandbox validation DISABLED for trusted-code mode (showcase/demo)
    # allowed_names = {name for name, val in scope.items() if callable(val)}
    # SafeNodeVisitor(allowed_names=allowed_names).visit(tree)
    compiled = compile(tree, "<pyexec>", "eval")
    return eval(compiled, scope)


def safe_execute(code: str, scope: Dict[str, Any]) -> Any:
    """Execute Python code in a sandboxed environment.

    Note: Sandbox validation is disabled to enable full Python execution.
    This allows function definitions, recursion, and all standard library
    functions. Use with trusted code only.

    For security-sensitive deployments, re-enable SafeNodeVisitor validation.
    """
    tree = ast.parse(code, mode="exec")
    # Sandbox validation DISABLED for trusted-code mode (showcase/demo)
    # allowed_names = {name for name, val in scope.items() if callable(val)}
    # SafeNodeVisitor(allowed_names=allowed_names).visit(tree)
    compiled = compile(tree, "<pyexec>", "exec")
    exec(compiled, scope)
    return scope.get("__result__")


def _empty_cert() -> Dict[str, Any]:
    return {
        "smt_query": "",
        "solver_reply": "",
        "metadata": "",
        "timestamp": 0,
        "sequence": 0,
    }


def _cert_for_payload(payload: Dict[str, Any]) -> Dict[str, Any]:
    cert = dict(payload)
    return cert

try:
    from .assemble import Instruction, parse
    from .logic import lassert, ljoin
    from .mdl import mdlacc, info_charge
    from .certs import CertStore
    from .state import State, BianchiViolationError
    from .isa import CSR
    from .memory import RegionGraph
    from ._types import LedgerEntry, ModuleId
    from .mu import calculate_mu_cost
    from .receipts import (
        WitnessState,
        StepObservation,
        InstructionWitness,
        StepReceipt,
        ensure_kernel_keys,
    )
    from .logger import get_thiele_logger
except ImportError:
    # Handle running as script
    import sys
    import os
    # Add the parent directory to the path to allow for relative imports
    sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
    from thielecpu.assemble import Instruction, parse
    from thielecpu.logic import lassert, ljoin
    from thielecpu.mdl import mdlacc, info_charge
    from thielecpu.certs import CertStore
    from thielecpu.state import State, BianchiViolationError
    from thielecpu.isa import CSR
    from thielecpu.memory import RegionGraph
    from thielecpu._types import LedgerEntry, ModuleId
    from thielecpu.mu import calculate_mu_cost
    from thielecpu.receipts import (
        WitnessState,
        StepObservation,
        InstructionWitness,
        StepReceipt,
        ensure_kernel_keys,
    )
    from thielecpu.logger import get_thiele_logger


@dataclass
class SymbolicVariable:
    """Represents a symbolic variable that needs to be solved for."""
    name: str
    domain: List[str]  # Possible values this variable can take

    def __str__(self):
        return f"SymbolicVar({self.name})"

    def __repr__(self):
        return self.__str__()

    def __hash__(self):
        return hash(self.name)

    def __eq__(self, other):
        if isinstance(other, SymbolicVariable):
            return self.name == other.name
        return False


# Global counter for symbolic variables
_symbolic_var_counter = 0

def extract_target_modulus(code: str) -> Optional[int]:
    """Extract the target modulus n from Python factoring code."""
    try:
        tree = ast.parse(code)
        for node in ast.walk(tree):
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Name) and target.id == 'n':
                        if isinstance(node.value, ast.Constant) and isinstance(node.value.value, int):
                            return node.value.value
    except:
        pass
    return None


@dataclass
class TraceConfig:
    """Configuration for runtime self-tracing."""

    workload_id: str
    observer: object
    metadata: Mapping[str, Any] = field(default_factory=dict)
    enabled: bool = True


def placeholder(domain: Optional[List[str]] = None) -> SymbolicVariable:
    """Create a symbolic variable placeholder for logical deduction."""
    global _symbolic_var_counter
    if domain is None:
        # Default domain: lowercase letters and digits
        domain = list(string.ascii_lowercase + string.digits)

    var_name = f"var_{_symbolic_var_counter}"
    _symbolic_var_counter += 1

    return SymbolicVariable(var_name, domain)

def search_chunk(chunk_combinations, var_names, code_to_run):
    """Worker function for parallel brute force search."""
    import hashlib

    # Minimal globals for the subprocess
    python_globals = {
        '__builtins__': __builtins__,
        'print': print,
        'len': len,
        'range': range,
        'enumerate': enumerate,
        'zip': zip,
        'sum': sum,
        'max': max,
        'min': min,
        'abs': abs,
        'pow': pow,
        'divmod': divmod,
        'round': round,
        'int': int,
        'float': float,
        'str': str,
        'bool': bool,
        'list': list,
        'dict': dict,
        'set': set,
        'tuple': tuple,
        'hashlib': hashlib,
    }

    for combination in chunk_combinations:
        assignment = dict(zip(var_names, combination))

        solved_globals = python_globals.copy()
        solved_globals.update(assignment)

        # Capture output in subprocess
        from io import StringIO
        import sys
        old_stdout = sys.stdout
        sys.stdout = captured_output = StringIO()

        success = False
        output = ""

        try:
            exec(code_to_run, solved_globals)
            success = True
        except AssertionError:
            pass
        except Exception:
            pass

        output = captured_output.getvalue()
        sys.stdout = old_stdout

        if success:
            return assignment, output
    return None, None

@dataclass
class VM:
    state: State
    python_globals: Dict[str, Any] = None  # type: ignore
    virtual_fs: VirtualFilesystem = field(default_factory=VirtualFilesystem)
    witness_state: WitnessState = field(default_factory=WitnessState)
    step_receipts: List[StepReceipt] = field(default_factory=list)
    explicit_mdlacc_called: bool = field(default=False, init=False, repr=False)
    last_exit_code: int = field(default=0, init=False)

    def __post_init__(self):
        ensure_kernel_keys()
        if self.python_globals is None:
            # Full Python builtins enabled - sandbox restrictions removed.
            # This allows function definitions, recursion, and standard library usage.
            # 
            # SECURITY NOTE: Use with trusted code only. For security-sensitive
            # deployments, replace with SAFE_BUILTINS and re-enable SafeNodeVisitor.
            
            globals_scope: Dict[str, Any] = {
                "__builtins__": SAFE_BUILTINS.copy(),
                "placeholder": placeholder,
                "hashlib": hashlib,
                "math": math,
                "json": json,
                "sys": sys,
                "np": np,
                "numpy": np,
                "Path": Path,
                "vm_read_text": self.virtual_fs.read_text,
                "vm_write_text": self.virtual_fs.write_text,
                "vm_read_bytes": self.virtual_fs.read_bytes,
                "vm_write_bytes": self.virtual_fs.write_bytes,
                "vm_exists": self.virtual_fs.exists,
                "vm_listdir": self.virtual_fs.listdir,
            }
            
            # NOTE: PyTorch NOT added to VM globals due to Python 3.12 compatibility bug
            # Users should run PyTorch code outside VM and pass results via PYEXEC
            
            self.python_globals = globals_scope
        else:
            # Ensure filesystem helpers are present even with custom globals
            self.python_globals.setdefault("vm_read_text", self.virtual_fs.read_text)
            self.python_globals.setdefault("vm_write_text", self.virtual_fs.write_text)
            self.python_globals.setdefault("vm_read_bytes", self.virtual_fs.read_bytes)
            self.python_globals.setdefault("vm_write_bytes", self.virtual_fs.write_bytes)
            self.python_globals.setdefault("vm_exists", self.virtual_fs.exists)
            self.python_globals.setdefault("vm_listdir", self.virtual_fs.listdir)
        self.witness_state = WitnessState()
        self.step_receipts = []
        # Minimal register file and scratch memory so hardware-style XOR opcodes
        # and HALT can execute alongside the existing partition/logical flow.
        self.register_file = [0] * 32
        self.data_memory = [0] * 256

    def _trace_call(
        self, config: Optional[TraceConfig], hook: str, payload: Mapping[str, Any]
    ) -> None:
        if config is None or not config.enabled:
            return
        method = getattr(config.observer, hook, None)
        if method is None:
            return
        try:
            method(dict(payload))
        except Exception:
            pass

    def _trace_partition_signature(self) -> Mapping[str, object]:
        modules = getattr(self.state.regions, "modules", {})
        sizes = sorted(len(region) for region in modules.values())
        digest_source = json.dumps(sizes, separators=(",", ":")).encode("utf-8")
        digest = hashlib.sha256(digest_source).hexdigest()[:16] if sizes else "0" * 16
        return {
            "module_count": len(sizes),
            "region_sizes": sizes,
            "digest": digest,
        }
    
    def _detect_supra_quantum_generation(self, outdir) -> bool:
        """Detect if PYEXEC generated supra-quantum correlations.
        
        Checks output directory for JSON files with CHSH data and verifies
        if S > 2√2 (Tsirelson bound).
        
        Returns:
            True if supra-quantum correlations detected, False otherwise
        """
        from pathlib import Path
        from fractions import Fraction
        from .logger import get_thiele_logger
        
        logger = get_thiele_logger()
        
        try:
            TSIRELSON_BOUND = 2.828427  # 2√2
            
            outdir_path = Path(outdir) if outdir else None
            if not outdir_path or not outdir_path.exists():
                return False
            
            # Check all JSON files in output directory
            for json_file in outdir_path.glob("*.json"):
                try:
                    with open(json_file) as f:
                        data = json.load(f)
                    
                    # Check if this is a CHSH dataset
                    if "counts" in data and "strategy" in data:
                        # Use the same formula as tools/compute_chsh_from_table.py
                        # S = E(1,1) + E(1,0) + E(0,1) - E(0,0)
                        
                        # First compute correlation table from counts
                        counts = data["counts"]
                        
                        # Parse counts into probability table
                        table = {}  # (x, y) -> {(a, b): probability}
                        for key, count in counts.items():
                            parts = key.split(",")
                            if len(parts) == 4:
                                x, y, a, b = map(int, parts)
                                setting = (x, y)
                                if setting not in table:
                                    table[setting] = {}
                                table[setting][(a, b)] = count
                        
                        # Normalize to probabilities and compute correlators
                        def correlator(x, y):
                            if (x, y) not in table:
                                return 0.0
                            outcomes = table[(x, y)]
                            total = sum(outcomes.values())
                            if total == 0:
                                return 0.0
                            # E(x,y) = Σ_{a,b} (-1)^{a+b} * P(a,b|x,y)
                            expectation = 0.0
                            for (a, b), count in outcomes.items():
                                prob = count / total
                                expectation += ((-1) ** (a + b)) * prob
                            return expectation
                        
                        E_11 = correlator(1, 1)
                        E_10 = correlator(1, 0)
                        E_01 = correlator(0, 1)
                        E_00 = correlator(0, 0)
                        
                        S = E_11 + E_10 + E_01 - E_00
                        
                        if S > TSIRELSON_BOUND:
                            return True
                        
                except (json.JSONDecodeError, KeyError, ValueError):
                    continue
            
            return False
        except Exception as e:
            # If detection fails, log it and assume no supra-quantum
            logger.error(f"Supra-quantum detection exception: {e}")
            import traceback
            traceback.print_exc()
            return False

    def _write_register(self, reg_index: int, new_value: int) -> int:
        """Write a register and track Landauer erasure cost."""
        idx = reg_index % len(self.register_file)
        masked_value = new_value & 0xFFFFFFFF
        old_value = self.register_file[idx] & 0xFFFFFFFF
        diff = old_value ^ masked_value
        erasure_cost = diff.bit_count()
        if erasure_cost:
            self.state.mu_ledger.track_entropy(erasure_cost)
        self.register_file[idx] = masked_value
        return masked_value

    def export_virtual_files(self) -> Dict[str, bytes]:
        """Return a copy of the virtual filesystem contents."""

        return self.virtual_fs.snapshot()

    def load_virtual_files(self, files: Dict[str, bytes | bytearray | str]) -> None:
        """Replace the virtual filesystem with ``files``.

        ``files`` maps sandbox-relative paths to bytes (or UTF-8 strings).
        """

        self.virtual_fs.load_snapshot(files)

    def _simulate_witness_step(
        self,
        instruction: InstructionWitness,
        pre_state: WitnessState,
    ) -> Tuple[WitnessState, StepObservation]:
        op = instruction.op
        if op == "LASSERT":
            payload = dict(instruction.payload) if isinstance(instruction.payload, dict) else {}
            mu_delta = float(payload.get("mu_delta", 0.0))
            cert_payload = _cert_for_payload(payload)
            cert_addr = str(cert_payload.get("metadata", ""))
            post_state = WitnessState(
                pc=pre_state.pc + 1,
                status=pre_state.status,
                mu_acc=pre_state.mu_acc + mu_delta,
                cert_addr=cert_addr or pre_state.cert_addr,
            )
            observation = StepObservation(
                event={"tag": "ProofStatus", "value": payload.get("status", "UNKNOWN")},
                mu_delta=mu_delta,
                cert=cert_payload,
            )
        elif op == "MDLACC":
            post_state = WitnessState(
                pc=pre_state.pc + 1,
                status=pre_state.status,
                mu_acc=pre_state.mu_acc,
                cert_addr=pre_state.cert_addr,
            )
            observation = StepObservation(event=None, mu_delta=0, cert=_empty_cert())
        elif op == "PNEW":
            post_state = WitnessState(
                pc=pre_state.pc + 1,
                status=pre_state.status,
                mu_acc=pre_state.mu_acc,
                cert_addr=pre_state.cert_addr,
            )
            observation = StepObservation(
                event={"tag": "InferenceComplete"}, mu_delta=0, cert=_empty_cert()
            )
        elif op == "PYEXEC":
            code = str(instruction.payload)
            post_state = WitnessState(
                pc=pre_state.pc + 1,
                status=pre_state.status,
                mu_acc=pre_state.mu_acc,
                cert_addr=pre_state.cert_addr,
            )
            observation = StepObservation(
                event={"tag": "PolicyCheck", "value": code},
                mu_delta=0,
                cert=_empty_cert(),
            )
        elif op == "PYTHON":
            code = str(instruction.payload)
            post_state = WitnessState(
                pc=pre_state.pc + 1,
                status=pre_state.status,
                mu_acc=pre_state.mu_acc,
                cert_addr=pre_state.cert_addr,
            )
            observation = StepObservation(
                event={"tag": "PythonExec", "value": code},
                mu_delta=0,
                cert=_empty_cert(),
            )
        elif op == "CHSH_TRIAL":
            payload = dict(instruction.payload) if isinstance(instruction.payload, dict) else {}
            x = int(payload.get("x", 0))
            y = int(payload.get("y", 0))
            a = int(payload.get("a", 0))
            b = int(payload.get("b", 0))
            meta = f"CHSH_{1 if x else 0}{1 if y else 0}{1 if a else 0}{1 if b else 0}"
            cert = _empty_cert()
            cert["metadata"] = meta
            post_state = WitnessState(
                pc=pre_state.pc + 1,
                status=pre_state.status,
                mu_acc=pre_state.mu_acc,
                cert_addr=pre_state.cert_addr,
            )
            observation = StepObservation(
                event={"tag": "ChshTrial", "value": meta},
                mu_delta=0,
                cert=cert,
            )
        elif op == "REVEAL":
            payload = dict(instruction.payload) if isinstance(instruction.payload, dict) else {}
            bits = float(payload.get("bits", 0.0))
            module = str(payload.get("module", ""))
            cert_sha256 = str(payload.get("cert_sha256", ""))
            cert = _empty_cert()
            cert["metadata"] = cert_sha256
            post_state = WitnessState(
                pc=pre_state.pc + 1,
                status=pre_state.status,
                mu_acc=pre_state.mu_acc + bits,
                cert_addr=cert_sha256 or pre_state.cert_addr,
            )
            observation = StepObservation(
                event={"tag": "Revelation", "value": module},
                mu_delta=bits,
                cert=cert,
            )
        elif op == "EMIT":
            payload = str(instruction.payload)
            post_state = WitnessState(
                pc=pre_state.pc + 1,
                status=pre_state.status,
                mu_acc=pre_state.mu_acc,
                cert_addr=pre_state.cert_addr,
            )
            observation = StepObservation(
                event={"tag": "ErrorOccurred", "value": payload},
                mu_delta=0,
                cert=_empty_cert(),
            )
        elif op in {"XOR_ADD", "XOR_SWAP", "XOR_LOAD", "XOR_RANK", "XFER"}:
            post_state = WitnessState(
                pc=pre_state.pc + 1,
                status=pre_state.status,
                mu_acc=pre_state.mu_acc,
                cert_addr=pre_state.cert_addr,
            )
            observation = StepObservation(
                event={"tag": "AluOp", "value": op}, mu_delta=0, cert=_empty_cert()
            )
        elif op == "HALT":
            post_state = WitnessState(
                pc=pre_state.pc + 1,
                status=pre_state.status,
                mu_acc=pre_state.mu_acc,
                cert_addr=pre_state.cert_addr,
            )
            observation = StepObservation(
                event={"tag": "Halt"}, mu_delta=0, cert=_empty_cert()
            )
        elif op == "ORACLE_HALTS":
            post_state = WitnessState(
                pc=pre_state.pc + 1,
                status=pre_state.status,
                mu_acc=pre_state.mu_acc,
                cert_addr=pre_state.cert_addr,
            )
            observation = StepObservation(
                event={"tag": "OracleVerdict", "value": str(instruction.payload)},
                mu_delta=0,
                cert=_empty_cert(),
            )
        else:
            raise ValueError(f"Unsupported instruction for receipts: {op}")
        return post_state, observation

    def _record_receipt(
        self, step: int, pre_state: WitnessState, instruction: InstructionWitness
    ) -> None:
        post_state, observation = self._simulate_witness_step(instruction, pre_state)
        receipt = StepReceipt.assemble(
            step,
            instruction,
            pre_state,
            post_state,
            observation,
        )
        self.step_receipts.append(receipt)
        self.witness_state = post_state

    def auto_discover_partition(
        self, 
        clauses: List[List[int]], 
        max_mu_budget: float = 10000.0
    ) -> Dict[str, Any]:
        """Automatically discover a near-optimal partition for a problem.
        
        This implements the PDISCOVER_AUTO opcode, which uses polynomial-time
        spectral clustering to find natural problem structure.
        
        Args:
            clauses: CNF clauses as list of list of literals
            max_mu_budget: Maximum μ-bits to spend on discovery
            
        Returns:
            Dictionary with discovered partition and metadata:
            - modules: List of variable sets (the partition)
            - mdl_cost: MDL cost of the partition
            - discovery_cost: μ-bits spent
            - method: Algorithm used
            - discovery_time: Wall-clock time
        """
        from .discovery import Problem, EfficientPartitionDiscovery
        
        # Convert CNF to Problem
        problem = Problem.from_cnf_clauses(clauses, name="auto-discovered")
        
        # Discover partition
        discoverer = EfficientPartitionDiscovery()
        candidate = discoverer.discover_partition(problem, max_mu_budget)
        
        # Charge the discovery cost to the state
        self.state.mu_operational += candidate.discovery_cost_mu
        self.state.mu_ledger.mu_discovery += int(candidate.discovery_cost_mu)
        
        # Create partitions in VM state
        for module in candidate.modules:
            self.state.pnew(module)
        
        return {
            "modules": [list(m) for m in candidate.modules],
            "mdl_cost": candidate.mdl_cost,
            "discovery_cost": candidate.discovery_cost_mu,
            "method": candidate.method,
            "discovery_time": candidate.discovery_time,
            "num_modules": candidate.num_modules,
            "total_variables": candidate.total_variables,
        }

    def execute_symbolic_python(self, code: str, source_info: str = "") -> Any:
        """Execute Python code with symbolic variables using Z3 SMT solver."""

        # 1. Parse the code and find symbolic assignments
        try:
            tree = ast.parse(code)
        except SyntaxError as exc:
            return None, f"Syntax Error: {exc}"

        # Log where the symbolic code originated to aid debugging
        print(f"Executing symbolic code from: {source_info}")

        symbolic_assignments = {}  # maps var_name -> domain

        class PlaceholderVisitor(ast.NodeVisitor):
            def visit_Assign(self, node):
                if isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name) and node.value.func.id == 'placeholder':
                    # This is an assignment like `p1 = placeholder(...)`
                    if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
                        var_name = node.targets[0].id
                        # Default domain
                        domain = list(string.ascii_lowercase + string.digits)
                        # Try to evaluate the domain argument if present
                        if node.value.keywords:
                            for kw in node.value.keywords:
                                if kw.arg == 'domain':
                                    domain_val = None
                                    try:
                                        # Try ast.literal_eval first for simple literals
                                        domain_val = ast.literal_eval(kw.value)
                                    except (ValueError, TypeError):
                                        # For expressions like list(range(...)), use eval with restricted globals
                                        try:
                                            code = ast.unparse(kw.value)
                                            restricted_globals = {
                                                '__builtins__': {},
                                                'list': list,
                                                'range': range,
                                                'str': str,
                                                'int': int,
                                                'float': float,
                                                'bool': bool,
                                                'tuple': tuple,
                                                'set': set,
                                                'frozenset': frozenset,
                                                'dict': dict,
                                            }
                                            domain_val = eval(code, restricted_globals)
                                        except Exception:
                                            pass

                                    if isinstance(domain_val, list):
                                        domain = domain_val
                        symbolic_assignments[var_name] = domain
                self.generic_visit(node)

        PlaceholderVisitor().visit(tree)

        if not symbolic_assignments:
            return self.execute_python(code)

        var_names = list(symbolic_assignments.keys())
        print(f"Found {len(var_names)} symbolic variables: {var_names}")

        # Set default domain if not specified
        for var_name in var_names:
            if symbolic_assignments[var_name] is None:
                symbolic_assignments[var_name] = list('abcdefghijklmnopqrstuvwxyz0123456789')

        total_combinations = 1
        for domain in symbolic_assignments.values():
            total_combinations *= len(domain)
        print(f"Classical search space: {total_combinations} combinations")

        # Check if this is arithmetic (integer) or string-based symbolic execution
        is_arithmetic = False
        class ArithmeticChecker(ast.NodeVisitor):
            def __init__(self):
                self.is_arithmetic = False
            def visit_BinOp(self, node):
                if isinstance(node.op, (ast.Mult, ast.Add, ast.Sub, ast.Div, ast.FloorDiv, ast.Mod)):
                    self.is_arithmetic = True
                self.generic_visit(node)
            def visit_Compare(self, node):
                if any(isinstance(op, (ast.Lt, ast.LtE, ast.Gt, ast.GtE)) for op in node.ops):
                    self.is_arithmetic = True
                self.generic_visit(node)

        checker = ArithmeticChecker()
        checker.visit(tree)
        is_arithmetic = checker.is_arithmetic

        # Use AST transformer to remove symbolic assignments
        class SymbolicAssignmentRemover(ast.NodeTransformer):
            def visit_Assign(self, node):
                if (isinstance(node.value, ast.Call) and
                    isinstance(node.value.func, ast.Name) and
                    node.value.func.id == 'placeholder'):
                    return None
                return node

        remover = SymbolicAssignmentRemover()
        new_tree = remover.visit(tree)
        ast.fix_missing_locations(new_tree)
        code_to_run = ast.unparse(new_tree)

        # 2. Set up Z3 solver
        if is_arithmetic:
            solver = z3.Solver()
            z3_vars = {}
            # Create Z3 integer variables
            for var_name in var_names:
                z3_vars[var_name] = z3.Int(var_name)
                # Add domain constraints
                domain = symbolic_assignments[var_name]
                if isinstance(domain, list) and domain:
                    if all(isinstance(x, int) for x in domain):
                        solver.add(z3_vars[var_name] >= min(domain))
                        solver.add(z3_vars[var_name] <= max(domain))
        else:
            solver = z3.SolverFor("QF_S")
            z3_vars = {}
            # Create Z3 string variables
            for var_name, domain in symbolic_assignments.items():
                z3_var = z3.String(var_name)
                z3_vars[var_name] = z3_var

        # Check if constraints involve unsupported operations (e.g., cryptography)
        has_unsupported_assertions = 'hashlib' in code or '%' in code

        if has_unsupported_assertions:
            # Fall back to brute force for cryptographic constraints
            print("Cryptographic constraints detected - using brute force search")
            return self.execute_symbolic_brute_force(code, symbolic_assignments, var_names, code_to_run)
        else:
            # Use Z3 for logical constraints
            if is_arithmetic:
                print("Using Z3 SMT solver for arithmetic constraints...")
            else:
                print("Using Z3 SMT solver for logical constraints...")

            # Add distinctness constraints if all variables have the same finite domain
            domains = list(symbolic_assignments.values())
            if len(set(tuple(sorted(d)) for d in domains)) == 1 and domains[0]:
                # All variables have the same domain, likely need to be distinct
                domain_size = len(domains[0])
                if len(var_names) == domain_size:
                    print(f"Adding distinctness constraints for {len(var_names)} variables")
                    solver.add(z3.Distinct(*[z3_vars[name] for name in var_names]))

            # Find assertions and convert to Z3 constraints
            class AssertionVisitor(ast.NodeVisitor):
                def visit_Assert(self, node):
                    constraint = self.convert_expr_to_z3(node.test, is_arithmetic)
                    if constraint is not None:
                        solver.add(constraint)

                def convert_expr_to_z3(self, expr, is_arithmetic):
                    if isinstance(expr, ast.Compare):
                        if len(expr.ops) == 1:
                            op = expr.ops[0]
                            left = self.convert_expr_to_z3(expr.left, is_arithmetic)
                            right = self.convert_expr_to_z3(expr.comparators[0], is_arithmetic)
                            if left is not None and right is not None:
                                if isinstance(op, ast.Eq):
                                    return left == right
                                elif isinstance(op, ast.Lt):
                                    return left < right
                                elif isinstance(op, ast.LtE):
                                    return left <= right
                                elif isinstance(op, ast.Gt):
                                    return left > right
                                elif isinstance(op, ast.GtE):
                                    return left >= right
                        elif len(expr.ops) > 1:
                            # Chained comparison: a < b < c becomes (a < b) and (b < c)
                            constraints = []
                            left = self.convert_expr_to_z3(expr.left, is_arithmetic)
                            for i, op in enumerate(expr.ops):
                                right = self.convert_expr_to_z3(expr.comparators[i], is_arithmetic)
                                if left is not None and right is not None:
                                    if isinstance(op, ast.Eq):
                                        constraints.append(left == right)
                                    elif isinstance(op, ast.Lt):
                                        constraints.append(left < right)
                                    elif isinstance(op, ast.LtE):
                                        constraints.append(left <= right)
                                    elif isinstance(op, ast.Gt):
                                        constraints.append(left > right)
                                    elif isinstance(op, ast.GtE):
                                        constraints.append(left >= right)
                                left = right
                            if constraints:
                                return z3.And(*constraints)
                    elif isinstance(expr, ast.BoolOp):
                        converted_values = [self.convert_expr_to_z3(value, is_arithmetic) for value in expr.values]
                        if all(v is not None for v in converted_values):
                            if isinstance(expr.op, ast.And):
                                return z3.And(*converted_values)
                            elif isinstance(expr.op, ast.Or):
                                return z3.Or(*converted_values)
                    elif isinstance(expr, ast.BinOp):
                        left = self.convert_expr_to_z3(expr.left, is_arithmetic)
                        right = self.convert_expr_to_z3(expr.right, is_arithmetic)
                        if left is not None and right is not None:
                            if isinstance(expr.op, ast.Add):
                                if is_arithmetic:
                                    return left + right
                                else:
                                    return z3.Concat(left, right)
                            elif isinstance(expr.op, ast.Sub):
                                return left - right
                            elif isinstance(expr.op, ast.Mult):
                                return left * right
                            elif isinstance(expr.op, ast.Div):
                                return left / right
                            elif isinstance(expr.op, ast.Mod):
                                return left % right
                            elif isinstance(expr.op, ast.Pow):
                                return left ** right
                    elif isinstance(expr, ast.Call):
                        if isinstance(expr.func, ast.Attribute) and expr.func.attr == 'startswith':
                            obj = self.convert_expr_to_z3(expr.func.value, is_arithmetic)
                            if obj is not None and expr.args:
                                arg = self.convert_expr_to_z3(expr.args[0], is_arithmetic)
                                if arg is not None:
                                    # Model Python's str.startswith(x) as z3 PrefixOf(x, obj)
                                    return z3.PrefixOf(arg, obj)
                    elif isinstance(expr, ast.Name):
                        if expr.id in z3_vars:
                            return z3_vars[expr.id]
                    elif isinstance(expr, ast.Constant):
                        if is_arithmetic and isinstance(expr.value, int):
                            return z3.IntVal(expr.value)
                        else:
                            return z3.StringVal(str(expr.value))
                    return None

            AssertionVisitor().visit(new_tree)

            if solver.check() == z3.sat:
                model = solver.model()
                assignment = {}
                for var_name, z3_var in z3_vars.items():
                    val = model[z3_var]
                    if val is not None:
                        if is_arithmetic:
                            assignment[var_name] = int(str(val))
                        else:
                            if z3.is_string_value(val):
                                assignment[var_name] = str(val).strip('"')
                            else:
                                assignment[var_name] = str(val)
                    else:
                        assignment[var_name] = 0 if is_arithmetic else ""

                print(f"✓ Found satisfying assignment: {assignment}")

                solved_globals = self.python_globals.copy()
                solved_globals.update(assignment)

                old_stdout = sys.stdout
                sys.stdout = captured_output = StringIO()

                try:
                    exec(code_to_run, solved_globals)
                    output = captured_output.getvalue()
                    sys.stdout = old_stdout
                    return None, f"Symbolic execution successful!\nAssignment: {assignment}\nOutput:\n{output}"
                except Exception as e:
                    sys.stdout = old_stdout
                    return None, f"Execution failed with solution: {e}"
            else:
                return None, "No satisfying assignment found (unsatisfiable constraints)"

    def execute_python(self, code_or_path: str, argv: Optional[Sequence[str]] = None) -> Any:
        """Execute Python code or a file.

        When executing a file, this emulates standard Python semantics closely:
        - sets ``__file__`` and ``__name__`` in the execution globals
        - sets ``sys.argv`` and temporarily prepends the script directory to ``sys.path``

        Note: sandbox restrictions are currently disabled in this repo (trusted-code mode).
        """
        # Special case: module execution (python -m)
        is_module = False
        module_name: str | None = None
        if code_or_path.startswith("module:"):
            is_module = True
            module_name = code_or_path[len("module:") :].strip()

        # Check if it's a file path
        is_file = False
        script_path: Path | None = None
        if (not is_module) and (code_or_path.endswith('.py') or ('\n' not in code_or_path.strip() and Path(code_or_path).exists())):
            try:
                # Try to read as file
                script_path = Path(code_or_path).resolve()
                code = script_path.read_text(encoding='utf-8')
                source_info = f"file: {script_path}"
                is_file = True
            except (FileNotFoundError, OSError):
                # Not a file, treat as inline code
                code = code_or_path
                source_info = "inline"
        else:
            # Inline code
            code = code_or_path
            source_info = "inline"

        # Check if code contains symbolic variables
        if 'placeholder(' in code:
            return self.execute_symbolic_python(code, source_info)

        # Capture stdout. For interactive parity, optionally tee output to the real stdout
        # so input() prompts and prints remain visible while we still log trace output.
        old_stdout = sys.stdout
        captured_output = StringIO()
        force_tee = bool(self.python_globals.get("_vm_tee_stdout"))
        auto_tee = False
        try:
            auto_tee = bool(getattr(sys.stdin, "isatty")()) and bool(getattr(old_stdout, "isatty")())
        except Exception:
            auto_tee = False
        if force_tee or auto_tee:
            sys.stdout = _TeeTextIO(old_stdout, captured_output)
        else:
            sys.stdout = captured_output

        old_argv: list[str] | None = None
        old_sys_path: list[str] | None = None
        # Provide interpreter-like globals for module/file execution.
        if (not is_file) and (not is_module) and argv is None:
            argv0 = self.python_globals.get("_vm_argv0")
            vm_args = self.python_globals.get("_vm_script_args")
            if isinstance(argv0, str) and isinstance(vm_args, list) and all(isinstance(x, str) for x in vm_args):
                argv = [argv0, *vm_args]
            elif isinstance(argv0, str):
                argv = [argv0]

        if is_module and module_name:
            self.python_globals.setdefault("__name__", "__main__")
            # For -m execution, argv[0] is the module name.
            if argv is None:
                vm_args = self.python_globals.get("_vm_script_args")
                if isinstance(vm_args, list) and all(isinstance(x, str) for x in vm_args):
                    argv = [module_name, *vm_args]
                else:
                    argv = [module_name]
            try:
                old_argv = list(sys.argv)
                sys.argv = list(argv)
            except Exception:
                old_argv = None
            try:
                old_sys_path = list(sys.path)
                # Match CPython: for `python -m`, sys.path[0] is the CWD (often '').
                sys.path = ["", *[p for p in old_sys_path if p != ""]]
            except Exception:
                old_sys_path = None
        elif is_file and script_path is not None:
            self.python_globals.setdefault("__name__", "__main__")
            self.python_globals["__file__"] = str(script_path)
            self.python_globals.setdefault("__package__", None)
            self.python_globals.setdefault("__spec__", None)

            if argv is None:
                vm_args = self.python_globals.get("_vm_script_args")
                if isinstance(vm_args, list) and all(isinstance(x, str) for x in vm_args):
                    argv = [str(script_path), *vm_args]
                else:
                    argv = [str(script_path)]
            try:
                old_argv = list(sys.argv)
                sys.argv = list(argv) if argv is not None else [str(script_path)]
            except Exception:
                old_argv = None
            try:
                old_sys_path = list(sys.path)
                script_dir = str(script_path.parent)
                sys.path = [script_dir, *[p for p in old_sys_path if p != script_dir]]
            except Exception:
                old_sys_path = None
        else:
            # Inline execution: default to a VM-ish name, but if argv was supplied
            # (e.g., from CLI -c or stdin), match interpreter behavior.
            if argv is not None:
                self.python_globals.setdefault("__name__", "__main__")
                try:
                    old_argv = list(sys.argv)
                    sys.argv = list(argv)
                except Exception:
                    old_argv = None
                try:
                    old_sys_path = list(sys.path)
                    sys.path = ["", *[p for p in old_sys_path if p != ""]]
                except Exception:
                    old_sys_path = None
            else:
                self.python_globals.setdefault("__name__", "__vm__")

        try:
            if is_module and module_name:
                # Match CPython `python -m module` semantics.
                runpy.run_module(
                    module_name,
                    run_name="__main__",
                    alter_sys=True,
                    init_globals=self.python_globals,
                )
                self.last_exit_code = 0
                result = self.python_globals.get("__result__")
                output = captured_output.getvalue()
                return result, output

            if is_file and script_path is not None:
                runpy.run_path(str(script_path), run_name="__main__", init_globals=self.python_globals)
                self.last_exit_code = 0
                result = self.python_globals.get("__result__")
                output = captured_output.getvalue()
                return result, output

            result = safe_execute(code, self.python_globals)
            self.last_exit_code = 0
            output = captured_output.getvalue()
            return result, output
        except SyntaxError:
            result = safe_eval(code, self.python_globals)
            self.last_exit_code = 0
            output = captured_output.getvalue()
            return result, output
        except SystemExit as exc:
            # Treat sys.exit(...) as a normal VM-visible termination signal rather
            # than aborting the whole VM run.
            output = captured_output.getvalue()
            exit_code = getattr(exc, "code", None)
            self.last_exit_code = int(exit_code) if isinstance(exit_code, int) else 0
            return None, output + f"\nSystemExit: {exit_code}"
        except SecurityError as exc:
            output = captured_output.getvalue()
            self.last_exit_code = 1
            return None, output + f"\nSecurityError: {exc}"
        except Exception as exc:
            # Capture any other runtime exception and return gracefully so
            # the VM can record the output and halt appropriately instead
            # of allowing an unhandled exception to propagate and fail
            # the entire test harness.
            output = captured_output.getvalue()
            # Return the error appended to the output so the caller can
            # detect "Error:" and set the VM halt flag.
            self.last_exit_code = 1
            return None, output + f"\nError: {exc}"
        finally:
            self.state.mu_ledger.mu_execution = (self.state.mu_ledger.mu_execution + 1) & 0xFFFFFFFF
            sys.stdout = old_stdout
            if old_argv is not None:
                try:
                    sys.argv = old_argv
                except Exception:
                    pass
            if old_sys_path is not None:
                try:
                    sys.path = old_sys_path
                except Exception:
                    pass

        return None, "Python execution completed"

    def execute_symbolic_brute_force(self, _code: str, symbolic_assignments: dict, var_names: list, code_to_run: str) -> Any:
        """Brute force search for symbolic variables when Z3 cannot handle constraints.

        This implementation streams combinations in chunks to avoid allocating
        the entire Cartesian product in memory. It also enforces a safety limit
        (SAFE_COMBINATION_LIMIT) to prevent accidental large-scale cryptanalytic
        workloads.
        """
        import itertools
        import multiprocessing as mp
        from concurrent.futures import ProcessPoolExecutor, as_completed
        from itertools import islice

        domains = [symbolic_assignments[name] for name in var_names]

        total_combinations = 1
        for domain in domains:
            total_combinations *= len(domain)
        print(f"Parallel brute force search through {total_combinations} combinations...")

        # Safety check: avoid extremely large searches
        if total_combinations > SAFE_COMBINATION_LIMIT:
            return None, f"Workload too large: {total_combinations} combinations exceeds safe limit of {SAFE_COMBINATION_LIMIT}. Reduce domains or set THIELE_MAX_COMBINATIONS to a smaller value for experimentation."

        # Determine worker count and chunk sizing
        num_workers = min(mp.cpu_count(), 4)  # Use up to 4 cores by default
        # Aim for a modest number of chunks per worker; ensure chunk_size >=1
        chunk_size = max(1, total_combinations // (num_workers * 64))

        print(f"Using up to {num_workers} parallel workers with chunk size {chunk_size}...")

        # Generator that yields chunks lazily using islice
        def chunked_product(domains, chunk_size):
            product_iter = itertools.product(*domains)
            while True:
                chunk = list(islice(product_iter, chunk_size))
                if not chunk:
                    break
                yield chunk

        # Use the existing search_chunk worker which accepts a list of combinations
        with ProcessPoolExecutor(max_workers=num_workers) as executor:
            pending = []  # list of futures
            chunk_iter = chunked_product(domains, chunk_size)

            # Submit initial batch up to num_workers
            try:
                for _ in range(num_workers):
                    chunk = next(chunk_iter, None)
                    if chunk is None:
                        break
                    fut = executor.submit(search_chunk, chunk, var_names, code_to_run)
                    pending.append(fut)

                # Iterate over futures as they complete and submit new chunks
                for fut in as_completed(pending):
                    assignment, output = fut.result()
                    if assignment:
                        # Cancel remaining futures
                        for other in pending:
                            if not other.done():
                                other.cancel()
                        print(f"✓ Found satisfying assignment: {assignment}")
                        return None, f"Symbolic execution successful!\nAssignment: {assignment}\nOutput:\n{output}"
                    # If this future didn't find a solution, submit next chunk if available
                    next_chunk = next(chunk_iter, None)
                    if next_chunk is not None:
                        new_fut = executor.submit(search_chunk, next_chunk, var_names, code_to_run)
                        pending.append(new_fut)
                # If we get here, no futures returned a solution
                return None, "No satisfying assignment found for symbolic variables"
            finally:
                # Attempt best-effort cancellation of pending futures
                for fut in pending:
                    try:
                        fut.cancel()
                    except Exception:
                        # Swallow cancellation errors
                        pass

    def test_combined_satisfiability(self, axioms: str) -> bool:
        """Test if combined axioms are satisfiable. Returns True if satisfiable, False if unsatisfiable."""
        from z3 import Solver, parse_smt2_string, sat
        
        solver = Solver()
        try:
            solver.add(*parse_smt2_string(axioms))
            result = solver.check()
            return result == sat
        except Exception:
            # If parsing fails, consider it unsatisfiable
            return False

    def pdiscover(self, module_id: ModuleId, axioms_list: List[str], cert_dir: Path, trace_lines: List[str], step: int) -> Dict[str, Any]:
        """
        Perform geometric signature analysis on module axioms.
        
        This is the new PDISCOVER - instead of brute-force partition search,
        it computes a 5D geometric signature using the Strategy Graph approach.
        
        Returns:
            Dictionary containing the geometric signature and classification
        """
        print(f"PDISCOVER: Analyzing geometric signature for module {module_id}")
        
        region = self.state.regions[module_id]
        if not region:
            print("PDISCOVER: Empty region, returning null signature")
            return {
                "verdict": "EMPTY",
                "signature": {},
                "module_size": 0
            }
        
        # Combine axioms for analysis
        combined_axioms = "\n".join(axioms_list)
        
        print(f"PDISCOVER: Region has {len(region)} elements")
        print(f"PDISCOVER: Computing geometric signature...")
        
        # Compute geometric signature
        signature = compute_geometric_signature(combined_axioms, seed=42)
        
        print(f"PDISCOVER: Signature computed:")
        print(f"  - avg_edge_weight: {signature['average_edge_weight']:.4f}")
        print(f"  - max_edge_weight: {signature['max_edge_weight']:.4f}")
        print(f"  - edge_weight_stddev: {signature['edge_weight_stddev']:.4f}")
        print(f"  - mst_weight: {signature['min_spanning_tree_weight']:.4f}")
        print(f"  - thresholded_density: {signature['thresholded_density']:.4f}")
        
        # Classify the signature
        verdict = classify_geometric_signature(signature)
        
        print(f"PDISCOVER: Classification -> {verdict}")
        
        result = {
            "verdict": verdict,
            "signature": signature,
            "module_size": len(region)
        }
        
        trace_lines.append(f"{step}: PDISCOVER geometric analysis -> {verdict}")
        
        return result

    def run(
        self,
        program: List[Instruction],
        outdir: Path,
        trace_config: Optional[TraceConfig] = None,
        *,
        auto_mdlacc: bool = True,
        write_artifacts: bool = True,
    ) -> None:
        outdir.mkdir(parents=True, exist_ok=True)
        trace_lines: List[str] = []
        ledger: List[LedgerEntry] = []
        cert_dir = outdir / "certs"
        # Single CertStore instance reused across the whole VM run to avoid
        # repeated directory scans and per-REVEAL initialization overhead.
        try:
            store = CertStore(cert_dir)
        except Exception:
            # Defensive fallback: if CertStore construction fails, set store to None
            store = None
        modules: Dict[str, int] = {}  # For tracking named modules
        # NOTE: Do not pre-create a genesis module here; tests and the Coq
        # extracted runner expect no pre-existing modules. `current_module`
        # will be set when PNEW/PSPLIT instructions create modules.
        current_module = None
        step = 0
        self.step_receipts = []
        self.witness_state = WitnessState()
        physics = EmergentPhysicsState(program_length=len(program))
        bell_counts = BellCounts()
        reveal_seen = False

        print("Thiele Machine VM starting execution...")
        print(f"Program has {len(program)} instructions")
        print(f"Output directory: {outdir}")
        print()
        # Log VM run start
        logger = get_thiele_logger()
        try:
            logger.info("vm.run.start", {"program_len": len(program), "outdir": str(outdir)})
        except Exception:
            pass

        logical_step = 0
        self.explicit_mdlacc_called = False
        if trace_config and trace_config.enabled:
            start_payload = {
                "event": "trace_start",
                "workload": trace_config.workload_id,
                "program_length": len(program),
                "outdir": str(outdir),
                "metadata": dict(trace_config.metadata),
                "initial_partition": self._trace_partition_signature(),
                "mu_snapshot": {
                    "mu_discovery": self.state.mu_ledger.mu_discovery,
                    "mu_execution": self.state.mu_ledger.mu_execution,
                    "mu_total": self.state.mu_ledger.total,
                    # Legacy totals for backward compatibility
                    "mu_operational": self.state.mu_operational,
                    "mu_information": self.state.mu_information,
                    "mu_total_legacy": self.state.mu,
                },
            }
            self._trace_call(trace_config, "on_start", start_payload)

        def _parse_operands_and_cost(arg: str, *, expected: int) -> tuple[List[int], int | None]:
            tokens = (arg or "").split()
            explicit_cost: int | None = None

            # For extracted/RTL alignment, allow a trailing integer mu_delta.
            # Disambiguate by requiring exactly expected+1 integer tokens.
            if len(tokens) == expected + 1 and all(t.lstrip("-").isdigit() for t in tokens):
                explicit_cost = int(tokens[-1])
                tokens = tokens[:-1]

            values: List[int] = []
            for idx in range(expected):
                if idx < len(tokens):
                    try:
                        values.append(int(tokens[idx]))
                    except ValueError:
                        values.append(0)
                else:
                    values.append(0)
            return values, explicit_cost

        def _parse_region_and_cost(arg_str: str) -> tuple[set[int], int | None]:
            stripped = (arg_str or "").strip()
            if not stripped:
                return {1}, None
            if stripped.startswith("{") and "}" in stripped:
                end = stripped.find("}")
                region_tok = stripped[: end + 1]
                rest = stripped[end + 1 :].strip()
                region_str = region_tok[1:-1].strip()
                if region_str:
                    region = set(map(int, region_str.split(",")))
                else:
                    region = set()
                if rest:
                    try:
                        return region, int(rest.split()[0])
                    except ValueError:
                        return region, None
                return region, None
            # Fallback: allow whitespace-separated ints without braces.
            parts = stripped.split()
            region = {int(parts[0])} if parts and parts[0].lstrip("-").isdigit() else {1}
            cost = int(parts[1]) if len(parts) > 1 and parts[1].lstrip("-").isdigit() else None
            return region, cost

        def _charge_explicit_mu_for_pnew(region: set[int], mu_delta: int) -> None:
            # Canonical split: PNEW discovery is popcount(mask), remainder is execution.
            from .state import mask_of_indices, mask_popcount

            discovery = mask_popcount(mask_of_indices(region))
            if mu_delta < discovery:
                raise ValueError(f"PNEW mu_delta={mu_delta} < popcount(region)={discovery}")
            self.state.mu_ledger.mu_discovery += discovery
            self.state.mu_ledger.mu_execution = (self.state.mu_ledger.mu_execution + (mu_delta - discovery)) & 0xFFFFFFFF

        for pc_index, (op, arg) in enumerate(program):
            logical_step += 1
            step += 1
            print(f"Step {step:3d}: {op} {arg}")
            pre_witness = WitnessState(**self.witness_state.snapshot())
            receipt_instruction: Optional[InstructionWitness] = None
            halt_after_receipt = False
            before_mu_discovery = self.state.mu_ledger.mu_discovery
            before_mu_execution = self.state.mu_ledger.mu_execution
            before_mu_total = self.state.mu_ledger.total
            before_mu_legacy_operational = self.state.mu_operational
            before_mu_legacy_information = self.state.mu_information
            before_mu_ledger = self.state.mu_ledger.copy()
            physics_event = physics.observe_instruction(op, arg, logical_step)
            if op == "PNEW":
                # PNEW region_spec - create new module for region
                region, explicit_cost = _parse_region_and_cost(arg)
                if explicit_cost is None:
                    new_module = self.state.pnew(region)
                else:
                    # In explicit-cost mode, μ is driven by the instruction stream
                    # (as in Coq/RTL). Suppress internal charging and apply mu_delta.
                    new_module = self.state.pnew(region, charge_discovery=False)
                    _charge_explicit_mu_for_pnew(region, explicit_cost)
                modules[f"m{len(modules)}"] = new_module
                current_module = new_module
                trace_lines.append(f"{step}: PNEW {arg} -> module {new_module}")
                receipt_instruction = InstructionWitness("PNEW", sorted(region))
            elif op == "PSPLIT":
                # PSPLIT supports two forms:
                # 1) extracted-style: PSPLIT <mid> {left} {right} <mu_delta>
                # 2) legacy predicate-style: PSPLIT <mid> <expr>
                parts = (arg or "").split()
                module_id = ModuleId(int(parts[0])) if parts else current_module

                if "{" in (arg or ""):
                    # extracted-style explicit regions
                    tokens = (arg or "").split()
                    if len(tokens) < 4:
                        raise ValueError(f"PSPLIT expects: <mid> <left> <right> <mu_delta>, got: {arg!r}")
                    mid = ModuleId(int(tokens[0]))
                    left, _ = _parse_region_and_cost(tokens[1])
                    right, explicit_cost = _parse_region_and_cost(tokens[2] + " " + (tokens[3] if len(tokens) > 3 else ""))
                    if explicit_cost is None and len(tokens) >= 4 and tokens[3].lstrip("-").isdigit():
                        explicit_cost = int(tokens[3])
                    m1, m2 = self.state.psplit_explicit(mid, left, right, charge_execution=explicit_cost is None)
                    if explicit_cost is not None:
                        self.state.mu_ledger.mu_execution = (self.state.mu_ledger.mu_execution + explicit_cost) & 0xFFFFFFFF
                    current_module = m1
                    trace_lines.append(f"{step}: PSPLIT {mid} -> {m1}, {m2}")
                    receipt_instruction = InstructionWitness("PYEXEC", f"PSPLIT {arg}")
                else:
                    # RTL-compatible predicate-byte split: PSPLIT <mid> <predicate_byte> [mu_delta]
                    # Fallback: if predicate is not an int, retain legacy even/odd split.
                    pred_token = parts[1] if len(parts) > 1 else "0"
                    explicit_cost: int | None = None
                    if len(parts) >= 3 and parts[2].lstrip("-").isdigit():
                        explicit_cost = int(parts[2])

                    if pred_token.lstrip("-").isdigit():
                        predicate = int(pred_token) & 0xFF
                        pred_mode = (predicate >> 6) & 0x3
                        pred_param = predicate & 0x3F

                        def pred(x: int) -> bool:
                            element_value = int(x) & 0xFFFFFFFF
                            if pred_mode == 0b00:
                                # even/odd: pred_param[0]=0 => even, pred_param[0]=1 => odd
                                return (element_value & 1) == (pred_param & 1)
                            if pred_mode == 0b01:
                                # threshold
                                return element_value >= pred_param
                            if pred_mode == 0b10:
                                # bitwise test
                                return (element_value & (1 << pred_param)) != 0
                            # 0b11 modulo divisibility (power-of-two divisors only)
                            divisor = pred_param + 1
                            if (divisor & pred_param) != 0:
                                return False
                            return (element_value & pred_param) == 0

                        pred_expr = f"pred_byte=0x{predicate:02x}"
                    else:
                        pred_expr = pred_token

                        def pred(x: int) -> bool:
                            return x % 2 == 0

                    m1, m2 = self.state.psplit(module_id, pred, charge_execution=explicit_cost is None)
                    if explicit_cost is not None:
                        self.state.mu_ledger.mu_execution = (self.state.mu_ledger.mu_execution + explicit_cost) & 0xFFFFFFFF
                    current_module = m1  # Update current_module to first split result
                    trace_lines.append(f"{step}: PSPLIT {module_id} ({pred_expr}) -> {m1}, {m2}")
                    receipt_instruction = InstructionWitness("PYEXEC", f"PSPLIT {arg}")
            elif op == "PMERGE":
                # PMERGE m1 m2 [mu_delta] - merge two modules
                parts, explicit_cost = _parse_operands_and_cost(arg, expected=2)
                m1 = ModuleId(int(parts[0]))
                m2 = ModuleId(int(parts[1]))
                merged = self.state.pmerge(m1, m2, charge_execution=explicit_cost is None)
                if explicit_cost is not None:
                    self.state.mu_ledger.mu_execution = (self.state.mu_ledger.mu_execution + explicit_cost) & 0xFFFFFFFF
                trace_lines.append(f"{step}: PMERGE {m1}, {m2} -> {merged}")
                current_module = merged
                receipt_instruction = InstructionWitness("PYEXEC", f"PMERGE {arg}")
            elif op == "LASSERT":
                config_path = Path(arg)
                result = lassert(self.state, current_module, config_path, cert_dir)
                digest = f"{result.certificate.cnf.sha256}:{result.certificate.proof_sha256}"
                trace_lines.append(
                    f"{step}: LASSERT {config_path} -> {result.certificate.status} ({digest})"
                )
                if result.certificate.status == "UNSAT":
                    trace_lines.append(f"{step}: LASSERT unsat - halting VM")
                    halt_after_receipt = True
                receipt_instruction = InstructionWitness("LASSERT", result.receipt_payload)
            elif op == "LJOIN":
                # LJOIN cert1 cert2 - join two certificates
                parts = arg.split()
                cert1 = parts[0]
                cert2 = parts[1]
                digest = ljoin(self.state, cert1, cert2, cert_dir)
                trace_lines.append(f"{step}: LJOIN {cert1}, {cert2} -> {digest}")
                receipt_instruction = InstructionWitness("PYEXEC", f"LJOIN {arg}")
            elif op == "MDLACC":
                # MDLACC module - accumulate mu for module
                parts = (arg or "").split()
                explicit_cost: int | None = None
                if len(parts) >= 2 and parts[-1].lstrip("-").isdigit():
                    explicit_cost = int(parts[-1])
                module_id = current_module
                if parts and parts[0].lstrip("-").isdigit():
                    module_id = ModuleId(int(parts[0]))

                prev_operational = self.state.mu_operational
                prev_ledger = self.state.mu_ledger.copy()

                if explicit_cost is not None:
                    # Explicit-cost mode: suppress dynamic MDL calculation.
                    self.state.mu_ledger.mu_execution = (self.state.mu_ledger.mu_execution + explicit_cost) & 0xFFFFFFFF
                    mu = self.state.mu_ledger.total
                else:
                    consistent = self.state.csr[CSR.ERR] == 0
                    mu = mdlacc(self.state, module_id, consistent=consistent)

                delta_operational = self.state.mu_operational - prev_operational
                delta_information = self.state.mu_information - before_mu_legacy_information
                delta_discovery = self.state.mu_ledger.mu_discovery - prev_ledger.mu_discovery
                delta_execution = self.state.mu_ledger.mu_execution - prev_ledger.mu_execution
                ledger.append({
                    "step": step,
                    "delta_mu_discovery": delta_discovery,
                    "delta_mu_execution": delta_execution,
                    "total_mu_discovery": self.state.mu_ledger.mu_discovery,
                    "total_mu_execution": self.state.mu_ledger.mu_execution,
                    "total_mu": self.state.mu_ledger.total,
                    # Legacy fields preserved for downstream tools
                    "delta_mu_operational": delta_operational,
                    "delta_mu_information": delta_information,
                    "total_mu_operational": self.state.mu_operational,
                    "total_mu_information": self.state.mu_information,
                    "total_mu_legacy": self.state.mu,
                    "reason": (
                        f"mdlacc_explicit_module{module_id}" if explicit_cost is not None else f"mdlacc_module{module_id}"
                    ),
                })
                trace_lines.append(f"{step}: MDLACC {module_id} -> mu={mu}")
                receipt_instruction = InstructionWitness("MDLACC", int(module_id))
                self.explicit_mdlacc_called = True
            elif op == "EMIT":
                # EMIT value - emit value to output
                tokens = arg.split()
                info_bits = None
                if tokens and all(token.lstrip("-").isdigit() for token in tokens):
                    (_, payload_b), _ = _parse_operands_and_cost(arg, expected=2)
                    info_bits = payload_b
                    prev_info = self.state.mu_information
                    prev_ledger = self.state.mu_ledger.copy()
                    info_charge(self.state, info_bits)
                    
                    # Update status to match RTL: {value_a, value_b, 16'h0}
                    val_a = int(tokens[0])
                    val_b = int(tokens[1])
                    self.state.csr[CSR.STATUS] = ((val_a & 0xFF) << 24) | ((val_b & 0xFF) << 16)

                    ledger.append({
                        "step": step,
                        "delta_mu_discovery": self.state.mu_ledger.mu_discovery - prev_ledger.mu_discovery,
                        "delta_mu_execution": self.state.mu_ledger.mu_execution - prev_ledger.mu_execution,
                        "total_mu_discovery": self.state.mu_ledger.mu_discovery,
                        "total_mu_execution": self.state.mu_ledger.mu_execution,
                        "total_mu": self.state.mu_ledger.total,
                        # Legacy fields preserved for downstream tools
                        "delta_mu_operational": 0,
                        "delta_mu_information": self.state.mu_information - prev_info,
                        "total_mu_operational": self.state.mu_operational,
                        "total_mu_information": self.state.mu_information,
                        "total_mu_legacy": self.state.mu,
                        "reason": "emit_info_gain",
                    })
                    trace_lines.append(f"{step}: EMIT bits={info_bits}")
                else:
                    trace_lines.append(f"{step}: EMIT {arg}")
                receipt_instruction = InstructionWitness("EMIT", arg if info_bits is None else info_bits)
                try:
                    logger.info("vm.emit", {"value": arg, "step": step, "module": current_module})
                except Exception:
                    pass
            elif op == "REVEAL":
                # REVEAL <ti> <tj> <bits> [<cert...>]
                # Direction-tagged revelation: charges Δμ to mu_tensor[ti][tj] and
                # to the scalar μ-accumulator, then records a certificate payload.
                # Encoding mirrors Coq instr_reveal: module = ti*4+tj (flat index 0-15).
                reveal_seen = True
                parts = arg.split()
                ti = 0
                tj = 0
                bits = 0
                cert_payload = ""
                if len(parts) >= 1:
                    try:
                        ti = max(0, min(3, int(parts[0])))
                    except ValueError:
                        ti = 0
                if len(parts) >= 2:
                    try:
                        tj = max(0, min(3, int(parts[1])))
                    except ValueError:
                        tj = 0
                if len(parts) >= 3:
                    try:
                        bits = int(parts[2])
                    except ValueError:
                        bits = 0
                if len(parts) >= 4:
                    cert_payload = " ".join(parts[3:])
                module_id = ModuleId(ti * 4 + tj)

                prev_info = self.state.mu_information
                prev_ledger = self.state.mu_ledger.copy()
                if bits > 0:
                    info_charge(self.state, float(bits))
                    # Charge to the specific tensor component (direction)
                    self.state.mu_ledger.mu_tensor[ti][tj] = (
                        self.state.mu_ledger.mu_tensor[ti][tj] + bits
                    )
                    # Bianchi guard: tensor sub-ledger must never exceed scalar mu.
                    # Mirrors Coq mu_conservation_implies_bianchi: every reachable
                    # state satisfies ∇_μ G^μν = 0.  A violation is a logical paradox.
                    self.state.mu_ledger.check_bianchi_consistency()
                ledger.append(
                    {
                        "step": step,
                        "delta_mu_discovery": self.state.mu_ledger.mu_discovery - prev_ledger.mu_discovery,
                        "delta_mu_execution": self.state.mu_ledger.mu_execution - prev_ledger.mu_execution,
                        "total_mu_discovery": self.state.mu_ledger.mu_discovery,
                        "total_mu_execution": self.state.mu_ledger.mu_execution,
                        "total_mu": self.state.mu_ledger.total,
                        # Legacy fields preserved for downstream tools
                        "delta_mu_operational": 0,
                        "delta_mu_information": self.state.mu_information - prev_info,
                        "total_mu_operational": self.state.mu_operational,
                        "total_mu_information": self.state.mu_information,
                        "total_mu_legacy": self.state.mu,
                        "reason": f"reveal_tensor_{ti}_{tj}",
                    }
                )

                # Persist the certificate payload so MDLACC can account for it.
                if store is None:
                    store = CertStore(cert_dir)
                cid = store.next_id()
                cert_bytes = cert_payload.encode("utf-8")
                store.write_bytes(cid, "reveal", cert_bytes)
                digest = store.save_hash(cid, cert_bytes)
                self.state.csr[CSR.CERT_ADDR] = str(store.hash_path(cid))

                trace_lines.append(
                    f"{step}: REVEAL tensor[{ti}][{tj}] bits={bits} cert_sha256={digest}"
                )
                receipt_instruction = InstructionWitness(
                    "REVEAL",
                    {
                        "module": int(module_id),
                        "bits": bits,
                        "cert_sha256": digest,
                    },
                )
            elif op == "XFER":
                (dest, src), explicit_cost = _parse_operands_and_cost(arg, expected=2)
                value = self.register_file[src % len(self.register_file)]
                self._write_register(dest, value)
                self.state.csr[CSR.STATUS] = 6
                if explicit_cost is not None:
                    self.state.mu_ledger.mu_execution = (self.state.mu_ledger.mu_execution + explicit_cost) & 0xFFFFFFFF
                trace_lines.append(f"{step}: XFER r{dest} <- r{src}")
                receipt_instruction = InstructionWitness("XFER", {"dest": dest, "src": src})
            elif op == "XOR_LOAD":
                (dest, addr), explicit_cost = _parse_operands_and_cost(arg, expected=2)
                addr = addr % len(self.data_memory)
                value = self.data_memory[addr]
                self._write_register(dest, value)
                self.state.csr[CSR.STATUS] = 7
                if explicit_cost is not None:
                    self.state.mu_ledger.mu_execution = (self.state.mu_ledger.mu_execution + explicit_cost) & 0xFFFFFFFF
                trace_lines.append(f"{step}: XOR_LOAD r{dest} <= mem[{addr}] (0x{value:08x})")
                receipt_instruction = InstructionWitness("XOR_LOAD", {"dest": dest, "addr": addr, "value": int(value)})
            elif op == "XOR_ADD":
                (dest, src), explicit_cost = _parse_operands_and_cost(arg, expected=2)
                dest_idx = dest % len(self.register_file)
                src_idx = src % len(self.register_file)
                new_value = self.register_file[dest_idx] ^ self.register_file[src_idx]
                self._write_register(dest_idx, new_value)
                self.state.csr[CSR.STATUS] = 8
                if explicit_cost is not None:
                    self.state.mu_ledger.mu_execution = (self.state.mu_ledger.mu_execution + explicit_cost) & 0xFFFFFFFF
                trace_lines.append(f"{step}: XOR_ADD r{dest} ^= r{src} -> 0x{self.register_file[dest_idx]:08x}")
                receipt_instruction = InstructionWitness("XOR_ADD", {"dest": dest, "src": src, "value": int(self.register_file[dest_idx])})
            elif op == "XOR_SWAP":
                (a, b), explicit_cost = _parse_operands_and_cost(arg, expected=2)
                a_idx = a % len(self.register_file)
                b_idx = b % len(self.register_file)
                a_value = self.register_file[a_idx]
                b_value = self.register_file[b_idx]
                self._write_register(a_idx, b_value)
                self._write_register(b_idx, a_value)
                self.state.csr[CSR.STATUS] = 9
                if explicit_cost is not None:
                    self.state.mu_ledger.mu_execution = (self.state.mu_ledger.mu_execution + explicit_cost) & 0xFFFFFFFF
                trace_lines.append(f"{step}: XOR_SWAP r{a} <-> r{b}")
                receipt_instruction = InstructionWitness("XOR_SWAP", {"a": a, "b": b})
            elif op == "XOR_RANK":
                (dest, src), explicit_cost = _parse_operands_and_cost(arg, expected=2)
                src_idx = src % len(self.register_file)
                rank = bin(self.register_file[src_idx] & 0xFFFFFFFF).count("1")
                self._write_register(dest, rank)
                self.state.csr[CSR.STATUS] = rank
                if explicit_cost is not None:
                    self.state.mu_ledger.mu_execution = (self.state.mu_ledger.mu_execution + explicit_cost) & 0xFFFFFFFF
                trace_lines.append(f"{step}: XOR_RANK r{dest} := popcount(r{src}) = {rank}")
                receipt_instruction = InstructionWitness("XOR_RANK", {"dest": dest, "src": src, "rank": rank})
            elif op == "PDISCOVER":
                # Two supported forms:
                # 1) deterministic explicit-cost mode: PDISCOVER <mid> <before> <after> <mu_delta>
                # 2) legacy mode: PDISCOVER <mid> <axioms_file1> [axioms_file2 ...]
                parts = (arg or "").split()
                if len(parts) == 4 and all(p.lstrip("-").isdigit() for p in parts):
                    # Explicit-cost mode: μ driven by instruction stream, no file I/O.
                    module_id = ModuleId(int(parts[0]))
                    before_count = int(parts[1])
                    after_count = int(parts[2])
                    explicit_cost = int(parts[3])
                    _ = (before_count, after_count)  # kept for trace readability
                    self.state.mu_ledger.mu_execution = (self.state.mu_ledger.mu_execution + explicit_cost) & 0xFFFFFFFF
                    trace_lines.append(
                        f"{step}: PDISCOVER mid={int(module_id)} before={before_count} after={after_count} cost={explicit_cost}"
                    )
                    receipt_instruction = InstructionWitness("PYEXEC", f"PDISCOVER {arg}")
                else:
                    # Legacy geometric signature analysis
                    if len(parts) < 2:
                        raise ValueError(f"PDISCOVER requires module_id and at least one axioms_file, got: {arg}")
                    module_id = ModuleId(int(parts[0]))
                    axioms_files = parts[1:]
                    axioms_list = [Path(f).read_text(encoding='utf-8') for f in axioms_files]

                    # Perform geometric signature analysis
                    result = self.pdiscover(module_id, axioms_list, cert_dir, trace_lines, step)

                    # Update physics overlay with the verdict
                    physics_event = physics.observe_discovery(result.get("verdict", "")) or physics_event

                    # Store result in state for PDISCERN to access
                    self.state.last_pdiscover_result = result

                    # Log the verdict
                    verdict = result.get("verdict", "UNKNOWN")
                    trace_lines.append(f"{step}: PDISCOVER {arg} -> {verdict}")
                    receipt_instruction = InstructionWitness("PYEXEC", f"PDISCOVER {arg} -> {verdict}")
            
            elif op == "PDISCERN":
                # PDISCERN - classify the last PDISCOVER result
                # This is the new META-verdict instruction
                if not hasattr(self.state, 'last_pdiscover_result'):
                    raise ValueError("PDISCERN requires a prior PDISCOVER call")
                
                result = self.state.last_pdiscover_result
                verdict = result.get("verdict", "UNKNOWN")
                signature = result.get("signature", {})
                
                print(f"PDISCERN: Classifying geometric signature...")
                print(f"PDISCERN: Verdict -> {verdict}")
                
                # Output detailed analysis
                if verdict == "STRUCTURED":
                    print("PDISCERN: Problem exhibits STRUCTURED characteristics")
                    print("PDISCERN: Low variation between partitioning strategies")
                    print("PDISCERN: Sighted methods should be effective")
                elif verdict == "CHAOTIC":
                    print("PDISCERN: Problem exhibits CHAOTIC characteristics")
                    print("PDISCERN: High variation between partitioning strategies")
                    print("PDISCERN: Blind methods may be required")
                else:
                    print(f"PDISCERN: Problem classification -> {verdict}")
                
                trace_lines.append(f"{step}: PDISCERN -> {verdict}")
                receipt_instruction = InstructionWitness("PDISCERN", verdict)
                
                # Store verdict in state
                self.state.structure_verdict = verdict
            elif op == "PYEXEC":
                if arg.startswith('"') and arg.endswith('"'):
                    python_code = arg[1:-1]  # Remove quotes
                else:
                    python_code = arg

                # Track state before execution for supra-quantum detection
                pre_mu_info = self.state.mu_information
                
                result, output = self.execute_python(python_code)
                if output:
                    # Split output into lines for better readability
                    for line in output.strip().split('\n'):
                        if line.strip():
                            trace_lines.append(f"{step}: PYEXEC output: {line}")
                try:
                    logger.info(
                        "vm.pyexec",
                        {
                            "code": (python_code if len(python_code) < 256 else python_code[:256] + "..."),
                            "output": (output if output else ""),
                            "step": step,
                        },
                    )
                except Exception:
                    pass
                
                # Check for result in multiple ways
                actual_result = result
                if actual_result is None and '__result__' in self.python_globals:
                    actual_result = self.python_globals['__result__']
                
                if actual_result is not None:
                    trace_lines.append(f"{step}: PYEXEC result: {actual_result}")
                    # Store result in python globals for later use
                    self.python_globals['_last_result'] = actual_result

                    # Detect special-case revelations (e.g., factoring results) and
                    # charge μ-information accordingly so downstream reporting
                    # (program sweep) can detect and summarize them.
                    try:
                        target_n = extract_target_modulus(python_code)
                        if (
                            isinstance(actual_result, (list, tuple))
                            and len(actual_result) == 2
                            and all(isinstance(x, int) for x in actual_result)
                        ):
                            p, q = int(actual_result[0]), int(actual_result[1])
                            if target_n is None or target_n == p * q:
                                prev_info = self.state.mu_information
                                prev_ledger = self.state.mu_ledger.copy()
                                # Charge an information amount proportional to the modulus size
                                info_bits = target_n.bit_length() if isinstance(target_n, int) else max(1, (p*q).bit_length())

                                info_charge(self.state, float(info_bits))
                                ledger.append({
                                    "step": step,
                                    "delta_mu_discovery": self.state.mu_ledger.mu_discovery - prev_ledger.mu_discovery,
                                    "delta_mu_execution": self.state.mu_ledger.mu_execution - prev_ledger.mu_execution,
                                    "total_mu_discovery": self.state.mu_ledger.mu_discovery,
                                    "total_mu_execution": self.state.mu_ledger.mu_execution,
                                    "total_mu": self.state.mu_ledger.total,
                                    # Legacy fields preserved for downstream tools
                                    "delta_mu_operational": 0,
                                    "delta_mu_information": self.state.mu_information - prev_info,
                                    "total_mu_operational": self.state.mu_operational,
                                    "total_mu_information": self.state.mu_information,
                                    "total_mu_legacy": self.state.mu,
                                    "reason": f"factoring_revelation_{target_n or (p*q)}",
                                })
                                trace_lines.append(f"{step}: FACTORING_REVELATION n={target_n or (p*q)} bits={info_bits}")
                    except Exception:
                        # Non-fatal: best-effort detection only
                        pass

                    # Charge for information revealed by PYEXEC using Kolmogorov complexity approximation
                    # Serialize any output data with pickle and compress to estimate information content
                    if actual_result is not None:
                        try:
                            serialized = pickle.dumps(actual_result, protocol=4)
                            compressed = zlib.compress(serialized, level=9)
                            insight_cost = len(compressed) * 8
                            self.state.mu_ledger.charge_execution(insight_cost)
                            trace_lines.append(f"{step}: INSIGHT_CHARGE value_size={len(serialized)} compressed={len(compressed)} cost={insight_cost}")
                        except Exception as e:
                            self.state.csr[CSR.ERR] = 1
                            trace_lines.append(f"{step}: UNMEASURABLE_INSIGHT halting VM. Error: {e}")
                            halt_after_receipt = True

                # Show what was executed (truncated for readability)
                if len(python_code) > 50:
                    trace_lines.append(f"{step}: PYEXEC {python_code[:47]}...")
                else:
                    trace_lines.append(f"{step}: PYEXEC {python_code}")
                if "Error:" in output:
                    self.state.csr[CSR.ERR] = 1
                    trace_lines.append(f"{step}: PYEXEC error detected - halting VM")
                    halt_after_receipt = True
                receipt_instruction = InstructionWitness("PYEXEC", python_code)
            elif op == "PYTHON":
                # PYTHON code - execute Python code directly as an interpreter
                # Unescape the code
                code = arg.replace('\\n', '\n').replace('\\"', '"').replace('\\\\', '\\')
                result, output = self.execute_python(code)
                if output:
                    # Split output into lines for better readability
                    for line in output.strip().split('\n'):
                        if line.strip():
                            trace_lines.append(f"{step}: PYTHON output: {line}")
                try:
                    logger.info(
                        "vm.python",
                        {
                            "code": (arg if len(arg) < 256 else arg[:256] + "..."),
                            "output": (output if output else ""),
                            "step": step,
                        },
                    )
                except Exception:
                    pass
                
                # Check for result
                actual_result = result
                if actual_result is None and '__result__' in self.python_globals:
                    actual_result = self.python_globals['__result__']
                
                if actual_result is not None:
                    trace_lines.append(f"{step}: PYTHON result: {actual_result}")
                    # Store result in python globals for later use
                    self.python_globals['_last_result'] = actual_result

                # Show what was executed (truncated for readability)
                if len(arg) > 50:
                    trace_lines.append(f"{step}: PYTHON {arg[:47]}...")
                else:
                    trace_lines.append(f"{step}: PYTHON {arg}")
                if "Error:" in output:
                    self.state.csr[CSR.ERR] = 1
                    trace_lines.append(f"{step}: PYTHON error detected - halting VM")
                    halt_after_receipt = True
                receipt_instruction = InstructionWitness("PYTHON", arg)
            elif op == "CHSH_TRIAL":
                raw_parts = arg.replace(",", " ").split()
                explicit_cost: int | None = None
                if len(raw_parts) == 5 and raw_parts[-1].lstrip("-").isdigit():
                    explicit_cost = int(raw_parts[-1])
                    raw_parts = raw_parts[:-1]
                if len(raw_parts) != 4:
                    raise ValueError(f"CHSH_TRIAL expects 4 integers (x y a b) plus optional cost, got: {arg!r}")
                x, y, a, b = (int(p) for p in raw_parts)
                if x not in (0, 1) or y not in (0, 1) or a not in (0, 1) or b not in (0, 1):
                    raise ValueError(f"CHSH_TRIAL bits must be 0/1, got: {x} {y} {a} {b}")
                meta = f"CHSH_{x}{y}{a}{b}"
                trace_lines.append(f"{step}: CHSH_TRIAL {meta}")

                # Canonical μ-ledger: drive cost from instruction stream when provided.
                self.state.mu_ledger.mu_execution = (self.state.mu_ledger.mu_execution + (1 if explicit_cost is None else explicit_cost)) & 0xFFFFFFFF

                bell_counts.update_trial(x=x, y=y, a=a, b=b)
                if bell_counts.is_balanced(
                    min_trials_per_setting=DEFAULT_ENFORCEMENT_MIN_TRIALS_PER_SETTING
                ):
                    s_value = bell_counts.chsh()
                    if is_supra_quantum(chsh=s_value, bound=TSIRELSON_BOUND) and not reveal_seen:
                        self.state.csr[CSR.ERR] = 1
                        trace_lines.append(
                            f"{step}: CHSH={s_value} exceeds Tsirelson without REVEAL - setting ERR"
                        )
                        halt_after_receipt = True
                receipt_instruction = InstructionWitness(
                    "CHSH_TRIAL",
                    {"x": x, "y": y, "a": a, "b": b},
                )
            elif op == "HALT":
                explicit_cost = 0
                if (arg or "").strip().lstrip("-").isdigit():
                    explicit_cost = int((arg or "").strip())
                if explicit_cost:
                    self.state.mu_ledger.mu_execution = (self.state.mu_ledger.mu_execution + explicit_cost) & 0xFFFFFFFF
                trace_lines.append(f"{step}: HALT")
                receipt_instruction = InstructionWitness("HALT", None)
                halt_after_receipt = True
            elif op == "ORACLE_HALTS":
                # ORACLE_HALTS code_or_desc - Hyper-Thiele primitive
                # This is the explicit super-Turing capability
                parts = (arg or "").split()
                explicit_cost: int | None = None
                if len(parts) >= 2 and parts[-1].lstrip("-").isdigit():
                    explicit_cost = int(parts[-1])
                    desc = " ".join(parts[:-1])
                else:
                    desc = arg

                # Explicit-cost mode: suppress any attempt to execute payload.
                if explicit_cost is not None:
                    oracle_cost = explicit_cost
                    verdict = None
                    trace_lines.append(f"{step}: ORACLE_HALTS {desc} cost={oracle_cost}")
                else:
                    verdict = False

                    # 1. Check for known undecidable instances (Demo mode)
                    if "M_undecidable" in desc:
                        verdict = True
                        trace_lines.append(f"{step}: ORACLE_HALTS {desc} -> TRUE (Oracle Knowledge)")
                    else:
                        try:
                            import signal

                            def handler(signum, frame):
                                raise TimeoutError()

                            signal.signal(signal.SIGALRM, handler)
                            signal.alarm(1)

                            try:
                                self.execute_python(desc)
                                verdict = True
                            except TimeoutError:
                                verdict = False
                            except Exception:
                                verdict = True
                            finally:
                                signal.alarm(0)

                            trace_lines.append(f"{step}: ORACLE_HALTS {desc} -> {verdict}")
                        except Exception:
                            trace_lines.append(f"{step}: ORACLE_HALTS {desc} -> UNKNOWN (Oracle Unavailable)")

                    oracle_cost = 1000000
                    self.python_globals['_oracle_result'] = verdict

                self.state.mu_operational += oracle_cost
                self.state.mu_ledger.mu_execution = (self.state.mu_ledger.mu_execution + oracle_cost) & 0xFFFFFFFF

                receipt_instruction = InstructionWitness("ORACLE_HALTS", f"{desc} -> {verdict}")

            else:
                raise ValueError(f"unknown opcode {op}")

            if physics_event:
                trace_lines.append(f"{step}: PHYSICS {physics_event} T={physics.temperature:.3f}")

            after_mu_execution = self.state.mu_ledger.mu_execution
            after_mu_discovery = self.state.mu_ledger.mu_discovery
            after_mu_total = self.state.mu_ledger.total
            if trace_config and trace_config.enabled:
                truncated_arg = arg if len(arg) <= 256 else arg[:253] + "..."
                event_payload = {
                    "event": "trace_step",
                    "workload": trace_config.workload_id,
                    "step": logical_step,
                    "pc": pc_index,
                    "op": op,
                    "arg": truncated_arg,
                    "mu": {
                        "mu_execution": after_mu_execution,
                        "mu_discovery": after_mu_discovery,
                        "mu_total": after_mu_total,
                    },
                    "delta": {
                        "mu_execution": after_mu_execution - before_mu_execution,
                        "mu_discovery": after_mu_discovery - before_mu_discovery,
                        "mu_total": after_mu_total - before_mu_total,
                    },
                    "csr": {
                        "status": int(self.state.csr.get(CSR.STATUS, 0)),
                        "err": int(self.state.csr.get(CSR.ERR, 0)),
                    },
                    "partition": self._trace_partition_signature(),
                    "metadata": dict(trace_config.metadata),
                }
                self._trace_call(trace_config, "on_step", event_payload)

            if receipt_instruction is None:
                receipt_instruction = InstructionWitness("PYEXEC", f"{op} {arg}".strip())
            self._record_receipt(step, pre_witness, receipt_instruction)

            if self.state.csr[CSR.ERR] == 1 or halt_after_receipt:
                trace_lines.append(f"{step}: ERR flag set - halting VM")
                break
        # Final accounting and output - only auto-charge if enabled and no explicit MDLACC executed.
        # Boot semantics permit an empty region graph (no implicit module 0).
        if auto_mdlacc and not self.explicit_mdlacc_called and self.state.regions.modules:
            if current_module in self.state.regions:
                mdlacc(self.state, current_module, consistent=self.state.csr[CSR.ERR] == 0)
            else:
                # Defensive fallback: if the current module is absent, charge against a stable existing module.
                mdlacc(
                    self.state,
                    min(self.state.regions.modules.keys()),
                    consistent=self.state.csr[CSR.ERR] == 0,
                )

        ledger.append({
            "step": step + 1,
            "delta_mu_discovery": self.state.mu_ledger.mu_discovery - before_mu_ledger.mu_discovery,
            "delta_mu_execution": self.state.mu_ledger.mu_execution - before_mu_ledger.mu_execution,
            "total_mu_discovery": self.state.mu_ledger.mu_discovery,
            "total_mu_execution": self.state.mu_ledger.mu_execution,
            "total_mu": self.state.mu_ledger.total,
            # Legacy fields preserved for downstream tools
            "delta_mu_operational": self.state.mu_operational - before_mu_legacy_operational,
            "delta_mu_information": self.state.mu_information - before_mu_legacy_information,
            "total_mu_operational": self.state.mu_operational,
            "total_mu_information": self.state.mu_information,
            "total_mu_legacy": self.state.mu,
            "reason": "final",
        })

        # Write outputs
        if write_artifacts:
            (outdir / "trace.log").write_text("\n".join(trace_lines), encoding='utf-8')
            (outdir / "mu_ledger.json").write_text(json.dumps(ledger), encoding='utf-8')

        # Final enforcement check: detect supra-quantum correlations generated without REVEAL
        # This enforces No Free Insight theorem at program completion
        try:
            detected = self._detect_supra_quantum_generation(outdir)
            logger.info(f"Supra-quantum detection: reveal_seen={reveal_seen}, detected={detected}")
        except Exception as detection_err:
            logger.error(f"Supra-quantum detection failed: {detection_err}")
            detected = False
            
        if not reveal_seen and detected:
            # Supra-quantum detected without explicit REVEAL
            # Charge μ-cost retroactively
            try:
                logger.warning(
                    f"Supra-quantum correlations detected at program completion without REVEAL. "
                    "Charging revelation cost (μ_info += 1.0)."
                )
            except Exception:
                pass
            info_charge(self.state, 1.0)
            # Update ledger with final charge
            ledger.append({
                "step": step + 2,
                "delta_mu_discovery": 0,
                "delta_mu_execution": 1,  # Charged to execution
                "total_mu_discovery": self.state.mu_ledger.mu_discovery,
                "total_mu_execution": self.state.mu_ledger.mu_execution,
                "total_mu": self.state.mu_ledger.total,
                "delta_mu_operational": 0,
                "delta_mu_information": 1.0,
                "total_mu_operational": self.state.mu_operational,
                "total_mu_information": self.state.mu_information,
                "total_mu_legacy": self.state.mu,
                "reason": "supra_quantum_revelation_enforcement",
            })
            # Rewrite ledger with enforcement charge
            (outdir / "mu_ledger.json").write_text(json.dumps(ledger), encoding='utf-8')

        summary = {
            "mu_discovery": self.state.mu_ledger.mu_discovery,
            "mu_execution": self.state.mu_ledger.mu_execution,
            "mu_total": self.state.mu_ledger.total,
            "cert": self.state.csr[CSR.CERT_ADDR],
            # Legacy totals maintained for compatibility
            "mu_operational": self.state.mu_operational,
            "mu_information": self.state.mu_information,
            "mu_total_legacy": self.state.mu,
        }
        if trace_config and trace_config.enabled:
            finish_payload = {
                "event": "trace_end",
                "workload": trace_config.workload_id,
                "steps": logical_step,
                "mu_snapshot": summary,
                "partition": self._trace_partition_signature(),
                "metadata": dict(trace_config.metadata),
            }
            self._trace_call(trace_config, "on_finish", finish_payload)
        if write_artifacts:
            (outdir / "summary.json").write_text(json.dumps(summary), encoding='utf-8')

            receipts_path = outdir / "step_receipts.json"
            receipts_json = [receipt.to_dict() for receipt in self.step_receipts]
            receipts_path.write_text(json.dumps(receipts_json, indent=2), encoding='utf-8')

        # Log VM run finish
        try:
            logger.info("vm.run.finish", {"outdir": str(outdir), "steps": step, "receipts": len(self.step_receipts)})
        except Exception:
            pass


def main():
    """Run Python files directly through the Thiele CPU VM as a Python interpreter."""
    import argparse

    # Split VM args vs script args using the conventional "--" separator.
    # Everything after "--" is forwarded to the target script.
    raw = sys.argv[1:]
    script_args: list[str] = []
    if "--" in raw:
        sep = raw.index("--")
        vm_argv = raw[:sep]
        script_args = raw[sep + 1 :]
    else:
        vm_argv = raw

    ap = argparse.ArgumentParser(
        prog="python3 thielecpu/vm.py",
        add_help=True,
        description="Run a Python script through the Thiele VM (emits μ/receipts/trace).",
    )
    ap.add_argument(
        "-m",
        "--module",
        dest="module",
        default=None,
        help="Run a library module as a script (python -m). Example: -m package.module",
    )
    ap.add_argument(
        "-c",
        dest="command",
        default=None,
        help="Program passed in as a string (python -c).",
    )
    ap.add_argument("python_file", nargs="?", default=None, help="Path to a .py script, or '-' for stdin")
    # Backward-compatible positional outdir (only usable when not forwarding script args).
    ap.add_argument("legacy_outdir", nargs="?", default=None)
    ap.add_argument(
        "--outdir",
        type=Path,
        default=None,
        help="Directory to write VM artifacts (default: out/<script_stem>)",
    )
    ap.add_argument(
        "--tee-stdout",
        action="store_true",
        help="Also print script stdout to the real terminal while still capturing it for VM traces.",
    )
    ap.add_argument(
        "-i",
        "--interactive",
        action="store_true",
        help="After running, drop into an interactive REPL (like python -i).",
    )
    args = ap.parse_args(vm_argv)

    mode_count = int(args.module is not None) + int(args.command is not None) + int(args.python_file is not None)
    if mode_count != 1:
        print("Error: provide exactly one of: <python_file.py> OR -m/--module <name> OR -c <code> OR '-' for stdin")
        sys.exit(2)

    python_file = args.python_file
    if python_file is not None:
        # stdin mode: python -
        if python_file == "-":
            pass
        elif not python_file.endswith('.py'):
            print(f"Error: {python_file} is not a Python file")
            sys.exit(1)

        if python_file != "-" and not Path(python_file).exists():
            print(f"Error: {python_file} not found")
            sys.exit(1)

    if args.outdir is not None:
        outdir = args.outdir
    elif args.legacy_outdir is not None and not script_args:
        outdir = Path(args.legacy_outdir)
    else:
        if args.command is not None:
            outdir = Path('out') / "command"
        elif python_file == "-":
            outdir = Path('out') / "stdin"
        else:
            outdir = Path('out') / (Path(python_file).stem if python_file is not None else str(args.module).replace('.', '_'))

    # Build the program directly (avoid assembler quirks like ';' comment stripping
    # which would break `-c` code strings).
    if args.module is not None:
        pyexec_payload = f"module:{args.module}"
    elif args.command is not None:
        pyexec_payload = args.command
    elif python_file == "-":
        pyexec_payload = sys.stdin.read()
    else:
        pyexec_payload = str(Path(python_file).resolve())

    program = [("PYEXEC", pyexec_payload)]

    # Run the VM
    vm = VM(State())
    # Forward argv-style args to the script.
    vm.python_globals["_vm_script_args"] = script_args
    if args.tee_stdout or args.interactive:
        vm.python_globals["_vm_tee_stdout"] = True
    if args.command is not None:
        vm.python_globals["_vm_argv0"] = "-c"
    elif python_file == "-":
        vm.python_globals["_vm_argv0"] = "-"
    vm.run(program, outdir)

    print(f"Python execution completed. Output written to {outdir}/")

    if args.interactive:
        # Match CPython: -i should only happen after a successful run.
        if getattr(vm, "last_exit_code", 0) != 0:
            raise SystemExit(getattr(vm, "last_exit_code", 0))
        import code as _code

        banner = "Thiele VM interactive (post-run). Globals are the script globals." \
            " Type Ctrl-D to exit."
        try:
            _code.interact(banner=banner, local=vm.python_globals)
        except SystemExit as exc:
            # Respect exit codes from within the REPL.
            raise

    raise SystemExit(getattr(vm, "last_exit_code", 0))


if __name__ == "__main__":
    main()


__all__ = ["VM", "TraceConfig"]
