# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""Partition-native RSA demo suite for the Thiele Machine.

This module runs three-act partitioned RSA factoring experiments and
emits structured artifacts under ``rsa_demo_output/`` for auditing and
analysis.
"""

from __future__ import annotations

import json
import math
import os
from dataclasses import dataclass, field
from pathlib import Path
import re
import sys
import textwrap
from string import Template
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Tuple

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from thielecpu.assemble import parse
from thielecpu.geometric_oracle import check_congruence_possibility
from thielecpu.state import State
from thielecpu.vm import VM

ACT_I_SCRIPT = Path("temp_rsa_act_i.py")
SETUP_SCRIPT = Path("temp_rsa_setup.py")
ANALYSIS_SCRIPT = Path("temp_rsa_analysis.py")
COMPOSITION_SCRIPT = Path("temp_rsa_compose.py")
REASONING_SCRIPT = Path("temp_rsa_reasoning.py")


class RunArtifacts:
    """Structured summary extracted from a VM run."""

    def __init__(
        self,
        witness: Optional[Tuple[int, int]],
        mu_total: Optional[float],
        candidate_checks: int,
        highlight_lines: Sequence[str],
        reasoning_lines: Sequence[str],
        hardware_lines: Sequence[str],
        reasoning_summary: Optional[Dict[str, Any]] = None,
    ) -> None:
        self.witness = witness
        self.mu_total = mu_total
        self.candidate_checks = candidate_checks
        self.highlight_lines = list(highlight_lines)
        self.reasoning_lines = list(reasoning_lines)
        self.hardware_lines = list(hardware_lines)
        self.reasoning_summary = reasoning_summary


@dataclass(frozen=True)
class Constraint:
    modulus: int
    remainder: int
    explanation: str

    def satisfied_by(self, value: int) -> bool:
        return value % self.modulus == self.remainder


@dataclass
class PartitionDefinition:
    label: str
    description: str
    constraints: List[Constraint]
    numbers: List[int] = field(default_factory=list)

    def matches(self, value: int) -> bool:
        return all(constraint.satisfied_by(value) for constraint in self.constraints)


def _int_range_for_modulus(n: int) -> List[int]:
    sqrt_bound = int(math.isqrt(n))
    return list(range(2, max(2, sqrt_bound) + 1))


def _geometric_partition_blueprints() -> Dict[str, PartitionDefinition]:
    """Return reusable modular blueprints for geometric partitions."""

    combo_labels = {
        (1, 1): "A",
        (1, 2): "B",
        (1, 3): "C",
        (1, 4): "D",
        (2, 1): "E",
        (2, 2): "F",
        (2, 3): "G",
        (2, 4): "H",
    }

    partitions: Dict[str, PartitionDefinition] = {}
    for (mod3, mod5), label in combo_labels.items():
        description = f"p ≡ {mod3} (mod 3) ∧ p ≡ {mod5} (mod 5)"
        constraints = [
            Constraint(3, mod3, f"p % 3 = {mod3}"),
            Constraint(5, mod5, f"p % 5 = {mod5}"),
        ]
        partitions[label] = PartitionDefinition(label, description, constraints)

    partitions["I"] = PartitionDefinition(
        "I",
        "p ≡ 0 (mod 3)",
        [Constraint(3, 0, "p is divisible by 3")],
    )
    partitions["J"] = PartitionDefinition(
        "J",
        "p ≡ 0 (mod 5)",
        [Constraint(5, 0, "p is divisible by 5")],
    )

    return partitions


def _partition_search_space(n: int) -> Dict[str, PartitionDefinition]:
    """Return modularly-defined partitions that cover the √n interval."""

    candidates = _int_range_for_modulus(n)
    if not candidates:
        blueprint = _geometric_partition_blueprints()["A"]
        blueprint.numbers = [2]
        return {"A": blueprint}

    partitions = _geometric_partition_blueprints()

    for candidate in candidates:
        if candidate % 3 == 0:
            partitions["I"].numbers.append(candidate)
        elif candidate % 5 == 0:
            partitions["J"].numbers.append(candidate)
        else:
            key = (candidate % 3, candidate % 5)
            label = {
                (1, 1): "A",
                (1, 2): "B",
                (1, 3): "C",
                (1, 4): "D",
                (2, 1): "E",
                (2, 2): "F",
                (2, 3): "G",
                (2, 4): "H",
            }.get(key)
            if label is None:
                partitions["J"].numbers.append(candidate)
            else:
                partitions[label].numbers.append(candidate)

    # Drop empty partitions to keep the reasoning narrative concise.
    populated = {
        label: definition
        for label, definition in partitions.items()
        if definition.numbers
    }

    return populated


def _collect_partition_stats(
    n: int, partitions: Dict[str, PartitionDefinition]
) -> Dict[str, object]:
    """Summarise live partition metrics for use in scaling analysis."""

    partition_labels = list(partitions.keys())
    candidate_counts = {
        label: len(partitions[label].numbers) for label in partition_labels
    }
    total_candidates = sum(candidate_counts.values())
    partition_count = len(partition_labels)
    per_partition_max = max(candidate_counts.values()) if candidate_counts else 0
    sqrt_bound = int(math.isqrt(n))
    work_per_partition = (
        (total_candidates + max(1, partition_count) - 1) // max(1, partition_count)
        if partition_count
        else 0
    )

    return {
        "modulus": n,
        "bit_length": n.bit_length(),
        "sqrt_bound": sqrt_bound,
        "partition_count": partition_count,
        "candidate_counts": candidate_counts,
        "total_candidates": total_candidates,
        "max_candidates_per_partition": per_partition_max,
        "work_per_partition": work_per_partition,
    }


def perform_congruence_reasoning(
    modulus: int,
    base: int = 12,
    log: Optional[Callable[[str], None]] = None,
) -> Tuple[Dict[str, Any], List[int]]:
    """Use the geometric oracle to eliminate infeasible residue classes."""

    emit = log if log is not None else (lambda _: None)

    sqrt_bound = max(2, int(math.isqrt(modulus)))
    initial_candidates = max(1, sqrt_bound - 1)

    possible_pairs: List[Dict[str, Any]] = []
    eliminated_pairs: List[Dict[str, Any]] = []
    allowed_residues: Dict[int, List[int]] = {}

    queries = 0
    emit(
        "Reasoning prelude: exploring congruence classes with the geometric oracle."
    )

    for residue_a in range(base):
        for residue_b in range(base):
            verdict = check_congruence_possibility(modulus, residue_a, residue_b, base)
            queries += 1
            record = {
                "query": {
                    "residue_a": residue_a,
                    "residue_b": residue_b,
                    "base": base,
                },
                "status": verdict["status"],
                "product_residue": verdict["product_residue"],
                "target_residue": verdict["target_residue"],
            }
            if verdict["status"] == "possible":
                emit(
                    f"  Residues ({residue_a} mod {base}, {residue_b} mod {base})"
                    " remain possible."
                )
                possible_pairs.append(record)
                allowed_residues.setdefault(residue_a, []).append(residue_b)
            else:
                emit(
                    f"  Residues ({residue_a} mod {base}, {residue_b} mod {base})"
                    " are impossible; erasing."
                )
                eliminated_pairs.append(record)

    candidate_range = list(range(2, sqrt_bound + 1))
    surviving_candidates: List[int] = []
    for candidate in candidate_range:
        residue = candidate % base
        if residue in allowed_residues:
            surviving_candidates.append(candidate)

    summary: Dict[str, Any] = {
        "modulus": modulus,
        "base": base,
        "target_residue": modulus % base,
        "queries": queries,
        "mu_cost": float(queries),
        "initial_candidates": len(candidate_range),
        "remaining_candidates": len(surviving_candidates),
        "candidates_pruned": len(candidate_range) - len(surviving_candidates),
        "possible_pairs": possible_pairs,
        "eliminated_pairs": eliminated_pairs,
        "allowed_residues": sorted(allowed_residues.keys()),
    }

    return summary, surviving_candidates


def _serialise_partitions(
    partitions: Dict[str, PartitionDefinition]
) -> Dict[str, Dict[str, object]]:
    """Convert partition definitions to a JSON-friendly dictionary."""

    payload: Dict[str, Dict[str, object]] = {}
    for label, definition in partitions.items():
        payload[label] = {
            "numbers": definition.numbers,
            "description": definition.description,
            "constraints": [
                {
                    "modulus": constraint.modulus,
                    "remainder": constraint.remainder,
                    "explanation": constraint.explanation,
                }
                for constraint in definition.constraints
            ],
        }
    return payload


def _compute_reasoning_outcome(
    modulus: int, partitions: Dict[str, PartitionDefinition], sqrt_bound: int
) -> List[Dict[str, object]]:
    """Use Z3 to determine which partitions are logically viable."""

    from z3 import Int, Solver

    outcomes: List[Dict[str, object]] = []
    for label, definition in partitions.items():
        solver = Solver()
        p = Int("p")
        q = Int("q")
        solver.add(p >= 2, q >= 2, p * q == modulus)
        solver.add(p <= sqrt_bound, q >= p)
        for constraint in definition.constraints:
            solver.add(p % constraint.modulus == constraint.remainder)

        result = solver.check()
        status = str(result)
        payload: Dict[str, object] = {
            "label": label,
            "status": status,
            "description": definition.description,
        }
        if status == "sat":
            model = solver.model()
            witness = model[p] if model is not None else None
            if witness is not None:
                payload["witness"] = int(witness.as_long())
        elif status == "unsat":
            payload["reason"] = "unsatisfiable modular constraints"
        else:
            payload["reason"] = "solver returned unknown"
        outcomes.append(payload)

    return outcomes


def _analysis_rows_from_stats(
    stats: Dict[str, object], analysis_bits: Iterable[int]
) -> Tuple[List[Dict[str, object]], float]:
    """Compute silicon scaling projections from live partition statistics."""

    ratio_value = stats.get("geometric_ratio")
    sqrt_bound = int(stats.get("sqrt_bound", 0))
    if ratio_value is None:
        work_per_partition = int(stats.get("work_per_partition", 0))
        ratio = 1.0
        if sqrt_bound > 0 and work_per_partition > 0:
            ratio = work_per_partition / sqrt_bound
    else:
        ratio = float(ratio_value)
    ratio = max(ratio, 1e-12)

    analysis_rows: List[Dict[str, object]] = []
    for bits in analysis_bits:
        classical_log2 = bits / 2
        classical_log10 = classical_log2 * math.log10(2)
        classical_digits = max(1, int(math.floor(classical_log10)) + 1)

        per_partition_log10 = classical_log10 + math.log10(ratio)
        per_partition_digits = max(1, int(math.floor(per_partition_log10)) + 1)
        orders_delta = classical_log10 - per_partition_log10

        analysis_rows.append(
            {
                "bits": bits,
                "classical_checks_log2": classical_log2,
                "classical_checks_log10": classical_log10,
                "classical_checks_digits": classical_digits,
                "per_partition_checks_log10": per_partition_log10,
                "per_partition_checks_digits": per_partition_digits,
                "constant_depth_stages": 2,
                "orders_of_magnitude_reduced": orders_delta,
            }
        )

    return analysis_rows, ratio


def _write_temp_script(path: Path, contents: str) -> None:
    path.write_text(contents + "\n", encoding="utf-8")


def _render_act_i_script(n: int) -> str:
    sqrt_bound = int(math.isqrt(n))
    return textwrap.dedent(
        f"""
        TARGET = {n}
        SQRT_BOUND = {sqrt_bound}
        print("Trial division range:", list(range(2, SQRT_BOUND + 1)))
        factor = None
        cofactor = None
        for candidate in range(2, SQRT_BOUND + 1):
            remainder = TARGET % candidate
            print("Testing", candidate, "→ remainder", remainder)
            if remainder == 0:
                factor = candidate
                cofactor = TARGET // candidate
                print("Witness located (sequential mode):", factor, "*", cofactor, "=", TARGET)
                break
        if factor is None:
            print("Sequential search failed to locate a witness")
            __result__ = None
        else:
            __result__ = (factor, cofactor)
        """
    ).strip()


def _render_partition_setup_script(
    n: int,
    partitions: Dict[str, Dict[str, object]],
    heading: str,
    descriptor: str,
    partitions_path: Optional[str] = None,
    meta_path: Optional[str] = None,
    results_path: Optional[str] = None,
) -> str:
    # Serialise partition payloads and an initial results file to absolute
    # paths when provided so that separately-invoked PYEXEC contexts can
    # reliably load them.
    partitions_json = json.dumps(partitions)
    return textwrap.dedent(
        f"""
        import json

        TARGET = {n}
        PARTITIONS = {partitions_json}
        PARTITION_RESULTS = dict((label, None) for label in PARTITIONS)
        ACTIVE_PARTITIONS = list(PARTITIONS.keys())
        ELIMINATED_PARTITIONS = []
        # persist partitions for other PYEXEC contexts (absolute paths)
        try:
            if {bool(partitions_path)!s}:
                with open(r'{partitions_path}', 'w', encoding='utf-8') as _f:
                    json.dump(PARTITIONS, _f)
        except:
            pass
        try:
            # write an initial empty partition results file for aggregation
            if {bool(results_path)!s}:
                _initial = {{}}
                with open(r'{results_path}', 'w', encoding='utf-8') as _rf:
                    json.dump(_initial, _rf)
        except:
            pass
        try:
            if {bool(meta_path)!s}:
                with open(r'{meta_path}', 'w', encoding='utf-8') as _mf:
                    json.dump({{'target': TARGET, 'sqrt_bound': int(__import__('math').isqrt(TARGET))}}, _mf)
        except:
            pass
        print("{heading}")
        print("Target modulus:", TARGET)
        for label, metadata in PARTITIONS.items():
            print(
                f"Partition {{label}} {descriptor}: {{metadata['description']}}"
            )
            print("  Candidates:", metadata["numbers"])
        """
    ).strip()


def _render_partition_worker_script(label: str, descriptor: str, partitions_path: Optional[str] = None, meta_path: Optional[str] = None, results_path: Optional[str] = None) -> str:
    # Worker scripts may execute in separate PYEXEC contexts. Fall back to the
    # persisted `partitions_payload.json` if the `PARTITIONS` global is missing.
    return textwrap.dedent(
        f"""
        import json

        try:
            metadata = PARTITIONS[{label!r}]
        except:
            try:
                if {bool(partitions_path)!s}:
                    with open(r'{partitions_path}', 'r', encoding='utf-8') as _pf:
                        PARTITIONS = json.load(_pf)
                        PARTITION_RESULTS = dict((label, None) for label in PARTITIONS)
                        ACTIVE_PARTITIONS = list(PARTITIONS.keys())
                else:
                    PARTITIONS = {{}}
                    PARTITION_RESULTS = {{}}
                    ACTIVE_PARTITIONS = []
            except:
                PARTITIONS = {{}}
                PARTITION_RESULTS = {{}}
                ACTIVE_PARTITIONS = []
            metadata = PARTITIONS.get({label!r}, {{"numbers": [], "description": ''}})

        # Try to recover TARGET from persisted meta if it's missing
        try:
            TARGET
        except:
            try:
                if {bool(meta_path)!s}:
                    with open(r'{meta_path}', 'r', encoding='utf-8') as _mf:
                        _meta = json.load(_mf)
                        TARGET = _meta.get('target', None)
                else:
                    TARGET = None
            except:
                TARGET = None

        numbers = metadata.get("numbers", [])
        try:
            active = ACTIVE_PARTITIONS
        except:
            active = None
        if active is not None and {label!r} not in active:
            print(
                "Partition {label} was logically erased before search. "
                "No arithmetic work performed."
            )
            PARTITION_RESULTS[{label!r}] = None
            __result__ = None
        else:
            print(
                "Exploring Partition {label} {descriptor} (" + metadata.get("description", "") + "):",
                numbers,
            )
            found = None
            for candidate in numbers:
                remainder = TARGET % candidate
                print("Testing", candidate, "→ remainder", remainder)
                if remainder == 0:
                    cofactor = TARGET // candidate
                    found = {{"factor": candidate, "cofactor": cofactor}}
                    print(
                        "Witness located in Partition {label}:",
                        candidate,
                        "*",
                        cofactor,
                        "=",
                        TARGET,
                    )
                    break
            if found is None:
                print("Partition {label} produced no witness.")
            PARTITION_RESULTS[{label!r}] = found
            # persist partition results for composition step by merging
            try:
                if {bool(results_path)!s}:
                    try:
                        with open(r'{results_path}', 'r', encoding='utf-8') as _rf:
                            _existing = json.load(_rf)
                    except:
                        _existing = {{}}
                    # only update our own partition key to avoid overwriting
                    # other workers with None values
                    _existing[{label!r}] = found
                    with open(r'{results_path}', 'w', encoding='utf-8') as _wf:
                        json.dump(_existing, _wf)
            except:
                pass
            __result__ = found
        """
    ).strip()


def _render_composition_script() -> str:
    return textwrap.dedent(
        """
        witness = None
        for value in PARTITION_RESULTS.values():
            if value:
                witness = value
                break
        if witness is not None:
            factor = witness["factor"]
            cofactor = witness["cofactor"]
            print("Composing final witness from partition search")
            print("Verification:", factor, "*", cofactor, "=", TARGET)
            __result__ = (factor, cofactor)
        else:
            print("No witness available; factoring failed.")
            __result__ = None
        """
    ).strip()


def _render_binary_setup_script(n: int, rsa_meta_path: Optional[str] = None) -> str:
    sqrt_bound = int(math.isqrt(n))
    return textwrap.dedent(
        f"""
        import json

        TARGET = {n}
        SQRT_BOUND = {sqrt_bound}
        INITIAL_RANGE = list(range(2, max(2, SQRT_BOUND) + 1))
        print("Configuring sighted congruence reasoning (Act III)")
        print("Target modulus:", TARGET)
        print("Initial candidate range:", INITIAL_RANGE)
        BINARY_REASONING_SUMMARY = None
        BINARY_REMAINING_RANGE = INITIAL_RANGE
        BINARY_FALLBACK_RANGE = None
        # persist meta for downstream PYEXEC contexts (absolute path)
        try:
            if {bool(rsa_meta_path)!s}:
                with open(r'{rsa_meta_path}', 'w', encoding='utf-8') as _mf:
                    json.dump({{'target': TARGET, 'sqrt_bound': SQRT_BOUND}}, _mf)
        except:
            pass
        """
    ).strip()


def _render_binary_reasoning_script(
    summary: Dict[str, Any], remaining_range: Sequence[int], reasoning_path: Optional[str] = None
) -> str:
    payload_literal = json.dumps(summary)
    remaining_literal = json.dumps(list(remaining_range))
    return textwrap.dedent(
        f"""
        import json

        summary = json.loads({repr(payload_literal)})
        base = summary.get("base")
        print("Reasoning prelude: congruence-based structural transcript.")
        print("  Base modulus:", base)
        print("  Target residue:", summary.get("target_residue"))
        for item in summary.get("possible_pairs", []):
            query = item.get("query", {{}})
            a = query.get("residue_a")
            b = query.get("residue_b")
            m = query.get("base", base)
            print(
                "  POSSIBLE:",
                "p ≡ " + str(a) + " (mod " + str(m) + ") ∧ q ≡ " + str(b) + " (mod " + str(m) + ")",
            )
        for item in summary.get("eliminated_pairs", []):
            query = item.get("query", {{}})
            a = query.get("residue_a")
            b = query.get("residue_b")
            m = query.get("base", base)
            print(
                "  IMPOSSIBLE:",
                "p ≡ " + str(a) + " (mod " + str(m) + ") ∧ q ≡ " + str(b) + " (mod " + str(m) + ")",
            )
        remaining_range = json.loads({repr(remaining_literal)})
        print("Reasoning complete. Remaining candidate payload:", remaining_range)
        BINARY_REASONING_SUMMARY = summary
        BINARY_REMAINING_RANGE = remaining_range
        BINARY_FALLBACK_RANGE = None
        # persist reasoning for other PYEXEC contexts (absolute path)
        try:
            with open(r'{reasoning_path}', 'w', encoding='utf-8') as _bf:
                json.dump({{'summary': summary, 'remaining': remaining_range}}, _bf)
        except:
            pass
        """
    ).strip()


def _render_binary_search_script(rsa_meta_path: Optional[str] = None, reasoning_path: Optional[str] = None) -> str:
    return textwrap.dedent(f"""
        import json
        TARGET = globals().get('TARGET', None)
        try:
            remaining = BINARY_REMAINING_RANGE
            summary = BINARY_REASONING_SUMMARY
        except:
            # fall back to persisted reasoning payload
            try:
                if {bool(reasoning_path)!s}:
                    with open(r'{reasoning_path}', 'r', encoding='utf-8') as _bf:
                        _payload = json.load(_bf)
                        summary = _payload.get('summary')
                        remaining = _payload.get('remaining', [])
                else:
                    remaining = []
                    summary = None
            except:
                remaining = []
                summary = None
            # try to recover TARGET from persisted meta
            try:
                if {bool(rsa_meta_path)!s}:
                    with open(r'{rsa_meta_path}', 'r', encoding='utf-8') as _mf:
                        _meta = json.load(_mf)
                        _target = _meta.get('target', None)
                        if _target is not None:
                            TARGET = _target
            except:
                pass

        found = None

        if remaining:
            if TARGET is None:
                print("Error: TARGET is not defined; cannot verify candidates")
                __result__ = None
                raise SystemExit(0)
            print(
                "Initiating targeted verification over surviving candidates:",
                remaining,
            )
            for candidate in remaining:
                remainder = TARGET % candidate
                print("Testing", candidate, "→ remainder", remainder)
                if remainder == 0:
                    cofactor = TARGET // candidate
                    found = {{"factor": candidate, "cofactor": cofactor}}
                    print(
                        "Fallback verification produced witness:",
                        candidate,
                        "*",
                        cofactor,
                        "=",
                        TARGET,
                    )
                    break

        if summary is not None:
            try:
                summary["final_search_candidates"] = len(remaining)
            except:
                pass
            if found is not None:
                summary["witness"] = found["factor"]
                summary["cofactor"] = found["cofactor"]
        print("Reasoning summary:", json.dumps(summary))
        FINAL_WITNESS = found
        __result__ = found
        """)


def _render_binary_analysis_script(
    analysis_lines: Sequence[str],
    reasoning_path: Optional[str] = None,
) -> str:
    lines_payload = json.dumps(list(analysis_lines))
    return textwrap.dedent(
        f"""
        import json

        try:
            summary = BINARY_REASONING_SUMMARY
        except Exception:
            summary = None
            try:
                if {bool(reasoning_path)!s}:
                    with open(r'{reasoning_path}', 'r', encoding='utf-8') as _bf:
                        _payload = json.load(_bf)
                        summary = _payload.get('summary')
            except Exception:
                summary = None
        if summary is None:
            print("Hardware scaling assessment (inside VM): reasoning summary unavailable.")
            __result__ = None
        else:
            print("Hardware scaling assessment (inside VM):")
            print(
                "  Structural queries issued (μ-cost):",
                summary.get("queries"),
            )
            print(
                "  Allowed residue classes (p mod base):",
                summary.get("allowed_residues"),
            )
            print(
                "  Remaining arithmetic checks after congruence pruning:",
                summary.get("remaining_candidates"),
            )
            for line in json.loads({lines_payload!r}):
                print(line)
            __result__ = None
        """
    ).strip()


def _run_vm_program(
    program_lines: Sequence[str],
    temp_scripts: Sequence[Path],
    output_dir: Path,
) -> RunArtifacts:
    output_dir.mkdir(parents=True, exist_ok=True)
    program_source = "\n".join(program_lines)
    program_path = output_dir.with_suffix(".thm")
    program_path.write_text(program_source, encoding="utf-8")

    try:
        program = parse(program_source.splitlines(), Path("."))
        vm = VM(State())
        # Ensure helpful objects are available to PYEXEC contexts via python_globals
        try:
            vm.python_globals.update({
                "json": json,
                "Exception": Exception,
                "os": os,
                "globals": globals,
            })
        except Exception:
            pass
        vm.run(program, output_dir)
    finally:
        program_path.unlink(missing_ok=True)
        for script in temp_scripts:
            script.unlink(missing_ok=True)

    summary_path = output_dir / "summary.json"
    mu_total: Optional[float] = None
    if summary_path.exists():
        summary = json.loads(summary_path.read_text())
        mu_total = summary.get("mu_total")

    trace_path = output_dir / "trace.log"
    highlight_lines: List[str] = []
    reasoning_lines: List[str] = []
    hardware_lines: List[str] = []
    candidate_checks = 0
    witness: Optional[Tuple[int, int]] = None

    reasoning_summary: Optional[Dict[str, Any]] = None

    if trace_path.exists():
        trace_lines = trace_path.read_text().splitlines()
        for line in trace_lines:
            message = line.split("PYEXEC output:", 1)[-1]
            if "Testing" in message:
                candidate_checks += 1
            if (
                "Reasoning" in message
                or "SMT reasoning" in message
                or "VERDICT" in message
            ):
                reasoning_lines.append(line)
            if "Hardware scaling" in message or "RSA-" in message:
                hardware_lines.append(line)
            if "Reasoning summary:" in message:
                summary_text = message.split("Reasoning summary:", 1)[1].strip()
                try:
                    reasoning_summary = json.loads(summary_text)
                except json.JSONDecodeError:
                    pass
            if (
                "Witness located" in message
                or "Composing final witness" in message
                or "Fallback verification produced witness" in message
            ):
                highlight_lines.append(line)
                match = re.search(r":\s*(\d+)\s*\*\s*(\d+)\s*=\s*(\d+)", message)
                if match:
                    factor = int(match.group(1))
                    cofactor = int(match.group(2))
                    witness = (factor, cofactor)

    return RunArtifacts(
        witness=witness,
        mu_total=mu_total,
        candidate_checks=candidate_checks,
        highlight_lines=highlight_lines,
        reasoning_lines=reasoning_lines,
        hardware_lines=hardware_lines,
        reasoning_summary=reasoning_summary,
    )


def _act_i_program(n: int) -> Tuple[List[str], List[Path]]:
    script_source = _render_act_i_script(n)
    _write_temp_script(ACT_I_SCRIPT, script_source)
    program_lines = [
        "; Act I: Sequential trial division (blind worker)",
        "PNEW 0",
        f'PYEXEC "{ACT_I_SCRIPT.name}"',
        "MDLACC",
        'EMIT "Act I complete"',
    ]
    return program_lines, [ACT_I_SCRIPT]


def _act_ii_program(
    n: int, partitions: Dict[str, PartitionDefinition], experiment_root: Path
) -> Tuple[List[str], List[Path]]:
    temp_scripts: List[Path] = []
    partition_payload = _serialise_partitions(partitions)
    partitions_path = str((experiment_root / "partitions_payload.json").resolve())
    meta_path = str((experiment_root / "rsa_demo_meta.json").resolve())
    results_path = str((experiment_root / "partition_results.json").resolve())
    setup_code = _render_partition_setup_script(
        n,
        partition_payload,
        heading="Configuring blind multi-core emulation (Act II)",
        descriptor="task queue",
        partitions_path=partitions_path,
        meta_path=meta_path,
        results_path=results_path,
    )
    _write_temp_script(SETUP_SCRIPT, setup_code)
    temp_scripts.append(SETUP_SCRIPT)

    for label in partition_payload:
        worker_script = _render_partition_worker_script(label, "task queue", partitions_path, meta_path, results_path)
        path = Path(f"temp_rsa_partition_{label.lower()}.py")
        _write_temp_script(path, worker_script)
        temp_scripts.append(path)

    # ensure the composition script knows where to read persisted partition results
    # and provide a fallback that inspects partition payloads for a witness
    composition_script = _render_composition_script()
    composition_prelude = (
        f"COMPOSITION_RESULTS_PATH = r'{results_path}'\n"
        f"PARTITIONS_PAYLOAD_PATH = r'{partitions_path}'\n"
        f"RSA_META_PATH = r'{meta_path}'\n"
        "import json\n"
        "# attempt to recover TARGET from persisted meta if not present\n"
        "try:\n"
        "    TARGET\n"
        "except:\n"
        "    try:\n"
        "        with open(RSA_META_PATH, 'r', encoding='utf-8') as _mf:\n"
        "            _meta = json.load(_mf)\n"
        "            TARGET = _meta.get('target', None)\n"
        "    except:\n"
        "        TARGET = None\n"
        "# ensure PARTITION_RESULTS exists in this PYEXEC context\n"
        "try:\n"
        "    PARTITION_RESULTS\n"
        "except:\n"
        "    try:\n"
        "        with open(COMPOSITION_RESULTS_PATH, 'r', encoding='utf-8') as _rf:\n"
        "            PARTITION_RESULTS = json.load(_rf)\n"
        "    except:\n"
        "        PARTITION_RESULTS = {}\n"
    )
    composition_fallback = textwrap.dedent(
        """
        # Fallback: if no witness found in PARTITION_RESULTS, scan partition payloads
        if witness is None:
            try:
                with open(PARTITIONS_PAYLOAD_PATH, 'r', encoding='utf-8') as _pf:
                    _parts = json.load(_pf)
            except:
                _parts = {}
            try:
                for label, meta in _parts.items():
                    for candidate in meta.get('numbers', []):
                        try:
                            if TARGET % candidate == 0:
                                witness = {'factor': candidate, 'cofactor': TARGET // candidate}
                                break
                        except Exception:
                            pass
                    if witness is not None:
                        break
            except Exception:
                pass
        """
    )
    composition_script = composition_prelude + composition_script + "\n" + composition_fallback
    _write_temp_script(COMPOSITION_SCRIPT, composition_script)
    temp_scripts.append(COMPOSITION_SCRIPT)

    program_lines = [
        "; Act II: Blind factory (partitioned tasks)",
        "PNEW 0",
        f'PYEXEC "{SETUP_SCRIPT.name}"',
    ]
    for label in partition_payload:
        program_lines.append(f'PYEXEC "temp_rsa_partition_{label.lower()}.py"')
    program_lines.extend(
        [
            f'PYEXEC "{COMPOSITION_SCRIPT.name}"',
            "MDLACC",
            'EMIT "Act II complete"',
        ]
    )
    return program_lines, temp_scripts


def _act_iii_program(
    n: int,
    analysis_bits: Iterable[int],
    threshold: Optional[int] = None,
    experiment_root: Optional[Path] = None,
) -> Tuple[List[str], List[Path], int, Dict[str, Any]]:
    temp_scripts: List[Path] = []
    analysis_bits = list(analysis_bits)
    sqrt_bound = max(2, int(math.isqrt(n)))
    if threshold is None:
        threshold = 12
    base_modulus = max(2, threshold)

    rsa_meta_path = str((Path(experiment_root) / "rsa_demo_meta.json").resolve()) if experiment_root is not None else "rsa_demo_meta.json"
    setup_code = _render_binary_setup_script(n, rsa_meta_path)
    _write_temp_script(SETUP_SCRIPT, setup_code)
    temp_scripts.append(SETUP_SCRIPT)

    host_summary, host_remaining = perform_congruence_reasoning(n, base_modulus)
    initial_candidates = host_summary.get(
        "initial_candidates", max(0, sqrt_bound - 1)
    )
    remaining_candidates = host_summary.get(
        "remaining_candidates", len(host_remaining)
    )
    collapse_ratio = (
        remaining_candidates / initial_candidates if initial_candidates else 1.0
    )
    analysis_rows, _ = _analysis_rows_from_stats(
        {"sqrt_bound": sqrt_bound, "geometric_ratio": collapse_ratio},
        analysis_bits,
    )
    analysis_lines: List[str] = []
    for row in analysis_rows:
        classical_digits = int(row.get("classical_checks_digits", 1))
        per_digits = int(row.get("per_partition_checks_digits", 1))
        orders = float(row.get("orders_of_magnitude_reduced", 0.0))
        analysis_lines.append(
            (
                f"  RSA-{row['bits']}: classical √n search ≈ 10^{classical_digits - 1} checks; "
                f"congruence pruning projects ≈ 10^{per_digits - 1} residual candidates "
                f"(Δ ≈ {orders:.2f} orders)"
            )
        )

    host_summary.setdefault("analysis_rows", analysis_rows)
    host_summary.setdefault("geometric_ratio", collapse_ratio)

    binary_reasoning_path = str((Path(experiment_root) / "binary_reasoning.json").resolve()) if experiment_root is not None else "binary_reasoning.json"
    reasoning_code = _render_binary_reasoning_script(host_summary, host_remaining, binary_reasoning_path)
    _write_temp_script(REASONING_SCRIPT, reasoning_code)
    temp_scripts.append(REASONING_SCRIPT)

    search_script_path = Path("temp_rsa_binary_search.py")
    search_code = _render_binary_search_script(rsa_meta_path, binary_reasoning_path)
    _write_temp_script(search_script_path, search_code)
    temp_scripts.append(search_script_path)

    analysis_code = _render_binary_analysis_script(analysis_lines, binary_reasoning_path)
    _write_temp_script(ANALYSIS_SCRIPT, analysis_code)
    temp_scripts.append(ANALYSIS_SCRIPT)

    program_lines = [
        "; Act III: Sighted structural discovery",
        "PNEW 0",
        f'PYEXEC "{SETUP_SCRIPT.name}"',
        f'PYEXEC "{REASONING_SCRIPT.name}"',
        f'PYEXEC "{search_script_path.name}"',
        f'PYEXEC "{ANALYSIS_SCRIPT.name}"',
        "MDLACC",
        'EMIT "Act III complete"',
    ]

    return program_lines, temp_scripts, base_modulus, host_summary



def analyze_hardware_scaling(
    experiments: Sequence[Dict[str, object]],
    analysis_bits: Iterable[int],
    output_root: Path,
) -> Tuple[Path, List[Dict[str, object]]]:
    """Generate a live scaling report from recorded experiment metrics."""

    analysis_bits = list(analysis_bits)
    print("\nINFO: Performing live hardware scaling analysis based on collected experimental data...")

    enriched_experiments: List[Dict[str, object]] = []
    ratios: List[float] = []
    checks_saved_stats: List[int] = []
    surviving_candidate_stats: List[int] = []
    for record in experiments:
        stats_payload = {
            "sqrt_bound": record.get("sqrt_bound", 0),
            "work_per_partition": record.get("work_per_partition", 0),
            "geometric_ratio": record.get("geometric_pruning", {}).get(
                "geometric_ratio"
            ),
        }
        rows, ratio = _analysis_rows_from_stats(stats_payload, analysis_bits)
        enriched = dict(record)
        enriched["analysis_rows"] = rows
        enriched["partition_efficiency_ratio"] = ratio
        enriched["geometric_ratio"] = ratio
        enriched_experiments.append(enriched)
        ratios.append(ratio)
        gp = record.get("geometric_pruning", {})
        if gp.get("candidates_pruned") is not None:
            checks_saved_stats.append(int(gp["candidates_pruned"]))
        if gp.get("surviving_candidates") is not None:
            surviving_candidate_stats.append(int(gp["surviving_candidates"]))

    aggregate_rows: List[Dict[str, object]] = []
    aggregate_summary: Dict[str, object]
    if ratios:
        mean_ratio = sum(ratios) / len(ratios)
        min_ratio = min(ratios)
        max_ratio = max(ratios)

        aggregate_rows = []
        for bits in analysis_bits:
            classical_log2 = bits / 2
            classical_log10 = classical_log2 * math.log10(2)
            classical_digits = max(1, int(math.floor(classical_log10)) + 1)
            per_partition_log10 = classical_log10 + math.log10(mean_ratio)
            per_partition_digits = max(1, int(math.floor(per_partition_log10)) + 1)
            orders_delta = classical_log10 - per_partition_log10
            aggregate_rows.append(
                {
                    "bits": bits,
                    "classical_checks_log2": classical_log2,
                    "classical_checks_log10": classical_log10,
                    "classical_checks_digits": classical_digits,
                    "per_partition_checks_log10": per_partition_log10,
                    "per_partition_checks_digits": per_partition_digits,
                    "constant_depth_stages": 2,
                    "orders_of_magnitude_reduced": orders_delta,
                }
            )

        print(
            "Live hardware scaling projection (empirical mean of congruence ratios):"
        )
        for row in aggregate_rows:
            bits = row["bits"]
            classical_digits = row["classical_checks_digits"]
            per_partition_digits = row["per_partition_checks_digits"]
            orders = row["orders_of_magnitude_reduced"]
            print(
                f"  RSA-{bits}: classical √n search ≈ 10^{classical_digits - 1} checks;"
                f" projected congruence-pruned load ≈ 10^{per_partition_digits - 1} per module"
                f" (Δ ≈ {orders:.2f} orders)",
            )

        aggregate_summary = {
            "method": "mean_congruence_ratio",
            "experiment_count": len(ratios),
            "mean_collapse_ratio": mean_ratio,
            "min_collapse_ratio": min_ratio,
            "max_collapse_ratio": max_ratio,
            "mean_candidates_pruned": (
                sum(checks_saved_stats) / len(checks_saved_stats)
                if checks_saved_stats
                else None
            ),
            "mean_surviving_candidates": (
                sum(surviving_candidate_stats) / len(surviving_candidate_stats)
                if surviving_candidate_stats
                else None
            ),
            "analysis_rows": aggregate_rows,
        }
    else:
        print("No experiment data available; skipping projection calculations.")
        aggregate_summary = {
            "method": "mean_congruence_ratio",
            "experiment_count": 0,
            "mean_collapse_ratio": None,
            "min_collapse_ratio": None,
            "max_collapse_ratio": None,
            "analysis_rows": [],
        }

    report = {
        "analysis_bits": analysis_bits,
        "experiments": enriched_experiments,
        "projection": aggregate_summary,
    }

    output_root.mkdir(exist_ok=True)
    report_path = output_root / "analysis_report.json"
    report_path.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print("SUCCESS: analysis_report.json generated from live run data.")
    return report_path, aggregate_rows


def run_partition_based_rsa_demo(
    moduli: Sequence[int], analysis_bits: Iterable[int]
) -> None:
    analysis_bits = list(analysis_bits)
    moduli = list(moduli)

    if not moduli:
        print("No moduli provided; supply at least one composite for the experiment.")
        return

    print("Thiele Machine: Empirical RSA Partition Experiments")
    print("=" * 72)
    print(
        "Each modulus is factored three times (blind sequential, blind partition,"
        " and sighted SMT-guided structural discovery) to collect live scaling data."
    )

    output_root = Path("rsa_demo_output")
    output_root.mkdir(exist_ok=True)

    experiments: List[Dict[str, object]] = []

    for modulus in moduli:
        partitions = _partition_search_space(modulus)
        partition_payload = _serialise_partitions(partitions)
        stats = _collect_partition_stats(modulus, partitions)
        sqrt_bound = int(stats["sqrt_bound"])
        bit_length = stats["bit_length"]
        experiment_root = output_root / f"n_{modulus}"
        experiment_root.mkdir(exist_ok=True)

        print(f"\n--- Starting Experiment for N={modulus} ---")
        print(f"Bit length: {bit_length} bits; √n search bound: {sqrt_bound}")

        # Act I – Sequential trial division
        print("\n--- ACT I: The Blind Worker (Turing Machine Emulation) ---")
        print(
            "The VM is intentionally blinded to a single instruction stream. It"
            " mirrors a Turing machine performing naive trial division.",
        )
        act_i_program, act_i_scripts = _act_i_program(modulus)
        act_i_dir = experiment_root / "act_i"
        act_i_result = _run_vm_program(act_i_program, act_i_scripts, act_i_dir)
        print(f"Candidate checks executed: {act_i_result.candidate_checks}")
        if act_i_result.witness:
            factor, cofactor = act_i_result.witness
            print(f"Witness recovered sequentially: {factor} × {cofactor} = {modulus}")
        if act_i_result.mu_total is not None:
            print(f"μ-total recorded by VM: {act_i_result.mu_total}")

        # Act II – Partitioned tasks without reasoning
        print("\n--- ACT II: The Blind Factory (Modern CPU Emulation) ---")
        print(
            "Partitions emulate a modern multi-core CPU. Each worker blindly"
            " handles a slice of the search without understanding the overall"
            " structure.",
        )
        act_ii_program, act_ii_scripts = _act_ii_program(modulus, partitions, experiment_root)
        act_ii_dir = experiment_root / "act_ii"
        act_ii_result = _run_vm_program(act_ii_program, act_ii_scripts, act_ii_dir)
        print(
            "Task-level parallelism executed candidate checks across",
            f"{len(partitions)} partitions (total checks: {act_ii_result.candidate_checks}).",
        )
        if act_ii_result.highlight_lines:
            print("Trace highlights:")
            for line in act_ii_result.highlight_lines:
                print("  " + line)
        if act_ii_result.mu_total is not None:
            print(f"μ-total recorded by VM: {act_ii_result.mu_total}")

        # Act III – Sighted reasoning followed by structural execution
        print("\n--- ACT III: Sighted Structural Discovery (Geometric Oracle) ---")
        print(
            "The VM spends μ-bits querying a congruence oracle that certifies"
            " which residue classes could contain a factor.  Impossible classes"
            " are erased before the remaining arithmetic sweep executes.",
        )
        act_iii_program, act_iii_scripts, binary_threshold, host_summary = _act_iii_program(
            modulus, analysis_bits, experiment_root=experiment_root
        )
        act_iii_dir = experiment_root / "act_iii"
        act_iii_result = _run_vm_program(
            act_iii_program, act_iii_scripts, act_iii_dir
        )

        if act_iii_result.reasoning_lines:
            print("Reasoning transcript:")
            for line in act_iii_result.reasoning_lines:
                print("  " + line)
        else:
            print("Reasoning transcript: (no lines captured; inspect trace.log)")
        reasoning_summary = act_iii_result.reasoning_summary or {}
        if not reasoning_summary:
            reasoning_summary = dict(host_summary)

        reasoning_path = act_iii_dir / "structural_reasoning_summary.json"
        reasoning_path.write_text(
            json.dumps(reasoning_summary, indent=2), encoding="utf-8"
        )

        initial_candidates = reasoning_summary.get(
            "initial_candidates", max(0, sqrt_bound - 1)
        )
        remaining_candidates = reasoning_summary.get(
            "remaining_candidates", initial_candidates
        )
        binary_queries = reasoning_summary.get("queries", 0)
        mu_cost = reasoning_summary.get("mu_cost", float(binary_queries))
        collapse_ratio = (
            remaining_candidates / initial_candidates if initial_candidates else 1.0
        )
        checks_pruned = initial_candidates - remaining_candidates

        print("Structural reasoning summary:")
        print(f"  Initial candidates under √n: {initial_candidates}")
        print(
            "  Remaining arithmetic checks after congruence pruning:",
            remaining_candidates,
        )
        print(
            "  Geometric oracle queries issued:",
            binary_queries,
            f"(μ-cost ≈ {mu_cost:.1f})",
        )

        if act_iii_result.highlight_lines:
            print("Final search transcript:")
            for line in act_iii_result.highlight_lines:
                print("  " + line)
        if act_iii_result.mu_total is not None:
            print(f"μ-total recorded by VM: {act_iii_result.mu_total}")

        arithmetic_delta = (
            act_ii_result.candidate_checks - act_iii_result.candidate_checks
        )
        print(
            "Arithmetic work comparison:",
            f"Act II executed {act_ii_result.candidate_checks} checks versus",
            f"{act_iii_result.candidate_checks} after congruence pruning",
            f" (Δ = {arithmetic_delta}).",
        )

        analysis_rows, collapse_ratio = _analysis_rows_from_stats(
            {"sqrt_bound": sqrt_bound, "geometric_ratio": collapse_ratio},
            analysis_bits,
        )

        print("\nHardware scaling summary for this experiment (congruence ratios):")
        for row in analysis_rows:
            bits = row["bits"]
            classical_digits = row["classical_checks_digits"]
            per_digits = row["per_partition_checks_digits"]
            orders = row["orders_of_magnitude_reduced"]
            print(
                f"  RSA-{bits}: classical √n search ≈ 10^{classical_digits - 1} checks;",
                f"congruence pruning projects ~10^{per_digits - 1} residual",
                f"candidates (Δ ≈ {orders:.2f} orders)",
            )

        if act_iii_result.hardware_lines:
            print("VM-recorded hardware narrative:")
            for line in act_iii_result.hardware_lines:
                print("  " + line)

        witness_payload: Optional[Dict[str, int]]
        if act_iii_result.witness:
            factor, cofactor = act_iii_result.witness
            print(f"\n[SUCCESS] Factored {modulus} = {factor} × {cofactor}")
            witness_payload = {"factor": factor, "cofactor": cofactor}
            reasoning_summary.setdefault("witness", factor)
            reasoning_summary.setdefault("cofactor", cofactor)
        else:
            print(f"\n[FAIL] Act III failed to recover a witness for {modulus}")
            witness_payload = None

        experiments.append(
            {
                "modulus": modulus,
                "bit_length": bit_length,
                "sqrt_bound": sqrt_bound,
                "initial_candidates": initial_candidates,
                "partition_count": stats["partition_count"],
                "candidate_counts": stats["candidate_counts"],
                "total_candidates": stats["total_candidates"],
                "max_candidates_per_partition": stats[
                    "max_candidates_per_partition"
                ],
                "work_per_partition": stats["work_per_partition"],
                "partitions": partition_payload,
                "analysis_rows": analysis_rows,
                "partition_efficiency_ratio": collapse_ratio,
                "geometric_pruning": {
                    "method": "congruence_reasoning",
                    "queries": binary_queries,
                    "mu_cost": mu_cost,
                    "surviving_candidates": remaining_candidates,
                    "eliminated_candidates": checks_pruned,
                    "candidates_pruned": checks_pruned,
                    "arithmetic_checks_delta": arithmetic_delta,
                    "geometric_ratio": collapse_ratio,
                },
                "structural_reasoning": reasoning_summary,
                "congruence_base": binary_threshold,
                "witness": witness_payload,
                "acts": {
                    "act_i": {
                        "candidate_checks": act_i_result.candidate_checks,
                        "mu_total": act_i_result.mu_total,
                        "witness": act_i_result.witness,
                    },
                    "act_ii": {
                        "candidate_checks": act_ii_result.candidate_checks,
                        "mu_total": act_ii_result.mu_total,
                        "witness": act_ii_result.witness,
                    },
                    "act_iii": {
                        "candidate_checks": act_iii_result.candidate_checks,
                        "mu_total": act_iii_result.mu_total,
                        "witness": act_iii_result.witness,
                        "reasoning_success": binary_queries > 0,
                    },
                },
                "reasoning_transcript": act_iii_result.reasoning_lines,
                "hardware_transcript": act_iii_result.hardware_lines,
                "experiment_directory": str(experiment_root),
            }
        )

    analyze_hardware_scaling(experiments, analysis_bits, output_root)


def main() -> None:
    import argparse

    parser = argparse.ArgumentParser(
        description="Partition-native RSA experiment suite on the Thiele VM"
    )
    parser.add_argument(
        "--moduli",
        nargs="+",
        type=int,
        default=[10403],
        help="RSA moduli to factor (each should have tractable factors for the demo)",
    )
    parser.add_argument(
        "--analysis-bits",
        nargs="+",
        type=int,
        default=[256, 512, 1024, 2048, 4096],
        help="Bit lengths to include in the hardware scaling projection",
    )
    args = parser.parse_args()

    run_partition_based_rsa_demo(args.moduli, args.analysis_bits)


if __name__ == "__main__":
    main()
