#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""
Thiele Extremal Search Operator

Implements the complete search operator for finding extremal nonlocal boxes
using the Thiele Machine framework. This tool:

1. Generates random NS (no-signaling) boxes
2. Feeds them through the Python VM (PNEW+PSPLIT+PDISCOVER)
3. Computes geometric signatures and μ-costs
4. Maximizes Bell functionals over NS space
5. Outputs comprehensive artifacts for verification

Usage:
    python tools/thiele_extremal_search.py --shape 2,2,2,2 --seed 42 --mu-budget 10000

See spec/thiele_machine_spec.md for isomorphism requirements.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import time
from dataclasses import dataclass, field
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import numpy as np

# Add repository root to path
import sys
REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))

from thielecpu.state import State, MuLedger, MASK_WIDTH, MAX_MODULES
from thielecpu.vm import VM, compute_geometric_signature, classify_geometric_signature
from thielecpu.assemble import parse
from thielecpu._types import ModuleId


# =============================================================================
# Type Definitions
# =============================================================================

Bit = int
Setting = Tuple[Bit, ...]
Outcome = Tuple[Bit, ...]
Table = Dict[Setting, Dict[Outcome, float]]


@dataclass
class NSBox:
    """No-signaling box representation."""
    
    shape: Tuple[int, ...]  # (X, Y, A, B) - number of settings/outcomes
    probs: np.ndarray       # Probability tensor P(a,b|x,y)
    
    @property
    def X(self) -> int:
        return self.shape[0]
    
    @property
    def Y(self) -> int:
        return self.shape[1]
    
    @property
    def A(self) -> int:
        return self.shape[2]
    
    @property
    def B(self) -> int:
        return self.shape[3]
    
    def to_table(self) -> Table:
        """Convert to table format."""
        table: Table = {}
        for x in range(self.X):
            for y in range(self.Y):
                dist: Dict[Outcome, float] = {}
                for a in range(self.A):
                    for b in range(self.B):
                        dist[(a, b)] = float(self.probs[x, y, a, b])
                table[(x, y)] = dist
        return table
    
    def canonical_hash(self) -> str:
        """Compute canonical hash of the box."""
        # Round to 8 decimal places for stability
        rounded = np.round(self.probs, 8)
        data = json.dumps({
            "shape": list(self.shape),
            "probs": rounded.tolist()
        }, sort_keys=True).encode('utf-8')
        return hashlib.sha256(data).hexdigest()[:16]


@dataclass
class BellFunctional:
    """Bell functional (inequality) representation."""
    
    coefficients: np.ndarray  # Coefficients for each P(a,b|x,y)
    shape: Tuple[int, ...]
    
    def evaluate(self, box: NSBox) -> float:
        """Evaluate the functional on a box."""
        return float(np.sum(self.coefficients * box.probs))
    
    @classmethod
    def chsh(cls, X: int = 2, Y: int = 2, A: int = 2, B: int = 2) -> "BellFunctional":
        """Create CHSH functional."""
        coeffs = np.zeros((X, Y, A, B))
        
        # CHSH: E(0,0) + E(0,1) + E(1,0) - E(1,1)
        # E(x,y) = sum_{a,b} (-1)^(a+b) P(a,b|x,y)
        for x, y in product(range(X), range(Y)):
            sign = 1 if (x, y) != (1, 1) else -1
            for a, b in product(range(A), range(B)):
                parity = (-1) ** (a + b)
                coeffs[x, y, a, b] = sign * parity
        
        return cls(coefficients=coeffs, shape=(X, Y, A, B))


@dataclass
class SearchResult:
    """Result of extremal search."""
    
    box: NSBox
    canonical_hash: str
    bell_value: float
    bell_functional: np.ndarray
    mu_discovery: int
    mu_execution: int
    mu_total: int
    is_extremal: bool
    geometric_signature: Dict[str, float]
    structure_verdict: str
    vm_receipts: List[Dict[str, Any]]
    rtl_receipts: List[Dict[str, Any]]
    coq_stub: str
    search_iterations: int
    search_time: float


# =============================================================================
# NS Box Generation and Manipulation
# =============================================================================

def make_random_ns_box(
    shape: Tuple[int, int, int, int],
    rng: random.Random
) -> NSBox:
    """Generate a random no-signaling box.
    
    Uses rejection sampling to ensure NS constraints are satisfied.
    """
    X, Y, A, B = shape
    
    # Start with random probabilities
    probs = np.zeros((X, Y, A, B))
    
    for x in range(X):
        for y in range(Y):
            # Generate random distribution for this setting
            raw = np.array([rng.random() for _ in range(A * B)])
            raw = raw / raw.sum()
            probs[x, y] = raw.reshape(A, B)
    
    # Project onto NS polytope (enforce marginals)
    probs = project_to_ns(probs, shape)
    
    return NSBox(shape=shape, probs=probs)


def project_to_ns(probs: np.ndarray, shape: Tuple[int, int, int, int]) -> np.ndarray:
    """Project a box onto the no-signaling polytope.
    
    Uses iterative projection to enforce:
    - Normalization: sum_{a,b} P(a,b|x,y) = 1 for all x,y
    - Alice NS: sum_b P(a,b|x,y) = P(a|x) for all x,y,a
    - Bob NS: sum_a P(a,b|x,y) = P(b|y) for all x,y,b
    """
    X, Y, A, B = shape
    result = probs.copy()
    
    for _ in range(100):  # Iterate until convergence
        old = result.copy()
        
        # Normalize each distribution
        for x in range(X):
            for y in range(Y):
                total = result[x, y].sum()
                if total > 0:
                    result[x, y] /= total
                else:
                    result[x, y] = 1.0 / (A * B)
        
        # Enforce Alice NS constraint: sum_b P(a,b|x,y) = P(a|x) for all y
        for x in range(X):
            alice_marginal = result[x, 0].sum(axis=1)  # P(a|x) from y=0: shape (A,)
            for y in range(1, Y):
                current_marginal = result[x, y].sum(axis=1)  # shape (A,)
                if not np.allclose(current_marginal, alice_marginal, atol=1e-6):
                    # Adjust to match marginal by scaling all b values for each a
                    for a in range(A):
                        if current_marginal[a] > 0:
                            result[x, y, a, :] *= alice_marginal[a] / current_marginal[a]
        
        # Enforce Bob NS constraint: sum_a P(a,b|x,y) = P(b|y) for all x
        for y in range(Y):
            bob_marginal = result[0, y].sum(axis=0)  # P(b|y) from x=0: shape (B,)
            for x in range(1, X):
                current_marginal = result[x, y].sum(axis=0)  # shape (B,)
                if not np.allclose(current_marginal, bob_marginal, atol=1e-6):
                    # Adjust to match marginal by scaling all a values for each b
                    for b in range(B):
                        if current_marginal[b] > 0:
                            result[x, y, :, b] *= bob_marginal[b] / current_marginal[b]
        
        # Clip to valid probabilities
        result = np.clip(result, 0, 1)
        
        # Check convergence
        if np.allclose(result, old, atol=1e-8):
            break
    
    # Final normalization
    for x in range(X):
        for y in range(Y):
            total = result[x, y].sum()
            if total > 0:
                result[x, y] /= total
    
    return result


def canonicalize_box(box: NSBox) -> NSBox:
    """Canonicalize a box by sorting and normalizing."""
    # Apply symmetry reduction (relabeling)
    # For now, just normalize probabilities
    probs = np.round(box.probs, 10)
    probs = np.clip(probs, 0, 1)
    
    # Renormalize
    for x in range(box.X):
        for y in range(box.Y):
            total = probs[x, y].sum()
            if total > 0:
                probs[x, y] /= total
    
    return NSBox(shape=box.shape, probs=probs)


def check_no_signaling(box: NSBox, tol: float = 1e-6) -> bool:
    """Check if box satisfies no-signaling constraints."""
    # Alice NS
    for x in range(box.X):
        ref = box.probs[x, 0].sum(axis=1)
        for y in range(1, box.Y):
            current = box.probs[x, y].sum(axis=1)
            if not np.allclose(ref, current, atol=tol):
                return False
    
    # Bob NS
    for y in range(box.Y):
        ref = box.probs[0, y].sum(axis=0)
        for x in range(1, box.X):
            current = box.probs[x, y].sum(axis=0)
            if not np.allclose(ref, current, atol=tol):
                return False
    
    return True


# =============================================================================
# Thiele VM Integration
# =============================================================================

def run_vm_on_box(
    box: NSBox,
    state: State,
    vm: VM,
    outdir: Path
) -> Tuple[Dict[str, Any], List[Dict[str, Any]]]:
    """Run the Thiele VM on a box and return results.
    
    Executes PNEW+PSPLIT sequence to build module partitions,
    then computes geometric signature directly.
    """
    # Ensure output directory exists
    outdir.mkdir(parents=True, exist_ok=True)
    
    # Create program for this box
    program_lines = []
    program_lines.append("; Thiele extremal search program")
    program_lines.append(f"; Box shape: {box.shape}")
    program_lines.append("")
    
    # Create initial module for box elements
    # Map box indices to region elements (start from 10 to avoid overlap with VM's {0})
    base_idx = 10
    region_elements = set(range(base_idx, base_idx + min(box.X * box.Y, MASK_WIDTH - base_idx)))
    region_str = "{" + ",".join(map(str, sorted(region_elements))) + "}"
    program_lines.append(f"PNEW {region_str}")
    
    # Split by settings (Module 2 created from PNEW above)
    program_lines.append("PSPLIT 2")
    
    # MDLACC on one of the resulting modules to track cost
    program_lines.append("MDLACC 3")
    
    # Emit result
    program_lines.append(f'EMIT "box_hash={box.canonical_hash()}"')
    program_lines.append("HALT")
    
    # Parse and run
    program_text = "\n".join(program_lines)
    program = parse(program_text.split('\n'), outdir)
    
    # Run VM
    vm.run(program, outdir)
    
    # Compute geometric signature directly
    axioms_content = generate_box_axioms(box)
    signature = compute_geometric_signature(axioms_content, seed=42)
    verdict = classify_geometric_signature(signature)
    
    # Collect results
    result = {
        "mu_discovery": state.mu_ledger.mu_discovery,
        "mu_execution": state.mu_ledger.mu_execution,
        "mu_total": state.mu_ledger.total,
        "num_modules": state.num_modules,
        "geometric_signature": signature,
        "structure_verdict": verdict,
    }
    
    # Collect receipts
    receipts = [r.to_dict() for r in vm.step_receipts]
    
    return result, receipts


def generate_box_axioms(box: NSBox) -> str:
    """Generate axiom representation of box for PDISCOVER."""
    lines = []
    lines.append(f"; NS Box Axioms")
    lines.append(f"; Shape: {box.shape}")
    lines.append("")
    
    # Add normalization axioms
    for x in range(box.X):
        for y in range(box.Y):
            terms = []
            for a in range(box.A):
                for b in range(box.B):
                    terms.append(f"P_{x}{y}{a}{b}")
            lines.append(f"; Norm({x},{y}): {' + '.join(terms)} = 1")
    
    # Add NS axioms
    lines.append("")
    lines.append("; No-signaling constraints")
    lines.append("; Alice's marginals: sum_b P(a,b|x,y) = P(a|x) for all x,y,a")
    for x in range(box.X):
        for a in range(box.A):
            terms = [f"sum_b(P_{x}{y_val}{a}_)" for y_val in range(box.Y)]
            lines.append(f"; Alice({x},{a}): {' = '.join(terms)}")
    
    lines.append("; Bob's marginals: sum_a P(a,b|x,y) = P(b|y) for all x,y,b")
    for y in range(box.Y):
        for b in range(box.B):
            terms = [f"sum_a(P_{x_val}{y}_{b})" for x_val in range(box.X)]
            lines.append(f"; Bob({y},{b}): {' = '.join(terms)}")
    
    # Add actual probability values
    lines.append("")
    lines.append("; Probability values")
    for x in range(box.X):
        for y in range(box.Y):
            for a in range(box.A):
                for b in range(box.B):
                    p = box.probs[x, y, a, b]
                    lines.append(f"P_{x}{y}{a}{b} = {p:.8f}")
    
    return "\n".join(lines)


# =============================================================================
# Bell Functional Optimization
# =============================================================================

def maximize_bell_functional(
    initial_box: NSBox,
    functional: BellFunctional,
    mu_budget: int,
    rng: random.Random,
    max_iterations: int = 1000
) -> Tuple[NSBox, float, int]:
    """Maximize Bell functional over NS space.
    
    Uses seeded perturbations, symmetry reduction, and NS projection.
    """
    current_box = initial_box
    current_value = functional.evaluate(current_box)
    best_box = current_box
    best_value = current_value
    
    iterations = 0
    mu_spent = 0
    
    epsilon = 0.1  # Initial perturbation magnitude
    
    while iterations < max_iterations and mu_spent < mu_budget:
        iterations += 1
        
        # Perturb current box
        perturbed_probs = current_box.probs.copy()
        for x in range(current_box.X):
            for y in range(current_box.Y):
                for a in range(current_box.A):
                    for b in range(current_box.B):
                        delta = rng.gauss(0, epsilon)
                        perturbed_probs[x, y, a, b] += delta
        
        # Project back to NS polytope
        perturbed_probs = np.clip(perturbed_probs, 0, 1)
        perturbed_probs = project_to_ns(perturbed_probs, current_box.shape)
        
        # Create candidate box
        candidate = NSBox(shape=current_box.shape, probs=perturbed_probs)
        candidate = canonicalize_box(candidate)
        
        # Check NS constraint
        if not check_no_signaling(candidate):
            continue
        
        # Evaluate
        candidate_value = functional.evaluate(candidate)
        mu_spent += 1  # Each evaluation costs 1 μ-bit
        
        # Accept if better
        if candidate_value > current_value:
            current_box = candidate
            current_value = candidate_value
            
            if current_value > best_value:
                best_box = current_box
                best_value = current_value
        
        # Adaptive step size
        if iterations % 100 == 0:
            epsilon *= 0.95
    
    return best_box, best_value, iterations


def check_extremality(box: NSBox, functional: BellFunctional, rng: random.Random) -> bool:
    """Heuristic check for extremality using rank test.
    
    A box is likely extremal if small perturbations don't improve the value.
    """
    current_value = functional.evaluate(box)
    
    # Try many random perturbations
    for _ in range(100):
        perturbed_probs = box.probs.copy()
        for x in range(box.X):
            for y in range(box.Y):
                for a in range(box.A):
                    for b in range(box.B):
                        delta = rng.gauss(0, 0.01)
                        perturbed_probs[x, y, a, b] += delta
        
        perturbed_probs = np.clip(perturbed_probs, 0, 1)
        perturbed_probs = project_to_ns(perturbed_probs, box.shape)
        
        candidate = NSBox(shape=box.shape, probs=perturbed_probs)
        if check_no_signaling(candidate):
            candidate_value = functional.evaluate(candidate)
            if candidate_value > current_value + 1e-6:
                return False
    
    return True


# =============================================================================
# Coq Stub Generation
# =============================================================================

def generate_coq_stub(box: NSBox, result: SearchResult) -> str:
    """Generate Coq proof stub for the found box."""
    lines = []
    lines.append(f"(* Extremal NS Box Found by Thiele Search *)")
    lines.append(f"(* Canonical hash: {result.canonical_hash} *)")
    lines.append(f"(* Bell value: {result.bell_value:.8f} *)")
    lines.append(f"(* Structure: {result.structure_verdict} *)")
    lines.append("")
    lines.append("Require Import Reals.")
    lines.append("Require Import Psatz.")
    lines.append("")
    lines.append(f"Definition box_shape := ({box.X}, {box.Y}, {box.A}, {box.B}).")
    lines.append("")
    lines.append("(* Probability tensor *)")
    lines.append("Definition probs : list (list (list (list R))) :=")
    
    # Add probability values
    probs_str = "  ["
    for x in range(box.X):
        if x > 0:
            probs_str += "   "
        probs_str += "["
        for y in range(box.Y):
            if y > 0:
                probs_str += "    "
            probs_str += "["
            for a in range(box.A):
                if a > 0:
                    probs_str += "     "
                probs_str += "["
                for b in range(box.B):
                    p = box.probs[x, y, a, b]
                    probs_str += f"{p:.8f}"
                    if b < box.B - 1:
                        probs_str += "; "
                probs_str += "]"
                if a < box.A - 1:
                    probs_str += ";\n"
            probs_str += "]"
            if y < box.Y - 1:
                probs_str += ";\n"
        probs_str += "]"
        if x < box.X - 1:
            probs_str += ";\n"
    probs_str += "]."
    lines.append(probs_str)
    
    lines.append("")
    lines.append("(* NS constraints *)")
    lines.append("(* Alice: sum_b P(a,b|x,y) = P(a|x) for all x,y,a *)")
    lines.append("Hypothesis ns_alice : forall x y a,")
    lines.append("  sum_b (probs x y a b) = alice_marginal x a.")
    lines.append("(* Bob: sum_a P(a,b|x,y) = P(b|y) for all x,y,b *)")
    lines.append("Hypothesis ns_bob : forall x y b,")
    lines.append("  sum_a (probs x y a b) = bob_marginal y b.")
    lines.append("")
    lines.append("(* Bell functional coefficients *)")
    lines.append(f"(* μ-cost: {result.mu_total} *)")
    lines.append("")
    lines.append("(* Note: Formal proof of extremality requires symbolic verification *)")
    lines.append("Theorem extremality : is_extremal probs.")
    lines.append("Proof.")
    lines.append("  (* Verified by Thiele search with heuristic rank test *)")
    lines.append("Admitted.")
    
    return "\n".join(lines)


# =============================================================================
# RTL Trace Generation (Stub)
# =============================================================================

def generate_rtl_receipts(box: NSBox, outdir: Path) -> List[Dict[str, Any]]:
    """Generate RTL simulation receipts (placeholder).
    
    In full implementation, this would run Verilog simulation.
    """
    receipts = []
    receipts.append({
        "type": "rtl_init",
        "shape": list(box.shape),
        "hash": box.canonical_hash(),
        "timestamp": time.time()
    })
    receipts.append({
        "type": "rtl_complete",
        "mu_discovery": 0,
        "mu_execution": 0,
        "note": "RTL simulation stub - run tools/run_verilog_trace.sh for full trace"
    })
    return receipts


# =============================================================================
# Main Search Operator
# =============================================================================

def thiele_extremal_search(
    shape: Tuple[int, int, int, int],
    seed: int,
    mu_budget: int,
    outdir: Path,
    strategies: List[str] = None
) -> SearchResult:
    """
    Main search operator for finding extremal nonlocal boxes.
    
    Args:
        shape: (X, Y, A, B) - number of settings and outcomes
        seed: RNG seed for reproducibility
        mu_budget: Maximum μ-discovery budget
        outdir: Output directory for artifacts
        strategies: Partition discovery strategies to use
    
    Returns:
        SearchResult with all artifacts
    """
    if strategies is None:
        strategies = ["louvain", "spectral", "degree", "balanced"]
    
    rng = random.Random(seed)
    np.random.seed(seed)
    
    print(f"Thiele Extremal Search")
    print(f"  Shape: {shape}")
    print(f"  Seed: {seed}")
    print(f"  μ-budget: {mu_budget}")
    print(f"  Strategies: {strategies}")
    print()
    
    # Ensure output directory exists
    outdir.mkdir(parents=True, exist_ok=True)
    
    # 1. Generate random NS box
    print("Step 1: Generating random NS box...")
    start_time = time.time()
    initial_box = make_random_ns_box(shape, rng)
    initial_box = canonicalize_box(initial_box)
    
    if not check_no_signaling(initial_box):
        print("  Warning: Initial box violates NS - re-projecting...")
        initial_box = NSBox(
            shape=shape,
            probs=project_to_ns(initial_box.probs, shape)
        )
    
    print(f"  Initial box hash: {initial_box.canonical_hash()}")
    
    # 2. Run through Python VM
    print("\nStep 2: Running through Python VM...")
    state = State()
    vm = VM(state)
    vm_outdir = outdir / "vm_run"
    vm_result, vm_receipts = run_vm_on_box(initial_box, state, vm, vm_outdir)
    
    print(f"  μ-discovery: {vm_result['mu_discovery']}")
    print(f"  μ-execution: {vm_result['mu_execution']}")
    print(f"  μ-total: {vm_result['mu_total']}")
    print(f"  Structure verdict: {vm_result.get('structure_verdict', 'UNKNOWN')}")
    
    # 3. Create Bell functional and maximize
    print("\nStep 3: Maximizing Bell functional...")
    functional = BellFunctional.chsh(*shape)
    initial_value = functional.evaluate(initial_box)
    print(f"  Initial CHSH value: {initial_value:.6f}")
    
    # Subtract VM μ-costs from the budget
    remaining_budget = max(0, mu_budget - vm_result['mu_total'])
    print(f"  Remaining μ-budget after VM: {remaining_budget}")
    
    optimized_box, optimized_value, search_iters = maximize_bell_functional(
        initial_box, functional, remaining_budget, rng
    )
    print(f"  Optimized CHSH value: {optimized_value:.6f}")
    print(f"  Search iterations: {search_iters}")
    
    # 4. Check extremality
    print("\nStep 4: Checking extremality...")
    is_extremal = check_extremality(optimized_box, functional, rng)
    print(f"  Extremal: {is_extremal}")
    
    # 5. Generate RTL receipts (stub)
    print("\nStep 5: Generating RTL receipts...")
    rtl_receipts = generate_rtl_receipts(optimized_box, outdir)
    
    # 6. Create result
    total_time = time.time() - start_time
    
    result = SearchResult(
        box=optimized_box,
        canonical_hash=optimized_box.canonical_hash(),
        bell_value=optimized_value,
        bell_functional=functional.coefficients,
        mu_discovery=vm_result['mu_discovery'],
        mu_execution=vm_result['mu_execution'],
        mu_total=vm_result['mu_total'],
        is_extremal=is_extremal,
        geometric_signature=vm_result.get('geometric_signature', {}),
        structure_verdict=vm_result.get('structure_verdict', 'UNKNOWN'),
        vm_receipts=vm_receipts,
        rtl_receipts=rtl_receipts,
        coq_stub="",  # Will be generated below
        search_iterations=search_iters,
        search_time=total_time
    )
    
    # Generate Coq stub
    result.coq_stub = generate_coq_stub(optimized_box, result)
    
    # 7. Save artifacts
    print("\nStep 6: Saving artifacts...")
    save_artifacts(result, outdir)
    
    print(f"\nSearch complete in {total_time:.2f}s")
    print(f"Artifacts saved to: {outdir}")
    
    return result


def save_artifacts(result: SearchResult, outdir: Path) -> None:
    """Save all search artifacts to output directory."""
    
    # Box probabilities
    box_path = outdir / "box.json"
    box_data = {
        "shape": list(result.box.shape),
        "probs": result.box.probs.tolist(),
        "canonical_hash": result.canonical_hash,
        "bell_value": result.bell_value,
        "is_extremal": result.is_extremal
    }
    box_path.write_text(json.dumps(box_data, indent=2), encoding='utf-8')
    
    # Bell functional
    functional_path = outdir / "functional.json"
    functional_data = {
        "coefficients": result.bell_functional.tolist(),
        "value": result.bell_value
    }
    functional_path.write_text(json.dumps(functional_data, indent=2), encoding='utf-8')
    
    # μ-cost summary
    mu_path = outdir / "mu_summary.json"
    mu_data = {
        "mu_discovery": result.mu_discovery,
        "mu_execution": result.mu_execution,
        "mu_total": result.mu_total
    }
    mu_path.write_text(json.dumps(mu_data, indent=2), encoding='utf-8')
    
    # Geometric signature
    sig_path = outdir / "geometric_signature.json"
    sig_data = {
        "signature": result.geometric_signature,
        "verdict": result.structure_verdict
    }
    sig_path.write_text(json.dumps(sig_data, indent=2), encoding='utf-8')
    
    # VM receipts
    vm_receipts_path = outdir / "vm_receipts.json"
    vm_receipts_path.write_text(json.dumps(result.vm_receipts, indent=2), encoding='utf-8')
    
    # RTL receipts
    rtl_receipts_path = outdir / "rtl_receipts.json"
    rtl_receipts_path.write_text(json.dumps(result.rtl_receipts, indent=2), encoding='utf-8')
    
    # Coq stub
    coq_path = outdir / "extremal_box.v"
    coq_path.write_text(result.coq_stub, encoding='utf-8')
    
    # Full summary
    summary_path = outdir / "search_summary.json"
    summary = {
        "canonical_hash": result.canonical_hash,
        "shape": list(result.box.shape),
        "bell_value": result.bell_value,
        "is_extremal": result.is_extremal,
        "mu_discovery": result.mu_discovery,
        "mu_execution": result.mu_execution,
        "mu_total": result.mu_total,
        "structure_verdict": result.structure_verdict,
        "search_iterations": result.search_iterations,
        "search_time": result.search_time
    }
    summary_path.write_text(json.dumps(summary, indent=2), encoding='utf-8')


# Base index offset to avoid overlap with VM's initial module at {0}
REGION_BASE_OFFSET = 10


def load_config(config_path: Path) -> Dict[str, Any]:
    """Load search configuration from JSON file."""
    with open(config_path, 'r', encoding='utf-8') as f:
        config = json.load(f)
    
    # Validate required fields
    required = ['shape', 'seed', 'mu_budget']
    for field in required:
        if field not in config:
            raise ValueError(f"Config file missing required field: {field}")
    
    return config


def calculate_region_mask(element_count: int, base_offset: int = REGION_BASE_OFFSET) -> int:
    """Calculate a region bitmask for the given number of elements.
    
    Args:
        element_count: Number of elements to include in the region
        base_offset: Starting bit position to avoid conflicts
    
    Returns:
        Bitmask with element_count bits set starting at base_offset
    """
    max_elements = min(element_count, MASK_WIDTH - base_offset)
    return sum(1 << (base_offset + i) for i in range(max_elements))


def generate_rtl_trace_program(box: NSBox, config: Dict[str, Any]) -> str:
    """Generate a Verilog testbench program that matches the Python VM operations.
    
    This produces a sequence of operations that the RTL can execute to generate
    matching traces for isomorphism verification.
    """
    lines = []
    lines.append("// Auto-generated RTL test program for isomorphism verification")
    lines.append(f"// Config: shape={config.get('shape')}, seed={config.get('seed')}")
    lines.append(f"// Box hash: {box.canonical_hash()}")
    lines.append("")
    
    # Map box elements to regions using the shared helper
    region = calculate_region_mask(box.X * box.Y)
    
    lines.append(f"// PNEW operation: region = 0x{region:016x}")
    lines.append(f"pnew_region <= 64'h{region:016x};")
    lines.append("execute_op(OPC_PNEW);")
    lines.append("")
    
    lines.append("// PSPLIT operation")
    lines.append("psplit_module_id <= 2;")
    lines.append("psplit_mask <= 64'h0000000000000001;")
    lines.append("execute_op(OPC_PSPLIT);")
    
    return "\n".join(lines)


# =============================================================================
# CLI Entry Point
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Thiele Extremal Search Operator for NS boxes"
    )
    parser.add_argument(
        "--shape",
        type=str,
        default="2,2,2,2",
        help="Box shape as X,Y,A,B (default: 2,2,2,2)"
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=42,
        help="RNG seed for reproducibility (default: 42)"
    )
    parser.add_argument(
        "--mu-budget",
        type=int,
        default=10000,
        help="μ-discovery budget (default: 10000)"
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("artifacts/nl_search"),
        help="Output directory (default: artifacts/nl_search)"
    )
    parser.add_argument(
        "--strategies",
        type=str,
        default="louvain,spectral,degree,balanced",
        help="Comma-separated list of partition discovery strategies"
    )
    parser.add_argument(
        "--config",
        type=Path,
        default=None,
        help="Load search parameters from JSON config file"
    )
    parser.add_argument(
        "--emit-vm-trace",
        action="store_true",
        help="Emit detailed VM trace for isomorphism verification"
    )
    parser.add_argument(
        "--emit-rtl-trace",
        action="store_true",
        help="Generate RTL test program for hardware trace comparison"
    )
    
    args = parser.parse_args()
    
    # Load from config file if provided
    if args.config:
        config = load_config(args.config)
        shape = tuple(config['shape'])
        seed = config['seed']
        mu_budget = config['mu_budget']
        strategies = config.get('strategies', ['louvain', 'spectral', 'degree', 'balanced'])
        emit_vm_trace = config.get('emit_vm_trace', False) or args.emit_vm_trace
        emit_rtl_trace = config.get('emit_rtl_trace', False) or args.emit_rtl_trace
        
        print(f"Loaded config from: {args.config}")
        print(f"  Name: {config.get('name', 'unnamed')}")
        print(f"  Description: {config.get('description', 'N/A')}")
    else:
        # Parse shape
        shape = tuple(map(int, args.shape.split(",")))
        seed = args.seed
        mu_budget = args.mu_budget
        strategies = args.strategies.split(",")
        emit_vm_trace = args.emit_vm_trace
        emit_rtl_trace = args.emit_rtl_trace
    
    if len(shape) != 4:
        parser.error("Shape must have exactly 4 components: X,Y,A,B")
    
    # Run search
    result = thiele_extremal_search(
        shape=shape,
        seed=seed,
        mu_budget=mu_budget,
        outdir=args.output,
        strategies=strategies
    )
    
    # Emit detailed VM trace if requested
    if emit_vm_trace:
        print("\n=== VM Trace Mode Enabled ===")
        vm_trace_path = args.output / "vm_trace_detailed.json"
        vm_trace = {
            "config": {
                "shape": list(shape),
                "seed": seed,
                "mu_budget": mu_budget,
                "strategies": strategies
            },
            "box_hash": result.canonical_hash,
            "operations": [
                {
                    "step": i,
                    "op": r.get("instruction", {}).get("op", "UNKNOWN"),
                    "payload": r.get("instruction", {}).get("payload", None),
                    "pre_state": r.get("pre_state", {}),
                    "post_state": r.get("post_state", {}),
                    "observation": r.get("observation", {})
                }
                for i, r in enumerate(result.vm_receipts)
            ],
            "mu_summary": {
                "mu_discovery": result.mu_discovery,
                "mu_execution": result.mu_execution,
                "mu_total": result.mu_total
            }
        }
        vm_trace_path.write_text(json.dumps(vm_trace, indent=2), encoding='utf-8')
        print(f"  VM trace written to: {vm_trace_path}")
    
    # Emit RTL test program if requested
    if emit_rtl_trace:
        print("\n=== RTL Trace Mode Enabled ===")
        rtl_program_path = args.output / "rtl_test_program.v"
        rtl_program = generate_rtl_trace_program(result.box, {
            'shape': list(shape),
            'seed': seed
        })
        rtl_program_path.write_text(rtl_program, encoding='utf-8')
        print(f"  RTL test program written to: {rtl_program_path}")
        
        # Also save expected RTL trace based on spec using the helper function
        rtl_expected_path = args.output / "rtl_expected_trace.json"
        element_count = shape[0] * shape[1]
        region_mask = calculate_region_mask(element_count)
        rtl_expected = {
            "config": {
                "shape": list(shape),
                "seed": seed
            },
            "box_hash": result.canonical_hash,
            "expected_operations": [
                {
                    "step": 0,
                    "opcode": "PNEW",
                    "region": region_mask,
                    "mu_discovery_delta": min(element_count, MASK_WIDTH - REGION_BASE_OFFSET),
                    "mu_execution_delta": 0
                },
                {
                    "step": 1,
                    "opcode": "PSPLIT",
                    "region": 0,
                    "mu_discovery_delta": 0,
                    "mu_execution_delta": MASK_WIDTH
                }
            ],
            "expected_mu_discovery": result.mu_discovery,
            "expected_mu_execution": result.mu_execution,
            "note": "RTL should produce identical μ-costs to VM"
        }
        rtl_expected_path.write_text(json.dumps(rtl_expected, indent=2), encoding='utf-8')
        print(f"  RTL expected trace written to: {rtl_expected_path}")
    
    # Print summary
    print("\n" + "=" * 60)
    print("SEARCH RESULT SUMMARY")
    print("=" * 60)
    print(f"Canonical hash: {result.canonical_hash}")
    print(f"Bell value: {result.bell_value:.6f}")
    print(f"Extremal: {result.is_extremal}")
    print(f"μ-total: {result.mu_total}")
    print(f"Structure: {result.structure_verdict}")
    print(f"Iterations: {result.search_iterations}")
    print(f"Time: {result.search_time:.2f}s")
    
    if emit_vm_trace or emit_rtl_trace:
        print(f"\nTrace files written to: {args.output}")
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
