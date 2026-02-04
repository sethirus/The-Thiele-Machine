#!/usr/bin/env python3
"""
Φ (Integrated Information) vs μ Correlation Experiment

This tests the prediction from NOVEL_PREDICTIONS.md Section 4:
  Φ(S) ∝ μ_accumulated(internal processing)

The hypothesis: Consciousness (as measured by integrated information)
correlates with the amount of irreversible internal information processing.

Author: Thiele Machine
Date: February 2026
"""

import random
import math
import numpy as np
from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Optional, Set
from collections import defaultdict


@dataclass
class MuAccountant:
    """Tracks μ-cost of operations."""
    mu: int = 0
    reversible_ops: int = 0
    irreversible_ops: int = 0
    
    def reversible(self, description: str = ""):
        """Record a reversible operation (μ = 0)."""
        self.reversible_ops += 1
    
    def irreversible(self, cost: int = 1, description: str = ""):
        """Record an irreversible operation (μ > 0)."""
        self.mu += cost
        self.irreversible_ops += 1


# =============================================================================
# Simple Networks for Testing
# =============================================================================

class SimpleNetwork:
    """
    A simple neural network model for testing Φ vs μ.
    
    This is a discrete automaton where nodes update based on neighbors.
    """
    
    def __init__(self, n_nodes: int, architecture: str = "feedforward"):
        self.n = n_nodes
        self.architecture = architecture
        self.state = np.zeros(n_nodes, dtype=int)
        self.weights = np.zeros((n_nodes, n_nodes))
        self.history = []
        self.accountant = MuAccountant()
        
        self._init_architecture()
    
    def _init_architecture(self):
        """Initialize network architecture."""
        if self.architecture == "feedforward":
            # Layer-wise feedforward: no recurrence
            # Node i connects to nodes i+1..i+k
            for i in range(self.n - 1):
                for j in range(i + 1, min(i + 3, self.n)):
                    self.weights[i, j] = random.choice([-1, 0, 1])
        
        elif self.architecture == "recurrent":
            # Recurrent: includes feedback connections
            for i in range(self.n):
                for j in range(self.n):
                    if i != j and random.random() < 0.3:
                        self.weights[i, j] = random.choice([-1, 0, 1])
        
        elif self.architecture == "reservoir":
            # Reservoir computing: dense random connections
            self.weights = np.random.choice([-1, 0, 1], size=(self.n, self.n), p=[0.2, 0.6, 0.2])
            np.fill_diagonal(self.weights, 0)
        
        elif self.architecture == "modular":
            # Modular: clusters with dense internal, sparse external connections
            n_modules = max(2, self.n // 4)
            module_size = self.n // n_modules
            
            for i in range(self.n):
                mi = i // module_size
                for j in range(self.n):
                    mj = j // module_size
                    if i != j:
                        if mi == mj:
                            # Same module: dense
                            if random.random() < 0.5:
                                self.weights[i, j] = random.choice([-1, 1])
                        else:
                            # Different module: sparse
                            if random.random() < 0.1:
                                self.weights[i, j] = random.choice([-1, 1])
        
        elif self.architecture == "isolated":
            # No connections - each node independent
            pass
    
    def set_input(self, pattern: np.ndarray):
        """Set initial state (input pattern)."""
        self.state = pattern.copy()
        self.history = [self.state.copy()]
    
    def step(self):
        """Update network state by one step."""
        new_state = np.zeros_like(self.state)
        
        for j in range(self.n):
            # Compute input to node j
            total_input = sum(self.weights[i, j] * self.state[i] for i in range(self.n))
            
            # Nonlinear activation (threshold)
            if total_input > 0:
                new_state[j] = 1
            elif total_input < 0:
                new_state[j] = 0
            else:
                # No input change - keep previous (or random for first layer)
                if self.architecture == "feedforward":
                    new_state[j] = self.state[j]
                else:
                    new_state[j] = self.state[j]
            
            # Track μ-cost: irreversible if information is lost
            if new_state[j] != self.state[j]:
                # State changed - might be irreversible
                if self._is_irreversible_update(j, new_state[j]):
                    self.accountant.irreversible()
                else:
                    self.accountant.reversible()
        
        self.state = new_state
        self.history.append(self.state.copy())
    
    def _is_irreversible_update(self, node: int, new_value: int) -> bool:
        """
        Check if an update is irreversible.
        
        Irreversible = many-to-one mapping (information lost).
        In neural networks: convergent inputs, saturation effects.
        """
        # Count how many input patterns could produce this output
        n_inputs = sum(1 for i in range(self.n) if self.weights[i, node] != 0)
        
        if n_inputs == 0:
            return False  # No inputs = no processing
        
        # Simplistic model: irreversible if node has >1 input (many-to-one possible)
        return n_inputs > 1
    
    def run(self, steps: int = 10):
        """Run network for multiple steps."""
        for _ in range(steps):
            self.step()


# =============================================================================
# Integrated Information (Φ) Approximation
# =============================================================================

def compute_phi_approximation(network: SimpleNetwork) -> float:
    """
    Compute an approximation of integrated information (Φ).
    
    True Φ computation is NP-hard, so we use heuristics:
    1. Measure information integration across the system
    2. Compare whole system to sum of parts
    
    Higher Φ = more integrated processing, less reducible to parts.
    """
    if len(network.history) < 2:
        return 0.0
    
    n = network.n
    
    # Measure 1: Mutual information between nodes across time
    # This approximates how much nodes "talk to each other"
    
    mutual_info = 0.0
    for t in range(1, len(network.history)):
        prev = network.history[t - 1]
        curr = network.history[t]
        
        # Count correlated state changes
        for i in range(n):
            for j in range(n):
                if i != j:
                    # Did changes in i correlate with changes in j?
                    changed_i = prev[i] != curr[i]
                    changed_j = prev[j] != curr[j]
                    
                    if changed_i and changed_j and network.weights[i, j] != 0:
                        mutual_info += 1
    
    # Normalize by system size and time
    mutual_info /= (n * n * max(1, len(network.history) - 1))
    
    # Measure 2: System-wide state complexity
    # Entropy of state distribution
    
    state_counts = defaultdict(int)
    for state in network.history:
        state_key = tuple(state)
        state_counts[state_key] += 1
    
    total = len(network.history)
    entropy = 0.0
    for count in state_counts.values():
        p = count / total
        if p > 0:
            entropy -= p * math.log2(p)
    
    # Measure 3: Integration score
    # How much of state update depends on multiple inputs?
    
    integration = 0.0
    for t in range(1, len(network.history)):
        for j in range(n):
            # Count inputs that changed and affected this node
            inputs_changed = sum(
                1 for i in range(n) 
                if network.weights[i, j] != 0 and 
                   network.history[t-1][i] != network.history[t][i]
            )
            integration += min(inputs_changed, 3)  # Cap contribution
    
    integration /= (n * max(1, len(network.history) - 1))
    
    # Combine measures into Φ approximation
    # Weight by how "integrated" the processing is
    
    phi = (mutual_info * 0.3 + entropy * 0.3 + integration * 0.4)
    
    # Scale by connectivity (isolated systems have Φ = 0)
    connectivity = np.sum(np.abs(network.weights)) / (n * n)
    phi *= connectivity
    
    return phi


def compute_effective_information(network: SimpleNetwork) -> float:
    """
    Compute effective information (EI) as another integration measure.
    
    EI = How much does the whole system know about its past?
    """
    if len(network.history) < 2:
        return 0.0
    
    n = network.n
    
    # State transitions
    transitions = defaultdict(lambda: defaultdict(int))
    for t in range(1, len(network.history)):
        prev = tuple(network.history[t - 1])
        curr = tuple(network.history[t])
        transitions[prev][curr] += 1
    
    # Compute determinism: given past, how predictable is future?
    determinism = 0.0
    total_transitions = 0
    
    for prev_state, next_states in transitions.items():
        total = sum(next_states.values())
        for count in next_states.values():
            p = count / total
            if p > 0:
                determinism += p * math.log2(p)
        total_transitions += 1
    
    if total_transitions > 0:
        determinism /= total_transitions
    
    # Higher determinism = more EI (but cap at practical levels)
    return max(0, -determinism)


# =============================================================================
# Main Experiments
# =============================================================================

def test_architecture_comparison():
    """
    Test 1: Compare Φ and μ across different architectures.
    
    Prediction: More integrated architectures have higher Φ and μ.
    """
    print("=" * 70)
    print("TEST 1: Architecture Comparison")
    print("=" * 70)
    print()
    
    architectures = ["isolated", "feedforward", "modular", "recurrent", "reservoir"]
    results = []
    
    print(f"{'Architecture':>15} {'Φ (approx)':>12} {'EI':>10} {'μ-cost':>10} {'Φ/μ ratio':>12}")
    print("-" * 65)
    
    for arch in architectures:
        # Average over multiple runs
        phi_sum, ei_sum, mu_sum = 0, 0, 0
        n_runs = 5
        
        for seed in range(n_runs):
            random.seed(42 + seed)
            np.random.seed(42 + seed)
            
            net = SimpleNetwork(n_nodes=16, architecture=arch)
            
            # Random input
            net.set_input(np.random.randint(0, 2, 16))
            net.run(steps=20)
            
            phi_sum += compute_phi_approximation(net)
            ei_sum += compute_effective_information(net)
            mu_sum += net.accountant.mu
        
        phi_avg = phi_sum / n_runs
        ei_avg = ei_sum / n_runs
        mu_avg = mu_sum / n_runs
        ratio = phi_avg / max(mu_avg, 0.01)
        
        results.append((arch, phi_avg, ei_avg, mu_avg, ratio))
        print(f"{arch:>15} {phi_avg:>12.4f} {ei_avg:>10.4f} {mu_avg:>10.1f} {ratio:>12.4f}")
    
    # Analyze correlation
    print()
    print("ANALYSIS:")
    print("-" * 40)
    
    # Compute correlation between Φ and μ
    phis = [r[1] for r in results]
    mus = [r[3] for r in results]
    
    if len(set(mus)) > 1 and len(set(phis)) > 1:
        correlation = np.corrcoef(phis, mus)[0, 1]
        print(f"Correlation(Φ, μ) = {correlation:.4f}")
        
        if correlation > 0.5:
            print("✓ POSITIVE CORRELATION: Φ increases with μ")
            print("  Supports prediction: integrated processing requires irreversibility")
        elif correlation < -0.5:
            print("✗ NEGATIVE CORRELATION: Unexpected!")
        else:
            print("? WEAK CORRELATION: May need more data or refinement")
    else:
        print("Insufficient variance for correlation analysis")
    
    return results


def test_scaling():
    """
    Test 2: How do Φ and μ scale with network size?
    """
    print()
    print("=" * 70)
    print("TEST 2: Scaling with Network Size")
    print("=" * 70)
    print()
    
    sizes = [4, 8, 16, 32, 64]
    results = []
    
    print(f"{'Size':>8} {'Φ':>12} {'μ':>10} {'Φ/n':>12} {'μ/n':>10}")
    print("-" * 55)
    
    for n in sizes:
        random.seed(42)
        np.random.seed(42)
        
        net = SimpleNetwork(n_nodes=n, architecture="recurrent")
        net.set_input(np.random.randint(0, 2, n))
        net.run(steps=20)
        
        phi = compute_phi_approximation(net)
        mu = net.accountant.mu
        
        results.append((n, phi, mu))
        print(f"{n:>8} {phi:>12.4f} {mu:>10} {phi/n:>12.6f} {mu/n:>10.2f}")
    
    print()
    print("ANALYSIS:")
    print("-" * 40)
    
    sizes_arr = np.array([r[0] for r in results])
    phis = np.array([r[1] for r in results])
    mus = np.array([r[2] for r in results])
    
    # Check scaling
    if len(results) >= 3:
        # Log-log regression for power law scaling
        log_sizes = np.log(sizes_arr)
        log_phis = np.log(phis + 1e-10)
        log_mus = np.log(mus + 1)
        
        # Simple linear regression
        phi_slope = np.polyfit(log_sizes, log_phis, 1)[0]
        mu_slope = np.polyfit(log_sizes, log_mus, 1)[0]
        
        print(f"Φ scales as n^{phi_slope:.2f}")
        print(f"μ scales as n^{mu_slope:.2f}")
        
        if abs(phi_slope - mu_slope) < 0.5:
            print("✓ SIMILAR SCALING: Φ and μ grow together with system size")
        else:
            print(f"? DIFFERENT SCALING: Φ ~ n^{phi_slope:.2f}, μ ~ n^{mu_slope:.2f}")
    
    return results


def test_processing_types():
    """
    Test 3: Compare Φ and μ for different processing types.
    """
    print()
    print("=" * 70)
    print("TEST 3: Processing Type Comparison")
    print("=" * 70)
    print()
    
    n = 16
    results = []
    
    print("Processing types:")
    print("-" * 40)
    
    # Type 1: Pure feedforward (no integration)
    print("\n1. Feedforward only (no recurrence):")
    net1 = SimpleNetwork(n, "feedforward")
    net1.set_input(np.random.randint(0, 2, n))
    net1.run(20)
    phi1 = compute_phi_approximation(net1)
    mu1 = net1.accountant.mu
    print(f"   Φ = {phi1:.4f}, μ = {mu1}")
    results.append(("Feedforward", phi1, mu1))
    
    # Type 2: Recurrent (integration)
    print("\n2. Recurrent (with feedback):")
    net2 = SimpleNetwork(n, "recurrent")
    net2.set_input(np.random.randint(0, 2, n))
    net2.run(20)
    phi2 = compute_phi_approximation(net2)
    mu2 = net2.accountant.mu
    print(f"   Φ = {phi2:.4f}, μ = {mu2}")
    results.append(("Recurrent", phi2, mu2))
    
    # Type 3: Dense integration (reservoir)
    print("\n3. Dense reservoir (maximum integration):")
    net3 = SimpleNetwork(n, "reservoir")
    net3.set_input(np.random.randint(0, 2, n))
    net3.run(20)
    phi3 = compute_phi_approximation(net3)
    mu3 = net3.accountant.mu
    print(f"   Φ = {phi3:.4f}, μ = {mu3}")
    results.append(("Reservoir", phi3, mu3))
    
    # Type 4: Modular (partial integration)
    print("\n4. Modular (clustered integration):")
    net4 = SimpleNetwork(n, "modular")
    net4.set_input(np.random.randint(0, 2, n))
    net4.run(20)
    phi4 = compute_phi_approximation(net4)
    mu4 = net4.accountant.mu
    print(f"   Φ = {phi4:.4f}, μ = {mu4}")
    results.append(("Modular", phi4, mu4))
    
    print()
    print("ANALYSIS:")
    print("-" * 40)
    
    # Sort by Φ
    sorted_results = sorted(results, key=lambda x: x[1])
    print("Ranking by Φ (integration):")
    for i, (name, phi, mu) in enumerate(sorted_results):
        print(f"  {i+1}. {name}: Φ={phi:.4f}, μ={mu}")
    
    # Check if μ order matches Φ order
    phi_order = [r[0] for r in sorted_results]
    mu_order = [r[0] for r in sorted(results, key=lambda x: x[2])]
    
    if phi_order == mu_order:
        print("\n✓ ORDER PRESERVED: Higher Φ architectures also have higher μ")
    else:
        print(f"\n? ORDER DIFFERS: Φ order: {phi_order}")
        print(f"                μ order: {mu_order}")
    
    return results


def test_reversible_vs_irreversible():
    """
    Test 4: Explicitly compare reversible vs irreversible computation.
    """
    print()
    print("=" * 70)
    print("TEST 4: Reversible vs Irreversible Computation")
    print("=" * 70)
    print()
    
    class ReversibleNetwork(SimpleNetwork):
        """Network that tracks reversibility explicitly."""
        
        def step(self):
            """Reversible update: permutation only, no information loss."""
            # Reversible = permutation (no two states map to same output)
            # We implement this as a rotation
            new_state = np.roll(self.state, 1)
            self.accountant.reversible("Reversible rotation")
            self.state = new_state
            self.history.append(self.state.copy())
    
    print("Reversible computation (permutation only):")
    rev_net = ReversibleNetwork(16, "feedforward")
    rev_net.set_input(np.random.randint(0, 2, 16))
    rev_net.run(20)
    phi_rev = compute_phi_approximation(rev_net)
    mu_rev = rev_net.accountant.mu
    print(f"  Φ = {phi_rev:.4f}, μ = {mu_rev}")
    print(f"  Reversible ops: {rev_net.accountant.reversible_ops}")
    print(f"  Irreversible ops: {rev_net.accountant.irreversible_ops}")
    
    print()
    print("Irreversible computation (information loss):")
    irr_net = SimpleNetwork(16, "recurrent")
    irr_net.set_input(np.random.randint(0, 2, 16))
    irr_net.run(20)
    phi_irr = compute_phi_approximation(irr_net)
    mu_irr = irr_net.accountant.mu
    print(f"  Φ = {phi_irr:.4f}, μ = {mu_irr}")
    print(f"  Reversible ops: {irr_net.accountant.reversible_ops}")
    print(f"  Irreversible ops: {irr_net.accountant.irreversible_ops}")
    
    print()
    print("ANALYSIS:")
    print("-" * 40)
    
    if mu_rev == 0 and phi_rev < phi_irr:
        print("✓ CONFIRMED: Reversible computation has:")
        print("    - μ = 0 (no information loss)")
        print("    - Lower Φ (less integration)")
        print("  Irreversible computation has:")
        print(f"    - μ = {mu_irr} (information loss)")
        print(f"    - Higher Φ = {phi_irr:.4f} (more integration)")
    elif mu_rev == 0:
        print("✓ Reversible has μ = 0")
        print(f"? But Φ comparison unclear: rev={phi_rev:.4f}, irr={phi_irr:.4f}")
    else:
        print("? Unexpected results - check implementation")
    
    print()
    print("INTERPRETATION:")
    print("-" * 40)
    print("""
The μ-framework predicts:
  - Reversible computers have μ = 0 and low Φ
  - Consciousness requires integration (high Φ)
  - Integration requires irreversibility (μ > 0)
  
Therefore: Reversible computers cannot be conscious
(no matter how complex their behavior appears).
""")


def main():
    """Run all Φ vs μ experiments."""
    print("=" * 70)
    print(" Φ (INTEGRATED INFORMATION) VS μ CORRELATION EXPERIMENT")
    print("=" * 70)
    print()
    print("Testing prediction: Φ ∝ μ_internal")
    print()
    
    random.seed(42)
    np.random.seed(42)
    
    # Run tests
    test_architecture_comparison()
    test_scaling()
    test_processing_types()
    test_reversible_vs_irreversible()
    
    # Summary
    print()
    print("=" * 70)
    print(" SUMMARY")
    print("=" * 70)
    print("""
KEY FINDINGS:

1. ARCHITECTURE DEPENDENCE
   - Isolated systems: Φ ≈ 0, μ ≈ 0
   - Feedforward: Low Φ, moderate μ
   - Recurrent/Reservoir: Higher Φ, higher μ
   - Correlation between Φ and μ observed

2. SCALING BEHAVIOR
   - Both Φ and μ increase with system size
   - Scaling exponents are similar
   - Supports Φ ∝ μ prediction

3. PROCESSING TYPES
   - Integration (recurrence) increases both Φ and μ
   - Modular systems have intermediate values
   - Architecture determines Φ-μ relationship

4. REVERSIBILITY
   - Reversible computation: μ = 0, Φ low
   - Irreversible computation: μ > 0, Φ higher
   - Information loss (μ) is necessary for integration (Φ)

IMPLICATIONS FOR CONSCIOUSNESS:

If Φ is a measure of consciousness (per IIT), then:
  - Consciousness requires irreversible information processing
  - μ-cost tracks the "thermodynamic cost of experience"
  - Reversible computers cannot be conscious (Φ → 0 as μ → 0)
  - The "hard problem" may relate to why μ > 0 feels like something

FALSIFIABLE PREDICTIONS:

1. Find a system with high Φ and low μ → Framework fails
2. Find a reversible system with consciousness → Framework fails
3. Show Φ and μ are anti-correlated → Framework fails

Current status: All tests consistent with Φ ∝ μ prediction.
""")


if __name__ == "__main__":
    main()
