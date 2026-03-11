#!/usr/bin/env python3
"""
Factoring via PDISCOVER

The hypothesis: PDISCOVER can perceive partition structure that
SAT solvers cannot. For N = pq, the natural partition is p vs q.

Can we encode N such that PDISCOVER reveals its factors?

Key insight from the Thiele Machine:
- PDISCOVER analyzes INTERACTION GRAPHS
- It looks for natural community structure (Louvain, spectral)
- If factors create visible communities, PDISCOVER finds them

This experiment tries to build an interaction graph from N
where the two factors appear as distinct communities.
"""

import sys
import math
import random
import time
from typing import Dict, List, Tuple, Set, Optional
import numpy as np

sys.path.insert(0, '/workspaces/The-Thiele-Machine')

from thielecpu.vm import compute_geometric_signature, classify_geometric_signature

try:
    import networkx as nx
    HAS_NETWORKX = True
except ImportError:
    HAS_NETWORKX = False
    print("Warning: networkx not available")


def build_multiplication_graph(n: int, sample_size: int = 200) -> str:
    """
    Build an interaction graph from multiplication structure.
    
    The idea: If N = pq, then the multiplication table mod N
    has a specific structure. Elements that are "close" in
    Z_p behave differently than elements "close" in Z_q.
    
    We encode this as SMT axioms for PDISCOVER to analyze.
    """
    # Sample random elements coprime to N
    nodes = []
    for _ in range(sample_size * 5):
        x = random.randint(2, n - 1)
        if math.gcd(x, n) == 1:
            nodes.append(x)
        if len(nodes) >= sample_size:
            break
    
    if len(nodes) < 10:
        return ""
    
    # Build axioms encoding multiplicative relationships
    axioms = []
    axioms.append("(set-logic QF_NIA)")
    
    # Declare variables for each node
    for i, x in enumerate(nodes):
        axioms.append(f"(declare-const x{i} Int)")
        axioms.append(f"(assert (= x{i} {x}))")
    
    # Add constraints about products
    # Key insight: a*b mod N encodes information about factors
    for i in range(min(len(nodes), 50)):
        for j in range(i + 1, min(len(nodes), 50)):
            prod = (nodes[i] * nodes[j]) % n
            axioms.append(f"(assert (= (mod (* x{i} x{j}) {n}) {prod}))")
    
    axioms.append("(check-sat)")
    return "\n".join(axioms)


def build_residue_graph_smtlib(n: int, sample_size: int = 100) -> str:
    """
    Build SMT-LIB encoding of residue structure.
    
    For N = pq, elements share common residues mod p or mod q.
    This creates implicit clustering that PDISCOVER might detect.
    """
    axioms = []
    axioms.append("(set-logic QF_NIA)")
    
    # Sample elements
    nodes = list(range(2, min(n, sample_size + 2)))
    
    # Encode as variables
    for i, x in enumerate(nodes):
        axioms.append(f"(declare-const r{i} Int)")
        res = x % n if n > x else x
        axioms.append(f"(assert (= r{i} {res}))")
    
    # Add GCD relationships - these encode factor structure!
    for i in range(len(nodes)):
        for j in range(i + 1, min(len(nodes), i + 20)):
            g = math.gcd(nodes[i] - nodes[j], n)
            if g > 1:
                axioms.append(f"; GCD({nodes[i]}, {nodes[j]}) mod N structure")
                axioms.append(f"(assert (> (mod (- r{i} r{j}) {g}) 0))")
    
    axioms.append("(check-sat)")
    return "\n".join(axioms)


def build_quadratic_residue_graph(n: int) -> str:
    """
    Build graph from quadratic residue structure.
    
    Key insight: For N = pq, the quadratic residues mod N
    form a group of size φ(N)/4. The structure of QRs
    reveals information about factors.
    
    Specifically: x is QR mod N iff x is QR mod p AND mod q.
    This creates a natural 2x2 structure.
    """
    sqrt_n = int(math.sqrt(n)) + 1
    
    # Find quadratic residues
    qr = set()
    for x in range(1, min(sqrt_n, 500)):
        r = (x * x) % n
        qr.add(r)
    
    axioms = []
    axioms.append("(set-logic QF_BV)")
    axioms.append("(declare-const qr_count (_ BitVec 32))")
    axioms.append(f"(assert (= qr_count #x{len(qr):08x}))")
    
    # Encode QR structure
    for i, r in enumerate(list(qr)[:50]):
        axioms.append(f"(declare-const qr{i} (_ BitVec 32))")
        axioms.append(f"(assert (= qr{i} #x{r:08x}))")
    
    axioms.append("(check-sat)")
    return "\n".join(axioms)


def build_order_graph(n: int, base: int = 2) -> str:
    """
    Build graph from multiplicative order structure.
    
    For N = pq, the order of a mod N divides lcm(p-1, q-1).
    The order structure reveals the factorization.
    """
    # Compute powers of base mod N
    powers = []
    x = 1
    for k in range(min(n, 1000)):
        powers.append((k, x))
        x = (x * base) % n
        if x == 1:
            break
    
    if len(powers) < 2:
        return ""
    
    axioms = []
    axioms.append("(set-logic QF_NIA)")
    
    for k, power in powers:
        axioms.append(f"(declare-const p{k} Int)")
        axioms.append(f"(assert (= p{k} {power}))")
    
    # Add order constraint if found
    order = len(powers)
    if powers[-1][1] == 1:
        axioms.append(f"; Order of {base} mod {n} is {order}")
        axioms.append(f"(declare-const order Int)")
        axioms.append(f"(assert (= order {order}))")
    
    axioms.append("(check-sat)")
    return "\n".join(axioms)


def factor_via_pdiscover(n: int) -> Dict:
    """
    Attempt to factor N using PDISCOVER.
    
    Strategy:
    1. Build multiple encodings of N's structure
    2. Run PDISCOVER on each
    3. Look for STRUCTURED verdict - indicates factors visible
    4. Extract factors from partition
    """
    start = time.time()
    
    results = {
        "n": n,
        "success": False,
        "factors": None,
        "elapsed": 0,
        "encodings_tried": []
    }
    
    encodings = [
        ("multiplication", build_multiplication_graph),
        ("residue", build_residue_graph_smtlib),
        ("quadratic_residue", build_quadratic_residue_graph),
        ("order", lambda n: build_order_graph(n, 2)),
    ]
    
    for name, builder in encodings:
        try:
            axioms = builder(n)
            if not axioms:
                results["encodings_tried"].append({
                    "name": name,
                    "status": "empty"
                })
                continue
            
            # Run PDISCOVER's geometric signature analysis
            signature = compute_geometric_signature(axioms, seed=42)
            verdict = classify_geometric_signature(signature)
            
            encoding_result = {
                "name": name,
                "verdict": verdict,
                "signature": signature
            }
            results["encodings_tried"].append(encoding_result)
            
            # If STRUCTURED, the encoding reveals something!
            if verdict == "STRUCTURED":
                print(f"  [PDISCOVER] {name}: STRUCTURED - potential factor structure detected")
                print(f"    avg_edge_weight: {signature['average_edge_weight']:.3f}")
                print(f"    edge_weight_stddev: {signature['edge_weight_stddev']:.3f}")
                
                # Try to extract factors...
                # The partition structure should relate to p vs q
                
        except Exception as e:
            results["encodings_tried"].append({
                "name": name,
                "status": f"error: {e}"
            })
    
    results["elapsed"] = time.time() - start
    return results


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(math.sqrt(n)) + 1, 2):
        if n % i == 0:
            return False
    return True


def generate_semiprime(bits: int) -> tuple:
    while True:
        p = random.getrandbits(bits // 2) | 1
        if is_prime(p) and p > 3:
            break
    while True:
        q = random.getrandbits(bits // 2) | 1
        if is_prime(q) and q > 3 and q != p:
            break
    return p * q, min(p, q), max(p, q)


def run_experiment():
    """Test PDISCOVER-based factoring."""
    random.seed(42)
    
    print("=" * 70)
    print("FACTORING VIA PDISCOVER")
    print("=" * 70)
    print("\nCan PDISCOVER perceive factor structure in number encodings?")
    print()
    
    for bits in [20, 24, 28]:
        print(f"\n{'='*70}")
        print(f"Testing {bits}-bit semiprimes")
        print(f"{'='*70}")
        
        for trial in range(3):
            n, p, q = generate_semiprime(bits)
            print(f"\nTrial {trial+1}: N = {n} = {p} × {q}")
            print("-" * 50)
            
            result = factor_via_pdiscover(n)
            
            print(f"\nPDISCOVER results:")
            for enc in result["encodings_tried"]:
                name = enc.get("name", "?")
                if "verdict" in enc:
                    verdict = enc["verdict"]
                    sig = enc.get("signature", {})
                    avg = sig.get("average_edge_weight", 0)
                    std = sig.get("edge_weight_stddev", 0)
                    print(f"  {name:20s}: {verdict:10s} (avg={avg:.2f}, std={std:.2f})")
                else:
                    print(f"  {name:20s}: {enc.get('status', 'unknown')}")


# Bonus: Try to find factors from STRUCTURED encoding
def extract_factors_from_structure(n: int, axioms: str) -> Optional[Tuple[int, int]]:
    """
    If PDISCOVER says STRUCTURED, try to extract the factors.
    
    This is the key missing piece: HOW do we get from
    "this has structure" to "here are the factors"?
    """
    # Build the clause graph that PDISCOVER uses internally
    # Then look at the actual partition
    
    # For now, this is a placeholder - the key research question
    # is: what does STRUCTURED mean for a number encoding?
    
    return None


if __name__ == "__main__":
    run_experiment()
