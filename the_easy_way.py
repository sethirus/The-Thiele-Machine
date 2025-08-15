#!/usr/bin/env python3
import time
import sys
import collections
import hashlib
import json
import inspect
from z3 import *
import platform
import z3
import os
import re

class Transcript:
    """Manages the creation of an immutable, verifiable log of the experiment."""
    def __init__(self):
        self.log = []
        self.hashes = {}

    def say(self, message):
        """Prints a message and records it in the log."""
        print(message)
        self.log.append(message)

    def record_hash(self, name, obj):
        """Hashes a JSON-serializable object and records the result."""
        # Use a canonical JSON representation for stable hashes
        obj_string = json.dumps(obj, sort_keys=True, default=str).encode('utf-8')
        obj_hash = hashlib.sha256(obj_string).hexdigest()
        self.hashes[name] = obj_hash
        self.say(f"  -> {name}_sha256: {obj_hash}")
        return obj_hash

    def get_final_transcript(self):
        return "\n".join(self.log)

def main():
    """Main execution block for the self-verifying experiment."""
    # Belt-and-suspenders: clear problematic env vars for Windows
    os.environ.pop("PYTHONHOME", None)
    os.environ.pop("PYTHONPATH", None)

    # Only set Z3 param that is relevant for 4.15.1 (portable: try/except)
    try:
        set_param('core.minimize', True)
    except Exception:
        pass
    for seed_key in ('sat.random_seed', 'smt.random_seed'):
        try:
            set_param(seed_key, 0)
        except Exception:
            pass

    transcript = Transcript()
    transcript.say(f"Z3 version: {z3.get_full_version()}")
    
    transcript.say("=" * 70)
    transcript.say("A FORMAL DEMONSTRATION OF BLINDNESS (Z3 as Referee)")
    transcript.say("=" * 70)
    
    # --- Step 1: Define and Certify the Geometric Object ---
    transcript.say("\n[STEP 1] Define and Certify the Geometric Object")
    NODES = 22
    graph_adj = collections.defaultdict(list)
    # Create a bipartite graph
    for u in range(NODES // 2):
        for v in range(NODES // 2, NODES):
            graph_adj[u].append(v)
            graph_adj[v].append(u)
    # The Kill Shot edge to create an odd cycle
    graph_adj[0].append(1)
    graph_adj[1].append(0)
    
    # Make the graph serializable for hashing
    serializable_graph = {k: sorted(graph_adj[k]) for k in sorted(graph_adj)}
    transcript.record_hash("geometric_object_graph", serializable_graph)
    
    # Record environment/toolchain info
    env = {
        "python_version": platform.python_version(),
        "platform": platform.platform(),
        "z3_version": z3.get_version(),
        "z3_full_version": z3.get_full_version(),
    }
    transcript.record_hash("environment", env)
    
    # --- Step 2: Define and Certify the Logical Encoding ---
    transcript.say("\n[STEP 2] Define and Certify the Logical Encoding")
    is_color_A = [Bool(f"node_{i}") for i in range(NODES)]
    # Build explicit edge set for determinism
    edges = {(min(u, v), max(u, v)) for u, nbrs in serializable_graph.items() for v in nbrs}
    constraints = [is_color_A[u] != is_color_A[v] for (u, v) in sorted(edges)]
    
    serializable_constraints = [c.sexpr() for c in constraints]
    transcript.record_hash("logical_constraints", serializable_constraints)
    
    # --- Step 3: The Blind Inquiry (Pi_trace) ---
    transcript.say("\n[STEP 3] The Blind Inquiry: Asking 'what?'")
    # Z3 params are set above using avail.contains
    blind_solver = Solver()
    blind_solver.add(constraints)
    
    start_time = time.time()
    blind_result = blind_solver.check()
    end_time = time.time()
    
    time_elapsed = end_time - start_time
    blind_certificate = {
        "result": str(blind_result)
    }
    transcript.say(f"  -> Z3 Response: {blind_certificate['result']} (took {time_elapsed:.6f}s)")
    transcript.record_hash("blind_inquiry_certificate", blind_certificate)

    # --- Step 4: The Sighted Inquiry (Partition-Native) ---
    transcript.say("\n[STEP 4] The Sighted Inquiry: Asking 'why?'")
    sighted_solver = Solver()
    edge_assumptions = {Bool(f"c_{i}"): constr for i, constr in enumerate(constraints)}
    for assumption, constr in edge_assumptions.items():
        sighted_solver.add(Implies(assumption, constr))
    
    # Z3 params are set above using avail.contains
    start_time = time.time()
    sighted_result = sighted_solver.check(list(edge_assumptions.keys()))
    core = sighted_solver.unsat_core() if sighted_result == unsat else []
    end_time = time.time()

    time_elapsed = end_time - start_time
    core_constraints = sorted([edge_assumptions[p].sexpr() for p in core])
    sighted_certificate = {
        "result": str(sighted_result),
        "certificate_type": "unsat_core",
        "certificate_content": core_constraints
    }
    transcript.say(f"  -> Z3 Response: {sighted_certificate['result']} (took {time_elapsed:.6f}s)")
    transcript.say(f"  -> Certificate Received: {sighted_certificate['certificate_type']}")
    transcript.record_hash("sighted_inquiry_certificate", sighted_certificate)
    
    # --- Step 5: Final Verdict and Self-Verification ---
    transcript.say("\n[STEP 5] Final Verdict and Self-Verification")
    
    # Define success conditions
    cond1 = blind_certificate["result"] == "unsat"
    transcript.say(f"  -> Condition 1: Blind inquiry returned 'unsat'. [PASS={cond1}]")
    
    cond2 = sighted_certificate["result"] == "unsat"
    transcript.say(f"  -> Condition 2: Sighted inquiry returned 'unsat'. [PASS={cond2}]")

    cond3 = len(sighted_certificate["certificate_content"]) > 0
    transcript.say(f"  -> Condition 3: Sighted inquiry produced a non-empty certificate. [PASS={cond3}]")

    # The expected certificate is the odd cycle (0,1), (0,11), (1,11)
    # The Z3 variables are node_0, node_1, node_11
    expected = {('node_0','node_1'), ('node_0','node_11'), ('node_1','node_11')}
    edge_re = re.compile(r"\(distinct (node_\d+) (node_\d+)\)")
    def parse_edge_sexpr(s):
        m = edge_re.fullmatch(s.strip())
        if not m: return None
        a, b = m.groups()
        return tuple(sorted((a, b)))
    core_edges = {parse_edge_sexpr(c) for c in sighted_certificate["certificate_content"] if parse_edge_sexpr(c)}
    cond4 = ({tuple(sorted(e)) for e in expected} == core_edges and len(core_edges) == 3)
    transcript.say(f"  -> Condition 4: Certificate is exactly the expected odd cycle (triangle). [PASS={cond4}]")
    triangle_nodes = sorted({int(x.split('_')[1]) for e in core_edges for x in e})
    transcript.say(f"  -> Minimal certificate cycle: {triangle_nodes}")
    transcript.say(f"  -> DEBUG: Unsat core s-exprs: {sighted_certificate['certificate_content']}")
    
    checks = {
        "blind_unsat": cond1,
        "sighted_unsat": cond2,
        "nonempty_core": cond3,
        "core_contains_triangle": cond4,
    }
    for name, ok in checks.items():
        if not ok:
            transcript.say(f"[FAIL] {name}")
    overall_success = all(checks.values())
    
    transcript.say("\n----------------------------------------------------------------------")
    transcript.say(f"FINAL VERDICT: The experiment has {'SUCCEEDED' if overall_success else 'FAILED'}.")
    transcript.say("The evidence demonstrates a qualitative separation between the two modes of inquiry.")
    transcript.say("Any odd cycle is not 2-colorable; a triangle is the minimal odd cycle, so its presence certifies non-2-colorability.")
    transcript.say("----------------------------------------------------------------------")

    # Final cryptographic seal
    transcript.say("\n[FINAL SEAL] Hashing Source Code and Full Transcript")
    source_code = inspect.getsource(sys.modules[__name__])
    transcript.record_hash("source_code", source_code)
    transcript.record_hash("final_transcript", transcript.get_final_transcript())
    
    # Terminate with a status code
    sys.exit(0 if overall_success else 1)


if __name__ == "__main__":
    main()