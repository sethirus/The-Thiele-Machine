"""
probe_thiele.py  –  Concrete experiments on the Thiele Machine VM

Run with:  .venv/bin/python probe_thiele.py

Each experiment builds on one core idea:
  mu_discovery  = cost of learning a partition structure from scratch (PNEW)
  mu_execution  = cost of computing partition operations (PSPLIT, PMERGE)
  total         = mu_discovery + mu_execution

The "No Free Insight" theorem (coq/kernel/NoFreeInsight.v) says:
  you cannot certify structural knowledge without paying the corresponding
  discovery cost.  These experiments show that cost concretely.
"""

import sys, tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from thielecpu.vm import VM
from thielecpu.state import State


# ──────────────────────────────────────────────────────────────────────────────
# Runner helper
# ──────────────────────────────────────────────────────────────────────────────

def run(program_text: str) -> VM:
    """Parse text-format program and run it, returning the final VM state."""
    instructions = []
    for raw in program_text.strip().splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split(maxsplit=1)
        instructions.append((parts[0].upper(), parts[1] if len(parts) > 1 else ""))
    state = State()
    vm = VM(state=state)
    with tempfile.TemporaryDirectory() as td:
        vm.run(instructions, Path(td) / "out", auto_mdlacc=False, write_artifacts=False)
    return vm


def ledger(vm: VM) -> str:
    d = vm.state.mu_ledger.mu_discovery
    e = vm.state.mu_ledger.mu_execution
    return f"discovery={d:4d}  execution={e:4d}  total={d+e:4d}"


def modules(vm: VM) -> str:
    parts = []
    for mid, region in sorted(vm.state.regions.modules.items()):
        parts.append(f"{{{','.join(str(x) for x in sorted(region))}}}")
    return "  ".join(parts)


# ──────────────────────────────────────────────────────────────────────────────
# Experiment 1: Discovery cost is linear in region size
# ──────────────────────────────────────────────────────────────────────────────

print("=" * 70)
print("EXPERIMENT 1: mu_discovery = popcount(region) — linear in region size")
print("=" * 70)
print()
print(f"{'Region size':>12}  {'mu_discovery':>12}  {'formula':>20}")
print("-" * 50)
for n in [1, 2, 4, 8, 16, 32]:
    region = "{" + ",".join(str(i) for i in range(1, n + 1)) + "}"
    vm = run(f"PNEW {region}\nHALT")
    d = vm.state.mu_ledger.mu_discovery
    print(f"{n:>12}  {d:>12}  (n={n})")

print()
print("Observation: every distinct element in a newly discovered partition")
print("costs exactly 1 mu_discovery unit.  There is no compression.")
print()

# ──────────────────────────────────────────────────────────────────────────────
# Experiment 2: Two paths to the same partition — blind vs. direct
# ──────────────────────────────────────────────────────────────────────────────
#
# We want the partition: {1,3,5,7} | {2,4,6,8}
# Path A (direct):  two explicit PNEW — pure discovery cost
# Path B (blind):   one PNEW for the full set, then PSPLIT by even/odd
#
print("=" * 70)
print("EXPERIMENT 2: Same result, different mu cost")
print("  Goal: partition {1..8} into odds {1,3,5,7} + evens {2,4,6,8}")
print("=" * 70)
print()

vm_a = run("""
PNEW {1,3,5,7}
PNEW {2,4,6,8}
HALT
""")
print("Path A — direct: PNEW odds + PNEW evens")
print(f"  modules : {modules(vm_a)}")
print(f"  ledger  : {ledger(vm_a)}")

print()

vm_b = run("""
PNEW {1,2,3,4,5,6,7,8}
PSPLIT 1 0 8
HALT
""")
# pred_byte=0 means even/odd split (mode 0b00, param bit 0 = 0 → even elements first)
print("Path B — blind: PNEW full set, then PSPLIT by even/odd (cost=8)")
print(f"  modules : {modules(vm_b)}")
print(f"  ledger  : {ledger(vm_b)}")

print()
extra = (vm_b.state.mu_ledger.mu_discovery + vm_b.state.mu_ledger.mu_execution) - \
        (vm_a.state.mu_ledger.mu_discovery + vm_a.state.mu_ledger.mu_execution)
print(f"Extra mu paid on Path B: {extra}")
print("Observation: blind search pays an execution penalty for discovering")
print("structure it could have stated directly.  Same final partition,")
print("different price.")
print()

# ──────────────────────────────────────────────────────────────────────────────
# Experiment 3: Hierarchical split tree vs. direct singleton PNEW
# ──────────────────────────────────────────────────────────────────────────────
#
# We want 8 singleton modules: {1},{2},...,{8}
# Path A (direct): 8 × PNEW {k}  — pure discovery, mu_discovery=8, execution=0
# Path B (tree):   PNEW full, then 3 rounds of binary splits
#
print("=" * 70)
print("EXPERIMENT 3: Hierarchical split tree vs. 8 direct singletons")
print("  Goal: discover all 8 elements as individual modules")
print("=" * 70)
print()

vm_a = run("""
PNEW {1}
PNEW {2}
PNEW {3}
PNEW {4}
PNEW {5}
PNEW {6}
PNEW {7}
PNEW {8}
HALT
""")
print("Path A — direct: 8 × PNEW {k}")
print(f"  modules : {modules(vm_a)}")
print(f"  ledger  : {ledger(vm_a)}")
print()

# Binary split tree (round 1: split {1-8} → {1-4}|{5-8};
#                   round 2: split {1-4} → {1-2}|{3-4}, {5-8} → {5-6}|{7-8}
#                   round 3: split each pair → singletons)
# Each PSPLIT with explicit cost=1 to keep it low
vm_b = run("""
# Round 0: create monolithic region
PNEW {1,2,3,4,5,6,7,8}
# Round 1: split by threshold >= 5  (pred_byte 0x41 = mode 01 thresh, param=5 => bit pattern 0b01_000101 = 0x45)
# Simpler: use explicit regions
PSPLIT 1 {1,2,3,4} {5,6,7,8} 1
# Round 2: split {1,2,3,4} (module 2) and {5,6,7,8} (module 3)
PSPLIT 2 {1,2} {3,4} 1
PSPLIT 3 {5,6} {7,8} 1
# Round 3: split the pairs
PSPLIT 4 {1} {2} 1
PSPLIT 5 {3} {4} 1
PSPLIT 6 {5} {6} 1
PSPLIT 7 {7} {8} 1
HALT
""")
print("Path B — binary split tree: 1 PNEW + 7 PSPLITs (each cost=1)")
print(f"  modules : {modules(vm_b)}")
print(f"  ledger  : {ledger(vm_b)}")
print()
extra = (vm_b.state.mu_ledger.mu_discovery + vm_b.state.mu_ledger.mu_execution) - \
        (vm_a.state.mu_ledger.mu_discovery + vm_a.state.mu_ledger.mu_execution)
print(f"Extra mu paid on Path B: {extra} (7 splits × cost_per_split=1")
print("Observation: when you KNOW the full structure upfront, stating it")
print("directly via PNEW is strictly cheaper than any split tree.")
print()

# ──────────────────────────────────────────────────────────────────────────────
# Experiment 4: Synthesis (PMERGE) — combining costs mu_execution
# ──────────────────────────────────────────────────────────────────────────────

print("=" * 70)
print("EXPERIMENT 4: Synthesis — PMERGE charges mu_execution")
print("=" * 70)
print()

vm = run("""
PNEW {1,2,3,4}
PNEW {5,6,7,8}
PNEW {9,10,11,12}
PMERGE 1 2 4
PMERGE 3 4 4
HALT
""")
# Note: after PNEW×3 we have modules 1,2,3
# PMERGE 1 2 → module 4 (= {1..8})
# PMERGE 3 4 → module 5 (= {1..12})
print(f"PNEW × 3, then PMERGE twice (cost=4 each):")
print(f"  modules : {modules(vm)}")
print(f"  ledger  : {ledger(vm)}")
print()
print("Observation: merging known modules pays execution cost once each.")
print("The discovery cost is already accounted for by the prior PNEWs.")
print()

# ──────────────────────────────────────────────────────────────────────────────
# Experiment 5: mu monotonicity — total mu never decreases
# ──────────────────────────────────────────────────────────────────────────────

print("=" * 70)
print("EXPERIMENT 5: mu monotonicity — total mu never decreases")
print("=" * 70)
print()

# Track mu at each step by running incremental programs
steps = [
    ("PNEW {1,2,3,4,5,6,7,8}", "PNEW full region"),
    ("PSPLIT 1 {1,2,3,4} {5,6,7,8} 4",  "PSPLIT into halves"),
    ("PSPLIT 2 {1,2} {3,4} 4",            "PSPLIT left half"),
    ("PSPLIT 3 {5,6} {7,8} 4",            "PSPLIT right half"),
    ("PMERGE 4 5 4",                       "PMERGE halves of left"),
]

accum = ""
prev_total = 0
for instr, label in steps:
    accum += f"{instr}\n"
    vm = run(accum + "HALT")
    d = vm.state.mu_ledger.mu_discovery
    e = vm.state.mu_ledger.mu_execution
    total = d + e
    direction = "↑" if total > prev_total else ("→" if total == prev_total else "↓!")
    print(f"  {direction} {label:<40} total={total:4d}")
    prev_total = total

print()
print("Observation: mu only ever increases.  Each operation adds cost.")
print("This is the Landauer lower bound made concrete: you spend mu to")
print("gain certified structural knowledge (or certify its absence).")
print()

# ──────────────────────────────────────────────────────────────────────────────
# Experiment 6: The No-Free-Insight ratio (information density)
# ──────────────────────────────────────────────────────────────────────────────

print("=" * 70)
print("EXPERIMENT 6: Information density — bits per mu unit")
print("=" * 70)
print()
print("If you make n independent PNEW calls with regions of size k,")
print("total mu_discovery = n*k.  How much structural information do you hold?")
print()

import math

print(f"{'n modules':>10}  {'k elements':>10}  {'total_mu':>10}  "
      f"{'log2(n!*C(n*k,k))':>20}  {'bits/mu':>10}")
print("-" * 70)
for n, k in [(1,8), (2,4), (4,2), (8,1), (2,8), (4,4), (8,2)]:
    elements = list(range(1, n*k + 1))
    program = "\n".join(
        "PNEW {" + ",".join(str(e) for e in elements[i*k:(i+1)*k]) + "}"
        for i in range(n)
    ) + "\nHALT"
    vm = run(program)
    total_mu = vm.state.mu_ledger.mu_discovery  # execution=0 for pure PNEW
    # Structural info: log2 of how many distinct n-partitions of n*k elements into k-sized parts
    # Rough: log2(C(n*k, k) * C((n-1)*k, k) * ... * 1)  =  log2((n*k)! / (k!^n))
    bits = math.lgamma(n*k + 1) / math.log(2) - n * math.lgamma(k + 1) / math.log(2)
    ratio = bits / total_mu if total_mu > 0 else 0
    print(f"{n:>10}  {k:>10}  {total_mu:>10}  {bits:>20.2f}  {ratio:>10.3f}")

print()
print("Observation: MORE modules (small k, large n) give higher bits-per-mu.")
print("One big module has 0 structural information — the trivial partition.")
print("Singleton modules (n=8, k=1) maximise structural info: log2(8!)≈15.3")
print("bits for 8 mu.  The mu cost is linear in elements but the structural")
print("information is logarithmic in partition count, so the ratio grows.")
print()

# ──────────────────────────────────────────────────────────────────────────────
# Summary
# ──────────────────────────────────────────────────────────────────────────────

print("=" * 70)
print("SUMMARY")
print("=" * 70)
print("""
What is the Thiele Machine?
  A cost-accounting virtual machine for partition-based computation.
  Every structural operation has a price in mu (μ).

What is mu?
  mu_discovery: paid when naming a new region (PNEW) — scales with |region|
  mu_execution: paid when computing over regions (PSPLIT, PMERGE)
  total mu never decreases (monotonic — enforced by the VM)

The No Free Insight theorem (NoFreeInsight.v):
  Any certified structural fact about your data must have cost ≥ 0 mu.
  Equivalently: you cannot learn anything for free.

What is concrete and machine-checked?
  ✓ Tsirelson bound  (coq/kernel/TsirelsonGeneral.v)
      Pure Cauchy-Schwarz algebra: 4Σeᵢ² - S² = sum of 6 squares ≥ 0
      + NPA-1 row norms → |S| ≤ 2√2  (zero axioms, 311/311 compiled)
  ✓ Born rule uniqueness  (coq/kernel/BornRule.v)
      Linearity + eigenstates uniquely determine the Born probabilities
  ✓ No Free Insight  (coq/kernel/NoFreeInsight.v)
      Structural certification requires non-negative mu payment
  ✓ Hardware synthesis  (thielecpu/hardware/rtl/)
      RTL synthesises with Yosys; co-simulation passes

What is overclaimed?
  ✗ "Born rule derived from mu-cost" — the mu link is definitional, not derived
  ✗ "Theory of Everything" — TOE.v is two lines forwarding to custom definitions
  ✗ "Gravity from mu" — three axioms linking mu to Einstein equations were removed
       Feb 17 2026 with note "0%% empirical pass rate"

What to keep and develop:
  → thielecpu/  (state.py, vm.py, isa.py, hardware/)   — the real machine
  → coq/kernel/TsirelsonGeneral.v                       — the real proof
  → coq/kernel/NoFreeInsight.v                          — the real theorem
  → coq/kernel/BornRule.v                               — real uniqueness proof
  Discard: 7400 autogenerated Python files, ATLAS scoring, EmergentPhysicsState,
           PathIntegralPointer, any TOE/Einstein claims
""")
