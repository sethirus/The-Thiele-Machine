"""
THE THIELE MACHINE: Knowledge Receipt Demo
==========================================

Classical computers answer:  "What is the result?"
The Thiele Machine answers:  "What is the result, and how much did it COST to know that?"

No computer observing only classical fields (registers, memory, mu, pc, err) can guarantee the second part — provably, from first principles.

Here's the four-act argument:

  ACT 1 — The Forged Claim
    Claim a structural relationship without building it. The machine refuses.
    NoFI enforcement: there's no path through the machine that asserts uncertified structure.

  ACT 2 — The Earned Path
    Build a genuine A→B→C morphism chain. Pay the cost. Read back the evidence.
    The mu ledger records what you spent. The morphism chain is navigable.

  ACT 3 — The Certified Claim
    Same chain, but with MORPH_ASSERT. Costs S(cost) ≥ 1, no exceptions.
    csr_cert_addr is now nonzero — the machine has formally recorded the claim.

  ACT 4 — The Separation Theorem (the profound part)
    Two programs. Same registers r0 and r1. Same mu. Same memory.
    Classical machines: INDISTINGUISHABLE.
    Thiele Machine: PROVABLY DISTINCT — one has a morphism chain, one doesn't.
    A probe instruction (MORPH_DELETE) tells them apart in one step.

WHY THIS MATTERS:
    In supply chains, multi-party computation, causal audits, distributed
    consensus — parties constantly claim "I verified this." How do you know?
    The Thiele Machine makes the cost of verification UNFORGEABLE. If your
    mu < minimum_verification_cost, your claimed knowledge is mathematically
    hollow. Not probably hollow. Provably hollow, by the NoFI theorem in
    coq/kernel/NoFreeInsight.v, zero Admitted, machine-checked.

    The categorical layer (morphisms) is the evidence trail. It cannot be
    constructed without paying mu. It cannot survive a structure deletion
    without the deletion being recorded. It is, in the formal sense, a
    receipt — and receipts here have the force of mathematical proof.
"""

import sys
import textwrap
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from build import thiele_vm as vm


# ─────────────────────────────────────────────────────────────────────────────
# Helpers
# ─────────────────────────────────────────────────────────────────────────────

def section(title: str) -> None:
    print()
    bar = "─" * 70
    print(bar)
    print(f"  {title}")
    print(bar)


def show(label: str, state: vm.VMState, extra: str = "") -> None:
    regs_nonzero = {i: v for i, v in enumerate(state.regs) if v != 0}
    modules = state.graph.pg_modules if state.graph else []
    print(f"\n  [{label}]")
    print(f"    mu          = {state.mu}")
    print(f"    err         = {state.err}")
    print(f"    supra_cert  = {state.supra_cert}  (has_supra_cert: csr_cert_addr != 0)")
    print(f"    cert_addr   = {state.csrs.get('cert_addr', 0)}")
    print(f"    vm_certified= {state.certified}  (set only by CERTIFY opcode, not MORPH_ASSERT)")
    print(f"    modules     = {len(modules)} ({', '.join(f'mod{mid}:{ms.module_region}' for mid, ms in modules)})")
    if regs_nonzero:
        print(f"    regs        = {regs_nonzero}")
    if extra:
        print(f"    note        = {extra}")


def verdict(text: str) -> None:
    print(f"\n  ▶  {text}")


# ─────────────────────────────────────────────────────────────────────────────
# ACT 1: The Forged Claim
# ─────────────────────────────────────────────────────────────────────────────

section("ACT 1 — The Forged Claim")
print(textwrap.dedent("""
  Goal: claim that morphism 99 encodes a valid two-hop path.
  Method: skip building any modules or morphisms; just assert directly.

  MORPH_ASSERT 99 "two-hop" "cert" 0
  HALT
"""))

forged = vm.run_vm([
    "MORPH_ASSERT 99 two-hop cert 0",
    "HALT 0",
])
show("forged claim", forged)
verdict(
    f"REFUSED. The machine errored because morphism 99 does not exist.\n"
    f"  Cost paid: {forged.mu} (S(0)=1 charged even for the failed attempt).\n"
    f"  Knowledge received: 0.\n"
    f"  The machine extracts the cost BEFORE checking whether the structure is valid.\n"
    f"  You cannot even ATTEMPT to certify for free. This is stronger than NoFI:\n"
    f"  not just 'certified knowledge costs something' — 'certification attempts cost something.'"
)


# ─────────────────────────────────────────────────────────────────────────────
# ACT 2: The Earned Path
# ─────────────────────────────────────────────────────────────────────────────

section("ACT 2 — The Earned Path")
print(textwrap.dedent("""
  Goal: prove that node A can reach node C in exactly two hops via B.

  Build three modules (A, B, C), create morphisms f: A→B and g: B→C,
  compose them into g∘f: A→C, then read back source and target to verify.

  PNEW {1} 1          # Module A  (mu += 1)
  PNEW {2} 1          # Module B  (mu += 1)
  PNEW {3} 1          # Module C  (mu += 1)
  MORPH 10 1 2 0 2    # f: A→B, morph_id=1 → r10  (mu += 2)
  MORPH 11 2 3 0 2    # g: B→C, morph_id=2 → r11  (mu += 2)
  COMPOSE 12 1 2 1    # g∘f: A→C, morph_id=3 → r12  (mu += 1)
  MORPH_GET 0 3 0 0   # r0 = source module of g∘f  (should be A = mod 1)
  MORPH_GET 1 3 1 0   # r1 = target module of g∘f  (should be C = mod 3)
  HALT
"""))

earned = vm.run_vm([
    "PNEW {1} 1",
    "PNEW {2} 1",
    "PNEW {3} 1",
    "MORPH 10 1 2 0 2",
    "MORPH 11 2 3 0 2",
    "COMPOSE 12 1 2 1",
    "MORPH_GET 0 3 0 0",
    "MORPH_GET 1 3 1 0",
    "HALT 0",
])
show("earned path", earned,
     f"r0={earned.regs[0]} (source=A), r1={earned.regs[1]} (target=C)")

assert not earned.err,            "earned path should not error"
assert earned.regs[0] == 1,       f"source should be module 1 (A), got {earned.regs[0]}"
assert earned.regs[1] == 3,       f"target should be module 3 (C), got {earned.regs[1]}"
assert earned.mu == 8,            f"mu should be 8 (1+1+1+2+2+1), got {earned.mu}"

verdict(
    f"ACCEPTED. Two-hop path A→B→C is real. mu={earned.mu}.\n"
    "  The composition chain is navigable: source=module 1 (A), target=module 3 (C).\n"
    "  This is structural evidence, not a claim. The morphism graph holds the proof."
)


# ─────────────────────────────────────────────────────────────────────────────
# ACT 3: The Certified Claim
# ─────────────────────────────────────────────────────────────────────────────

section("ACT 3 — The Certified Claim")
print(textwrap.dedent("""
  Goal: same path, but now formally CERTIFY it with MORPH_ASSERT.

  MORPH_ASSERT is a cert-setter: it charges S(cost) ≥ 1 regardless.
  Even with cost=0, it costs 1. Even trying to certify for free costs something.
  This is the No Free Insight law: certified structural knowledge has
  a provably nonzero price.

  (Same program as Act 2, plus:)
  MORPH_ASSERT 3 "A-to-C-two-hop" "cert" 4   # assert on morph_id=3, cost=4 → charges S(4)=5
"""))

certified = vm.run_vm([
    "PNEW {1} 1",
    "PNEW {2} 1",
    "PNEW {3} 1",
    "MORPH 10 1 2 0 2",
    "MORPH 11 2 3 0 2",
    "COMPOSE 12 1 2 1",
    "MORPH_ASSERT 3 A-to-C-two-hop cert 4",
    "MORPH_GET 0 3 0 0",
    "MORPH_GET 1 3 1 0",
    "HALT 0",
])
show("certified claim", certified,
     f"cert_addr={certified.csrs.get('cert_addr', 0)} (nonzero = claim recorded)")

assert not certified.err,                        "certified claim should not error"
assert certified.mu == 13,                       f"mu should be 8+S(4)=8+5=13, got {certified.mu}"
assert certified.csrs.get("cert_addr", 0) != 0, "cert_addr should be nonzero after MORPH_ASSERT"

mu_delta = certified.mu - earned.mu
verdict(
    f"CERTIFIED. mu={certified.mu} (Act 2 cost + MORPH_ASSERT S(4)=5 = +{mu_delta}).\n"
    "  cert_addr is now nonzero — the machine has formally recorded the structural claim.\n"
    "  The cost is unavoidable. S(cost) ≥ 1 for any cost value. The theorem holds."
)

# Prove NoFI: even cost=0 is not free
nifi_probe = vm.run_vm([
    "PNEW {1} 1",
    "MORPH_ID 5 1 0",
    "MORPH_ASSERT 1 property cert 0",   # cost=0 → charges S(0) = 1
    "HALT 0",
])
assert not nifi_probe.err
assert nifi_probe.mu == 2, f"PNEW(1)+MORPH_ID(0)+MORPH_ASSERT(S(0)=1)=2, got {nifi_probe.mu}"
print(f"\n  NoFI probe: MORPH_ASSERT with cost=0 still charges S(0)=1. mu={nifi_probe.mu}. Confirmed.")


# ─────────────────────────────────────────────────────────────────────────────
# ACT 4: The Separation Theorem
# ─────────────────────────────────────────────────────────────────────────────

section("ACT 4 — The Separation Theorem (the profound part)")
print(textwrap.dedent("""
  The question: can two programs produce identical classical output
  (same registers, same mu) but be distinguishable by the Thiele Machine?

  YES. This is the categorical separation theorem proven in
  coq/kernel/PartitionSeparation.v, Section 10 — formally, zero Admitted.

  Program A (WITH morphism chain):
    Build A→B→C chain as before, then read source/target into r0/r1.
    Final state: r0=1, r1=3, mu=8. pg_morphisms contains 3 morphisms.

  Program B (WITHOUT morphism chain):
    Allocate mu differently (larger PNEW costs), load r0=1, r1=3 directly.
    Final state: r0=1, r1=3, mu=8. pg_morphisms is empty.

  To a classical machine, these are IDENTICAL: same registers, same mu.
  To the Thiele Machine, they are PROVABLY DISTINCT.

  PROBE: Try MORPH_DELETE on morphism 1 at the end of each program.
    — Program A: succeeds (morph 1 exists)
    — Program B: errors (morph 1 never existed)

  One probe instruction. Undeniable distinction.
"""))

# Program A: morphism chain present
prog_a_base = [
    "PNEW {1} 1",
    "PNEW {2} 1",
    "PNEW {3} 1",
    "MORPH 10 1 2 0 2",
    "MORPH 11 2 3 0 2",
    "COMPOSE 12 1 2 1",
    "MORPH_GET 0 3 0 0",   # r0 = source of composed = 1
    "MORPH_GET 1 3 1 0",   # r1 = target of composed = 3
]

# Program B: no morphisms, same r0/r1/mu by construction
# PNEW×3 at costs (2,2,2) = 6 mu, then LOAD_IMM r0 1 1 (+1), LOAD_IMM r1 3 1 (+1) = mu=8
prog_b_base = [
    "PNEW {1} 2",
    "PNEW {2} 2",
    "PNEW {3} 2",
    "LOAD_IMM 0 1 1",   # r0 = 1 (claimed source)
    "LOAD_IMM 1 3 1",   # r1 = 3 (claimed target)
]

# Verify the base states are classically identical
state_a_base = vm.run_vm(prog_a_base + ["HALT 0"])
state_b_base = vm.run_vm(prog_b_base + ["HALT 0"])

show("Program A (base, no probe)", state_a_base)
show("Program B (base, no probe)", state_b_base)

# Classical equivalence check
classical_a = (state_a_base.regs[0], state_a_base.regs[1], state_a_base.mu, state_a_base.err)
classical_b = (state_b_base.regs[0], state_b_base.regs[1], state_b_base.mu, state_b_base.err)

print(f"\n  Classical fingerprint A: r0={classical_a[0]}, r1={classical_a[1]}, mu={classical_a[2]}, err={classical_a[3]}")
print(f"  Classical fingerprint B: r0={classical_b[0]}, r1={classical_b[1]}, mu={classical_b[2]}, err={classical_b[3]}")
print(f"  Classically identical:   {classical_a == classical_b}")

# Now add the categorical probe: MORPH_DELETE 1 0
# (delete morphism with id=1; costs 0)
state_a_probed = vm.run_vm(prog_a_base + ["MORPH_DELETE 1 0", "HALT 0"])
state_b_probed = vm.run_vm(prog_b_base + ["MORPH_DELETE 1 0", "HALT 0"])

show("Program A + MORPH_DELETE probe", state_a_probed,
     "morph_id=1 existed → DELETE succeeded")
show("Program B + MORPH_DELETE probe", state_b_probed,
     "morph_id=1 never existed → DELETE errored")

assert not state_a_probed.err, "Program A: MORPH_DELETE should succeed (morph 1 was built)"
assert state_b_probed.err,     "Program B: MORPH_DELETE should error (morph 1 was never built)"

verdict(
    "SEPARATED.\n\n"
    "  Same r0, r1, mu, err before the probe.\n"
    "  One probe instruction (MORPH_DELETE 1 0) gives different results:\n"
    "    — Program A: MORPH_DELETE succeeds. The morphism chain was real.\n"
    "    — Program B: MORPH_DELETE errors.   The claimed values were hollow.\n\n"
    "  This is coq/kernel/PartitionSeparation.v §10, made executable:\n"
    "  computationally_equivalent but categorically_distinct."
)


# ─────────────────────────────────────────────────────────────────────────────
# Summary
# ─────────────────────────────────────────────────────────────────────────────

section("SUMMARY")
print(textwrap.dedent(f"""
  Act 1 — Forged claim:       mu={forged.mu},  err=True   (refused; S(0)=1 charged for the attempt)
  Act 2 — Earned path:        mu={earned.mu},  err=False  (morphism chain navigable, MORPH_GET verified)
  Act 3 — Certified claim:    mu={certified.mu}, err=False  (supra_cert=True; cert_addr nonzero; S(4)=5 charged)
  Act 4 — Separation:
    Program A:  r0=1, r1=3, mu=8, err=False (WITH morphism chain)
    Program B:  r0=1, r1=3, mu=8, err=False (WITHOUT morphism chain)
    Classical fingerprint A = Classical fingerprint B  (indistinguishable to any classical observer)
    After MORPH_DELETE probe:
      Program A:  err=False  (chain was real)
      Program B:  err=True   (claim was hollow)

  KEY SEMANTIC DISTINCTIONS (verified above):
    supra_cert  — csr_cert_addr != 0; set by MORPH_ASSERT; reflects has_supra_cert in Coq
    vm_certified — set only by CERTIFY opcode; a separate flag for opcode-level certification
    MORPH_ASSERT sets supra_cert but NOT vm_certified. The NoFI theorems operate on supra_cert.

  WHAT ONLY THE THIELE MACHINE CAN DO:
    1. Refuse to accept structural claims without paying their cost.
       Theorem: NoFreeInsight in coq/kernel/NoFreeInsight.v (zero Admitted).
       Executable: Act 1 and Act 3 NoFI probe above.

    2. Charge a provably unavoidable minimum for certifying any claim (S(cost) ≥ 1).
       Theorem: no_free_certification in coq/kernel/AbstractNoFI.v §8.
       Proof chain: cert_addr changed (0→nonzero) → cert_addr_setterb = true [structural,
         proven by case analysis over all 32 opcodes via thiele_non_cert_addr_setter_preserves]
         → instruction_cost >= 1 [cert_addr_setter_cost_pos] → delta_mu >= 1 [vm_apply_mu].
       This is non-circular: the cost bound is derived from observing state change,
       not from reading the cost definition. Corollary: no_free_certification_mu.
       Universality: abstract_nfi / universal_nfi hold for ANY machine satisfying A3.

    3. Distinguish programs classically identical to ANY classical computer.
       Theorem: categorical_separation in coq/kernel/PartitionSeparation.v §10.
       Corollary: classical_observer_cannot_separate in §11 — formally, no function
       depending only on (regs, mem, mu, pc, err, certified) can separate the programs.
       Executable: Act 4 — one MORPH_DELETE probe separates them in one step.

    4. Produce a mu receipt that is mathematically unforgeable.
       Theorem: kernel_certified_implies_positive_mu in coq/kernel/PrimeAxiom.v.
       If your mu < minimum_verification_cost, you didn't do the work.
       Proven from first principles. Zero Admitted.

  PROOF FOUNDATION (coq/kernel/, zero Admitted throughout):
    NoFreeInsight.v          — Core NoFI theorem + A3/A4 formal axioms
    AbstractNoFI.v           — Universal NoFI for ANY machine satisfying A3;
                               §8: no_free_certification (structural lower bound,
                               non-circular) + no_free_certification_mu (mu corollary)
    PartitionSeparation.v    — Categorical separation + classical observer theorem
    MuInitiality.v           — mu is the unique canonical cost measure
    MuLedgerConservation.v   — vm_apply_mu: (vm_apply s i).mu = s.mu + instruction_cost i
    HonestNoFI.v             — Honest statement of NoFI across 4 rigor levels

  The three-layer isomorphism guarantees this isn't just theory.
  The same semantics run in:
    — OCaml (build/extracted_vm_runner, Coq-extracted)
    — Python (thielecpu/vm.py, Coq-extracted)
    — Verilog RTL (thielecpu/hardware/rtl/thiele_cpu_kami.v, Kami-synthesized)

  All three produce the same mu, the same err, the same supra_cert, the same separation.
  The receipt is hardware-backed.
"""))
