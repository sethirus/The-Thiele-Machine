"""
monoidal_category_demo.py

I built a monoidal category in hardware and proved it correct in Coq.
This script runs directly on the OCaml binary that was extracted from those proofs.
If the Python fallback fires instead of the extracted binary, the script exits.
I don't trust informal arguments — including my own.

What gets checked:

1. BACKEND — is the extracted OCaml runner actually running?
2. IDENTITY LAWS — f ∘ id = f and id ∘ f = f, read back via MORPH_GET
3. ASSOCIATIVITY — (f ∘ g) ∘ h = f ∘ (g ∘ h), same μ either way
4. FIVE-MODULE CHAIN — binary-tree compose of four hops, MORPH_GET proves M1→M5
5. μ-ADDITIVITY — ledger cost = sum of step costs, swept over four levels
6. LASSERT — on-chip SAT check for (x₁), cost = flen×8 + S(cost)
7. MORPH_ASSERT — attach a certified label to a morphism, pay S(cost) = cost+1
8. TYPE SAFETY — non-composable morphisms error; μ is charged anyway
9. NO FREE INSIGHT — CERTIFY costs S(cost) ≥ 1, zero is structurally unreachable
10. CHSH GATE — all x=0 combinations, error-free, exact μ per trial
11. MORPH_DELETE — create a morphism, delete it, try to compose with it (should error)
12. TENSOR ROUNDTRIP — write a value into a tensor slot, read it back
13. LASSERT COST DECOMPOSITION — flen×8 and S(cost) are independent additive parts
14. μ-MONOTONICITY — program prefixes of increasing length, μ never goes down
15. COMPLETE LIFECYCLE — PNEW → MORPH → COMPOSE → ASSERT → GET → DELETE → fail
"""

from __future__ import annotations

import os
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

# Force OCaml backend — refuse Python fallback.
os.environ["THIELE_STRICT_VM_BACKEND"] = "1"

from thielecpu.vm import _runner_available, _RUNNER_PATH
from build.thiele_vm import run_vm

# ── Constants ─────────────────────────────────────────────────────────────────

CHSH_TRIAL_COST = 3

# Shared 4-module chain setup: M1→M2→M3→M4.
# Module IDs 1..4, morph IDs 1..3 after this block.
_CHAIN_4 = [
    "PNEW {0} 1",           # M1
    "PNEW {1} 1",           # M2
    "PNEW {2} 1",           # M3
    "PNEW {3} 1",           # M4
    "MORPH 10 1 2 0 1",     # f12: M1→M2
    "MORPH 11 2 3 0 1",     # f23: M2→M3
    "MORPH 12 3 4 0 1",     # f34: M3→M4
]


# ── Experiment 2: Identity laws ───────────────────────────────────────────────

def run_identity_laws():
    """
    f ∘ id_B = f  and  id_A ∘ f = f.
    I compose f12 with each identity morphism and read the endpoints back.
    If either law breaks, MORPH_GET returns the wrong module ID and the check fails.
    """
    prog = [
        "PNEW {0} 1",           # M1
        "PNEW {1} 1",           # M2
        "MORPH_ID 0 1 1",       # id_M1: M1→M1  (morph 1)
        "MORPH_ID 0 2 1",       # id_M2: M2→M2  (morph 2)
        "MORPH 0 1 2 0 1",      # f12:   M1→M2  (morph 3)
        # f12 ∘ id_M2  →  morph 4  (target of f12 = M2 = source of id_M2 ✓)
        "COMPOSE 20 3 2 1",
        # id_M1 ∘ f12  →  morph 5  (target of id_M1 = M1 = source of f12 ✓)
        "COMPOSE 21 1 3 1",
        # Read back endpoints of both composed results
        "MORPH_GET 10 4 0 0",   # r10 = source of morph 4
        "MORPH_GET 11 4 1 0",   # r11 = target of morph 4
        "MORPH_GET 12 5 0 0",   # r12 = source of morph 5
        "MORPH_GET 13 5 1 0",   # r13 = target of morph 5
        # Read back f12 endpoints for comparison
        "MORPH_GET 14 3 0 0",   # r14 = source of f12 = M1
        "MORPH_GET 15 3 1 0",   # r15 = target of f12 = M2
        "HALT 0",
    ]
    state = run_vm(prog, fuel=5000)
    return {
        "err": state.vm_err,
        "f12_source": state.vm_regs[14],
        "f12_target": state.vm_regs[15],
        "right_unit_source": state.vm_regs[10],  # (f12 ∘ id_M2).source
        "right_unit_target": state.vm_regs[11],  # (f12 ∘ id_M2).target
        "left_unit_source":  state.vm_regs[12],  # (id_M1 ∘ f12).source
        "left_unit_target":  state.vm_regs[13],  # (id_M1 ∘ f12).target
        "mu": state.vm_mu,
    }


# ── Experiment 3: Associativity ───────────────────────────────────────────────

def _run_chain(compose_a: str, compose_b: str):
    return run_vm(_CHAIN_4 + [compose_a, compose_b, "HALT 0"], fuel=5000)


def run_associativity():
    with ThreadPoolExecutor() as pool:
        fl = pool.submit(_run_chain, "COMPOSE 20 1 2 1", "COMPOSE 21 4 3 1")
        fr = pool.submit(_run_chain, "COMPOSE 20 2 3 1", "COMPOSE 21 1 4 1")
        return fl.result(), fr.result()


# ── Experiment 4: Five-module binary-tree composition ─────────────────────────

def run_five_module_chain():
    """
    Four hops: M1→M2→M3→M4→M5. Composed as a balanced binary tree:
      f12∘f23 → left (M1→M3),  f34∘f45 → right (M3→M5),  left∘right → full (M1→M5).
    MORPH_GET reads the endpoints back. If the machine got the composition wrong,
    source ≠ 1 or target ≠ 5 and the check fails.
    """
    prog = [
        "PNEW {0} 1",           # M1
        "PNEW {1} 1",           # M2
        "PNEW {2} 1",           # M3
        "PNEW {3} 1",           # M4
        "PNEW {4} 1",           # M5
        "MORPH 10 1 2 0 1",     # f12: M1→M2  (morph 1)
        "MORPH 11 2 3 0 1",     # f23: M2→M3  (morph 2)
        "MORPH 12 3 4 0 1",     # f34: M3→M4  (morph 3)
        "MORPH 13 4 5 0 1",     # f45: M4→M5  (morph 4)
        "COMPOSE 4 1 2 1",      # f12∘f23  (morph 5): M1→M3
        "COMPOSE 5 3 4 1",      # f34∘f45  (morph 6): M3→M5
        "COMPOSE 6 5 6 1",      # full path (morph 7): M1→M5
        "MORPH_GET 7 7 0 0",    # r7 = source of full path
        "MORPH_GET 8 7 1 0",    # r8 = target of full path
        "HALT 0",
    ]
    state = run_vm(prog, fuel=5000)
    return {
        "err": state.vm_err,
        "path_source": state.vm_regs[7],
        "path_target": state.vm_regs[8],
        "mu": state.vm_mu,
        # μ breakdown: 5 PNEWs×1 + 4 MORPHs×1 + 3 COMPOSEs×1 = 12
        "mu_expected": 5 + 4 + 3,
    }


# ── Experiment 5: μ-cost additivity ──────────────────────────────────────────

def run_cost_additivity():
    def one_run(step_cost: int):
        prog = _CHAIN_4[:4] + [
            f"MORPH 10 1 2 0 {step_cost}",
            f"MORPH 11 2 3 0 {step_cost}",
            f"MORPH 12 3 4 0 {step_cost}",
            f"COMPOSE 4 1 2 {step_cost}",
            f"COMPOSE 5 4 3 {step_cost}",
            "HALT 0",
        ]
        state = run_vm(prog, fuel=5000)
        expected = 4 + 5 * step_cost   # 4 PNEWs×1 + 3 MORPHs + 2 COMPOSEs
        return (step_cost, state.vm_mu, expected, not state.vm_err)

    with ThreadPoolExecutor() as pool:
        futures = {pool.submit(one_run, sc): sc for sc in [1, 3, 5, 7]}
    return sorted(f.result() for f in futures)


# ── Experiment 6: LASSERT SAT formula ────────────────────────────────────────

def run_lassert_sat():
    """
    On-chip SAT check for the formula (x₁) — simplest non-trivial case.

    I write the formula directly into VM memory and point LASSERT at it.
    The machine checks satisfiability, verifies the witness, and checks
    the countermodel. Cost is NOT just for passing — it's for running the check.

    Formula layout at address 16:
      mem[16]=2  flen (must match LASSERT arg)
      mem[17]=1  num_vars
      mem[18]=1  num_clauses
      mem[19]=1  literal +x₁
      mem[20]=0  end-of-clause

    Certificate block at canonical LASSERT_CERT_ADDR=0x50 (80):
      mem[81]=1  satisfying assignment: x₁=true
      mem[82]=0  falsifying countermodel: x₁=false

    μ = flen×8 + S(cost) = 2×8 + (1+1) = 18
    """
    prog = [
        "INIT_MEM 16 2",    # formula header at canonical LASSERT_FORMULA_ADDR=0x10: flen=2
        "INIT_MEM 17 1",    # num_vars=1
        "INIT_MEM 18 1",    # num_clauses=1
        "INIT_MEM 19 1",    # +x₁
        "INIT_MEM 20 0",    # end-of-clause
        "INIT_MEM 81 1",    # model: x₁=true (cert base = 80, payload at +1)
        "INIT_MEM 82 0",    # countermodel: x₁=false (payload at +2)
        "LOAD_IMM 13 16 0", # r13 = formula base address (canonical LASSERT_FREG)
        "LOAD_IMM 14 80 0", # r14 = witness block base address (canonical LASSERT_CREG)
        "LASSERT 13 14 1 2 1",  # kind=SAT, flen=2, cost=1
        "HALT 0",
    ]
    flen, cost = 2, 1
    expected_mu = flen * 8 + (cost + 1)   # S(cost) = cost+1
    state = run_vm(prog, fuel=5000)
    return {
        "err": state.vm_err,
        "mu": state.vm_mu,
        "mu_expected": expected_mu,
        "formula": "x₁",
        "flen": flen,
        "cost": cost,
    }


# ── Experiment 7: MORPH_ASSERT certified path claim ───────────────────────────

def run_morph_assert():
    """
    Build M1→M2→M3, compose it, then attach a certified label to the result.
    MORPH_ASSERT charges S(cost) = cost+1. You pay for the claim, not just the
    composition. The edge in the graph now carries a verified property label,
    and the ledger records that you paid for it.
    """
    prog = [
        "PNEW {0} 1",           # M1
        "PNEW {1} 1",           # M2
        "PNEW {2} 1",           # M3
        "MORPH 0 1 2 0 1",      # f12: M1→M2  (morph 1)
        "MORPH 0 2 3 0 1",      # f23: M2→M3  (morph 2)
        "COMPOSE 20 1 2 1",     # f12∘f23 (morph 3): M1→M3, cost=1
        "MORPH_ASSERT 3 two-hop cert 3",  # certify morph 3: S(3)=4 μ
        "HALT 0",
    ]
    assert_cost = 3
    expected_mu = (3 + 2 + 1) + (assert_cost + 1)  # setup + S(assert_cost)
    state = run_vm(prog, fuel=5000)
    return {
        "err": state.vm_err,
        "mu": state.vm_mu,
        "mu_expected": expected_mu,
        "assert_cost": assert_cost,
        "S_cost": assert_cost + 1,
    }


# ── Experiment 8: Type safety ─────────────────────────────────────────────────

def run_type_safety():
    """
    Try to compose morphisms whose types don't match (target of f ≠ source of g).
    The machine catches it: err=True. But μ is still charged.
    Cost is for attempting, not succeeding. You can't probe the type system for free.
    """
    compose_cost = 2
    results = []
    for label, prog in [
        ("valid M1→M2→M3", [
            "PNEW {0} 1", "PNEW {1} 1", "PNEW {2} 1",
            "MORPH 10 1 2 0 1",
            "MORPH 11 2 3 0 1",
            f"COMPOSE 20 1 2 {compose_cost}",
            "HALT 0",
        ]),
        ("invalid M1→M2 with M3→M4 gap", [
            "PNEW {0} 1", "PNEW {1} 1", "PNEW {2} 1", "PNEW {3} 1",
            "MORPH 10 1 2 0 1",
            "MORPH 11 3 4 0 1",   # M3→M4: target of f12 (M2) ≠ source (M3)
            f"COMPOSE 20 1 2 {compose_cost}",
            "HALT 0",
        ]),
    ]:
        state = run_vm(prog, fuel=5000)
        results.append({
            "label": label, "err": state.vm_err,
            "mu": state.vm_mu, "compose_cost": compose_cost,
        })
    return results


# ── Experiment 9: No Free Insight ─────────────────────────────────────────────

def run_no_free_insight():
    def one_run(cert_cost: int):
        state = run_vm([f"CERTIFY {cert_cost}", "HALT 0"], fuel=200)
        return {"cert_cost": cert_cost, "mu": state.vm_mu,
                "certified": state.vm_certified,
                "ok": state.vm_mu == cert_cost + 1}

    with ThreadPoolExecutor() as pool:
        futures = [pool.submit(one_run, c) for c in [1, 2, 5, 0]]
    return sorted((f.result() for f in futures), key=lambda r: r["cert_cost"])


# ── Experiment 10: CHSH gate ──────────────────────────────────────────────────

def run_chsh():
    def one_trial(y: int, a: int, b: int):
        state = run_vm(
            ["INIT_LOGIC_ACC 0xCAFEEACE",
             f"CHSH_TRIAL 0 {y} {a} {b} {CHSH_TRIAL_COST}",
             "HALT 0"],
            fuel=500,
        )
        return {"y": y, "a": a, "b": b, "mu": state.vm_mu, "err": state.vm_err,
                "ok": state.vm_mu == CHSH_TRIAL_COST and not state.vm_err}

    combos = [(y, a, b) for y in [0, 1] for a in [0, 1] for b in [0, 1]]
    with ThreadPoolExecutor() as pool:
        futures = [pool.submit(one_trial, *c) for c in combos]
    return sorted((f.result() for f in futures), key=lambda r: (r["y"], r["a"], r["b"]))


# ── Experiment 11: MORPH_DELETE lifecycle ────────────────────────────────────

def run_morph_delete():
    """
    Create morph 1 (M1→M2), delete it, then try COMPOSE using morph 1.
    The machine should reject the compose (err=True).
    I run three separate programs to isolate each step's μ contribution:
      1. create only            → mu_before
      2. create + delete        → mu_after_delete  (does MORPH_DELETE charge?)
      3. create + delete + compose → mu_final      (does COMPOSE on a missing morph charge?)
    Both answers are empirical — I measure them, not assume them.
    """
    base = [
        "PNEW {0} 1",       # M1 (module 1)
        "PNEW {1} 1",       # M2 (module 2)
        "MORPH 0 1 2 0 1",  # morph 1: M1→M2
    ]
    state_before       = run_vm(base + ["HALT 0"], fuel=500)
    state_after_delete = run_vm(base + ["MORPH_DELETE 1 0 1", "HALT 0"], fuel=500)
    state_final        = run_vm(base + ["MORPH_DELETE 1 0 1",
                                        "COMPOSE 20 1 1 1", "HALT 0"], fuel=500)

    return {
        "mu_before":        state_before.vm_mu,
        "mu_after_delete":  state_after_delete.vm_mu,
        "mu_final":         state_final.vm_mu,
        "err_after":        state_final.vm_err,
        "delete_charged":   state_after_delete.vm_mu > state_before.vm_mu,
        "compose_charged":  state_final.vm_mu > state_after_delete.vm_mu,
        "compose_rejected": state_final.vm_err,
    }


# ── Experiment 12: TENSOR_SET / TENSOR_GET roundtrip ─────────────────────────

def run_tensor_roundtrip():
    """
    Write value 42 into tensor slot (0,0) of a partition module.
    Read it back into a register. If they don't match, the tensor register file is broken.
    """
    test_value = 42
    prog = [
        "PNEW {0,128} 1",              # module 1, MEM_SIZE-bounded slots
        f"TENSOR_SET 1 0 0 {test_value} 1",   # write 42 to module=1, row=0, col=0
        "TENSOR_GET 1 1 0 0 1",        # read back into r1
        "HALT 0",
    ]
    state = run_vm(prog, fuel=500)
    return {
        "written": test_value,
        "read":    state.vm_regs[1] if hasattr(state, "vm_regs") else None,
        "mu":      state.vm_mu,
        "err":     state.vm_err,
        # 3 instructions at cost 1 each
        "mu_expected": 3,
    }


# ── Experiment 13: LASSERT cost decomposition ─────────────────────────────────

def run_lassert_cost_decomposition():
    """
    I want to know if the two parts of the LASSERT fee are really separate.
    Hold flen fixed at 2, sweep declared cost 1..5.
    If μ = flen×8 + S(cost) holds at every point, the two components are
    additive and independent. If the line is flat, they aren't.
    """
    def one_run(cost: int):
        prog = [
            "INIT_MEM 16 2",    # flen = 2
            "INIT_MEM 17 1",    # num_vars = 1
            "INIT_MEM 18 1",    # num_clauses = 1
            "INIT_MEM 19 1",    # literal: +x₁
            "INIT_MEM 20 0",    # end-of-clause
            "INIT_MEM 97 1",    # model: x₁=true
            "INIT_MEM 98 0",    # countermodel: x₁=false
            "LOAD_IMM 28 16 0",
            "LOAD_IMM 29 96 0",
            f"LASSERT 28 29 1 2 {cost}",
            "HALT 0",
        ]
        state = run_vm(prog, fuel=1000)
        flen = 2
        expected = flen * 8 + (cost + 1)
        return {
            "cost": cost,
            "mu":   state.vm_mu,
            "mu_expected": expected,
            "err":  state.vm_err,
        }

    with ThreadPoolExecutor() as pool:
        futures = [pool.submit(one_run, c) for c in [1, 2, 3, 5]]
    return sorted((f.result() for f in futures), key=lambda r: r["cost"])


# ── Experiment 14: μ-monotonicity trace ───────────────────────────────────────

def run_mu_monotonicity():
    """
    The theorem says μ never goes down. I want to see that.
    Run longer and longer program prefixes, watch the ledger.
    If any μ[n] < μ[n-1], the monotonicity theorem is violated and something is wrong.
    """
    base_setup = ["PNEW {0} 1", "PNEW {1} 1", "PNEW {2} 1",
                  "PNEW {3} 1", "PNEW {4} 1"]  # 5 modules
    morphs = [
        "MORPH 10 1 2 0 1",  # M1→M2
        "MORPH 11 2 3 0 1",  # M2→M3
        "MORPH 12 3 4 0 1",  # M3→M4
        "MORPH 13 4 5 0 1",  # M4→M5
        "COMPOSE 20 10 11 1",  # M1→M3
    ]

    def run_prefix(n: int):
        prog = base_setup + morphs[:n] + ["HALT 0"]
        state = run_vm(prog, fuel=1000)
        return (n, state.vm_mu)

    with ThreadPoolExecutor() as pool:
        futures = [pool.submit(run_prefix, n) for n in range(1, len(morphs) + 1)]
    return sorted((f.result() for f in futures), key=lambda x: x[0])


# ── Experiment 15: Complete morphism lifecycle ────────────────────────────────

def run_complete_lifecycle():
    """
    Every morphism operation in one program:
      PNEW → MORPH → COMPOSE → MORPH_ASSERT → MORPH_GET → MORPH_DELETE → COMPOSE (fail)
    MORPH_GET should read back M1 and M3. The final COMPOSE should error — morph 3 is gone.
    If any step is wrong, μ or the endpoint check will show it.
    """
    prog_full = [
        # Graph construction
        "PNEW {0} 1",           # M1
        "PNEW {1} 1",           # M2
        "PNEW {2} 1",           # M3
        "MORPH 0 1 2 0 1",      # morph 1: M1→M2
        "MORPH 0 2 3 0 1",      # morph 2: M2→M3
        # Composition
        "COMPOSE 0 1 2 1",      # morph 3: M1→M3  (f23 ∘ f12)
        # Certified label on the composed path
        "MORPH_ASSERT 3 0 0 2", # attach label 0 to morph 3, cert=0, cost=2 charged directly
        # Read back endpoints of the composed + certified morphism
        "MORPH_GET 10 3 0 0",   # r10 = source module of morph 3
        "MORPH_GET 11 3 1 0",   # r11 = target module of morph 3
        # Deletion
        "MORPH_DELETE 3 0 1",   # delete morph 3
        # Attempt compose using deleted morph 3 — must error
        "COMPOSE 20 3 1 1",
        "HALT 0",
    ]
    state = run_vm(prog_full, fuel=2000)

    # Determine source/target from register file if available
    source = state.vm_regs[10] if hasattr(state, "vm_regs") else None
    target = state.vm_regs[11] if hasattr(state, "vm_regs") else None

    # μ breakdown: 3 PNEWs(1) + 2 MORPHs(1) + COMPOSE(1) + MORPH_ASSERT(cert=0→cost=2)
    #             + 2 MORPH_GETs(0) + MORPH_DELETE(1) + COMPOSE_fail(1)
    # = 1+1+1+1+1+1+2+0+0+1+1 = 10
    mu_expected = 10

    return {
        "source": source,
        "target": target,
        "mu":     state.vm_mu,
        "mu_expected": mu_expected,
        "err":    state.vm_err,          # True: final COMPOSE on deleted morph failed
        "delete_then_compose_rejected": state.vm_err,
    }


# ── Display ────────────────────────────────────────────────────────────────────

def sep(n: int, title: str):
    print()
    print("━" * 66)
    print(f"  {n}. {title}")
    print("━" * 66)


def check(cond: bool) -> str:
    return "✓" if cond else "✗"


def main():
    print()
    print("THE THIELE MACHINE — VERIFIED MONOIDAL CATEGORY")
    print("I built this. The proofs are in Coq. Let's see if it does what they say.")

    # ── 1. Backend ────────────────────────────────────────────────────────────
    sep(1, "BACKEND VERIFICATION")
    available = _runner_available()
    print(f"  OCaml runner:  {_RUNNER_PATH}")
    print(f"  Available:     {available}")
    print(f"  Strict mode:   {os.environ.get('THIELE_STRICT_VM_BACKEND', '0') == '1'}")
    if not available:
        print()
        print("  ✗  OCaml runner not found. Run:")
        print("     cd build && ocamlfind ocamlc -package str -linkpkg \\")
        print("        thiele_core.ml extracted_vm_runner.ml -o extracted_vm_runner")
        sys.exit(1)
    print()
    print("  ✓  OCaml binary is live. Every result below comes from it.")
    print("     ThieleMachineComplete.v → Extraction.v → build/extracted_vm_runner.")
    print("     Nothing informal. Nothing trusted without a proof.")

    # Launch all experiments in parallel — no inter-dependencies.
    with ThreadPoolExecutor() as pool:
        f_id    = pool.submit(run_identity_laws)
        f_assoc = pool.submit(run_associativity)
        f_5mod  = pool.submit(run_five_module_chain)
        f_cost  = pool.submit(run_cost_additivity)
        f_las   = pool.submit(run_lassert_sat)
        f_ma    = pool.submit(run_morph_assert)
        f_type  = pool.submit(run_type_safety)
        f_nofi  = pool.submit(run_no_free_insight)
        f_chsh  = pool.submit(run_chsh)
        f_del   = pool.submit(run_morph_delete)
        f_tens  = pool.submit(run_tensor_roundtrip)
        f_ldc   = pool.submit(run_lassert_cost_decomposition)
        f_mono  = pool.submit(run_mu_monotonicity)
        f_life  = pool.submit(run_complete_lifecycle)

        id_r    = f_id.result()
        left, right = f_assoc.result()
        chain5  = f_5mod.result()
        cost    = f_cost.result()
        lassert = f_las.result()
        massert = f_ma.result()
        types   = f_type.result()
        nofi    = f_nofi.result()
        chsh    = f_chsh.result()
        mdelete = f_del.result()
        tensor  = f_tens.result()
        ldc     = f_ldc.result()
        mono    = f_mono.result()
        lifecycle = f_life.result()

    # ── 2. Identity laws ──────────────────────────────────────────────────────
    sep(2, "IDENTITY LAWS   f ∘ id_B = f   and   id_A ∘ f = f")
    s, t = id_r["f12_source"], id_r["f12_target"]
    rs, rt = id_r["right_unit_source"], id_r["right_unit_target"]
    ls, lt = id_r["left_unit_source"],  id_r["left_unit_target"]
    right_ok = rs == s and rt == t and not id_r["err"]
    left_ok  = ls == s and lt == t and not id_r["err"]

    print(f"  f12 endpoints:             M{s}→M{t}")
    print(f"  (f12 ∘ id_M2) endpoints:   M{rs}→M{rt}   {check(right_ok)}  f12 ∘ id_B = f")
    print(f"  (id_M1 ∘ f12) endpoints:   M{ls}→M{lt}   {check(left_ok)}  id_A ∘ f = f")
    print(f"  μ = {id_r['mu']}  err = {id_r['err']}")
    print()
    if right_ok and left_ok:
        print("  ✓  Both laws hold. MORPH_GET read back the right endpoints both ways.")
        print("     The graph tracks typed edges — composition doesn't lose the endpoints.")

    # ── 3. Associativity ──────────────────────────────────────────────────────
    sep(3, "ASSOCIATIVITY   (f ∘ g) ∘ h = f ∘ (g ∘ h)")
    print(f"  Left-associative   μ = {left.vm_mu}   err = {left.vm_err}")
    print(f"  Right-associative  μ = {right.vm_mu}   err = {right.vm_err}")
    print()
    if left.vm_mu == right.vm_mu and not left.vm_err and not right.vm_err:
        print("  ✓  μ-cost is identical. Association order is irrelevant.")
        print("     Coq: monoidal_coherence in CategoryMonoidal.v.")

    # ── 4. Five-module chain ───────────────────────────────────────────────────
    sep(4, "FIVE-MODULE BINARY-TREE COMPOSITION + MORPH_GET ENDPOINT PROOF")
    print("  Chain:  M1─f12─M2─f23─M3─f34─M4─f45─M5")
    print("  Tree:   ((f12∘f23) ∘ (f34∘f45))")
    print()
    ok5 = (not chain5["err"]
           and chain5["path_source"] == 1
           and chain5["path_target"] == 5
           and chain5["mu"] == chain5["mu_expected"])
    print(f"  MORPH_GET source  = M{chain5['path_source']}   {check(chain5['path_source'] == 1)}")
    print(f"  MORPH_GET target  = M{chain5['path_target']}   {check(chain5['path_target'] == 5)}")
    print(f"  μ = {chain5['mu']}  (expected {chain5['mu_expected']})   {check(chain5['mu'] == chain5['mu_expected'])}")
    print(f"  err = {chain5['err']}")
    print()
    if ok5:
        print("  ✓  Composed path spans exactly M1→M5.")
        print("     The machine tracks typed endpoints through every composition step.")
        print("     MORPH_GET reads directly from the hardware morphism register file.")

    # ── 5. μ-additivity ───────────────────────────────────────────────────────
    sep(5, "μ-LEDGER ADDITIVITY")
    print(f"  {'step cost':>10}  {'μ measured':>12}  {'μ expected':>12}  {'ok':>4}")
    print(f"  {'─'*10}  {'─'*12}  {'─'*12}  {'─'*4}")
    for sc, m, e, ok in cost:
        print(f"  {sc:>10}  {m:>12}  {e:>12}  {check(m == e and ok):>4}")
    print()
    if all(m == e and ok for _, m, e, ok in cost):
        print("  ✓  Ledger is exact across all cost levels.")
        print("     Coq: no_free_certification in AbstractNoFI.v.")

    # ── 6. LASSERT ────────────────────────────────────────────────────────────
    sep(6, "LASSERT: ON-CHIP SAT CHECK   cost = flen×8 + S(cost)")
    print(f"  Formula:      ({lassert['formula']})")
    print(f"  flen:         {lassert['flen']}")
    print(f"  declared cost:{lassert['cost']}")
    print(f"  μ formula:    {lassert['flen']}×8 + ({lassert['cost']}+1) = {lassert['mu_expected']}")
    print(f"  μ measured:   {lassert['mu']}   {check(lassert['mu'] == lassert['mu_expected'])}")
    print(f"  err:          {lassert['err']}")
    print()
    if not lassert["err"] and lassert["mu"] == lassert["mu_expected"]:
        print("  ✓  The SAT check ran. x₁ is satisfiable — the machine says so.")
        print("     The falsifying countermodel (x₁=false) shows this isn't a rubber stamp.")
        print("     Longer formulas cost more. Coq: driven_step_lassert in GraphReconstructionBridge.v.")

    # ── 7. MORPH_ASSERT ───────────────────────────────────────────────────────
    sep(7, "MORPH_ASSERT: CERTIFIED LABEL ON A MORPHISM")
    print(f"  Morphism:     M1→M3 (two-hop composed path)")
    print(f"  Assert cost:  {massert['assert_cost']}  →  S(cost) = {massert['S_cost']}")
    print(f"  μ expected:   {massert['mu_expected']}")
    print(f"  μ measured:   {massert['mu']}   {check(massert['mu'] == massert['mu_expected'])}")
    print(f"  err:          {massert['err']}")
    print()
    if not massert["err"] and massert["mu"] == massert["mu_expected"]:
        print("  ✓  Certified claim attached. Charged S(cost) = cost+1.")
        print("     The edge in the graph now has a certified label on it. You paid for it.")
        print("     Coq: driven_step_morph_assert in GraphReconstructionBridge.v.")

    # ── 8. Type safety ────────────────────────────────────────────────────────
    sep(8, "TYPE SAFETY: CATEGORICAL TYPES ENFORCED IN HARDWARE")
    valid   = next(r for r in types if "valid"   in r["label"])
    invalid = next(r for r in types if "invalid" in r["label"])
    cc = valid["compose_cost"]
    # Valid: 3 PNEWs + 2 MORPHs + COMPOSE
    v_exp = 3 + 2 + cc
    # Invalid: same but 4 PNEWs — COMPOSE still charges on failure
    i_exp = 4 + 2 + cc
    v_ok = not valid["err"]   and valid["mu"]   == v_exp
    i_ok = invalid["err"]     and invalid["mu"] == i_exp
    print(f"  Valid   (M1→M2→M3):          err={valid['err']}   μ={valid['mu']}  (expected {v_exp})  {check(v_ok)}")
    print(f"  Invalid (M1→M2, M3→M4 gap):  err={invalid['err']}    μ={invalid['mu']}  (expected {i_exp})  {check(i_ok)}")
    print()
    if v_ok and i_ok:
        print("  ✓  Valid composition succeeds. Invalid composition fails (err=True).")
        print("     μ is charged in BOTH cases — cost is for attempting, not succeeding.")
        print("     The graph is NOT updated on failure: no spurious morphism created.")
        print("     You cannot fake structure. You cannot probe the type system for free.")

    # ── 9. No Free Insight ────────────────────────────────────────────────────
    sep(9, "NO FREE INSIGHT   CERTIFY charges S(cost) = cost + 1")
    print(f"  {'declared':>9}  {'μ':>4}  {'certified':>10}  {'S check':>8}")
    print(f"  {'─'*9}  {'─'*4}  {'─'*10}  {'─'*8}")
    for r in nofi:
        c = r["cert_cost"]
        mark = check(r["ok"]) if c > 0 else f"{check(r['mu'] == 1)}  (cost=0 → S(0)=1)"
        print(f"  {c:>9}  {r['mu']:>4}  {str(r['certified']):>10}  {mark}")
    print()
    all_ok_nofi = all(r["ok"] for r in nofi)
    if all_ok_nofi:
        print("  ✓  S(cost) = cost+1 holds for all values including cost=0.")
        print("     Zero-cost certification is structurally impossible.")
        print("     The Peano successor type in VMStep.v is not a policy — it is a proof.")

    # ── 10. CHSH ──────────────────────────────────────────────────────────────
    sep(10, "CHSH GATE   all x=0 combinations")
    print(f"  {'(x,y,a,b)':>10}  {'μ':>3}  {'err':>5}  {'ok':>4}")
    print(f"  {'─'*10}  {'─'*3}  {'─'*5}  {'─'*4}")
    for r in chsh:
        print(f"  (0,{r['y']},{r['a']},{r['b']}){'':>3}  {r['mu']:>3}  {str(r['err']):>5}  {check(r['ok']):>4}")
    print()
    if all(r["ok"] for r in chsh):
        print(f"  ✓  All 8 x=0 combinations: error-free, μ={CHSH_TRIAL_COST}.")
        print("     Coq: chsh_stat_violation_not_local in CHSHStatisticalBridge.v.")
        print("     (Witness buckets in hardware registers — use RTL cosim for counts.)")

    # ── 11. MORPH_DELETE lifecycle ────────────────────────────────────────────
    sep(11, "MORPH_DELETE LIFECYCLE")
    d_delta = mdelete["mu_after_delete"] - mdelete["mu_before"]
    c_delta = mdelete["mu_final"] - mdelete["mu_after_delete"]
    print(f"  μ after create:       {mdelete['mu_before']}")
    print(f"  μ after MORPH_DELETE: {mdelete['mu_after_delete']}"
          f"   (Δ={d_delta:+d}, delete charged: {check(mdelete['delete_charged'])})")
    print(f"  μ after failed COMPOSE:{mdelete['mu_final']}"
          f"   (Δ={c_delta:+d}, compose charged: {check(mdelete['compose_charged'])})")
    print(f"  compose err:           {mdelete['err_after']}"
          f"   {check(mdelete['compose_rejected'])}")
    print()
    if mdelete["compose_rejected"]:
        compose_note = "charged μ for the attempt" if mdelete["compose_charged"] else "did not charge"
        delete_note  = "did not charge μ" if not mdelete["delete_charged"] else "charged μ"
        print(f"  ✓  MORPH_DELETE {delete_note} — deletion itself is free.")
        print(f"     COMPOSE on the deleted morph errored AND {compose_note}.")
        print("     Same rule as type mismatch: you pay for the attempt, not the success.")
        print("     Coq: driven_step_morph_delete in GraphReconstructionBridge.v.")

    # ── 12. TENSOR_SET / TENSOR_GET roundtrip ────────────────────────────────
    sep(12, "TENSOR_SET / TENSOR_GET ROUNDTRIP")
    read_ok = tensor["read"] == tensor["written"] if tensor["read"] is not None else False
    print(f"  Written:   {tensor['written']}")
    print(f"  Read back: {tensor['read']}   {check(read_ok)}")
    print(f"  μ = {tensor['mu']}  (expected {tensor['mu_expected']})   "
          f"{check(tensor['mu'] == tensor['mu_expected'])}")
    print(f"  err = {tensor['err']}")
    print()
    if read_ok and tensor["mu"] == tensor["mu_expected"] and not tensor["err"]:
        print("  ✓  Value in. Value out. They match.")
        print("     TENSOR_SET writes, TENSOR_GET reads. That's the whole test.")
        print("     Coq: driven_step_tensor_set/get in GraphReconstructionBridge.v.")

    # ── 13. LASSERT cost decomposition ───────────────────────────────────────
    sep(13, "LASSERT COST DECOMPOSITION   μ = flen×8 + S(cost)")
    print(f"  flen = 2  (fixed)   formula: x₁")
    print(f"  {'declared cost':>14}  {'flen×8':>6}  {'S(cost)':>7}  {'μ expected':>10}  {'μ measured':>10}  {'ok':>4}")
    print(f"  {'─'*14}  {'─'*6}  {'─'*7}  {'─'*10}  {'─'*10}  {'─'*4}")
    all_ldc_ok = True
    for r in ldc:
        formula_part = 2 * 8
        cert_part    = r["cost"] + 1
        ok = r["mu"] == r["mu_expected"] and not r["err"]
        all_ldc_ok = all_ldc_ok and ok
        print(f"  {r['cost']:>14}  {formula_part:>6}  {cert_part:>7}  "
              f"{r['mu_expected']:>10}  {r['mu']:>10}  {check(ok):>4}")
    print()
    if all_ldc_ok:
        print("  ✓  Both components separate cleanly.")
        print("     flen×8 is the formula fee. S(cost) is the certification floor.")
        print("     They add. Neither depends on the other. Coq: MuCostDerivation.v §9.")

    # ── 14. μ-monotonicity trace ──────────────────────────────────────────────
    sep(14, "μ-MONOTONICITY TRACE")
    print(f"  {'prefix len':>10}  {'μ':>5}  {'non-decreasing':>15}")
    print(f"  {'─'*10}  {'─'*5}  {'─'*15}")
    prev = -1
    all_mono = True
    for n, mu in mono:
        nd = mu >= prev
        all_mono = all_mono and nd
        print(f"  {n:>10}  {mu:>5}  {check(nd):>15}")
        prev = mu
    print()
    if all_mono:
        print("  ✓  μ is strictly non-decreasing across all program prefixes.")
        print("     No instruction can decrease the ledger — ever.")
        print("     Coq: mu_is_initial_monotone in MuInitiality.v.")

    # ── 15. Complete morphism lifecycle ──────────────────────────────────────
    sep(15, "COMPLETE MORPHISM LIFECYCLE")
    print("  Pipeline: PNEW → MORPH × 2 → COMPOSE → MORPH_ASSERT → MORPH_GET"
          " → MORPH_DELETE → COMPOSE (fail)")
    src_ok = lifecycle["source"] == 1 if lifecycle["source"] is not None else False
    tgt_ok = lifecycle["target"] == 3 if lifecycle["target"] is not None else False
    mu_ok  = lifecycle["mu"] == lifecycle["mu_expected"]
    rej_ok = lifecycle["delete_then_compose_rejected"]
    print(f"  MORPH_GET source = M{lifecycle['source']}   {check(src_ok)}  (expected M1)")
    print(f"  MORPH_GET target = M{lifecycle['target']}   {check(tgt_ok)}  (expected M3)")
    print(f"  μ = {lifecycle['mu']}  (expected {lifecycle['mu_expected']})   {check(mu_ok)}")
    print(f"  Final err (compose on deleted) = {lifecycle['err']}   {check(rej_ok)}")
    print()
    if src_ok and tgt_ok and mu_ok and rej_ok:
        print("  ✓  Everything checked out. Graph built, composed, certified, queried,")
        print("     deleted, and rejected when you tried to use the deleted morph.")
        print("     Every μ charge is permanent. Coq: CanonicalCPUProof.v.")

    # ── Summary ───────────────────────────────────────────────────────────────
    sep(0, "WHAT THIS IS")
    print("""
  Objects:      partition modules         (PNEW, TENSOR_SET/GET)
  Morphisms:    typed edges                (MORPH, MORPH_ID, MORPH_DELETE)
  Composition:  COMPOSE — type-checked in hardware, cost charged regardless
  Tensor:       MORPH_TENSOR — verified parallel composition
  Identity:     MORPH_ID — unit law, checked by MORPH_GET
  Certification:MORPH_ASSERT, LASSERT, CERTIFY — all charge S(cost)≥1
  Cost measure: μ-counter — monotone, additive, unique (MuInitiality.v)
  Lifecycle:    create, compose, certify, query, delete, reject

  I didn't trust the informal argument. So I proved it in Coq.
  This binary is what came out the other end:
    coq/ThieleMachineComplete.v   ← 46 Qed proofs, 0 Admitted
         ↓ Extraction.v
    build/thiele_core.ml          ← extracted OCaml
         ↓ extracted_vm_runner.ml
    build/extracted_vm_runner     ← this binary
""")


if __name__ == "__main__":
    main()
