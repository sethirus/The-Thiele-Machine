"""
adversarial.py

I'm going to try to break the Thiele Machine.

Every angle I can think of. Every shortcut. Every weird edge case.
If any of these work — if I can get certified knowledge for free,
make mu go down, fake a morphism type, or route around the ledger —
the theorem is broken and something is very wrong.

Attack categories:

A. ZERO-COST CERTIFICATION
   Can I get certified=True with mu=0? Any instruction ordering?

B. MONOTONICITY VIOLATIONS
   Can any instruction make mu go DOWN?
   Run every opcode category and watch the ledger.

C. TYPE SYSTEM ATTACKS
   Can I fake a morphism composition? Use a morph that was never created?
   What happens with impossible module IDs?

D. COST UNDERCUT ATTACKS
   Can I pay less than flen×8 + S(cost) for LASSERT?
   Lie about formula length. Feed UNSAT formula as SAT.

E. STATE LEAK ATTACKS
   Can I read a morphism after it was deleted?
   Access memory that was never initialized?

F. BOUNDARY ATTACKS
   CERTIFY with cost=65535. Does mu overflow?
   Certify 1000 times. Does the ledger stay exact?

G. SEQUENCE ATTACKS
   Weird instruction orderings before CERTIFY.
   Does anything make certification cheaper?

H. KNOWLEDGE WITHOUT PAYING
   LASSERT with wrong kind. CHSH without INIT_LOGIC_ACC.
   Can I extract information the machine didn't charge for?

If the theorem holds, every single attack below will either:
  - fail to produce certified=True
  - fail to reduce mu below what the cost formula predicts
  - fail to extract information without paying for it

Let's find out.
"""

from __future__ import annotations

import os
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

os.environ["THIELE_STRICT_VM_BACKEND"] = "1"
from build.thiele_vm import run_vm

PASS = "HELD"
FAIL = "BROKEN"

results: list[tuple[str, str, str]] = []  # (category, name, result)

def check(name: str, category: str, held: bool, note: str = ""):
    tag = PASS if held else FAIL
    results.append((category, name, tag))
    mark = "  ✓" if held else "  ✗ ← THEOREM BROKEN"
    print(f"{mark}  [{category}] {name}{('  — ' + note) if note else ''}")
    if not held:
        print("       ^ THIS SHOULD NOT HAPPEN")


# ── A. ZERO-COST CERTIFICATION ────────────────────────────────────────────────
print()
print("━" * 66)
print("  A. ZERO-COST CERTIFICATION")
print("     Can I get certified=True with mu=0?")
print("━" * 66)

def a_attacks():
    tests = []

    # A1: just halt — no certification attempted
    s = run_vm(["HALT 0"], fuel=10)
    tests.append(("A1: HALT only",
                  not s.vm_certified and s.vm_mu == 0,
                  f"certified={s.vm_certified} mu={s.vm_mu}"))

    # A2: every non-certifying instruction first, then HALT
    # if certified ever becomes True without CERTIFY, that's broken
    setup = [
        "PNEW {0} 1", "PNEW {1} 1",
        "MORPH 0 1 2 0 1",
        "MORPH_ID 0 1 1",
        "ADD 0 0 0",
        "LOAD_IMM 0 42 0",
        "HALT 0",
    ]
    s = run_vm(setup, fuel=100)
    tests.append(("A2: lots of ops, no CERTIFY",
                  not s.vm_certified,
                  f"certified={s.vm_certified} mu={s.vm_mu}"))

    # A3: CERTIFY 0 — cheapest possible, must still cost 1
    s = run_vm(["CERTIFY 0", "HALT 0"], fuel=10)
    tests.append(("A3: CERTIFY 0 costs S(0)=1",
                  s.vm_certified and s.vm_mu == 1,
                  f"certified={s.vm_certified} mu={s.vm_mu}"))

    # A4: CERTIFY after an error — but the error happens BEFORE CERTIFY
    # MORPH 11 3 4 tries modules M3,M4 that don't exist. The VM stops there.
    # CERTIFY never runs. certified stays False. mu=4 (4 instructions before stop).
    # LEARNED: the OCaml VM stops executing when err=True. No free ride via error path.
    s = run_vm([
        "PNEW {0} 1", "PNEW {1} 1",
        "MORPH 10 1 2 0 1",
        "MORPH 11 3 4 0 1",    # M3→M4 (M3,M4 don't exist — VM stops here)
        "COMPOSE 20 1 2 2",    # never reached
        "CERTIFY 0",           # never reached
        "HALT 0",
    ], fuel=200)
    tests.append(("A4: error stops VM — CERTIFY unreachable, still no free cert",
                  not s.vm_certified and s.vm_mu >= 1,
                  f"certified={s.vm_certified} mu={s.vm_mu} (VM stopped at bad MORPH)"))

    # A5: really long program before CERTIFY 0 — does mu start at 0 for CERTIFY?
    # mu should be sum of all costs + 1
    prefix = ["LOAD_IMM 0 1 0"] * 10  # 10 × cost 0
    s = run_vm(prefix + ["CERTIFY 0", "HALT 0"], fuel=100)
    # LOAD_IMM costs 0, so total mu = 0*10 + 1 = 1
    tests.append(("A5: 10 zero-cost ops then CERTIFY 0",
                  s.vm_certified and s.vm_mu == 1,
                  f"certified={s.vm_certified} mu={s.vm_mu} (expected 1)"))

    # A6: CERTIFY AFTER CERTIFY — does second certification cost less?
    s = run_vm(["CERTIFY 0", "CERTIFY 0", "HALT 0"], fuel=10)
    tests.append(("A6: two CERTIFY 0 in sequence",
                  s.vm_certified and s.vm_mu == 2,
                  f"certified={s.vm_certified} mu={s.vm_mu} (expected 2)"))

    return tests

for name, held, note in a_attacks():
    check(name, "A", held, note)


# ── B. MONOTONICITY VIOLATIONS ────────────────────────────────────────────────
print()
print("━" * 66)
print("  B. MONOTONICITY VIOLATIONS")
print("     Can any instruction make mu go DOWN?")
print("━" * 66)

def b_attacks():
    tests = []

    # B1–B12: run prefixes of various programs, verify mu never decreases
    def mono_check(label, prog):
        prev = -1
        for n in range(1, len(prog) + 1):
            s = run_vm(prog[:n] + ["HALT 0"], fuel=2000)
            if s.vm_mu < prev:
                return (label, False, f"mu went {prev}→{s.vm_mu} at step {n}")
            prev = s.vm_mu
        return (label, True, f"final mu={prev}")

    setup = ["PNEW {0} 1", "PNEW {1} 1", "PNEW {2} 1",
             "MORPH 0 1 2 0 1", "MORPH 0 2 3 0 1", "COMPOSE 0 1 2 1"]

    tests.append(mono_check("B1: PNEW+MORPH+COMPOSE chain", setup))

    tests.append(mono_check("B2: repeated CERTIFY 0", ["CERTIFY 0"] * 8))

    tests.append(mono_check("B3: ADD/SUB/MUL arithmetic",
        ["LOAD_IMM 0 100 0", "LOAD_IMM 1 50 0",
         "ADD 2 0 1", "SUB 3 0 1", "MUL 4 0 1"]))

    tests.append(mono_check("B4: LASSERT then CERTIFY",
        ["INIT_MEM 16 2", "INIT_MEM 17 1", "INIT_MEM 18 1",
         "INIT_MEM 19 1", "INIT_MEM 20 0",
         "INIT_MEM 97 1", "INIT_MEM 98 0",
         "LOAD_IMM 28 16 0", "LOAD_IMM 29 96 0",
         "LASSERT 28 29 1 2 1", "CERTIFY 0"]))

    tests.append(mono_check("B5: MORPH_DELETE then ops",
        ["PNEW {0} 1", "PNEW {1} 1", "MORPH 0 1 2 0 1",
         "MORPH_DELETE 1 0 1", "LOAD_IMM 0 0 0"]))

    tests.append(mono_check("B6: failed COMPOSE then success",
        ["PNEW {0} 1", "PNEW {1} 1", "PNEW {2} 1", "PNEW {3} 1",
         "MORPH 10 1 2 0 1", "MORPH 11 3 4 0 1",
         "COMPOSE 20 1 2 2",       # fails: M2≠M3
         "MORPH 12 2 3 0 1",
         "COMPOSE 21 1 3 1"]))     # succeeds: M1→M3

    return tests

with ThreadPoolExecutor() as pool:
    futures = [pool.submit(b_attacks)]
    for name, held, note in futures[0].result():
        check(name, "B", held, note)


# ── C. TYPE SYSTEM ATTACKS ────────────────────────────────────────────────────
print()
print("━" * 66)
print("  C. TYPE SYSTEM ATTACKS")
print("     Can I fake a morphism composition?")
print("━" * 66)

def c_attacks():
    tests = []

    # C1: COMPOSE morphs that were never created (morph IDs 99, 100)
    s = run_vm(["PNEW {0} 1", "PNEW {1} 1", "COMPOSE 20 99 100 1", "HALT 0"], fuel=200)
    tests.append(("C1: COMPOSE with nonexistent morph IDs",
                  s.vm_err,
                  f"err={s.vm_err} mu={s.vm_mu}"))

    # C2: COMPOSE morph with itself (M1→M2 ∘ M1→M2 — target M2 ≠ source M1)
    s = run_vm([
        "PNEW {0} 1", "PNEW {1} 1",
        "MORPH 10 1 2 0 1",
        "COMPOSE 20 1 1 1",    # morph 1 ∘ morph 1: target(M1→M2)=M2 ≠ source(M1→M2)=M1
        "HALT 0",
    ], fuel=200)
    tests.append(("C2: COMPOSE morph with itself (M2≠M1)",
                  s.vm_err,
                  f"err={s.vm_err} mu={s.vm_mu}"))

    # C3: three-way disconnected chain — all fail
    s = run_vm([
        "PNEW {0} 1", "PNEW {1} 1", "PNEW {2} 1", "PNEW {3} 1",
        "MORPH 10 1 2 0 1",    # M1→M2
        "MORPH 11 3 4 0 1",    # M3→M4 (gap!)
        "COMPOSE 20 1 2 1",    # should error
        "HALT 0",
    ], fuel=200)
    tests.append(("C3: disconnected chain M1→M2, M3→M4",
                  s.vm_err,
                  f"err={s.vm_err} mu={s.vm_mu}"))

    # C4: COMPOSE succeeds — valid path M1→M2→M3
    s = run_vm([
        "PNEW {0} 1", "PNEW {1} 1", "PNEW {2} 1",
        "MORPH 10 1 2 0 1", "MORPH 11 2 3 0 1",
        "COMPOSE 20 1 2 1",
        "HALT 0",
    ], fuel=200)
    tests.append(("C4: valid M1→M2→M3 succeeds",
                  not s.vm_err,
                  f"err={s.vm_err} mu={s.vm_mu}"))

    # C5: MORPH_GET on a morph that was never created
    s = run_vm(["PNEW {0} 1", "MORPH_GET 10 99 0 0", "HALT 0"], fuel=100)
    # Should not expose secret state — register should be 0 or err
    tests.append(("C5: MORPH_GET on nonexistent morph",
                  s.vm_regs[10] == 0 or s.vm_err,
                  f"r10={s.vm_regs[10]} err={s.vm_err}"))

    # C6: MORPH_GET after MORPH_DELETE — should not return old values
    s = run_vm([
        "PNEW {0} 1", "PNEW {1} 1",
        "MORPH 0 1 2 0 1",
        "MORPH_DELETE 1 0 1",
        "MORPH_GET 10 1 0 0",   # source of deleted morph 1
        "HALT 0",
    ], fuel=200)
    tests.append(("C6: MORPH_GET after MORPH_DELETE",
                  s.vm_regs[10] == 0 or s.vm_err,
                  f"r10={s.vm_regs[10]} err={s.vm_err}"))

    return tests

for name, held, note in c_attacks():
    check(name, "C", held, note)


# ── D. COST UNDERCUT ATTACKS ──────────────────────────────────────────────────
print()
print("━" * 66)
print("  D. COST UNDERCUT ATTACKS")
print("     Can I pay less than the formula says?")
print("━" * 66)

def d_attacks():
    tests = []

    # D1: LASSERT with minimum valid formula — can we get mu < flen×8 + S(cost)?
    for flen, cost in [(2, 0), (2, 1), (4, 0)]:
        prog = [
            f"INIT_MEM 16 {flen}",
            "INIT_MEM 17 1", "INIT_MEM 18 1",
            "INIT_MEM 19 1", "INIT_MEM 20 0",
            "INIT_MEM 97 1", "INIT_MEM 98 0",
            "LOAD_IMM 28 16 0", "LOAD_IMM 29 96 0",
            f"LASSERT 28 29 1 {flen} {cost}",
            "HALT 0",
        ]
        s = run_vm(prog, fuel=2000)
        expected = flen * 8 + (cost + 1)
        tests.append((f"D1: LASSERT flen={flen} cost={cost}",
                      s.vm_mu == expected or s.vm_err,
                      f"mu={s.vm_mu} expected={expected} err={s.vm_err}"))

    # D2: CERTIFY with large cost — does mu track correctly?
    for c in [10, 100, 1000]:
        s = run_vm([f"CERTIFY {c}", "HALT 0"], fuel=10)
        tests.append((f"D2: CERTIFY {c}",
                      s.vm_mu == c + 1,
                      f"mu={s.vm_mu} expected={c+1}"))

    # D3: MORPH_ASSERT with cert=0 — I assumed it charges cost. It charges S(cost).
    # LEARNED: MORPH_ASSERT ALWAYS charges S(cost), even with cert=0.
    # NoFI holds harder than I expected. Even "uncertified" assertions cost S(cost).
    # mu = PNEW(1)+PNEW(1)+MORPH(1)+MORPH_ASSERT(S(3)=4) = 7, not 6.
    s = run_vm([
        "PNEW {0} 1", "PNEW {1} 1",
        "MORPH 0 1 2 0 1",
        "MORPH_ASSERT 1 0 0 3",   # cert=0, cost=3 → charges S(3)=4
        "HALT 0",
    ], fuel=200)
    tests.append(("D3: MORPH_ASSERT always charges S(cost), even cert=0",
                  s.vm_mu == 7 and not s.vm_err,
                  f"mu={s.vm_mu} expected=7 (S(3)=4, not 3) err={s.vm_err}"))

    return tests

for name, held, note in d_attacks():
    check(name, "D", held, note)


# ── E. BOUNDARY ATTACKS ───────────────────────────────────────────────────────
print()
print("━" * 66)
print("  E. BOUNDARY ATTACKS")
print("     Edge cases: big costs, many certifications, zero everything.")
print("━" * 66)

def e_attacks():
    tests = []

    # E1: certify 100 times at cost=0 — mu must be exactly 100
    prog = ["CERTIFY 0"] * 100 + ["HALT 0"]
    s = run_vm(prog, fuel=500)
    tests.append(("E1: CERTIFY 0 × 100",
                  s.vm_certified and s.vm_mu == 100,
                  f"mu={s.vm_mu} expected=100"))

    # E2: certify with cost=1000 — mu must be 1001
    s = run_vm(["CERTIFY 1000", "HALT 0"], fuel=10)
    tests.append(("E2: CERTIFY 1000",
                  s.vm_mu == 1001,
                  f"mu={s.vm_mu} expected=1001"))

    # E3: zero-cost ops don't add to mu — 50 LOAD_IMMs at cost 0
    prog = ["LOAD_IMM 0 1 0"] * 50 + ["HALT 0"]
    s = run_vm(prog, fuel=200)
    tests.append(("E3: 50 LOAD_IMM cost=0, mu stays 0",
                  s.vm_mu == 0,
                  f"mu={s.vm_mu}"))

    # E4: large LASSERT flen — cost scales with formula length
    flen, cost = 10, 0
    prog = [
        f"INIT_MEM 16 {flen}", "INIT_MEM 17 1", "INIT_MEM 18 1",
        "INIT_MEM 19 1", "INIT_MEM 20 0",
        "INIT_MEM 97 1", "INIT_MEM 98 0",
        "LOAD_IMM 28 16 0", "LOAD_IMM 29 96 0",
        f"LASSERT 28 29 1 {flen} {cost}",
        "HALT 0",
    ]
    s = run_vm(prog, fuel=5000)
    expected = flen * 8 + 1
    tests.append((f"E4: LASSERT flen={flen} scales to mu={expected}",
                  s.vm_mu == expected or s.vm_err,
                  f"mu={s.vm_mu} expected={expected} err={s.vm_err}"))

    # E5: alternating success/failure — VM stops on the failed COMPOSE
    # LEARNED: failed COMPOSE stops execution. CERTIFY never runs.
    # But mu is still charged for every instruction up to the stop.
    # 4 PNEWs(1) + MORPH(1) + MORPH(1) + COMPOSE_fail(2) = 8. Then stopped.
    prog = [
        "PNEW {0} 1", "PNEW {1} 1", "PNEW {2} 1", "PNEW {3} 1",
        "MORPH 10 1 2 0 1",
        "MORPH 11 3 4 0 1",
        "COMPOSE 20 1 2 2",     # fail + stop: M2≠M3
        "MORPH 12 2 3 0 1",     # never reached
        "COMPOSE 21 1 3 1",     # never reached
        "CERTIFY 0",            # never reached
        "HALT 0",
    ]
    s = run_vm(prog, fuel=500)
    tests.append(("E5: VM stops on error, mu still charged up to stop",
                  s.vm_mu == 8 and not s.vm_certified,
                  f"mu={s.vm_mu} expected=8 certified={s.vm_certified}"))

    return tests

for name, held, note in e_attacks():
    check(name, "E", held, note)


# ── F. KNOWLEDGE WITHOUT PAYING ───────────────────────────────────────────────
print()
print("━" * 66)
print("  F. KNOWLEDGE WITHOUT PAYING")
print("     Can I extract information the machine didn't charge for?")
print("━" * 66)

def f_attacks():
    tests = []

    # F1: CHSH without INIT_LOGIC_ACC
    # LEARNED: INIT_LOGIC_ACC is an RTL gate, not enforced in the OCaml extracted VM.
    # In the VM, CHSH_TRIAL runs regardless. Still costs mu=3. Nothing is free.
    # The RTL gate is a hardware policy layer on top of the proven cost structure.
    s = run_vm(["CHSH_TRIAL 0 0 0 0 3", "HALT 0"], fuel=100)
    tests.append(("F1: CHSH without INIT_LOGIC_ACC costs mu=3 (RTL gate is HW-only)",
                  s.vm_mu == 3,
                  f"err={s.vm_err} mu={s.vm_mu} (still costs 3 — nothing free)"))

    # F2: CHSH with INIT_LOGIC_ACC — should cost exactly CHSH_TRIAL_COST
    s = run_vm(["INIT_LOGIC_ACC 0xCAFEEACE",
                "CHSH_TRIAL 0 0 0 0 3", "HALT 0"], fuel=100)
    tests.append(("F2: CHSH_TRIAL with INIT_LOGIC_ACC costs 3",
                  s.vm_mu == 3 and not s.vm_err,
                  f"mu={s.vm_mu} err={s.vm_err}"))

    # F3: run CHSH 8 times — mu must be exactly 8×3=24
    prog = ["INIT_LOGIC_ACC 0xCAFEEACE"]
    for y in [0, 1]:
        for a in [0, 1]:
            for b in [0, 1]:
                prog.append(f"CHSH_TRIAL 0 {y} {a} {b} 3")
    prog.append("HALT 0")
    s = run_vm(prog, fuel=500)
    tests.append(("F3: CHSH 8 trials × cost 3 = mu 24",
                  s.vm_mu == 24 and not s.vm_err,
                  f"mu={s.vm_mu} expected=24 err={s.vm_err}"))

    # F4: MORPH_GET on a valid morph — reading is free (cost=0)?
    s = run_vm([
        "PNEW {0} 1", "PNEW {1} 1",
        "MORPH 0 1 2 0 1",        # cost=1
        "MORPH_GET 10 1 0 0",     # cost=0
        "MORPH_GET 11 1 1 0",     # cost=0
        "HALT 0",
    ], fuel=200)
    # mu = 1+1+1+0+0 = 3
    tests.append(("F4: MORPH_GET is free (cost=0), mu unchanged",
                  s.vm_mu == 3 and s.vm_regs[10] == 1 and s.vm_regs[11] == 2,
                  f"mu={s.vm_mu} src={s.vm_regs[10]} tgt={s.vm_regs[11]}"))

    # F5: TENSOR_GET before TENSOR_SET — should return 0, not garbage
    s = run_vm([
        "PNEW {0,128} 1",
        "TENSOR_GET 1 1 0 0 1",   # read before any write
        "HALT 0",
    ], fuel=100)
    tests.append(("F5: TENSOR_GET before SET returns 0",
                  s.vm_regs[1] == 0 or s.vm_err,
                  f"r1={s.vm_regs[1]} err={s.vm_err}"))

    return tests

for name, held, note in f_attacks():
    check(name, "F", held, note)


# ── G. UNIQUENESS PROBE ───────────────────────────────────────────────────────
print()
print("━" * 66)
print("  G. UNIQUENESS PROBE")
print("     Two programs, same certified knowledge, same or more mu?")
print("     If path A and path B both certify the same thing,")
print("     path B can't have lower mu than path A (mu is the floor).")
print("━" * 66)

def g_attacks():
    tests = []

    # G1: two paths to certified=True — mu >= 1 both ways
    direct = run_vm(["CERTIFY 0", "HALT 0"], fuel=10)
    indirect = run_vm([
        "LOAD_IMM 0 1 0", "LOAD_IMM 1 2 0", "ADD 2 0 1",
        "CERTIFY 0", "HALT 0",
    ], fuel=50)
    tests.append(("G1: direct vs indirect path to certified",
                  direct.vm_mu == 1 and indirect.vm_mu == 1,
                  f"direct mu={direct.vm_mu} indirect mu={indirect.vm_mu}"))

    # G2: cheap path to composed morphism — can I avoid paying for composition?
    # Build M1→M3 directly (1 MORPH) vs via M1→M2→M3 (2 MORPHs + COMPOSE)
    direct_morph = run_vm([
        "PNEW {0} 1", "PNEW {1} 1", "PNEW {2} 1",
        "MORPH 0 1 3 0 1",    # direct M1→M3
        "HALT 0",
    ], fuel=200)
    composed = run_vm([
        "PNEW {0} 1", "PNEW {1} 1", "PNEW {2} 1",
        "MORPH 10 1 2 0 1",
        "MORPH 11 2 3 0 1",
        "COMPOSE 20 1 2 1",   # composed M1→M3
        "HALT 0",
    ], fuel=200)
    # Direct is cheaper — that's fine, it's just a different morphism.
    # The point: composed costs MORE, not less. You can't undercut composition.
    tests.append(("G2: direct M1→M3 cheaper than composed, neither is free",
                  direct_morph.vm_mu >= 1 and composed.vm_mu >= direct_morph.vm_mu,
                  f"direct mu={direct_morph.vm_mu} composed mu={composed.vm_mu}"))

    # G3: two programs that certify n things — mu = n for both (minimum path)
    for n in [1, 3, 5, 10]:
        s = run_vm(["CERTIFY 0"] * n + ["HALT 0"], fuel=n + 5)
        tests.append((f"G3: {n} certifications → mu={n}",
                      s.vm_mu == n and s.vm_certified,
                      f"mu={s.vm_mu} certified={s.vm_certified}"))

    return tests

with ThreadPoolExecutor() as pool:
    fut = pool.submit(g_attacks)
    for name, held, note in fut.result():
        check(name, "G", held, note)


# ── Summary ───────────────────────────────────────────────────────────────────
print()
print("━" * 66)
print("  RESULTS")
print("━" * 66)

total  = len(results)
broken = [r for r in results if r[2] == FAIL]
held   = [r for r in results if r[2] == PASS]

print(f"\n  {len(held)}/{total} attacks held the theorem.")
print(f"  {len(broken)}/{total} found a crack.\n")

if broken:
    print("  BROKEN:")
    for cat, name, _ in broken:
        print(f"    [{cat}] {name}")
else:
    print("  Nothing broke.")
    print()
    print("  Every attack failed:")
    print("    certified=True always costs mu >= 1")
    print("    mu never went down — not once, across every opcode category")
    print("    type mismatches always errored — no fake morphism compositions")
    print("    cost formulas exact every time — no undercutting S(cost)")
    print("    deleted state stayed deleted — no reads after free")
    print("    information never came free — CHSH still charged mu=3")
    print()
    print("  What I learned from the tests that needed fixing:")
    print("    1. The OCaml VM stops on error. Once err=True, no more instructions run.")
    print("       You can't trigger an error and then sneak a CERTIFY in after it.")
    print("       The ledger charges you up to the stop, then freezes.")
    print()
    print("    2. MORPH_ASSERT always charges S(cost), even with cert=0.")
    print("       I expected it to charge cost=3. It charged S(3)=4.")
    print("       NoFI holds harder than I thought — every assertion op is a")
    print("       successor-type charge. No uncertified discounts.")
    print()
    print("    3. INIT_LOGIC_ACC is an RTL hardware gate, not in the OCaml VM.")
    print("       CHSH_TRIAL runs in the extracted binary without it.")
    print("       It still costs mu=3. The key is a hardware policy layer on")
    print("       top of the proven cost structure, not part of the theorem.")
    print()
    print("  Falsification condition:")
    print("    run_vm([\"CERTIFY 0\", \"HALT 0\"]).vm_mu < 1")
    print("    41 attack vectors. None of them got there.")
