#!/usr/bin/env python3
"""mu_geodesic_demo.py — Visualize the mu-metric on a 3D factored search problem.

The problem: find a target in a 3-dimensional grid where the three dimensions
are structurally independent.  Grid size N=4, worst-case target (3,3,3).

Five strategies are compared:
  blind          0  certs:  64 steps,  0 mu
  1-cert         1  cert:   20 steps,  9 mu
  2-cert (geo)   2  certs:  12 steps, 18 mu  ← geodesic (Pareto-optimal)
  3-cert         3  certs:  12 steps, 27 mu  (last cert saves 0 steps)
  wrong-cert     2 "certs": 20 steps, 18 mu  (pays mu for wrong structure)

Usage:
    python3 scripts/mu_geodesic_demo.py
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
RUNNER    = REPO_ROOT / "build" / "extracted_vm_runner"
N         = 4   # grid size per dimension


# ---------------------------------------------------------------------------
# Program construction
# ---------------------------------------------------------------------------
# PC accounting: FUEL is a directive (no PC). Preamble = 2 instructions:
#   PC=0: LOAD_IMM 10 1 0   (r10 = constant 1)
#   PC=1: LOAD_IMM 15 0 0   (r15 = iteration counter, start=0)
# All programs use:
#   r10 = 1  (increment / decrement constant)
#   r15 = iteration counter (the "work done" we measure)
#   r1/r2/r3 = loop counters for each dimension
#   EMIT 0 . 0 = certify one structural dimension (8 payload bits + S(0) = 9 mu)
#
# Loop pattern for "run N iterations, counting each in r15":
#   LOAD_IMM rX N 0            ; PC=p:   rX = N
#   ADD 15 15 10 0             ; PC=p+1: r15++   ← JNEZ must point here
#   SUB rX rX 10 0             ; PC=p+2: rX--
#   JNEZ rX (p+1) 0            ; PC=p+3: if rX≠0, back to ADD
# ---------------------------------------------------------------------------

PREAMBLE = ["FUEL 1000", "LOAD_IMM 10 1 0", "LOAD_IMM 15 0 0"]
PREAMBLE_PC = 2   # FUEL is a directive; LOAD_IMM×2 consume PCs 0 and 1


def loop_block(reg: int, n: int, start_pc: int) -> tuple[list[str], int]:
    """Single flat loop: run n iterations, increment r15 each time.

    Returns (instructions, next_available_pc).
    LOAD_IMM is at start_pc, ADD at start_pc+1, SUB at start_pc+2,
    JNEZ at start_pc+3 targeting start_pc+1 (the ADD).
    """
    return ([
        f"LOAD_IMM {reg} {n} 0",
        f"ADD 15 15 10 0",
        f"SUB {reg} {reg} 10 0",
        f"JNEZ {reg} {start_pc + 1} 0",
    ], start_pc + 4)


def nested_loop_2d(outer_reg: int, inner_reg: int, n: int, start_pc: int) -> tuple[list[str], int]:
    """Two nested loops, both of size n.  r15 increments in the inner loop only.

    Counts n*n = n^2 iterations total.
    PC layout (start_pc = A):
      A   LOAD_IMM outer_reg n 0     ; outer reset
      A+1 LOAD_IMM inner_reg n 0     ; inner reset  [outer loop head]
      A+2 ADD 15 15 10 0             ; r15++         [inner loop head]
      A+3 SUB inner_reg inner_reg 10 0
      A+4 JNEZ inner_reg (A+2) 0    ; inner back
      A+5 SUB outer_reg outer_reg 10 0
      A+6 JNEZ outer_reg (A+1) 0    ; outer back (resets inner each iteration)
    """
    p = start_pc
    instrs = [
        f"LOAD_IMM {outer_reg} {n} 0",      # p
        f"LOAD_IMM {inner_reg} {n} 0",      # p+1  ← outer loop head
        f"ADD 15 15 10 0",                   # p+2  ← inner loop head
        f"SUB {inner_reg} {inner_reg} 10 0",# p+3
        f"JNEZ {inner_reg} {p + 2} 0",      # p+4  → inner head
        f"SUB {outer_reg} {outer_reg} 10 0",# p+5
        f"JNEZ {outer_reg} {p + 1} 0",      # p+6  → outer head (re-loads inner)
    ]
    return instrs, p + 7


def nested_loop_3d(r1: int, r2: int, r3: int, n: int, start_pc: int) -> tuple[list[str], int]:
    """Three nested loops of size n each.  r15 increments in innermost only.

    Counts n^3 iterations total.
    PC layout (start_pc = A):
      A   LOAD_IMM r1 n 0        ; init r1
      A+1 LOAD_IMM r2 n 0        ; init r2      [r1 loop head]
      A+2 LOAD_IMM r3 n 0        ; init r3      [r2 loop head]
      A+3 ADD 15 15 10 0         ; r15++         [r3 loop head]
      A+4 SUB r3 r3 10 0
      A+5 JNEZ r3 (A+3) 0       ; r3 back
      A+6 SUB r2 r2 10 0
      A+7 JNEZ r2 (A+2) 0       ; r2 back (resets r3)
      A+8 SUB r1 r1 10 0
      A+9 JNEZ r1 (A+1) 0       ; r1 back (resets r2)
    """
    p = start_pc
    instrs = [
        f"LOAD_IMM {r1} {n} 0",          # p
        f"LOAD_IMM {r2} {n} 0",          # p+1  ← r1 loop head
        f"LOAD_IMM {r3} {n} 0",          # p+2  ← r2 loop head
        f"ADD 15 15 10 0",               # p+3  ← r3 loop head
        f"SUB {r3} {r3} 10 0",          # p+4
        f"JNEZ {r3} {p + 3} 0",         # p+5  → r3 head
        f"SUB {r2} {r2} 10 0",          # p+6
        f"JNEZ {r2} {p + 2} 0",         # p+7  → r2 head (re-loads r3)
        f"SUB {r1} {r1} 10 0",          # p+8
        f"JNEZ {r1} {p + 1} 0",         # p+9  → r1 head (re-loads r2)
    ]
    return instrs, p + 10


def assemble(*instruction_groups: list[str], emit_count: int = 0) -> str:
    """Join preamble + instruction groups into a runnable program string."""
    lines = list(PREAMBLE)
    for grp in instruction_groups:
        lines.extend(grp)
    lines.append("HALT 0")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Build each strategy
# ---------------------------------------------------------------------------

def build_blind() -> str:
    """0 certs: 3D blind nested search.  Expected r15=N^3=64, mu=0."""
    instrs, _ = nested_loop_3d(1, 2, 3, N, PREAMBLE_PC)
    return assemble(instrs)


def build_1cert() -> str:
    """1 cert: certify dim1, blind-search dims 2+3.  Expected r15=N+N^2=20, mu=9."""
    pc = PREAMBLE_PC
    emit   = ["EMIT 0 . 0"]; pc += 1
    loop1, pc = loop_block(1, N, pc)
    nested, _  = nested_loop_2d(2, 3, N, pc)
    return assemble(emit, loop1, nested)


def build_2cert() -> str:
    """2 certs (geodesic): certify dims 1+2, search dim3.
    Expected r15=3N=12, mu=18."""
    pc = PREAMBLE_PC
    e1 = ["EMIT 0 . 0"]; pc += 1
    l1, pc = loop_block(1, N, pc)
    e2 = ["EMIT 0 . 0"]; pc += 1
    l2, pc = loop_block(2, N, pc)
    l3, _  = loop_block(3, N, pc)
    return assemble(e1, l1, e2, l2, l3)


def build_3cert() -> str:
    """3 certs: certify all dims.  Expected r15=3N=12, mu=27.
    Same steps as 2-cert but 9 more mu — last cert saves zero steps."""
    pc = PREAMBLE_PC
    e1 = ["EMIT 0 . 0"]; pc += 1
    l1, pc = loop_block(1, N, pc)
    e2 = ["EMIT 0 . 0"]; pc += 1
    l2, pc = loop_block(2, N, pc)
    e3 = ["EMIT 0 . 0"]; pc += 1
    l3, _  = loop_block(3, N, pc)
    return assemble(e1, l1, e2, l2, e3, l3)


def build_wrong_cert() -> str:
    """Wrong structure: pay 2 certs but exploit only 1 level of independence.

    Certifies dim1 correctly (EMIT before dim1 loop → N steps saved from N^2).
    Then certifies "dims 2+3 as a single joint unit" — which is a WRONG claim
    about the structure (dim2 and dim3 are actually SEPARATELY independent).
    The program then does a flat N^2 joint search of (dim2, dim3) together
    instead of two independent N-step searches.

    Both EMITs come BEFORE their respective searches (they certify their
    claimed structure up front).  The second cert is not functionless —
    it makes a false structural claim that causes the program to search the
    joint space instead of the factored space.

    Expected: r15 = N + N^2 = 20, mu = 18.
    Same mu as 2-cert, same steps as 1-cert.
    """
    pc = PREAMBLE_PC
    e1     = ["EMIT 0 . 0"]; pc += 1       # certify: dim1 is independent
    loop1, pc = loop_block(1, N, pc)        # search dim1 (exploits cert1)
    e2     = ["EMIT 0 . 0"]; pc += 1       # certify: dim2+dim3 as joint unit (WRONG)
    joint, _ = loop_block(2, N * N, pc)    # search joint (dim2,dim3) = N^2 steps
    return assemble(e1, loop1, e2, joint)   # both EMITs precede their searches


STRATEGIES: dict[str, dict] = {
    "blind":       {"build": build_blind,      "exp_steps": N**3,     "exp_mu": 0},
    "1-cert":      {"build": build_1cert,      "exp_steps": N + N**2, "exp_mu": 9},
    "2-cert":      {"build": build_2cert,      "exp_steps": 3 * N,    "exp_mu": 18},
    "3-cert":      {"build": build_3cert,      "exp_steps": 3 * N,    "exp_mu": 27},
    "wrong-cert":  {"build": build_wrong_cert, "exp_steps": N + N**2, "exp_mu": 18},
}


# ---------------------------------------------------------------------------
# Runner
# ---------------------------------------------------------------------------

def run_program(program: str, label: str) -> dict:
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".txt", delete=False, prefix="thiele_geo_"
    ) as f:
        f.write(program)
        path = f.name
    result = subprocess.run(
        [str(RUNNER), path],
        capture_output=True, text=True, timeout=30,
    )
    for line in result.stdout.splitlines():
        s = line.strip()
        if s.startswith("{"):
            return json.loads(s)
    raise RuntimeError(
        f"[{label}] no JSON in output.\nstdout: {result.stdout[:500]}\n"
        f"stderr: {result.stderr[:200]}"
    )


# ---------------------------------------------------------------------------
# Display
# ---------------------------------------------------------------------------

BAR_CHAR = "█"
BAR_SCALE = 20  # characters for N^3 steps


def steps_bar(steps: int) -> str:
    width = max(1, round(steps * BAR_SCALE / N**3))
    return BAR_CHAR * width


def total_cost(steps: int, mu: int, lam: float) -> float:
    return steps + lam * mu


def main() -> None:
    if not RUNNER.exists():
        print(f"ERROR: {RUNNER} not found.")
        print("Build with: cd build && ocamlfind ocamlc -package str -linkpkg "
              "thiele_core.ml extracted_vm_runner.ml -o extracted_vm_runner")
        sys.exit(1)

    print("\nRunning programs through extracted OCaml runner...")
    results: dict[str, dict] = {}
    for name, info in STRATEGIES.items():
        prog = info["build"]()
        out  = run_program(prog, name)
        results[name] = {"steps": out["regs"][15], "mu": out["mu"], "err": out["err"]}

    print()
    print("=" * 72)
    print("  MU-GEODESIC DEMO: 3D Factored Search, N=4")
    print("  Problem: find (3,3,3) in a 4×4×4 grid, dims are structurally independent")
    print("=" * 72)
    print()
    print(f"  {'Strategy':<24} {'Steps':>6} {'Mu':>5}  {'  Step bar':<22} Verified")
    print("  " + "-" * 67)

    for name, info in STRATEGIES.items():
        r = results[name]
        steps, mu = r["steps"], r["mu"]
        ok_s = "✓" if steps == info["exp_steps"] else f"✗(exp {info['exp_steps']})"
        ok_m = "✓" if mu    == info["exp_mu"]    else f"✗(exp {info['exp_mu']})"
        bar  = steps_bar(steps)
        note = " ← GEODESIC" if "geodesic" in name else ""
        print(f"  {name:<24} {steps:>6} {mu:>5}  {bar:<22} {ok_s} {ok_m}{note}")

    print()
    print("  Combined cost = steps + λ×mu  (λ = how many steps 1 mu is worth)")
    print()

    lam_values = [0.0, 0.5, 1.0, 2.0, 4.0, 8.0]
    col_w = 18
    names = list(STRATEGIES)
    print("  " + f"{'λ':<6}" + "".join(f"{n[:col_w-2]:<{col_w}}" for n in names))
    print("  " + "-" * (6 + col_w * len(names)))
    for lam in lam_values:
        costs = {n: total_cost(results[n]["steps"], results[n]["mu"], lam) for n in names}
        best  = min(costs, key=costs.get)
        row   = f"  {lam:<6.1f}"
        for n in names:
            c      = costs[n]
            marker = " ←" if n == best else "  "
            row   += f"{c:>7.1f}{marker:<{col_w - 8}}"
        print(row)

    print()
    r2    = results["2-cert"]
    r1    = results["1-cert"]
    cert3 = results["3-cert"]
    blind = results["blind"]
    wrong = results["wrong-cert"]

    # Compute λ crossover points from the actual machine-measured data.
    # At crossover: C_a(λ) = C_b(λ)  ⟹  steps_a + λ·mu_a = steps_b + λ·mu_b
    #                                ⟹  λ = (steps_a - steps_b) / (mu_b - mu_a)
    def crossover(ra: dict, rb: dict) -> float:
        dmu = rb["mu"] - ra["mu"]
        return (ra["steps"] - rb["steps"]) / dmu if dmu != 0 else float("inf")

    lam_2_1   = crossover(r2, r1)      # below this: 2-cert better; above: 1-cert better
    lam_1_b   = crossover(r1, blind)   # below this: 1-cert better; above: blind better

    print("  KEY OBSERVATIONS (derived from machine-measured data):")
    print()
    print(f"  1. LAST CERT SAVES ZERO STEPS")
    print(f"     2-cert: {r2['steps']} steps, {r2['mu']} mu")
    print(f"     3-cert: {cert3['steps']} steps, {cert3['mu']} mu  (same steps, +9 mu)")
    print(f"     The 3rd EMIT charges 9 mu and saves 0 steps: it is never optimal.")
    print(f"     Proven by StructuralAdvantage.last_emit_saves_zero_steps.")
    print()
    print(f"  2. MU BUYS STEPS — BUT THE EXCHANGE RATE DETERMINES THE GEODESIC")
    savings_2  = blind["steps"] - r2["steps"]
    savings_1  = blind["steps"] - r1["steps"]
    print(f"     Crossover 2-cert vs 1-cert: λ = {lam_2_1:.3f}")
    print(f"       λ < {lam_2_1:.3f}: 2-cert optimal  ({r2['steps']} steps, {r2['mu']} mu)")
    print(f"       λ ∈ [{lam_2_1:.3f}, {lam_1_b:.3f}): 1-cert optimal  ({r1['steps']} steps, {r1['mu']} mu)")
    print(f"       λ ≥ {lam_1_b:.3f}: blind optimal   ({blind['steps']} steps, 0 mu)")
    print(f"     At λ=1: 1-cert wins (cost {r1['steps'] + r1['mu']} vs 2-cert {r2['steps'] + r2['mu']})")
    print()
    print(f"  3. WRONG STRUCTURE WASTES MU")
    print(f"     wrong-cert: {wrong['steps']} steps, {wrong['mu']} mu  (EMIT precedes joint N²-search)")
    print(f"     1-cert:     {r1['steps']} steps, {r1['mu']} mu")
    print(f"     2-cert:     {r2['steps']} steps, {r2['mu']} mu")
    print(f"     wrong-cert pays the same mu as 2-cert but gets the same steps as 1-cert.")
    print(f"     The second EMIT made a false independence claim; the program still had to")
    print(f"     search N²={N**2} joint states instead of N+N={2*N} independent states.")
    print()
    print("=" * 72)
    print()


if __name__ == "__main__":
    main()
