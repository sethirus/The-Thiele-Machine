#!/usr/bin/env python3
"""validate_copilot_cert.py — Validate a THIELE-DECOMP certificate from Copilot output.

Reads source files for THIELE-DECOMP comment blocks, then runs the claimed
decomposition strategy through the Thiele Machine and compares it against:
  - The blind baseline (0 mu, N^k steps)
  - The geodesic (optimal cert count, minimum total cost)

Output tells you whether Copilot found the geodesic, over-certified, under-certified,
or used the wrong structure.

Usage:
    python3 scripts/validate_copilot_cert.py <source_file>
    python3 scripts/validate_copilot_cert.py --demo
"""

from __future__ import annotations

import json
import math
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Optional

REPO_ROOT = Path(__file__).resolve().parent.parent
RUNNER    = REPO_ROOT / "build" / "extracted_vm_runner"

# ---------------------------------------------------------------------------
# Thiele program builder (mirrors mu_geodesic_demo.py)
# ---------------------------------------------------------------------------

PREAMBLE_PC = 2   # FUEL is a directive; two LOAD_IMM preamble instructions use PCs 0,1


def loop_block(reg: int, n: int, start_pc: int) -> tuple[list[str], int]:
    """Flat loop: run n iterations, increment r15 each time."""
    return ([
        f"LOAD_IMM {reg} {n} 0",
        f"ADD 15 15 10 0",
        f"SUB {reg} {reg} 10 0",
        f"JNEZ {reg} {start_pc + 1} 0",
    ], start_pc + 4)


def nested_loop(registers: list[int], n: int, start_pc: int) -> tuple[list[str], int]:
    """k-deep nested loops of size n each, counting only at innermost level.

    Generates the pattern:
        LOAD_IMM r[0] n
        LOAD_IMM r[1] n        ← r[0] loop head
        ...
        LOAD_IMM r[k-1] n      ← r[k-2] loop head
        ADD 15 15 10 0         ← r[k-1] loop head
        SUB r[k-1] r[k-1] 10
        JNEZ r[k-1] → r[k-1] loop head
        SUB r[k-2] r[k-2] 10
        JNEZ r[k-2] → r[k-2] loop head
        ...
        SUB r[0] r[0] 10
        JNEZ r[0] → r[0] loop head
    """
    k = len(registers)
    if k == 0:
        return [], start_pc
    if k == 1:
        return loop_block(registers[0], n, start_pc)

    p = start_pc
    # LOAD_IMM instructions: one for each register (outermost first)
    loads = [f"LOAD_IMM {r} {n} 0" for r in registers]  # PCs: p .. p+k-1
    # The head of loop i (0-indexed) is:
    #   i=0: PC=p (load of r[0]) — but actually the "head" is where we jump back to
    #   For loop i, the head = PC of LOAD_IMM r[i]
    # The innermost loop head is PC=p+k-1 (LOAD_IMM of last register)
    # Wait — only the innermost has ADD. Let me redo:
    #   LOAD_IMM r[0]: PC=p          ← outer reset (initial, not a loop head)
    #   LOAD_IMM r[1]: PC=p+1        ← outer loop head (jump here to restart mid)
    #   LOAD_IMM r[2]: PC=p+2        ← mid loop head
    #   ...
    #   LOAD_IMM r[k-1]: PC=p+k-1   ← inner reset (not a loop head, just resets)
    # Actually the natural structure is different. Let me use the pattern from demo:
    #
    # For 2-deep (r0, r1):
    #   LOAD_IMM r0 n       PC=p      (initial, outer)
    #   LOAD_IMM r1 n       PC=p+1    ← outer_head (jump here after outer iter)
    #   ADD r15             PC=p+2    ← inner_head
    #   SUB r1              PC=p+3
    #   JNEZ r1 → p+2      PC=p+4   (inner)
    #   SUB r0              PC=p+5
    #   JNEZ r0 → p+1      PC=p+6   (outer → resets inner via LOAD_IMM at p+1)
    #
    # Generalizing to k-deep: the first LOAD_IMM (r[0]) is one-time initialization.
    # For i in 1..k-1: LOAD_IMM r[i] is the loop head of r[i-1].
    # The ADD is the loop head of r[k-1].
    # SUB and JNEZ for each register (innermost first).

    instrs: list[str] = []
    # Initial LOAD_IMM for r[0]
    instrs.append(f"LOAD_IMM {registers[0]} {n} 0")   # PC=p
    loop_heads: list[int] = []
    # LOAD_IMM for r[1..k-1] — these are the loop heads of r[0..k-2]
    for i in range(1, k):
        loop_heads.append(p + len(instrs))             # head of r[i-1]'s loop
        instrs.append(f"LOAD_IMM {registers[i]} {n} 0")
    # ADD: innermost loop head
    inner_head = p + len(instrs)
    instrs.append("ADD 15 15 10 0")
    # SUB + JNEZ for innermost
    instrs.append(f"SUB {registers[k-1]} {registers[k-1]} 10 0")
    instrs.append(f"JNEZ {registers[k-1]} {inner_head} 0")
    # SUB + JNEZ for each outer loop (innermost-to-outermost)
    for i in range(k - 2, -1, -1):
        head = loop_heads[i] if i < len(loop_heads) else p + 1
        instrs.append(f"SUB {registers[i]} {registers[i]} 10 0")
        instrs.append(f"JNEZ {registers[i]} {head} 0")

    return instrs, p + len(instrs)


def build_program(k_dims: int, k_cert: int, n: int) -> str:
    """Build a program certifying k_cert out of k_dims dimensions, each of size n.

    Certified dimensions are flat loops with EMIT before.
    Uncertified dimensions form a nested blind search.
    Returns the full program string.
    """
    lines = ["FUEL 10000", "LOAD_IMM 10 1 0", "LOAD_IMM 15 0 0"]
    pc = PREAMBLE_PC

    # k_cert certified dimensions (each: EMIT + flat loop of n)
    for i in range(k_cert):
        reg = i + 1
        lines.append("EMIT 0 . 0")
        pc += 1
        instrs, pc = loop_block(reg, n, pc)
        lines.extend(instrs)

    # remaining k_dims - k_cert dimensions: nested blind search
    blind_dims = k_dims - k_cert
    if blind_dims > 0:
        regs = [i + k_cert + 1 for i in range(blind_dims)]
        instrs, _ = nested_loop(regs, n, pc)
        lines.extend(instrs)

    lines.append("HALT 0")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Runner
# ---------------------------------------------------------------------------

def run_program(program: str) -> dict:
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".txt", delete=False, prefix="thiele_val_"
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
    raise RuntimeError(f"No JSON output.\nstdout: {result.stdout[:500]}")


# ---------------------------------------------------------------------------
# Certificate parser
# ---------------------------------------------------------------------------

CERT_RE = re.compile(
    r'THIELE-DECOMP:\s*(\{.*?\})',
    re.DOTALL | re.MULTILINE,
)


def parse_cert(text: str) -> Optional[dict]:
    """Extract and parse the first THIELE-DECOMP block in text."""
    match = CERT_RE.search(text)
    if not match:
        return None
    raw = match.group(1)
    # Strip comment prefixes (#, //, *) from each line
    cleaned = "\n".join(
        re.sub(r'^\s*[#/*]+\s?', '', line)
        for line in raw.splitlines()
    )
    try:
        return json.loads(cleaned)
    except json.JSONDecodeError as e:
        raise ValueError(f"Could not parse THIELE-DECOMP block: {e}\nRaw:\n{cleaned}")


# ---------------------------------------------------------------------------
# Geodesic computation
# ---------------------------------------------------------------------------

def strategy_cost(kc: int, k: int, n: int) -> tuple[int, int]:
    """Return (steps, mu) for a given k_cert strategy."""
    steps = kc * n + (n ** (k - kc) if k - kc > 0 else 0)
    mu    = kc * 9
    return steps, mu


def geodesic(k: int, n: int, lam: float = 1.0) -> tuple[int, int, int]:
    """Find the optimal k_cert for k dimensions of size n at exchange rate lam.

    Returns (best_k_cert, best_steps, best_mu).
    """
    best_cost = float("inf")
    best = (0, n**k, 0)
    for kc in range(k + 1):
        steps, mu = strategy_cost(kc, k, n)
        cost = steps + lam * mu
        if cost < best_cost:
            best_cost = cost
            best = (kc, steps, mu)
    return best


def optimal_lambda_range(kc: int, k: int, n: int) -> tuple[float, float]:
    """Return the range of λ values for which kc-cert is the optimal strategy.

    The marginal savings from going kc-1 → kc certs is:
        saved_steps = steps(kc-1) - steps(kc)
        extra_mu    = 9
    kc-cert is better than (kc-1)-cert when: saved_steps > 9 * lam
    i.e., lam < saved_steps / 9

    Returns (lam_min, lam_max) where kc is optimal.
    """
    steps_kc, _ = strategy_cost(kc, k, n)
    lam_lo = 0.0
    lam_hi = float("inf")
    if kc > 0:
        steps_prev, _ = strategy_cost(kc - 1, k, n)
        saved = steps_prev - steps_kc
        # kc better than kc-1 when: saved > 9*lam  →  lam < saved/9
        lam_hi = min(lam_hi, saved / 9.0)
    if kc < k:
        steps_next, _ = strategy_cost(kc + 1, k, n)
        saved_next = steps_kc - steps_next
        # kc+1 better than kc when: saved_next > 9*lam  →  lam < saved_next/9
        # so kc stays optimal when: lam >= saved_next/9
        lam_lo = max(lam_lo, saved_next / 9.0)
    return (lam_lo, lam_hi)


# ---------------------------------------------------------------------------
# Validation
# ---------------------------------------------------------------------------

def validate(cert: dict) -> None:
    dims       = cert.get("dimensions", [])
    certified  = cert.get("certified", [])
    n          = int(cert.get("search_size_per_dim", 4))
    k          = len(dims)
    k_cert     = len(certified)
    problem    = cert.get("problem", "(unnamed)")
    claim      = cert.get("independence_claim", "(no claim provided)")

    if k == 0:
        print("ERROR: no dimensions declared in certificate.")
        return
    if k_cert > k:
        print(f"ERROR: certified ({k_cert}) > total dimensions ({k}).")
        return

    print(f"  Problem:    {problem}")
    print(f"  Dims ({k}):    {', '.join(dims)}")
    print(f"  Certified:  {', '.join(certified) if certified else '(none)'}")
    print(f"  Claim:      {claim}")
    print(f"  N per dim:  {n}")
    print()

    # Run all strategies from 0-cert to k-cert
    bar_scale = max(1, n**k)
    print(f"  {'Strategy':<22} {'Steps':>6} {'Mu':>5}  {'Cost(λ=1)':>9}  "
          f"{'Optimal when λ=':>18}  Bar")
    print("  " + "-" * 70)

    results: dict[int, dict] = {}
    for kc in range(k + 1):
        prog  = build_program(k, kc, n)
        out   = run_program(prog)
        steps = out["regs"][15]
        mu    = out["mu"]
        results[kc] = {"steps": steps, "mu": mu}

    for kc, r in results.items():
        steps, mu = r["steps"], r["mu"]
        total = steps + mu
        lam_lo, lam_hi = optimal_lambda_range(kc, k, n)
        if lam_lo >= lam_hi:
            lam_str = "never"
        elif lam_hi == float("inf"):
            lam_str = f"≥ {lam_lo:.2f}"
        elif lam_lo == 0.0:
            lam_str = f"< {lam_hi:.2f}"
        else:
            lam_str = f"{lam_lo:.2f} – {lam_hi:.2f}"
        bar   = "█" * max(1, round(steps * 12 / bar_scale))
        tag   = f"{kc}-cert" + (" (YOURS)" if kc == k_cert else "")
        print(f"  {tag:<22} {steps:>6} {mu:>5}  {total:>9}  {lam_str:>18}  {bar}")

    print()

    # Verdict at λ=1, plus show the full λ range
    your_r   = results[k_cert]
    your_lo, your_hi = optimal_lambda_range(k_cert, k, n)

    if your_hi == float("inf"):
        your_range = f"λ ≥ {your_lo:.2f} — includes λ=1"
        is_geodesic_at_lam1 = True
    elif your_lo == 0.0:
        your_range = f"λ < {your_hi:.2f}"
        is_geodesic_at_lam1 = (1.0 < your_hi)
    else:
        your_range = f"{your_lo:.2f} ≤ λ < {your_hi:.2f}"
        is_geodesic_at_lam1 = (your_lo <= 1.0 < your_hi)

    if is_geodesic_at_lam1:
        print(f"  VERDICT: ✓ GEODESIC at λ=1 — your decomposition is mu-optimal")
        print(f"  when 1 mu is worth 1 step.  Your strategy is optimal for {your_range}.")
    else:
        best_kc, _, _ = geodesic(k, n, lam=1.0)
        best_r = results[best_kc]
        best_lo, best_hi = optimal_lambda_range(best_kc, k, n)
        if best_hi == float("inf"):
            best_range = f"λ ≥ {best_lo:.2f}"
        else:
            best_range = f"λ < {best_hi:.2f}"

        if k_cert < best_kc:
            extra_steps = your_r["steps"] - best_r["steps"]
            extra_mu    = best_r["mu"] - your_r["mu"]
            print(f"  VERDICT: UNDER-CERTIFIED at λ=1.")
            print(f"  {best_kc}-cert saves {extra_steps} more steps for {extra_mu} more mu.")
            print(f"  Your strategy IS optimal for {your_range}.")
        else:
            wasted = your_r["mu"] - best_r["mu"]
            print(f"  VERDICT: OVER-CERTIFIED at λ=1.")
            print(f"  The extra cert(s) cost {wasted} mu but saved 0 steps (at this N).")
            print(f"  Your strategy IS optimal for {your_range}.")
        print(f"  At λ=1, {best_kc}-cert is optimal (optimal for {best_range}).")


# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------

DEMO_SOURCE = '''
def find_in_3d_grid(grid, target_x, target_y, target_z):
    """Find target in a 3D grid where axes are independent."""
    # Search each axis independently after certifying independence
    for x in range(grid.size_x):
        for y in range(grid.size_y):
            for z in range(grid.size_z):
                if grid[x][y][z] == (target_x, target_y, target_z):
                    return (x, y, z)
    return None

# THIELE-DECOMP: {
#   "problem": "find (target_x, target_y, target_z) in independent 3D grid",
#   "dimensions": ["x_axis", "y_axis", "z_axis"],
#   "certified": ["x_axis", "y_axis"],
#   "search_size_per_dim": 4,
#   "independence_claim": "grid axes are orthogonal; cell (x,y,z) depends only on its own axis values"
# }
'''

DEMO_OVER = '''
def solve_partitioned_problem(data):
    """Solve three independent sub-problems."""
    pass

# THIELE-DECOMP: {
#   "problem": "three independent sub-problems each with 4 states",
#   "dimensions": ["part_A", "part_B", "part_C"],
#   "certified": ["part_A", "part_B", "part_C"],
#   "search_size_per_dim": 4,
#   "independence_claim": "parts are data-disjoint with no shared state"
# }
'''

DEMO_WRONG = '''
def wrong_decomp(data):
    """Claimed 2 certs but wrong grouping."""
    pass

# THIELE-DECOMP: {
#   "problem": "three independent sub-problems, but treating B+C as a unit",
#   "dimensions": ["part_A", "part_BC_joint", "part_D"],
#   "certified": ["part_A", "part_D"],
#   "search_size_per_dim": 4,
#   "independence_claim": "A and D are independent; B+C treated as joint"
# }
'''


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    if not RUNNER.exists():
        print(f"ERROR: {RUNNER} not found.")
        print("Build with: cd build && ocamlfind ocamlc -package str -linkpkg "
              "thiele_core.ml extracted_vm_runner.ml -o extracted_vm_runner")
        sys.exit(1)

    args = sys.argv[1:]

    if "--demo" in args or not args:
        demos = [
            ("Copilot suggests GEODESIC decomposition", DEMO_SOURCE),
            ("Copilot OVER-CERTIFIES (last cert saves nothing)", DEMO_OVER),
        ]
        for title, source in demos:
            print("=" * 68)
            print(f"  {title}")
            print("=" * 68)
            cert = parse_cert(source)
            if cert is None:
                print("  No THIELE-DECOMP block found.")
                continue
            validate(cert)
            print()
        return

    for path_str in args:
        path = Path(path_str)
        if not path.exists():
            print(f"ERROR: {path} not found.")
            continue
        text = path.read_text()
        print(f"{'=' * 68}")
        print(f"  Validating: {path}")
        print(f"{'=' * 68}")
        cert = parse_cert(text)
        if cert is None:
            print("  No THIELE-DECOMP block found in this file.")
            print("  Add a THIELE-DECOMP comment block (see copilot-instructions.md).")
        else:
            validate(cert)
        print()


if __name__ == "__main__":
    main()
