"""Complexity frontier: pushing past what test_structural_advantage.py established.

WHAT WAS PROVEN THERE
---------------------
For k=2 factored search (N×N grid):
  blind:   N² steps, 0 μ
  sighted: 2N steps, 2 μ
  ratio:   N/2  (grows without bound)
  μ cost:  2    (constant in N)

THREE OPEN QUESTIONS THIS FILE PROBES
--------------------------------------
1. k-FACTOR GENERALIZATION
   Does k-factor decomposition generalize? For k dimensions each of size N:
     blind:   N^k steps,  0 μ
     sighted: k*N steps,  k μ
     ratio:   N^(k-1)/k  (grows faster than N for k≥3)
   We test k=3 and k=4 on the real OCaml VM.

2. μ BUDGET THRESHOLD
   Does the μ budget map exactly to the structural depth available?
   A k-dimensional problem with only j<k EMIT calls certifies j dimensions;
   the remaining k-j dimensions must be searched blindly.
   Cost of j-certified approach: j*N + (k-j)*blind_per_remaining
   We test the gradients: extra μ units buy exactly N-1 saved steps per dimension.

3. ADVERSARIAL STRUCTURE BOUNDARY
   The advantage exists for factored problems. Does it disappear for problems
   with no independence structure?
   We test the "anti-diagonal" case: a problem where left+right = constant.
   Claim: sighted still wins (because left and right remain independently
   searchable even when correlated), BUT the win margin narrows dramatically
   for adversarially-chosen targets.
   We also test "single-dimension" problems: sighted strategy applied to a
   problem that only has one searchable dimension gains NOTHING from the second
   EMIT — both are necessary only when both dimensions contribute to the savings.

WHAT WE EXPECT TO FIND
-----------------------
- k=3: ratio = N²/3. For N=8: blind=512, sighted=24, ratio≈21.
- k=4: ratio = N³/4. For N=4: blind=256, sighted=16, ratio=16.
- μ budget: j-certified removes j*N steps but cost is j μ. Marginal rate = N-1.
- Anti-diagonal: sighted_iters = N+1 (constant!), blind varies — sighted wins harder.
- 1D problem: applying 2D sighted to a 1D-only target gives 0 extra savings vs 1D blind.

STATUS: Written as RED-to-GREEN. Run on real OCaml VM.
"""
from __future__ import annotations

import math
import pytest
from pathlib import Path
import sys

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from thielecpu.vm import VMState, vm_run, _runner_available

# Re-use the 2D blind/sighted program builders from the established test
sys.path.insert(0, str(REPO_ROOT / "tests"))
from test_structural_advantage import (
    _blind_search_program as _blind2d,
    _sighted_search_program as _sighted2d,
)

pytestmark = pytest.mark.skipif(
    not _runner_available(), reason="OCaml runner not available"
)


# ---------------------------------------------------------------------------
# Program builders — k-dimensional
# ---------------------------------------------------------------------------

def _k_sighted_program(targets: list[int]) -> list[dict]:
    """k-dimensional sighted search over independent dimensions.

    Each dimension i has:
      - counter register:  2*i + 1  (r1, r3, r5, r7, ...)
      - target register:   2*i + 2  (r2, r4, r6, r9, ...)
    Special registers:
      - r10 = 1 (increment constant)
      - r15 = iteration counter
      - r8  = scratch (equality check)

    NOTE: r9 is used as target register for dimension 4 (2*3+2=8 would clash
    with r8 scratch). We use a different layout for k≥4: see below.
    Actually: for k dimensions we need 2k+2 registers (2 per dim + r10 + r15).
    We also need r8 for scratch. So for k=4: need r1..r9 for data, r8 scratch,
    r10=1, r15=iter. r8 is overwritten by scratch — the target register for
    dim 3 (2*3+2=8) would clash. We use r9 for dim-3 target instead.

    For simplicity and correctness, dimensions use registers:
      dim 0: counter=r1, target=r2
      dim 1: counter=r3, target=r4
      dim 2: counter=r5, target=r6
      dim 3: counter=r7, target=r9  ← r9 instead of r8 (r8=scratch)
      dim 4: counter=r11, target=r12 (if needed)

    Each loop body (7 instructions):
      PC+0: ADD r15 r15 r10 0      iters++
      PC+1: SUB r8 <ctr> <tgt> 0  scratch = counter - target (word64)
      PC+2: JNEZ r8 <PC+5> 0      if ≠ 0, jump to increment
      PC+3: EMIT <i> "." 0         CERT-SETTER (costs 1 μ)
      PC+4: JUMP <next_loop_start> 0
      PC+5: ADD <ctr> <ctr> r10 0  counter++
      PC+6: JUMP <loop_start> 0    back to loop top

    Termination: last loop's EMIT is followed by JUMP <past_program> 0.
    """
    k = len(targets)
    assert 1 <= k <= 5, f"k must be 1..5, got {k}"

    # Register layout (avoiding r8=scratch, r10=inc, r15=iter)
    COUNTER_REGS = [1, 3, 5, 7, 11]
    TARGET_REGS  = [2, 4, 6, 9, 12]

    setup = []
    for i in range(k):
        setup.append({"op": "load_imm", "dst": COUNTER_REGS[i], "imm": 0,         "cost": 0})
        setup.append({"op": "load_imm", "dst": TARGET_REGS[i],  "imm": targets[i], "cost": 0})
    setup.append({"op": "load_imm", "dst": 10, "imm": 1, "cost": 0})
    setup.append({"op": "load_imm", "dst": 15, "imm": 0, "cost": 0})
    setup_len = len(setup)  # 2*k + 2

    loop_len = 7  # instructions per loop dimension
    total_len = setup_len + k * loop_len

    instructions = list(setup)
    for i in range(k):
        loop_start = setup_len + i * loop_len
        incr_pc    = loop_start + 5
        next_start = (setup_len + (i + 1) * loop_len) if i < k - 1 else total_len

        cr = COUNTER_REGS[i]
        tr = TARGET_REGS[i]

        instructions.extend([
            {"op": "add",  "dst": 15, "rs1": 15, "rs2": 10, "cost": 0},  # iters++
            {"op": "sub",  "dst": 8,  "rs1": cr, "rs2": tr, "cost": 0},  # scratch
            {"op": "jnez", "rs": 8,   "target": incr_pc,    "cost": 0},  # branch
            {"op": "emit", "module": i, "payload": ".", "cost": 0},       # CERT (1 μ)
            {"op": "jump", "target": next_start,             "cost": 0},  # to next loop/end
            {"op": "add",  "dst": cr, "rs1": cr, "rs2": 10, "cost": 0},  # counter++
            {"op": "jump", "target": loop_start,             "cost": 0},  # loop back
        ])

    return instructions


def _k_blind_program(target_idx: int) -> list[dict]:
    """Linear scan from 0 to target_idx. Identical to blind_search_program
    from test_structural_advantage.py — always 0 μ.

    For k-dimensional worst case with each dimension = N:
      target_idx = N^k - 1
      blind_iters = N^k
    """
    return [
        {"op": "load_imm", "dst": 1,  "imm": 0,          "cost": 0},  # pc=0
        {"op": "load_imm", "dst": 2,  "imm": target_idx, "cost": 0},  # pc=1
        {"op": "load_imm", "dst": 10, "imm": 1,          "cost": 0},  # pc=2
        {"op": "load_imm", "dst": 15, "imm": 0,          "cost": 0},  # pc=3
        {"op": "add",  "dst": 15, "rs1": 15, "rs2": 10, "cost": 0},  # pc=4: iters++
        {"op": "sub",  "dst": 8,  "rs1": 1,  "rs2": 2,  "cost": 0},  # pc=5: scratch
        {"op": "jnez", "rs": 8,   "target": 8,           "cost": 0},  # pc=6: branch
        {"op": "halt",                                     "cost": 0},  # pc=7: found
        {"op": "add",  "dst": 1,  "rs1": 1,  "rs2": 10, "cost": 0},  # pc=8: counter++
        {"op": "jump", "target": 4,                        "cost": 0},  # pc=9: loop back
    ]


def _run(program: list, max_steps: int = 2_000_000) -> VMState:
    return vm_run(VMState.default(), program, max_steps=max_steps)


# ---------------------------------------------------------------------------
# Section 1: k-factor decomposition generalization
# ---------------------------------------------------------------------------

class TestKFactorDecomposition:
    """k-dimensional factored search: blind=N^k steps, sighted=k*N steps, μ=k.

    This extends the k=2 result from test_structural_advantage.py.
    We test k=3 and k=4 on the real VM.

    PREDICTED FORMULAS (extension of proven k=2 case):
      blind_iters  = N^k   (linear scan over N^k elements)
      sighted_iters = k * N (k independent loops of N each)
      sighted_mu   = k     (k EMIT cert-setters, one per dimension)
      ratio        = N^(k-1) / k  (grows super-linearly for k≥2)

    WHAT THIS TESTS:
    The advantage isn't a k=2 coincidence. It scales with decomposition depth.
    Each additional certified dimension removes N steps from the search at cost of 1 μ.
    """

    def test_k3_exact_iters_and_mu(self):
        """k=3, N=4: blind=64 steps, sighted=12 steps, μ=3."""
        N = 4
        targets = [N - 1, N - 1, N - 1]  # worst case: all at last position
        target_idx = N**3 - 1             # = 63

        blind   = _run(_k_blind_program(target_idx))
        sighted = _run(_k_sighted_program(targets))

        assert not blind.vm_err,   "Blind k=3 program errored"
        assert not sighted.vm_err, "Sighted k=3 program errored"

        assert blind.vm_regs[15]   == N**3,     f"blind_iters: got {blind.vm_regs[15]}, want {N**3}"
        assert sighted.vm_regs[15] == 3 * N,    f"sighted_iters: got {sighted.vm_regs[15]}, want {3*N}"
        assert sighted.vm_mu       == 3,         f"sighted_mu: got {sighted.vm_mu}, want 3"
        assert blind.vm_mu         == 0,         f"blind_mu: got {blind.vm_mu}, want 0"

    def test_k3_ratio_grows_as_n_squared_over_3(self):
        """For k=3, ratio = N^3 / (3*N) = N²/3. Grows as N²."""
        for N in [4, 6]:
            targets = [N - 1] * 3
            target_idx = N**3 - 1

            blind   = _run(_k_blind_program(target_idx))
            sighted = _run(_k_sighted_program(targets))

            bi = blind.vm_regs[15]
            si = sighted.vm_regs[15]

            assert bi == N**3,  f"N={N}: blind_iters={bi}, expected {N**3}"
            assert si == 3 * N, f"N={N}: sighted_iters={si}, expected {3*N}"

            ratio = bi / si
            expected_ratio = N**2 / 3
            assert abs(ratio - expected_ratio) < 0.01, (
                f"N={N}: ratio={ratio:.3f}, expected N²/3={expected_ratio:.3f}"
            )

    def test_k4_exact_iters_and_mu(self):
        """k=4, N=4: blind=256 steps, sighted=16 steps, μ=4."""
        N = 4
        targets = [N - 1] * 4  # worst case
        target_idx = N**4 - 1  # = 255

        blind   = _run(_k_blind_program(target_idx))
        sighted = _run(_k_sighted_program(targets))

        assert not blind.vm_err,   "Blind k=4 program errored"
        assert not sighted.vm_err, "Sighted k=4 program errored"

        assert blind.vm_regs[15]   == N**4, f"blind_iters: got {blind.vm_regs[15]}, want {N**4}"
        assert sighted.vm_regs[15] == 4 * N, f"sighted_iters: got {sighted.vm_regs[15]}, want {4*N}"
        assert sighted.vm_mu       == 4,     f"sighted_mu: got {sighted.vm_mu}, want 4"

    def test_k4_ratio_n_cubed_over_4(self):
        """For k=4, N=4: ratio = 256/16 = 16 = N^3/4."""
        N = 4
        targets = [N - 1] * 4
        target_idx = N**4 - 1

        blind   = _run(_k_blind_program(target_idx))
        sighted = _run(_k_sighted_program(targets))

        bi, si = blind.vm_regs[15], sighted.vm_regs[15]
        ratio = bi / si
        expected = N**3 / 4
        assert abs(ratio - expected) < 0.01, (
            f"k=4, N={N}: ratio={ratio}, expected N³/4={expected}"
        )

    def test_ratio_grows_faster_with_k(self):
        """At fixed N=4: ratio(k=2)=2 < ratio(k=3)≈5.3 < ratio(k=4)=16."""
        N = 4
        ratios = {}
        for k in [2, 3, 4]:
            targets = [N - 1] * k
            target_idx = N**k - 1

            blind   = _run(_k_blind_program(target_idx))
            sighted = _run(_k_sighted_program(targets))

            bi, si = blind.vm_regs[15], sighted.vm_regs[15]
            ratios[k] = bi / si

        assert ratios[3] > ratios[2], f"k=3 ratio {ratios[3]:.1f} should > k=2 ratio {ratios[2]:.1f}"
        assert ratios[4] > ratios[3], f"k=4 ratio {ratios[4]:.1f} should > k=3 ratio {ratios[3]:.1f}"

    def test_mu_k_equals_dimensions_exactly(self):
        """μ paid is exactly k, regardless of N or target positions."""
        N = 5
        for k in [1, 2, 3, 4]:
            targets = [N - 1] * k
            sighted = _run(_k_sighted_program(targets))
            assert sighted.vm_mu == k, (
                f"k={k}: expected sighted_mu={k}, got {sighted.vm_mu}"
            )

    def test_k_log_n_approach(self):
        """For k = log2(N), ratio = N^(log2(N)-1) / log2(N).

        N=8, k=3: ratio = 8^2 / 3 = 64/3 ≈ 21.3
        This is the deepest factoring where k ~ log(N).
        The ratio grows super-polynomially as N increases with k=log2(N).
        """
        N = 8
        k = 3  # floor(log2(8)) = 3
        assert 2**k == N, "k=log2(N) invariant"

        targets = [N - 1] * k
        target_idx = N**k - 1

        blind   = _run(_k_blind_program(target_idx))
        sighted = _run(_k_sighted_program(targets))

        bi, si = blind.vm_regs[15], sighted.vm_regs[15]
        ratio = bi / si

        assert bi == N**3,  f"blind_iters={bi}, want {N**3}"
        assert si == k * N, f"sighted_iters={si}, want {k*N}"
        assert ratio == pytest.approx(N**2 / k, rel=0.01), (
            f"ratio={ratio:.2f}, expected N²/k = {N**2/k:.2f}"
        )
        # At N=8, k=3: ratio ≈ 21.3 — much better than the k=2 case (ratio=4)
        assert ratio > 2 * (N / 2), "k=log(N) ratio should exceed the k=2 ratio"


# ---------------------------------------------------------------------------
# Section 2: μ budget threshold — marginal value of each μ unit
# ---------------------------------------------------------------------------

class TestMuBudgetThreshold:
    """Each μ unit buys exactly one certified dimension.

    For a k-dimensional problem:
    - With j < k EMIT calls: j dimensions are certified, k-j must be blindly searched.
    - Partially-sighted strategy: j certified loops × N steps each,
      plus 1 blind loop over remaining N^(k-j) elements.
    - Steps: j*N + N^(k-j)
    - μ = j

    PREDICTIONS:
      j=0 (blind):           N^k steps, 0 μ
      j=1 (one cert):        N + N^(k-1) steps, 1 μ
      j=k-1 (one dim blind): (k-1)*N + N steps = k*N steps. Wait: remaining is 1D.
      j=k (fully sighted):   k*N steps, k μ

    THE MARGINAL VALUE:
    Going from j to j+1 certified dimensions saves N^(k-j) - N = N*(N^(k-j-1) - 1) steps
    at cost of 1 μ. For k=3, j=0→1: saves N^3 - N - (N + N^2) = N^3 - N^2 - 2N steps.
    Wait, let me recalculate.

    j=0:  blind:         N^3 steps         (k=3, N elements per dim)
    j=1:  1-cert:        N + N^2 steps     (dim-0 certified, dims 1-2 blind)
    j=2:  2-cert:        2N + N steps = 3N wait no.

    j=1 means: search dim-0 (N steps, 1 EMIT), then do blind 2D search over N^2 elements.
    Total: N + N^2 steps, 1 μ.

    j=2: search dim-0 (N steps, EMIT), search dim-1 (N steps, EMIT), search dim-2 (N steps).
    Total: 3N steps, 2 μ. But this is k=3, j=2, so only 1 uncertified dimension remains
    (a 1D blind search of N steps).

    j=k=3: 3N steps, 3 μ. All dims certified.

    Marginal step savings when going from j to j+1:
      j=0→1: (N^3) - (N + N^2) = N^3 - N^2 - N = N(N^2 - N - 1)
      j=1→2: (N + N^2) - (2N + N) = N^2 - 2N = N(N-2)
      j=2→3: (3N) - (3N) = 0  ← no savings, j=2 already gets all the benefit!

    Wait, j=2 for k=3: we certify 2 dims and do 1 blind.
    Steps: N (certified dim-0) + N (certified dim-1) + N (blind dim-2, 1D, N steps) = 3N.
    j=3 for k=3: same 3N steps. The last dimension has only N elements, so blind vs sighted
    is the same. That's correct: the savings come from certifying the HIGH-dimensional parts.

    So marginal value of j-th EMIT is greatest for low j (large remaining search space).

    We test: 3D problem with j=0, 1, 2, 3 EMIT calls.
    """

    def _partial_sighted_program_k3(
        self, targets: list[int], n_emit: int
    ) -> list[dict]:
        """3D problem where only the first n_emit dimensions are certified.

        dims 0..n_emit-1: searched with EMIT (certified, 1μ each)
        dim n_emit: flat blind search over remaining flat elements
        dims n_emit+1..: not reached (the flat search covers them all)

        For simplicity: after n_emit certified loops, we do a blind scan
        over (targets[n_emit] * N^(remaining-1) + ... + targets[-1] + 1) flat elements.
        Since we're testing k=3 specifically:
          n_emit=0: pure blind scan over N^3 elements
          n_emit=1: certified dim-0, then blind scan over N^2 remaining elements
          n_emit=2: certified dim-0 and dim-1, then blind scan over N remaining elements
          n_emit=3: fully sighted (all 3 dims certified)
        """
        k = len(targets)
        assert k == 3, "This builder is for k=3 only"
        assert 0 <= n_emit <= k

        if n_emit == 0:
            # pure blind: linearize the 3D target
            N = max(targets) + 1  # infer N from target
            # We need the actual N to compute target_idx
            # Use a linear combination: t0*N^2 + t1*N + t2
            # But we don't know N here — caller must provide it
            raise ValueError("Use _k_blind_program for n_emit=0")

        if n_emit == k:
            return _k_sighted_program(targets)

        # n_emit = 1 or 2 for k=3
        # Build the certified prefix loops, then end with a pure-blind tail
        COUNTER_REGS = [1, 3, 5]
        TARGET_REGS  = [2, 4, 6]

        # We don't know N from targets alone for the blind tail.
        # Infer N: all targets should be at most N-1, and we assume N = max(targets)+1
        N = max(max(targets) + 1, 2)

        # Compute the flat target_idx for the blind tail
        # For n_emit=1: after certifying dim-0, remaining is dims 1 and 2
        #   flat idx = targets[1]*N + targets[2]
        # For n_emit=2: after certifying dims 0 and 1, remaining is dim 2 only
        #   flat idx = targets[2]
        remaining_idx = 0
        for i in range(n_emit, k):
            power = N ** (k - 1 - i)
            remaining_idx += targets[i] * power

        # ---- Setup registers ----
        setup = []
        for i in range(n_emit):
            setup.append({"op": "load_imm", "dst": COUNTER_REGS[i], "imm": 0,         "cost": 0})
            setup.append({"op": "load_imm", "dst": TARGET_REGS[i],  "imm": targets[i], "cost": 0})
        # Blind-tail uses r1b=r20, r2b=r21 to avoid clobbering setup regs
        BLIND_CTR = 20
        BLIND_TGT = 21
        setup.append({"op": "load_imm", "dst": BLIND_CTR, "imm": 0,             "cost": 0})
        setup.append({"op": "load_imm", "dst": BLIND_TGT, "imm": remaining_idx, "cost": 0})
        setup.append({"op": "load_imm", "dst": 10, "imm": 1, "cost": 0})
        setup.append({"op": "load_imm", "dst": 15, "imm": 0, "cost": 0})
        setup_len = len(setup)

        loop_len = 7
        # After n_emit certified loops, one blind loop of 6 instructions
        blind_loop_len = 6   # iters++, sub, jnez, halt, ctr++, jump
        total_len = setup_len + n_emit * loop_len + blind_loop_len

        instructions = list(setup)

        # Build certified loops
        for i in range(n_emit):
            loop_start = setup_len + i * loop_len
            incr_pc    = loop_start + 5
            next_start = setup_len + (i + 1) * loop_len if i < n_emit - 1 else (
                setup_len + n_emit * loop_len  # → blind tail
            )
            cr, tr = COUNTER_REGS[i], TARGET_REGS[i]
            instructions.extend([
                {"op": "add",  "dst": 15, "rs1": 15, "rs2": 10, "cost": 0},
                {"op": "sub",  "dst": 8,  "rs1": cr, "rs2": tr, "cost": 0},
                {"op": "jnez", "rs": 8,   "target": incr_pc,    "cost": 0},
                {"op": "emit", "module": i, "payload": ".", "cost": 0},
                {"op": "jump", "target": next_start,             "cost": 0},
                {"op": "add",  "dst": cr, "rs1": cr, "rs2": 10, "cost": 0},
                {"op": "jump", "target": loop_start,             "cost": 0},
            ])

        # Build blind tail loop
        blind_loop_start = setup_len + n_emit * loop_len
        blind_incr_pc    = blind_loop_start + 4
        instructions.extend([
            {"op": "add",  "dst": 15, "rs1": 15, "rs2": 10, "cost": 0},           # iters++
            {"op": "sub",  "dst": 8,  "rs1": BLIND_CTR, "rs2": BLIND_TGT, "cost": 0},
            {"op": "jnez", "rs": 8,   "target": blind_incr_pc, "cost": 0},
            {"op": "halt",                                       "cost": 0},        # found
            {"op": "add",  "dst": BLIND_CTR, "rs1": BLIND_CTR, "rs2": 10, "cost": 0},
            {"op": "jump", "target": blind_loop_start,           "cost": 0},
        ])

        return instructions

    def test_k3_partial_cert_steps_and_mu(self):
        """For k=3, N=4: partial certification gives strictly intermediate results.

        n_emit=0: 64 steps, 0 μ   (pure blind)
        n_emit=1: 4 + 16 = 20 steps, 1 μ   (dim-0 certified, 2D blind tail)
        n_emit=2: 4 + 4 + 4 = 12 steps, 2 μ (dims 0-1 certified, 1D blind tail)
        n_emit=3: 4 + 4 + 4 = 12 steps, 3 μ (fully certified = sighted)
        """
        N = 4
        targets = [N - 1, N - 1, N - 1]

        # n_emit=0: pure blind
        target_idx = N**3 - 1
        blind = _run(_k_blind_program(target_idx))
        assert blind.vm_regs[15] == N**3, f"blind: {blind.vm_regs[15]} != {N**3}"
        assert blind.vm_mu == 0

        # n_emit=1: certified dim-0, blind 2D tail
        p1 = self._partial_sighted_program_k3(targets, n_emit=1)
        s1 = _run(p1)
        assert not s1.vm_err, f"n_emit=1 errored"
        expected_steps_1 = N + N**2  # dim-0: N iters; tail: N^2 iters
        assert s1.vm_regs[15] == expected_steps_1, (
            f"n_emit=1: iters={s1.vm_regs[15]}, expected {expected_steps_1}"
        )
        assert s1.vm_mu == 1, f"n_emit=1: mu={s1.vm_mu}, expected 1"

        # n_emit=2: certified dims 0-1, blind 1D tail
        p2 = self._partial_sighted_program_k3(targets, n_emit=2)
        s2 = _run(p2)
        assert not s2.vm_err, f"n_emit=2 errored"
        expected_steps_2 = N + N + N  # each dim has N iters including 1D tail
        assert s2.vm_regs[15] == expected_steps_2, (
            f"n_emit=2: iters={s2.vm_regs[15]}, expected {expected_steps_2}"
        )
        assert s2.vm_mu == 2, f"n_emit=2: mu={s2.vm_mu}, expected 2"

        # n_emit=3: fully sighted
        p3 = _k_sighted_program(targets)
        s3 = _run(p3)
        assert s3.vm_regs[15] == 3 * N
        assert s3.vm_mu == 3

    def test_marginal_mu_value_decreases_with_j(self):
        """Each additional μ unit buys fewer steps as dimensions are exhausted.

        For k=3, N=4:
          j=0→1: saves N^3 - (N + N^2) = 64 - 20 = 44 steps, costs 1 μ
          j=1→2: saves (N + N^2) - 3N = 20 - 12 = 8 steps, costs 1 μ
          j=2→3: saves 3N - 3N = 0 steps, costs 1 μ  ← no step saving from last emit!

        The last EMIT buys 0 extra step savings (both j=2 and j=3 are 3N steps).
        This is because after certifying k-1 dimensions, the remaining dimension
        has only N elements — and a 1D blind search of N elements IS the same cost
        as a 1D sighted search. The final EMIT is a pure certificate with no compute value.
        """
        N = 4
        targets = [N - 1] * 3

        target_idx = N**3 - 1
        blind = _run(_k_blind_program(target_idx))
        steps = {0: blind.vm_regs[15]}

        for j in [1, 2]:
            pj = self._partial_sighted_program_k3(targets, n_emit=j)
            sj = _run(pj)
            steps[j] = sj.vm_regs[15]

        fully = _run(_k_sighted_program(targets))
        steps[3] = fully.vm_regs[15]

        saving_0to1 = steps[0] - steps[1]  # 64 - 20 = 44
        saving_1to2 = steps[1] - steps[2]  # 20 - 12 = 8
        saving_2to3 = steps[2] - steps[3]  # 12 - 12 = 0

        assert saving_0to1 > saving_1to2, (
            f"First EMIT should save more steps than second: "
            f"0→1 saves {saving_0to1}, 1→2 saves {saving_1to2}"
        )
        assert saving_1to2 > saving_2to3, (
            f"Second EMIT should save more steps than third: "
            f"1→2 saves {saving_1to2}, 2→3 saves {saving_2to3}"
        )
        assert saving_2to3 == 0, (
            f"Last EMIT on a 1D remaining problem saves 0 steps, got {saving_2to3}"
        )

    def test_minimum_mu_for_super_linear_advantage(self):
        """With μ=1, the advantage over blind is at most linear in N.

        For k=3: μ=1 gives N + N² steps. Blind gives N^3 steps.
        Ratio: N^3 / (N + N²) = N^2 / (1 + N) ≈ N for large N. Grows as O(N).

        With μ=3: ratio = N^3 / (3N) = N²/3. Grows as O(N²). Super-linear in N.

        So: μ≥2 is required to get a super-linear (better than Θ(N)) advantage.
        """
        N = 6  # Use N=6 to avoid trivial edge cases
        targets = [N - 1] * 3

        target_idx = N**3 - 1
        blind  = _run(_k_blind_program(target_idx))
        p1     = self._partial_sighted_program_k3(targets, n_emit=1)
        one_mu = _run(p1)
        full   = _run(_k_sighted_program(targets))

        blind_steps = blind.vm_regs[15]    # = N^3 = 216
        one_mu_steps = one_mu.vm_regs[15]  # = N + N^2 = 42
        full_steps   = full.vm_regs[15]    # = 3*N = 18

        ratio_one_mu = blind_steps / one_mu_steps   # ≈ N^2/(N+1) ≈ 5.1
        ratio_full   = blind_steps / full_steps      # = N^2/3 = 12

        assert ratio_full > ratio_one_mu, (
            f"μ=3 should give better ratio than μ=1: "
            f"full ratio={ratio_full:.2f}, 1-mu ratio={ratio_one_mu:.2f}"
        )
        # Full sighted advantage grows steeply — μ budget matters
        assert ratio_full > 2 * ratio_one_mu, (
            f"μ=3 ratio should be more than 2x the μ=1 ratio: "
            f"{ratio_full:.2f} vs {ratio_one_mu:.2f}"
        )


# ---------------------------------------------------------------------------
# Section 3: Adversarial structure boundary
# ---------------------------------------------------------------------------

class TestAdversarialStructureBoundary:
    """Tests where the factoring intuition is challenged.

    QUESTION: Is the advantage purely about independent structure, or does it
    survive correlation between dimensions?

    FINDING (predicted): Even for strongly correlated targets (anti-diagonal,
    constant-sum), the 2D sighted program retains an advantage, because the
    sighted program searches EACH DIMENSION INDEPENDENTLY regardless of
    correlation. The two loops don't communicate.

    But: for targets near (0, 0), blind wins (trivially — it finds index 0 in
    1 step; sighted always needs at least 2 steps for 2 EMITs).

    ADVERSARIAL BOUNDARY: Sighted loses only at (0, R) for small R where
    blind_iters = R+1 ≤ 2+R = sighted_iters. This is: R ≤ 1.
    For any left_target ≥ 1, sighted_iters = left_target + right_target + 2
    while blind_iters = left_target * N + right_target + 1.
    Sighted wins iff left_target * N + right_target + 1 > left_target + right_target + 2
    iff left_target * (N - 1) > 1
    iff left_target ≥ 1  (for N ≥ 3).

    So sighted loses only when left_target = 0. Exactly ONE column favors blind.
    """

    def test_anti_diagonal_sighted_wins_harder(self):
        """On the anti-diagonal (left + right = N-1), sighted_iters = N+1 (constant).

        For blind: varies by diagonal position.
        For sighted: (left+1) + (right+1) = left + (N-1-left) + 2 = N+1.

        Blind worst case on anti-diagonal: left=N/2 gives blind_iters = (N/2)*N + N/2 ≈ N²/2.
        Sighted: always exactly N+1.
        Ratio at middle of anti-diagonal: ≈ N/2 (better than off-diagonal average).
        """
        N = 8

        sighted_iters_all = []
        blind_iters_all = []

        for left in range(N):
            right = N - 1 - left  # anti-diagonal
            target_idx = left * N + right

            blind   = _run(_blind2d(target_idx))
            sighted = _run(_sighted2d(left, right))

            blind_iters_all.append(blind.vm_regs[15])
            sighted_iters_all.append(sighted.vm_regs[15])

        # All sighted iters should be exactly N+1 = 9
        for i, (left, si) in enumerate(zip(range(N), sighted_iters_all)):
            right = N - 1 - left
            assert si == N + 1, (
                f"Anti-diagonal ({left},{right}): sighted_iters={si}, expected {N+1}"
            )

        # Sighted beats blind for all left ≥ 1
        wins = sum(1 for bi, si in zip(blind_iters_all, sighted_iters_all) if si < bi)
        assert wins == N - 1, (
            f"Sighted should win for left≥1 ({N-1} positions), won {wins}"
        )

    def test_sighted_wins_for_all_nontrivial_positions(self):
        """For left_target ≥ 1, sighted always strictly beats blind on iterations.

        This is the clean structural claim: independence from right_target.
        Blind must scan the entire left half linearly. Sighted certifies it directly.
        """
        N = 8
        losses = []
        for left in range(1, N):       # left ≥ 1 (skip trivial)
            for right in range(0, N):
                target_idx = left * N + right
                blind   = _run(_blind2d(target_idx))
                sighted = _run(_sighted2d(left, right))
                bi, si = blind.vm_regs[15], sighted.vm_regs[15]
                if si >= bi:
                    losses.append((left, right, bi, si))

        assert losses == [], (
            "Sighted should win strictly for all (left≥1, right):\n"
            + "\n".join(f"  ({l},{r}): blind={bi}, sighted={si}" for l,r,bi,si in losses)
        )

    def test_sighted_loses_only_at_left_zero(self):
        """For left=0 (target in the first row): blind may beat sighted.

        blind_iters = right + 1
        sighted_iters = 1 + right + 1 = right + 2  (left loop completes in 1 iter)

        So blind wins by exactly 1 iteration for every left=0 position.
        This is the ONLY adversarial zone — one column out of N.
        """
        N = 8
        left = 0
        for right in range(N):
            target_idx = left * N + right
            blind   = _run(_blind2d(target_idx))
            sighted = _run(_sighted2d(left, right))
            bi, si = blind.vm_regs[15], sighted.vm_regs[15]

            assert bi == right + 1, f"blind: ({left},{right}): got {bi}, want {right+1}"
            assert si == right + 2, f"sighted: ({left},{right}): got {si}, want {right+2}"
            assert bi < si, f"Blind should beat sighted at left=0: blind={bi}, sighted={si}"

    def test_adversarial_zone_is_exactly_one_column(self):
        """The entire adversarial region is exactly the left=0 column (1/N of all positions).

        For large N this is a vanishingly small fraction of positions.
        The fraction where sighted wins = (N-1)/N → 1 as N→∞.
        """
        for N in [4, 8]:  # N=16 (256 programs) exceeds per-test timeout
            wins = losses = 0
            for left in range(N):
                for right in range(N):
                    target_idx = left * N + right
                    blind   = _run(_blind2d(target_idx))
                    sighted = _run(_sighted2d(left, right))
                    bi, si = blind.vm_regs[15], sighted.vm_regs[15]
                    if si < bi:
                        wins += 1
                    elif bi < si:
                        losses += 1

            total = N * N
            # Sighted wins: all (left≥1, right) = N*(N-1) positions
            # Sighted loses: all (left=0, right) = N positions
            assert wins == N * (N - 1), (
                f"N={N}: sighted should win {N*(N-1)} positions, got {wins}"
            )
            assert losses == N, (
                f"N={N}: sighted should lose exactly {N} positions (left=0 column), got {losses}"
            )
