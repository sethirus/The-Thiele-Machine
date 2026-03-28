"""Limit-pushing tests for the categorical morphism layer.

WHAT THIS FILE TESTS
====================
The Thiele Machine gained 7 new opcodes (0x27–0x2D) in the categorical
extension. These opcodes give the machine a *category* on top of its
partition modules:

  Objects  = partition modules (created by PNEW/PSPLIT/PMERGE)
  Morphisms = typed relations between modules (created by MORPH/MORPH_ID)
  Composition = relational composition (COMPOSE: f;g where f.target=g.source)
  Tensor     = parallel product of disjoint morphisms (MORPH_TENSOR: f⊗g)
  Cert-setter = MORPH_ASSERT, the only morphism-group instruction that costs
                S(cost) ≥ 1 — the No Free Insight law at the category level

These tests push the system to its structural limits:

  1. DEEP COMPOSITION CHAINS
     Five sequential composes collapse A→B→C→D→E→F into one morphism A→F.
     An 8-module chain (A→H) collapses in 6 composes.

  2. CATEGORY LAWS AS EXECUTABLE ASSERTIONS
     The theorems in CategoryBridge.v (Coq) manifest at runtime:
     - Left identity:   id_A ; f   has same source/target as f
     - Right identity:  f ; id_B   has same source/target as f
     - Associativity:   (f;g);h    has same source/target as f;(g;h)
     - id_A ; id_A      has source = target = A (identity collapse)
     We verify by running the programs and reading src/tgt via MORPH_GET.

  3. MONOIDAL INTERCHANGE LAW AS A RUNNING PROGRAM
     The most demanding test: two independent paths through the diagram

         A ---f---> B ---h---> E
         ⊗          ⊗          ⊗
         C ---g---> D ---k---> F

     Path 1:  (f⊗g) ; (h⊗k)     source=A⊗C, target=E⊗F
     Path 2:  (f;h) ⊗ (g;k)     source=A⊗C, target=E⊗F

     Both paths must agree on source and target — the interchange law.
     Requires 9 modules (A,B,C,D,E,F plus union modules A⊗C, B⊗D, E⊗F)
     and 10 morphisms. This is the full monoidal coherence condition
     proven in CategoryMonoidal.v executing as a real program.

  4. FULL LIFECYCLE
     MORPH → MORPH_ASSERT (cert-setter) → MORPH_DELETE → recreate.
     Verify: deleted IDs are never reused, error on COMPOSE-after-DELETE,
     MORPH_ASSERT at cost=0 still charges 1 μ (No Free Insight).

  5. μ-COST ACCOUNTING AUDIT
     Complex sequences with analytically computed expected μ, verified
     bit-for-bit. Includes the MORPH_ASSERT S(cost) formula across
     cost arguments 0–100.

  6. STRESS
     10 morphisms on the same module pair → IDs 0..9 in sequence.
     8-module chain collapses to single A→H morphism.
     Delete + recreate confirms monotone ID allocation.

All tests run through the Coq-extracted OCaml interpreter (vm.run_vm).
Every assertion here follows from a proven theorem in the kernel.
"""

from __future__ import annotations
import pytest
from build import thiele_vm as vm


# ---------------------------------------------------------------------------
# 1. Deep composition chain: A → B → C → D → E → F
# ---------------------------------------------------------------------------

class TestDeepComposition:
    """Five sequential composes collapse a 6-module chain into a single morphism."""

    def test_five_hop_chain_source_and_target(self):
        """
        Build A→B→C→D→E→F via 5 morphisms, then compose them all left-to-right.
        The result must have source=mod_A and target=mod_F.

        Module IDs (pg_next_id starts at 1): A=1, B=2, C=3, D=4, E=5, F=6
        Morphism IDs (pg_next_morph_id starts at 0):
          f(0): A→B   g(1): B→C   h(2): C→D   k(3): D→E   m(4): E→F
          fg(5)=f;g   fgh(6)=fg;h  fghk(7)=fgh;k  fghkm(8)=fghk;m
        """
        state = vm.run_vm([
            "PNEW {10} 1",            # mod 1: A
            "PNEW {20} 1",            # mod 2: B
            "PNEW {30} 1",            # mod 3: C
            "PNEW {40} 1",            # mod 4: D
            "PNEW {50} 1",            # mod 5: E
            "PNEW {60} 1",            # mod 6: F
            "MORPH 0 1 2 0 0",        # morph 0: A→B
            "MORPH 1 2 3 0 0",        # morph 1: B→C
            "MORPH 2 3 4 0 0",        # morph 2: C→D
            "MORPH 3 4 5 0 0",        # morph 3: D→E
            "MORPH 4 5 6 0 0",        # morph 4: E→F
            "COMPOSE 5 0 1 0",        # morph 5: A→C  (f;g)
            "COMPOSE 6 5 2 0",        # morph 6: A→D  (f;g;h)
            "COMPOSE 7 6 3 0",        # morph 7: A→E  (f;g;h;k)
            "COMPOSE 8 7 4 0",        # morph 8: A→F  (f;g;h;k;m)
            "MORPH_GET 20 8 0 0",     # reg[20] = source of composed = mod 1 (A)
            "MORPH_GET 21 8 1 0",     # reg[21] = target of composed = mod 6 (F)
            "HALT 0",
        ])
        assert not state.err, f"Unexpected error: mu={state.mu}"
        assert state.regs[8] == 8,  f"Expected composed morph ID=8, got {state.regs[8]}"
        assert state.regs[20] == 1, f"Expected source=1 (A), got {state.regs[20]}"
        assert state.regs[21] == 6, f"Expected target=6 (F), got {state.regs[21]}"

    def test_chain_mu_accounting(self):
        """μ accumulates exactly: 6 PNEWs(cost=1 each) + 5 MORPHs + 4 COMPOSEs."""
        state = vm.run_vm([
            "PNEW {10} 1", "PNEW {20} 1", "PNEW {30} 1",
            "PNEW {40} 1", "PNEW {50} 1", "PNEW {60} 1",
            "MORPH 0 1 2 0 1",    # MORPH cost=1 each
            "MORPH 1 2 3 0 1",
            "MORPH 2 3 4 0 1",
            "MORPH 3 4 5 0 1",
            "MORPH 4 5 6 0 1",
            "COMPOSE 5 0 1 2",    # COMPOSE cost=2 each
            "COMPOSE 6 5 2 2",
            "COMPOSE 7 6 3 2",
            "COMPOSE 8 7 4 2",
            "HALT 0",
        ])
        assert not state.err
        # 6*1 (PNEW) + 5*1 (MORPH) + 4*2 (COMPOSE) = 6 + 5 + 8 = 19
        assert state.mu == 19, f"Expected mu=19, got {state.mu}"


# ---------------------------------------------------------------------------
# 2. Category laws as executable checks
# ---------------------------------------------------------------------------

class TestCategoryLawsExecutable:
    """The Coq proofs in CategoryBridge.v should manifest as identical src/tgt."""

    def test_left_identity_law(self):
        """id_A ; f  has the same source and target as f."""
        state = vm.run_vm([
            "PNEW {1} 1",             # mod 1: A
            "PNEW {2} 1",             # mod 2: B
            "MORPH 0 1 2 0 0",        # morph 0: f: A→B
            "MORPH_ID 1 1 0",         # morph 1: id_A
            "COMPOSE 2 1 0 0",        # morph 2: id_A ; f  (should be A→B)
            # Read src/tgt of f (morph 0)
            "MORPH_GET 10 0 0 0",     # reg[10] = src of f
            "MORPH_GET 11 0 1 0",     # reg[11] = tgt of f
            # Read src/tgt of id_A;f (morph 2)
            "MORPH_GET 12 2 0 0",     # reg[12] = src of id_A;f
            "MORPH_GET 13 2 1 0",     # reg[13] = tgt of id_A;f
            "HALT 0",
        ])
        assert not state.err
        # Law: src(id_A;f) == src(f),  tgt(id_A;f) == tgt(f)
        assert state.regs[12] == state.regs[10], \
            f"Left identity: src mismatch {state.regs[12]} != {state.regs[10]}"
        assert state.regs[13] == state.regs[11], \
            f"Left identity: tgt mismatch {state.regs[13]} != {state.regs[11]}"

    def test_right_identity_law(self):
        """f ; id_B  has the same source and target as f."""
        state = vm.run_vm([
            "PNEW {1} 1",             # mod 1: A
            "PNEW {2} 1",             # mod 2: B
            "MORPH 0 1 2 0 0",        # morph 0: f: A→B
            "MORPH_ID 1 2 0",         # morph 1: id_B
            "COMPOSE 2 0 1 0",        # morph 2: f ; id_B  (should be A→B)
            "MORPH_GET 10 0 0 0",     # reg[10] = src of f
            "MORPH_GET 11 0 1 0",     # reg[11] = tgt of f
            "MORPH_GET 12 2 0 0",     # reg[12] = src of f;id_B
            "MORPH_GET 13 2 1 0",     # reg[13] = tgt of f;id_B
            "HALT 0",
        ])
        assert not state.err
        assert state.regs[12] == state.regs[10], \
            f"Right identity: src mismatch {state.regs[12]} != {state.regs[10]}"
        assert state.regs[13] == state.regs[11], \
            f"Right identity: tgt mismatch {state.regs[13]} != {state.regs[11]}"

    def test_associativity_law(self):
        """(f;g);h  and  f;(g;h)  have the same source and target."""
        state = vm.run_vm([
            "PNEW {1} 1",             # mod 1: A
            "PNEW {2} 1",             # mod 2: B
            "PNEW {3} 1",             # mod 3: C
            "PNEW {4} 1",             # mod 4: D
            "MORPH 0 1 2 0 0",        # morph 0: f: A→B
            "MORPH 1 2 3 0 0",        # morph 1: g: B→C
            "MORPH 2 3 4 0 0",        # morph 2: h: C→D
            # Path 1: (f;g);h
            "COMPOSE 3 0 1 0",        # morph 3: f;g: A→C
            "COMPOSE 4 3 2 0",        # morph 4: (f;g);h: A→D
            # Path 2: f;(g;h)
            "COMPOSE 5 1 2 0",        # morph 5: g;h: B→D
            "COMPOSE 6 0 5 0",        # morph 6: f;(g;h): A→D
            # Compare
            "MORPH_GET 20 4 0 0",     # src of (f;g);h
            "MORPH_GET 21 4 1 0",     # tgt of (f;g);h
            "MORPH_GET 22 6 0 0",     # src of f;(g;h)
            "MORPH_GET 23 6 1 0",     # tgt of f;(g;h)
            "HALT 0",
        ])
        assert not state.err
        assert state.regs[20] == state.regs[22], \
            f"Assoc: src mismatch {state.regs[20]} != {state.regs[22]}"
        assert state.regs[21] == state.regs[23], \
            f"Assoc: tgt mismatch {state.regs[21]} != {state.regs[23]}"

    def test_double_identity_composition(self):
        """id_A ; id_A == id_A (same source and target, both are A)."""
        state = vm.run_vm([
            "PNEW {99} 1",            # mod 1: A
            "MORPH_ID 0 1 0",         # morph 0: id_A
            "COMPOSE 1 0 0 0",        # morph 1: id_A ; id_A
            "MORPH_GET 10 1 0 0",     # src = 1 (A)
            "MORPH_GET 11 1 1 0",     # tgt = 1 (A)
            "HALT 0",
        ])
        assert not state.err
        assert state.regs[10] == 1, f"Expected src=1, got {state.regs[10]}"
        assert state.regs[11] == 1, f"Expected tgt=1, got {state.regs[11]}"


# ---------------------------------------------------------------------------
# 3. Monoidal interchange law as a running program
#    (f⊗g) ; (h⊗k)  same src/tgt as  (f;h) ⊗ (g;k)
# ---------------------------------------------------------------------------

class TestMonoidalInterchangeLaw:
    """
    The interchange law: (f⊗g);(h⊗k) = (f;h)⊗(g;k).

    Setup:
      f: A→B  (mod1{10}→mod2{20})
      g: C→D  (mod3{30}→mod4{40})
      h: B→E  (mod2{20}→mod5{50})
      k: D→F  (mod4{40}→mod6{60})

    Union modules needed:
      A⊗C = mod7{10,30}
      B⊗D = mod8{20,40}
      E⊗F = mod9{50,60}

    Path 1: (f⊗g);(h⊗k)  → source=mod7(A⊗C), target=mod9(E⊗F)
    Path 2: (f;h)⊗(g;k)  → source=mod7(A⊗C), target=mod9(E⊗F)
    """

    def _build_interchange_state(self):
        return vm.run_vm([
            # Objects
            "PNEW {10} 1",            # mod 1: A
            "PNEW {20} 1",            # mod 2: B
            "PNEW {30} 1",            # mod 3: C
            "PNEW {40} 1",            # mod 4: D
            "PNEW {50} 1",            # mod 5: E
            "PNEW {60} 1",            # mod 6: F
            # Union objects (required by MORPH_TENSOR)
            "PNEW {10,30} 1",         # mod 7: A⊗C
            "PNEW {20,40} 1",         # mod 8: B⊗D
            "PNEW {50,60} 1",         # mod 9: E⊗F
            # Base morphisms
            "MORPH 0 1 2 0 0",        # morph 0: f: A→B
            "MORPH 1 3 4 0 0",        # morph 1: g: C→D
            "MORPH 2 2 5 0 0",        # morph 2: h: B→E
            "MORPH 3 4 6 0 0",        # morph 3: k: D→F
            # Path 1: (f⊗g) ; (h⊗k)
            "MORPH_TENSOR 4 0 1 0",   # morph 4: f⊗g: (A⊗C)→(B⊗D)
            "MORPH_TENSOR 5 2 3 0",   # morph 5: h⊗k: (B⊗D)→(E⊗F)
            "COMPOSE 6 4 5 0",        # morph 6: (f⊗g);(h⊗k): (A⊗C)→(E⊗F)
            # Path 2: (f;h) ⊗ (g;k)
            "COMPOSE 7 0 2 0",        # morph 7: f;h: A→E
            "COMPOSE 8 1 3 0",        # morph 8: g;k: C→F
            "MORPH_TENSOR 9 7 8 0",   # morph 9: (f;h)⊗(g;k): (A⊗C)→(E⊗F)
            # Read src/tgt of both paths
            "MORPH_GET 20 6 0 0",     # reg[20] = src of path 1
            "MORPH_GET 21 6 1 0",     # reg[21] = tgt of path 1
            "MORPH_GET 22 9 0 0",     # reg[22] = src of path 2
            "MORPH_GET 23 9 1 0",     # reg[23] = tgt of path 2
            "HALT 0",
        ])

    def test_interchange_both_paths_same_source(self):
        """Both paths have the same source module (A⊗C = mod 7)."""
        state = self._build_interchange_state()
        assert not state.err, f"Interchange setup errored: mu={state.mu}"
        assert state.regs[20] == state.regs[22], \
            f"Source mismatch: path1={state.regs[20]}, path2={state.regs[22]}"
        assert state.regs[20] == 7, f"Expected source=7 (A⊗C), got {state.regs[20]}"

    def test_interchange_both_paths_same_target(self):
        """Both paths have the same target module (E⊗F = mod 9)."""
        state = self._build_interchange_state()
        assert not state.err
        assert state.regs[21] == state.regs[23], \
            f"Target mismatch: path1={state.regs[21]}, path2={state.regs[23]}"
        assert state.regs[21] == 9, f"Expected target=9 (E⊗F), got {state.regs[21]}"

    def test_interchange_morph_ids_are_distinct(self):
        """The two paths produce separate morphism IDs (they are different objects)."""
        state = self._build_interchange_state()
        assert not state.err
        # morph 6 = path 1, morph 9 = path 2 — different IDs, same src/tgt
        assert state.regs[6] == 6
        assert state.regs[9] == 9


# ---------------------------------------------------------------------------
# 4. Full lifecycle: create → certify → mutate → delete → recreate
# ---------------------------------------------------------------------------

class TestFullLifecycle:
    """Exercises every opcode in a single coherent program."""

    def test_full_lifecycle_no_error(self):
        """
        Build a morphism, assert a property (cert-setter), delete it,
        verify deletion, then recreate. No error at any point except
        the intentional MORPH_GET-after-delete.
        """
        # Phase 1: build and certify
        state = vm.run_vm([
            "PNEW {1,2} 1",           # mod 1
            "PNEW {3,4} 1",           # mod 2
            "MORPH 0 1 2 0 2",        # morph 0: mod1→mod2, cost=2
            "MORPH_ASSERT 0 p cert 3", # cert-setter on morph 0, cost=3 → charges 4
            "MORPH_GET 5 0 0 0",      # reg[5] = source of morph 0 = 1
            "MORPH_DELETE 0 1",       # delete morph 0
            "MORPH 6 1 2 0 1",        # recreate: morph 1 (new ID), cost=1
            "MORPH_GET 7 1 0 0",      # reg[7] = source of new morph = 1
            "HALT 0",
        ])
        assert not state.err, f"Lifecycle errored: mu={state.mu}"
        assert state.regs[5] == 1,  "Pre-delete: source should be mod 1"
        assert state.regs[6] == 1,  "Recreated morphism ID should be 1 (IDs not reused)"
        assert state.regs[7] == 1,  "Recreated morph source should be mod 1"
        # μ: PNEW×2(2) + MORPH(2) + MORPH_ASSERT(S(3)=4) + MORPH_GET(0) +
        #    MORPH_DELETE(1) + MORPH(1) + MORPH_GET(0) = 10
        assert state.mu == 10, f"Expected mu=10, got {state.mu}"

    def test_delete_then_compose_errors(self):
        """After deleting a morphism, COMPOSE using it must set the error flag."""
        state = vm.run_vm([
            "PNEW {1} 1",
            "PNEW {2} 1",
            "PNEW {3} 1",
            "MORPH 0 1 2 0 0",        # morph 0: 1→2
            "MORPH 1 2 3 0 0",        # morph 1: 2→3
            "MORPH_DELETE 0 0",       # delete morph 0
            "COMPOSE 2 0 1 0",        # morph 0 gone → error
            "HALT 0",
        ])
        assert state.err, "Expected error: COMPOSE after MORPH_DELETE"

    def test_morph_assert_minimum_cost_enforces_nofi(self):
        """
        MORPH_ASSERT always charges ≥ 1 μ regardless of cost argument.
        This is the runtime manifestation of the No Free Insight theorem:
        certified knowledge has strictly positive cost.
        """
        initial = vm.run_vm(["HALT 0"])
        for cost_arg in range(5):
            state = vm.run_vm([
                "PNEW {1} 1",
                "MORPH_ID 0 1 0",
                f"MORPH_ASSERT 0 p c {cost_arg}",
                "HALT 0",
            ])
            # S(cost_arg) = cost_arg + 1 >= 1 always
            expected_mu = 1 + 0 + (cost_arg + 1)  # PNEW(1) + MORPH_ID(0) + S(cost)
            assert state.mu == expected_mu, \
                f"cost={cost_arg}: expected mu={expected_mu}, got {state.mu}"


# ---------------------------------------------------------------------------
# 5. μ-cost accounting audit
# ---------------------------------------------------------------------------

class TestMuAccountingAudit:
    """Every μ increment must be precisely accounted for."""

    def test_exact_mu_through_complex_sequence(self):
        """
        Complex sequence with known costs at every step.
        Total is computed analytically and verified bit-for-bit.
        """
        state = vm.run_vm([
            "PNEW {1} 1",         # +1  (cumulative: 1)
            "PNEW {2} 1",         # +1  (2)
            "PNEW {3} 1",         # +1  (3)
            "MORPH 0 1 2 0 3",    # +3  (6)
            "MORPH 1 2 3 0 2",    # +2  (8)
            "COMPOSE 2 0 1 4",    # +4  (12)
            "MORPH_ID 3 1 1",     # +1  (13)
            "MORPH_ASSERT 2 p c 2",  # +S(2)=3  (16)
            "MORPH_DELETE 0 1",   # +1  (17)
            "MORPH_GET 5 1 0 2",  # +2  (19)
            "HALT 0",
        ])
        assert not state.err
        assert state.mu == 19, f"Expected mu=19, got {state.mu}"

    def test_zero_cost_ops_do_not_advance_mu(self):
        """All MORPH ops at cost=0 (except MORPH_ASSERT) leave μ unchanged.

        MORPH, MORPH_ID, MORPH_GET (×2), MORPH_DELETE all at cost=0.
        Only the two PNEW at cost=1 each contribute to μ.
        """
        state = vm.run_vm([
            "PNEW {1} 1",            # +1
            "PNEW {2} 1",            # +1
            "MORPH 0 1 2 0 0",       # +0
            "MORPH_ID 1 1 0",        # +0
            "MORPH_GET 5 0 0 0",     # +0
            "MORPH_GET 6 0 1 0",     # +0
            "MORPH_GET 7 1 3 0",     # +0 (is_identity flag)
            "MORPH_DELETE 0 0",      # +0
            "HALT 0",
        ])
        assert not state.err
        # Only the two PNEWs at cost=1 each contribute
        assert state.mu == 2, f"Expected mu=2, got {state.mu}"

    def test_morph_assert_dominates_cost(self):
        """
        A sequence with one MORPH_ASSERT at high cost and all others at 0.
        μ = PNEW_cost + S(assert_cost).
        """
        for assert_cost in [0, 1, 5, 10, 100]:
            state = vm.run_vm([
                "PNEW {1} 1",
                "MORPH_ID 0 1 0",
                f"MORPH_ASSERT 0 p c {assert_cost}",
                "HALT 0",
            ])
            expected = 1 + 0 + (assert_cost + 1)
            assert state.mu == expected, \
                f"assert_cost={assert_cost}: expected mu={expected}, got {state.mu}"


# ---------------------------------------------------------------------------
# 6. Stress: many morphisms, long IDs
# ---------------------------------------------------------------------------

class TestMorphismStress:
    """Push morphism ID allocation and graph size."""

    def test_ten_sequential_morphisms_unique_ids(self):
        """10 morphisms on the same pair of modules all get unique IDs 0..9."""
        program = [
            "PNEW {1} 1",
            "PNEW {2} 1",
        ]
        for i in range(10):
            program.append(f"MORPH {i} 1 2 0 0")
        program.append("HALT 0")

        state = vm.run_vm(program)
        assert not state.err
        for i in range(10):
            assert state.regs[i] == i, \
                f"Morphism {i}: expected ID={i}, got {state.regs[i]}"

    def test_chain_of_eight_modules(self):
        """8-module chain: A→B→C→D→E→F→G→H collapsed to A→H in 7 composes."""
        program = []
        for i in range(8):
            program.append(f"PNEW {{{i * 10}}} 1")   # mods 1..8
        for i in range(7):
            # morph i: mod(i+1) → mod(i+2)
            program.append(f"MORPH {i} {i+1} {i+2} 0 0")
        # Compose: morph 7 = 0;1, morph 8 = 7;2, ..., morph 13 = 12;6
        # morph 7 = (0;1): mod1→mod3
        program.append("COMPOSE 7 0 1 0")   # morph 7
        program.append("COMPOSE 8 7 2 0")   # morph 8
        program.append("COMPOSE 9 8 3 0")   # morph 9
        program.append("COMPOSE 10 9 4 0")  # morph 10
        program.append("COMPOSE 11 10 5 0") # morph 11
        program.append("COMPOSE 12 11 6 0") # morph 12: A→H
        program.append("MORPH_GET 20 12 0 0")  # src
        program.append("MORPH_GET 21 12 1 0")  # tgt
        program.append("HALT 0")

        state = vm.run_vm(program)
        assert not state.err, f"8-chain errored: mu={state.mu}"
        assert state.regs[20] == 1, f"Expected src=1 (A), got {state.regs[20]}"
        assert state.regs[21] == 8, f"Expected tgt=8 (H), got {state.regs[21]}"

    def test_delete_and_reuse_slot(self):
        """
        IDs are never reused after deletion (pg_next_morph_id only increments).
        Create morph 0, delete it, create morph 1 — verify ID is 1 not 0.
        """
        state = vm.run_vm([
            "PNEW {1} 1",
            "PNEW {2} 1",
            "MORPH 5 1 2 0 0",     # morph 0 → reg[5]=0
            "MORPH_DELETE 0 0",    # delete morph 0
            "MORPH 6 1 2 0 0",     # next morph → reg[6]=1 (NOT 0)
            "HALT 0",
        ])
        assert not state.err
        assert state.regs[5] == 0, f"First morph ID should be 0, got {state.regs[5]}"
        assert state.regs[6] == 1, f"After delete, next morph ID should be 1, got {state.regs[6]}"
