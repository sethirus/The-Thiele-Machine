"""Integration tests for the 7 categorical morphism opcodes (Phase 4–6).

Tests the MORPH, COMPOSE, MORPH_ID, MORPH_DELETE, MORPH_ASSERT, MORPH_TENSOR,
and MORPH_GET instructions end-to-end through the Coq-extracted OCaml runner.

Each test corresponds to a scenario from CATEGORICAL_EXTENSION_PLAN.md Part 10.
All invariants verified here follow from formally proven theorems in:
  - coq/kernel/CategoryLaws.v    (relational compose laws)
  - coq/kernel/CategoryBridge.v  (graph-level laws + NoFI consistency)
  - coq/kernel/CategoryMonoidal.v (tensor bifunctor + monoidal coherence)

NOTE: Module IDs start from 1 (pg_next_id initializes to 1 in the kernel).
      Morphism IDs start from 0 (pg_next_morph_id initializes to 0).
      Region syntax {a,b,...} is a list of individual cell IDs, NOT a range.
"""

from __future__ import annotations

import pytest
from build import thiele_vm as vm


# ---------------------------------------------------------------------------
# MORPH: create a morphism between two modules
# ---------------------------------------------------------------------------

class TestMorphCreate:
    """MORPH writes the new morphism ID to a destination register."""

    def test_morph_returns_id_to_register(self):
        """MORPH 5 1 2 0 cost writes morphism-ID 0 to reg[5]."""
        state = vm.run_vm([
            "PNEW {0,1} 1",       # module 1
            "PNEW {2,3} 1",       # module 2
            "MORPH 5 1 2 0 2",    # create morph 1→2, morph ID=0 → reg[5], cost=2
            "HALT 0",
        ])
        assert not state.err, f"MORPH errored: mu={state.mu}"
        assert state.regs[5] == 0, f"Expected first morphism ID=0, got {state.regs[5]}"
        # mu: PNEW×2 (cost 1 each) + MORPH (cost 2) = 4
        assert state.mu == 4, f"mu={state.mu}, expected 4"

    def test_morph_failure_on_missing_module(self):
        """MORPH with non-existent module IDs sets err flag."""
        state = vm.run_vm([
            "PNEW {0,1} 1",         # creates module 1 only
            "MORPH 5 1 99 0 0",     # dst_mod=99 does not exist → error
            "HALT 0",
        ])
        assert state.err, "Expected error when dst_mod does not exist"

    def test_morph_ids_increment_per_creation(self):
        """Each successive morphism creation gets a higher ID."""
        state = vm.run_vm([
            "PNEW {0,1} 1",       # module 1
            "PNEW {2,3} 1",       # module 2
            "MORPH 5 1 2 0 0",    # morph ID=0 → reg[5]
            "MORPH 6 1 2 0 0",    # morph ID=1 → reg[6]
            "MORPH 7 1 2 0 0",    # morph ID=2 → reg[7]
            "HALT 0",
        ])
        assert not state.err
        assert state.regs[5] == 0
        assert state.regs[6] == 1
        assert state.regs[7] == 2


# ---------------------------------------------------------------------------
# MORPH_ID: create identity morphism
# ---------------------------------------------------------------------------

class TestMorphId:
    """MORPH_ID creates an identity morphism for a module."""

    def test_morph_id_writes_id_to_register(self):
        """MORPH_ID 3 1 cost creates identity morphism for module 1, writes ID to reg[3]."""
        state = vm.run_vm([
            "PNEW {0,1} 1",       # module 1
            "MORPH_ID 3 1 1",     # identity morph for module-1, ID=0 → reg[3], cost=1
            "HALT 0",
        ])
        assert not state.err, f"MORPH_ID errored: mu={state.mu}"
        assert state.regs[3] == 0, f"Expected morphism ID=0, got {state.regs[3]}"
        # mu: PNEW (cost 1) + MORPH_ID (cost 1) = 2
        assert state.mu == 2

    def test_morph_id_get_is_identity_flag(self):
        """MORPH_GET with selector=3 returns 1 for an identity morphism."""
        state = vm.run_vm([
            "PNEW {5,6} 1",       # module 1
            "MORPH_ID 3 1 0",     # identity morph for module-1, ID=0 → reg[3]
            "MORPH_GET 4 0 3 0",  # selector=3 (is_identity flag) from morph-0 → reg[4]
            "HALT 0",
        ])
        assert not state.err
        assert state.regs[4] == 1, f"Expected is_identity=1, got {state.regs[4]}"

    def test_morph_id_failure_on_missing_module(self):
        """MORPH_ID with non-existent module ID sets err flag."""
        state = vm.run_vm([
            "MORPH_ID 3 99 0",    # module 99 does not exist
            "HALT 0",
        ])
        assert state.err, "Expected error when module does not exist"


# ---------------------------------------------------------------------------
# COMPOSE: compose two morphisms
# ---------------------------------------------------------------------------

class TestMorphCompose:
    """COMPOSE combines two morphisms when their endpoints match."""

    def test_compose_succeeds_with_matching_endpoints(self):
        """COMPOSE works when m1.target == m2.source."""
        state = vm.run_vm([
            "PNEW {1} 1",         # module 1 (source of f)
            "PNEW {2} 1",         # module 2 (intermediate)
            "PNEW {3} 1",         # module 3 (target of g)
            "MORPH 5 1 2 0 1",    # morph 0: 1→2
            "MORPH 6 2 3 0 1",    # morph 1: 2→3
            "COMPOSE 7 0 1 1",    # compose morph-0;morph-1: 1→3, ID=2 → reg[7]
            "HALT 0",
        ])
        assert not state.err, f"COMPOSE errored: mu={state.mu}"
        assert state.regs[7] == 2, f"Expected composed morphism ID=2, got {state.regs[7]}"
        # mu: PNEW×3 (3) + MORPH×2 (2) + COMPOSE (1) = 6
        assert state.mu == 6

    def test_compose_type_mismatch_errors(self):
        """COMPOSE fails when m1.target != m2.source."""
        state = vm.run_vm([
            "PNEW {1} 1",         # module 1
            "PNEW {2} 1",         # module 2
            "PNEW {3} 1",         # module 3
            "MORPH 5 1 2 0 0",    # morph 0: 1→2 (target = module 2)
            "MORPH 6 1 3 0 0",    # morph 1: 1→3 (source = module 1 ≠ module 2)
            "COMPOSE 7 0 1 0",    # morph0.target=2 ≠ morph1.source=1 → error
            "HALT 0",
        ])
        assert state.err, "Expected error for type mismatch in COMPOSE"

    def test_compose_failure_on_missing_morphism(self):
        """COMPOSE with non-existent morphism IDs sets err flag."""
        state = vm.run_vm([
            "PNEW {1} 1",
            "COMPOSE 7 0 1 0",    # morph IDs 0 and 1 don't exist yet
            "HALT 0",
        ])
        assert state.err, "Expected error when morphism does not exist"


# ---------------------------------------------------------------------------
# MORPH_DELETE: remove a morphism from the graph
# ---------------------------------------------------------------------------

class TestMorphDelete:
    """MORPH_DELETE removes a morphism by ID."""

    def test_morph_delete_removes_morphism(self):
        """After MORPH_DELETE, a COMPOSE using the deleted morphism fails."""
        state = vm.run_vm([
            "PNEW {1} 1",          # module 1
            "PNEW {2} 1",          # module 2
            "PNEW {3} 1",          # module 3
            "MORPH 5 1 2 0 0",     # morph 0: 1→2
            "MORPH 6 2 3 0 0",     # morph 1: 2→3
            "MORPH_DELETE 0 0",    # delete morph-0
            "COMPOSE 7 0 1 0",     # morph-0 is gone → COMPOSE should error
            "HALT 0",
        ])
        assert state.err, "Expected error: COMPOSE after MORPH_DELETE of morph-0"

    def test_morph_delete_allows_new_morphism_creation(self):
        """After deleting a morphism, new morphisms can still be created."""
        state = vm.run_vm([
            "PNEW {1} 1",          # module 1
            "PNEW {2} 1",          # module 2
            "MORPH 5 1 2 0 0",     # morph 0: 1→2
            "MORPH_DELETE 0 0",    # delete morph-0
            "MORPH 6 1 2 0 0",     # new morph: 1→2, ID=1 (pg_next_morph_id incremented)
            "HALT 0",
        ])
        assert not state.err, "Expected success after delete + new MORPH"
        # New morphism ID is 1 (pg_next_morph_id does not reuse deleted IDs)
        assert state.regs[6] == 1, f"Expected new morphism ID=1, got {state.regs[6]}"

    def test_morph_delete_failure_on_missing_morphism(self):
        """MORPH_DELETE on non-existent morphism ID sets err flag."""
        state = vm.run_vm([
            "MORPH_DELETE 99 0",    # morphism 99 does not exist
            "HALT 0",
        ])
        assert state.err, "Expected error when deleting non-existent morphism"


# ---------------------------------------------------------------------------
# MORPH_ASSERT: cert-setter instruction
# ---------------------------------------------------------------------------

class TestMorphAssert:
    """MORPH_ASSERT charges S(cost)≥1 and is the only cert-setter morph op."""

    def test_morph_assert_charges_s_cost(self):
        """MORPH_ASSERT with cost=3 charges S(3)=4 mu-units."""
        state = vm.run_vm([
            "PNEW {1} 1",              # module 1, cost=1
            "MORPH_ID 5 1 0",          # identity morph, cost=0
            "MORPH_ASSERT 0 p c 3",    # assert on morph-0, cost=3 → actual S(3)=4
            "HALT 0",
        ])
        assert not state.err, f"MORPH_ASSERT errored: mu={state.mu}"
        # mu: PNEW(1) + MORPH_ID(0) + MORPH_ASSERT(S(3)=4) = 5
        assert state.mu == 5, f"Expected mu=5, got {state.mu}"

    def test_morph_assert_cost_zero_still_charges_one(self):
        """MORPH_ASSERT with cost=0 charges S(0)=1 (cannot be free)."""
        state = vm.run_vm([
            "PNEW {1} 1",              # module 1 cost=1
            "MORPH_ID 5 1 0",          # identity morph cost=0
            "MORPH_ASSERT 0 p c 0",    # cost=0 → S(0)=1
            "HALT 0",
        ])
        assert not state.err
        # mu: PNEW(1) + MORPH_ID(0) + MORPH_ASSERT(S(0)=1) = 2
        assert state.mu == 2, f"Expected mu=2, got {state.mu}"

    def test_morph_assert_on_missing_morphism_errors(self):
        """MORPH_ASSERT on non-existent morphism ID sets err flag."""
        state = vm.run_vm([
            "MORPH_ASSERT 99 p c 1",    # morph 99 does not exist
            "HALT 0",
        ])
        assert state.err, "Expected error when morphism does not exist"


# ---------------------------------------------------------------------------
# Cascade delete: PSPLIT/PMERGE removes morphisms referencing deleted modules
# ---------------------------------------------------------------------------

class TestCascadeDelete:
    """When a module is removed (PMERGE), all morphisms referencing it are deleted."""

    def test_cascade_delete_on_pmerge(self):
        """PMERGE removes modules, cascade-deleting any morphisms that reference them."""
        state = vm.run_vm([
            "PNEW {1,2} 1",        # module 1: region={1,2}
            "PNEW {3,4} 1",        # module 2: region={3,4}
            "PNEW {5,6} 1",        # module 3: region={5,6}
            "MORPH 10 1 3 0 0",    # morph 0: module-1 → module-3
            # Merge module-1 and module-2 → destroys mod-1 and mod-2, creates mod-4
            "PMERGE 1 2 1",        # merge: destroys mod-1 (and cascade-deletes morph-0)
            # Now morph-0 should be gone; MORPH_DELETE on it should fail
            "MORPH_DELETE 0 0",    # should error — morph-0 was cascade-deleted
            "HALT 0",
        ])
        assert state.err, "Expected error: MORPH_DELETE on cascade-deleted morphism"

    def test_cascade_delete_compose_fails_after_merge(self):
        """After PMERGE removes source module, COMPOSE using the deleted morphism fails."""
        state = vm.run_vm([
            "PNEW {1,2} 1",        # module 1
            "PNEW {3,4} 1",        # module 2
            "PNEW {5,6} 1",        # module 3
            "MORPH 10 1 3 0 0",    # morph 0: module-1 → module-3
            "MORPH 11 3 2 0 0",    # morph 1: module-3 → module-2
            "PMERGE 1 2 1",        # merge mod-1 and mod-2 → cascade-deletes morph-0
            "PNEW {1,2} 1",        # recreate a module (module 5)
            "MORPH 12 5 3 0 0",    # morph 2: module-5 → module-3
            "COMPOSE 13 0 2 0",    # try compose morph-0;morph-2 → morph-0 gone → error
            "HALT 0",
        ])
        assert state.err, "Expected error: COMPOSE after cascade delete of morph-0"


# ---------------------------------------------------------------------------
# MORPH_TENSOR: parallel composition of morphisms
# ---------------------------------------------------------------------------

class TestMorphTensor:
    """MORPH_TENSOR creates the parallel (tensor) product of two morphisms."""

    def test_morph_tensor_succeeds_on_disjoint_regions(self):
        """MORPH_TENSOR succeeds when source and target regions are disjoint,
        and union modules already exist in the graph."""
        # f: module-1 {A} → module-3 {B}
        # g: module-2 {C} → module-4 {D}
        # Need extra modules: module-5 {A,C} and module-6 {B,D}
        state = vm.run_vm([
            "PNEW {10} 1",         # module 1: A={10} (source of f)
            "PNEW {20} 1",         # module 2: C={20} (source of g)
            "PNEW {30} 1",         # module 3: B={30} (target of f)
            "PNEW {40} 1",         # module 4: D={40} (target of g)
            "PNEW {10,20} 1",      # module 5: A∪C={10,20} (source of f⊗g)
            "PNEW {30,40} 1",      # module 6: B∪D={30,40} (target of f⊗g)
            "MORPH 10 1 3 0 0",    # morph 0: mod1→mod3 (A→B)
            "MORPH 11 2 4 0 0",    # morph 1: mod2→mod4 (C→D)
            "MORPH_TENSOR 12 0 1 1",  # tensor: (A→B)⊗(C→D), morph ID=2 → reg[12]
            "HALT 0",
        ])
        assert not state.err, f"MORPH_TENSOR errored: mu={state.mu}"
        assert state.regs[12] == 2, f"Expected tensor morphism ID=2, got {state.regs[12]}"
        # mu: PNEW×6 (6) + MORPH×2 (0) + MORPH_TENSOR (1) = 7
        assert state.mu == 7

    def test_morph_tensor_fails_without_union_modules(self):
        """MORPH_TENSOR fails if union modules (A∪C, B∪D) don't exist in the graph."""
        state = vm.run_vm([
            "PNEW {10} 1",         # module 1
            "PNEW {20} 1",         # module 2
            "PNEW {30} 1",         # module 3
            "PNEW {40} 1",         # module 4
            # intentionally do NOT create modules for union regions
            "MORPH 10 1 3 0 0",
            "MORPH 11 2 4 0 0",
            "MORPH_TENSOR 12 0 1 0",   # no union modules → error
            "HALT 0",
        ])
        assert state.err, "Expected error: union modules not in graph"


# ---------------------------------------------------------------------------
# MORPH_GET: read morphism properties into a register
# ---------------------------------------------------------------------------

class TestMorphGet:
    """MORPH_GET reads morphism metadata (source, target, coupling length, is_identity)."""

    def test_morph_get_source(self):
        """MORPH_GET with selector=0 returns the source module ID."""
        state = vm.run_vm([
            "PNEW {1} 1",          # module 1
            "PNEW {2} 1",          # module 2
            "MORPH 5 1 2 0 0",     # morph 0: module-1 → module-2
            "MORPH_GET 8 0 0 0",   # selector=0 (source) of morph-0 → reg[8]
            "HALT 0",
        ])
        assert not state.err
        assert state.regs[8] == 1, f"Expected source module ID=1, got {state.regs[8]}"

    def test_morph_get_target(self):
        """MORPH_GET with selector=1 returns the target module ID."""
        state = vm.run_vm([
            "PNEW {1} 1",          # module 1
            "PNEW {2} 1",          # module 2
            "MORPH 5 1 2 0 0",     # morph 0: module-1 → module-2
            "MORPH_GET 9 0 1 0",   # selector=1 (target) of morph-0 → reg[9]
            "HALT 0",
        ])
        assert not state.err
        assert state.regs[9] == 2, f"Expected target module ID=2, got {state.regs[9]}"

    def test_morph_get_coupling_length(self):
        """MORPH_GET with selector=2 returns the number of coupling pairs."""
        state = vm.run_vm([
            "PNEW {1} 1",          # module 1
            "PNEW {2} 1",          # module 2
            "MORPH 5 1 2 0 0",     # morph with empty coupling
            "MORPH_GET 10 0 2 0",  # selector=2 (coupling length) → reg[10]
            "HALT 0",
        ])
        assert not state.err
        assert state.regs[10] == 0, f"Expected coupling length=0, got {state.regs[10]}"

    def test_morph_get_is_identity_false_for_non_id(self):
        """MORPH_GET with selector=3 returns 0 for a non-identity morphism."""
        state = vm.run_vm([
            "PNEW {1} 1",          # module 1
            "PNEW {2} 1",          # module 2
            "MORPH 5 1 2 0 0",     # regular morphism (not identity)
            "MORPH_GET 11 0 3 0",  # selector=3 (is_identity) → reg[11]
            "HALT 0",
        ])
        assert not state.err
        assert state.regs[11] == 0, f"Expected is_identity=0, got {state.regs[11]}"

    def test_morph_get_is_identity_true_for_id_morphism(self):
        """MORPH_GET with selector=3 returns 1 for an identity morphism."""
        state = vm.run_vm([
            "PNEW {1} 1",          # module 1
            "MORPH_ID 5 1 0",      # identity morphism for module-1
            "MORPH_GET 11 0 3 0",  # selector=3 → is_identity flag
            "HALT 0",
        ])
        assert not state.err
        assert state.regs[11] == 1, f"Expected is_identity=1, got {state.regs[11]}"

    def test_morph_get_failure_on_missing_morphism(self):
        """MORPH_GET on non-existent morphism ID sets err flag."""
        state = vm.run_vm([
            "MORPH_GET 11 99 0 0",  # morph 99 does not exist
            "HALT 0",
        ])
        assert state.err, "Expected error when morphism does not exist"


# ---------------------------------------------------------------------------
# Cross-opcode invariants
# ---------------------------------------------------------------------------

class TestCategoricalInvariants:
    """Cross-opcode invariants derived from the category law proofs."""

    def test_morph_mu_cost_matches_instruction_cost(self):
        """Each MORPH at cost=c increments mu by exactly c."""
        state = vm.run_vm([
            "PNEW {0} 1",        # PNEW cost=1
            "PNEW {1} 1",        # PNEW cost=1
            "MORPH 5 1 2 0 7",   # MORPH cost=7
            "HALT 0",
        ])
        assert not state.err
        assert state.mu == 1 + 1 + 7, f"Expected mu=9, got {state.mu}"

    def test_morph_assert_cost_always_positive(self):
        """MORPH_ASSERT cannot be executed at zero net mu-cost (charges S(cost) >= 1)."""
        # Even with cost=0, S(0)=1 is charged
        init_mu = 0
        state = vm.run_vm([
            "PNEW {1} 1",
            "MORPH_ID 5 1 0",
            "MORPH_ASSERT 0 p c 0",  # cost=0 → S(0)=1 charged
            "HALT 0",
        ])
        assert not state.err
        # mu > 0 after execution (NoFI: certified knowledge has positive mu cost)
        assert state.mu > 0, f"Expected mu>0 after MORPH_ASSERT, got {state.mu}"

    def test_all_seven_morph_opcodes_parse_without_error(self):
        """All 7 categorical opcodes parse and execute without a parse-level crash."""
        # Minimal programs that exercise each opcode at least once
        programs = [
            (["PNEW {1} 1", "PNEW {2} 1", "MORPH 5 1 2 0 0", "HALT 0"],
             "MORPH"),
            (["PNEW {1} 1", "MORPH_ID 5 1 0", "HALT 0"],
             "MORPH_ID"),
            (["PNEW {1} 1", "PNEW {2} 1", "PNEW {3} 1",
              "MORPH 5 1 2 0 0", "MORPH 6 2 3 0 0", "COMPOSE 7 0 1 0", "HALT 0"],
             "COMPOSE"),
            (["PNEW {1} 1", "MORPH_ID 5 1 0", "MORPH_DELETE 0 0", "HALT 0"],
             "MORPH_DELETE"),
            (["PNEW {1} 1", "MORPH_ID 5 1 0", "MORPH_ASSERT 0 p c 1", "HALT 0"],
             "MORPH_ASSERT"),
            (["PNEW {10} 1", "PNEW {20} 1", "PNEW {30} 1", "PNEW {40} 1",
              "PNEW {10,20} 1", "PNEW {30,40} 1",
              "MORPH 10 1 3 0 0", "MORPH 11 2 4 0 0",
              "MORPH_TENSOR 12 0 1 0", "HALT 0"],
             "MORPH_TENSOR"),
            (["PNEW {1} 1", "PNEW {2} 1", "MORPH 5 1 2 0 0",
              "MORPH_GET 8 0 0 0", "HALT 0"],
             "MORPH_GET"),
        ]
        for prog, name in programs:
            # Run without crashing; do not assert err (some may legitimately error)
            try:
                state = vm.run_vm(prog)
                # Just confirm the runner returned a valid VMState
                assert isinstance(state.mu, int), f"{name}: mu is not int"
                assert isinstance(state.err, bool), f"{name}: err is not bool"
            except Exception as exc:
                pytest.fail(f"{name} raised an unexpected exception: {exc}")
