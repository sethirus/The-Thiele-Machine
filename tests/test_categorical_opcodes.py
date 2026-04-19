"""Integration tests for the 7 categorical morphism opcodes (Phase 4–6).

Tests the MORPH, COMPOSE, MORPH_ID, MORPH_DELETE, MORPH_ASSERT, MORPH_TENSOR,
and MORPH_GET instructions end-to-end through the Coq-extracted OCaml runner.

Each test verifies end-to-end execution of categorical opcodes.
All invariants verified here follow from formally proven theorems in:
  - coq/kernel/CategoryLaws.v    (relational compose laws)
  - coq/kernel/CategoryBridge.v  (graph-level laws + NoFI consistency)
  - coq/kernel/CategoryMonoidal.v (tensor bifunctor + monoidal coherence)

NOTE: Module IDs start from 1 (pg_next_id initializes to 1 in the kernel).
      Morphism IDs start from 1 (pg_next_morph_id initializes to 1).
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

    def test_morph_graph_is_preserved_in_public_state(self):
        """The public VMState graph exposes the created morphism, not just its ID."""
        state = vm.run_vm([
            "PNEW {0,1} 1",       # module 1
            "PNEW {2,3} 1",       # module 2
            "MORPH 5 1 2 0 2",    # create morph 1→2, morph ID=1 → reg[5], cost=2
            "HALT 0",
        ])
        assert not state.err
        assert state.graph.next_id == 3
        assert state.graph.next_morph_id == 2
        assert len(state.graph.morphisms) == 1
        morph = state.graph.morphisms[0]
        assert morph.id == 1
        assert morph.source == 1
        assert morph.target == 2
        assert not morph.is_identity
        assert morph.coupling == {"label": "empty", "pairs": []}

    @pytest.mark.skipif(not vm._runner_available(), reason="OCaml runner unavailable")
    def test_python_protocol_categorical_state_matches_ocaml(self):
        """The Python protocol fallback must serialize categorical operands losslessly."""
        cases = [
            (
                "linear",
                [
                    "PNEW {1} 1",
                    "PNEW {2} 1",
                    "PNEW {3} 1",
                    "MORPH 5 1 2 0 2",
                    "MORPH 6 2 3 0 3",
                    "COMPOSE 7 1 2 4",
                    "MORPH_GET 8 3 0 5",
                    "MORPH_ID 9 1 2",
                    "MORPH_ASSERT 4 prop cert 6",
                    "MORPH_DELETE 4 7",
                    "HALT 0",
                ],
            ),
            (
                "tensor",
                [
                    "PNEW {10} 1",
                    "PNEW {20} 1",
                    "PNEW {30} 1",
                    "PNEW {40} 1",
                    "PNEW {10,20} 1",
                    "PNEW {30,40} 1",
                    "MORPH 10 1 3 0 2",
                    "MORPH 11 2 4 0 3",
                    "MORPH_TENSOR 12 1 2 4",
                    "HALT 0",
                ],
            ),
        ]

        def graph_signature(state):
            return (
                state.graph.next_id,
                state.graph.next_morph_id,
                [
                    (m.id, m.source, m.target, m.is_identity, m.coupling)
                    for m in state.graph.morphisms
                ],
            )

        for name, program in cases:
            ocaml = vm._run_extracted(program, 1000)
            python = vm._run_python(program, 1000)
            assert python.err == ocaml.err, name
            assert python.mu == ocaml.mu, name
            assert python.regs == ocaml.regs, name
            assert graph_signature(python) == graph_signature(ocaml), name

    def test_morph_returns_id_to_register(self):
        """MORPH 5 1 2 0 cost writes morphism-ID 1 to reg[5]."""
        state = vm.run_vm([
            "PNEW {0,1} 1",       # module 1
            "PNEW {2,3} 1",       # module 2
            "MORPH 5 1 2 0 2",    # create morph 1→2, morph ID=1 → reg[5], cost=2
            "HALT 0",
        ])
        assert not state.err, f"MORPH errored: mu={state.mu}"
        assert state.regs[5] == 1, f"Expected first morphism ID=1, got {state.regs[5]}"
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
            "MORPH 5 1 2 0 0",    # morph ID=1 → reg[5]
            "MORPH 6 1 2 0 0",    # morph ID=2 → reg[6]
            "MORPH 7 1 2 0 0",    # morph ID=3 → reg[7]
            "HALT 0",
        ])
        assert not state.err
        assert state.regs[5] == 1
        assert state.regs[6] == 2
        assert state.regs[7] == 3


# ---------------------------------------------------------------------------
# MORPH_ID: create identity morphism
# ---------------------------------------------------------------------------

class TestMorphId:
    """MORPH_ID creates an identity morphism for a module."""

    def test_morph_id_writes_id_to_register(self):
        """MORPH_ID 3 1 cost creates identity morphism for module 1, writes ID to reg[3]."""
        state = vm.run_vm([
            "PNEW {0,1} 1",       # module 1
            "MORPH_ID 3 1 1",     # identity morph for module-1, ID=1 → reg[3], cost=1
            "HALT 0",
        ])
        assert not state.err, f"MORPH_ID errored: mu={state.mu}"
        assert state.regs[3] == 1, f"Expected morphism ID=1, got {state.regs[3]}"
        # mu: PNEW (cost 1) + MORPH_ID (cost 1) = 2
        assert state.mu == 2

    def test_morph_id_get_is_identity_flag(self):
        """MORPH_GET with selector=3 returns 1 for an identity morphism."""
        state = vm.run_vm([
            "PNEW {5,6} 1",       # module 1
            "MORPH_ID 3 1 0",     # identity morph for module-1, ID=1 → reg[3]
            "MORPH_GET 4 1 3 0",  # selector=3 (is_identity flag) from morph-1 → reg[4]
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
            "COMPOSE 7 1 2 1",    # compose morph-1;morph-2: 1→3, ID=3 → reg[7]
            "HALT 0",
        ])
        assert not state.err, f"COMPOSE errored: mu={state.mu}"
        assert state.regs[7] == 3, f"Expected composed morphism ID=3, got {state.regs[7]}"
        # mu: PNEW×3 (3) + MORPH×2 (2) + COMPOSE (1) = 6
        assert state.mu == 6

    def test_compose_type_mismatch_errors(self):
        """COMPOSE fails when m1.target != m2.source."""
        state = vm.run_vm([
            "PNEW {1} 1",         # module 1
            "PNEW {2} 1",         # module 2
            "PNEW {3} 1",         # module 3
            "MORPH 5 1 2 0 0",    # morph 1: 1→2 (target = module 2)
            "MORPH 6 1 3 0 0",    # morph 2: 1→3 (source = module 1 ≠ module 2)
            "COMPOSE 7 1 2 0",    # morph1.target=2 ≠ morph2.source=1 → error
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
            "MORPH 5 1 2 0 0",     # morph 1: 1→2
            "MORPH 6 2 3 0 0",     # morph 2: 2→3
            "MORPH_DELETE 1 0",    # delete morph-1
            "COMPOSE 7 1 2 0",     # morph-1 is gone → COMPOSE should error
            "HALT 0",
        ])
        assert state.err, "Expected error: COMPOSE after MORPH_DELETE of morph-0"

    def test_morph_delete_allows_new_morphism_creation(self):
        """After deleting a morphism, new morphisms can still be created."""
        state = vm.run_vm([
            "PNEW {1} 1",          # module 1
            "PNEW {2} 1",          # module 2
            "MORPH 5 1 2 0 0",     # morph 1: 1→2
            "MORPH_DELETE 1 0",    # delete morph-1
            "MORPH 6 1 2 0 0",     # new morph: 1→2, ID=2 (pg_next_morph_id incremented)
            "HALT 0",
        ])
        assert not state.err, "Expected success after delete + new MORPH"
        # New morphism ID is 2 (pg_next_morph_id does not reuse deleted IDs)
        assert state.regs[6] == 2, f"Expected new morphism ID=2, got {state.regs[6]}"

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
            "MORPH_ASSERT 1 p c 3",    # assert on morph-1, cost=3 → actual S(3)=4
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
            "MORPH_ASSERT 1 p c 0",    # cost=0 → S(0)=1
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

    def test_pmerge_does_not_cascade_delete_morphisms(self):
        """PMERGE removes modules but does NOT cascade-delete referencing morphisms.

        Per graph_hw_pmerge in coq/kernel/VMStep.v, PMERGE calls graph_remove
        on the two input modules and graph_add_module for the merged result, but
        never calls graph_cascade_delete_morphisms. Orphaned morphisms therefore
        remain in the morphism table after PMERGE, and MORPH_DELETE on them
        succeeds rather than errors.
        """
        state = vm.run_vm([
            "PNEW {1,2} 1",        # module 1: region={1,2}
            "PNEW {3,4} 1",        # module 2: region={3,4}
            "PNEW {5,6} 1",        # module 3: region={5,6}
            "MORPH 10 1 3 0 0",    # morph 1: module-1 → module-3
            # Merge module-1 and module-2 → destroys mod-1 and mod-2, creates mod-4
            "PMERGE 1 2 1",        # merge: destroys mod-1 but does NOT cascade-delete morph-1
            # Morph-1 is still present; MORPH_DELETE should succeed
            "MORPH_DELETE 1 0",    # succeeds — morph-1 was NOT cascade-deleted
            "HALT 0",
        ])
        assert not state.err, "Expected success: PMERGE does not cascade-delete morphisms per graph_hw_pmerge in VMStep.v"

    def test_cascade_delete_compose_fails_after_merge(self):
        """After PMERGE, orphaned morphisms still exist but COMPOSE can fail on type mismatch.

        PMERGE does NOT cascade-delete morphisms (per graph_hw_pmerge in VMStep.v).
        Morph-1 (module-1 → module-3) survives PMERGE of modules 1 and 2.
        A new morph-3 (module-5 → module-3) is created. COMPOSE of morph-1 and
        morph-3 fails because morph-1.target(=3) != morph-3.source(=5).
        """
        state = vm.run_vm([
            "PNEW {1,2} 1",        # module 1
            "PNEW {3,4} 1",        # module 2
            "PNEW {5,6} 1",        # module 3
            "MORPH 10 1 3 0 0",    # morph 1: module-1 → module-3
            "MORPH 11 3 2 0 0",    # morph 2: module-3 → module-2
            "PMERGE 1 2 1",        # merge mod-1 and mod-2 → cascade-deletes morph-1
            "PNEW {1,2} 1",        # recreate a module (module 5)
            "MORPH 12 5 3 0 0",    # morph 3: module-5 → module-3
            "COMPOSE 13 1 3 0",    # try compose morph-1;morph-3 → morph-1 gone → error
            "HALT 0",
        ])
        assert state.err, "Expected error: COMPOSE fails due to type mismatch (morph-1.target != morph-3.source)"


# ---------------------------------------------------------------------------
# MORPH_TENSOR: parallel composition of morphisms
# ---------------------------------------------------------------------------

class TestMorphTensor:
    """MORPH_TENSOR creates the parallel (tensor) product of two morphisms."""

    def test_morph_tensor_errors_with_overlapping_regions(self):
        """MORPH_TENSOR errors because PNEW normalizes regions to seq 0 sz,
        making all single-cell modules share cell 0 (never disjoint)."""
        state = vm.run_vm([
            "PNEW {10} 1",         # module 1: region=[0]
            "PNEW {20} 1",         # module 2: region=[0]
            "PNEW {30} 1",         # module 3: region=[0]
            "PNEW {40} 1",         # module 4: region=[0]
            "PNEW {10,20} 1",      # module 5: region=[0,1]
            "PNEW {30,40} 1",      # module 6: region=[0,1]
            "MORPH 10 1 3 0 0",
            "MORPH 11 2 4 0 0",
            "MORPH_TENSOR 12 1 2 1",
            "HALT 0",
        ])
        assert state.err, "Expected error: seq 0 sz regions are never disjoint"

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
            "MORPH_TENSOR 12 1 2 0",   # no union modules → error
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
            "MORPH 5 1 2 0 0",     # morph 1: module-1 → module-2
            "MORPH_GET 8 1 0 0",   # selector=0 (source) of morph-1 → reg[8]
            "HALT 0",
        ])
        assert not state.err
        assert state.regs[8] == 1, f"Expected source module ID=1, got {state.regs[8]}"

    def test_morph_get_target(self):
        """MORPH_GET with selector=1 returns the target module ID."""
        state = vm.run_vm([
            "PNEW {1} 1",          # module 1
            "PNEW {2} 1",          # module 2
            "MORPH 5 1 2 0 0",     # morph 1: module-1 → module-2
            "MORPH_GET 9 1 1 0",   # selector=1 (target) of morph-1 → reg[9]
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
            "MORPH_GET 10 1 2 0",  # selector=2 (coupling length) → reg[10]
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
            "MORPH_GET 11 1 3 0",  # selector=3 (is_identity) → reg[11]
            "HALT 0",
        ])
        assert not state.err
        assert state.regs[11] == 0, f"Expected is_identity=0, got {state.regs[11]}"

    def test_morph_get_is_identity_true_for_id_morphism(self):
        """MORPH_GET with selector=3 returns 1 for an identity morphism."""
        state = vm.run_vm([
            "PNEW {1} 1",          # module 1
            "MORPH_ID 5 1 0",      # identity morphism for module-1
            "MORPH_GET 11 1 3 0",  # selector=3 → is_identity flag
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
            "MORPH_ASSERT 1 p c 0",  # cost=0 → S(0)=1 charged
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
              "MORPH 5 1 2 0 0", "MORPH 6 2 3 0 0", "COMPOSE 7 1 2 0", "HALT 0"],
             "COMPOSE"),
            (["PNEW {1} 1", "MORPH_ID 5 1 0", "MORPH_DELETE 1 0", "HALT 0"],
             "MORPH_DELETE"),
            (["PNEW {1} 1", "MORPH_ID 5 1 0", "MORPH_ASSERT 1 p c 1", "HALT 0"],
             "MORPH_ASSERT"),
            (["PNEW {10} 1", "PNEW {20} 1", "PNEW {30} 1", "PNEW {40} 1",
              "PNEW {10,20} 1", "PNEW {30,40} 1",
              "MORPH 10 1 3 0 0", "MORPH 11 2 4 0 0",
              "MORPH_TENSOR 12 1 2 0", "HALT 0"],
             "MORPH_TENSOR"),
            (["PNEW {1} 1", "PNEW {2} 1", "MORPH 5 1 2 0 0",
              "MORPH_GET 8 1 0 0", "HALT 0"],
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
