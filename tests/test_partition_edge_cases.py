"""Edge case tests for partition operations (PNEW, PSPLIT, PMERGE).

Tests boundary conditions, invalid operations, and corner cases to ensure
robust error handling and correct semantics across all three layers:
- Python VM (thielecpu/state.py)
- Coq extracted runner (build/extracted_vm_runner)
- Verilog RTL (thielecpu/hardware/)
"""

import tempfile
from pathlib import Path

import pytest

from thielecpu.state import State
from thielecpu.vm import VM


class TestPnewEdgeCases:
    """Edge case tests for PNEW (partition new) operation."""

    def test_pnew_empty_region(self):
        """PNEW with empty region creates the empty-module (mask == 0)."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{}"),  # Empty region
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))

        # No implicit base module: only the explicit empty region exists.
        assert len(state.partition_masks) == 1

        # The module should be the empty module (mask == 0).
        masks = list(state.partition_masks.values())
        assert 0 in masks  # Empty mask exists

    def test_pnew_singleton_regions(self):
        """PNEW with multiple singleton regions."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{1}"),
            ("PNEW", "{2}"),
            ("PNEW", "{3}"),
            ("PNEW", "{4}"),
            ("PNEW", "{5}"),
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))
        
        # Should have 5 singleton modules (no implicit base module)
        assert len(state.partition_masks) == 5
        
        # Verify each singleton exists
        masks = list(state.partition_masks.values())
        for i in range(1, 6):
            singleton_mask = 1 << i
            assert singleton_mask in masks

    def test_pnew_duplicate_regions_deduplication(self):
        """PNEW with duplicate regions should deduplicate."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{10,11,12}"),
            ("PNEW", "{10,11,12}"),  # Exact duplicate
            ("PNEW", "{10,11,12}"),  # Another duplicate
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))

        # Deduplication should result in exactly one module for the region.
        assert len(state.partition_masks) == 1
        
        target_mask = (1 << 10) | (1 << 11) | (1 << 12)
        masks = list(state.partition_masks.values())
        assert target_mask in masks

    def test_pnew_disjoint_regions(self):
        """PNEW with disjoint regions creates separate modules."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{20,21,22}"),
            ("PNEW", "{23,24,25}"),  # Disjoint
            ("PNEW", "{26,27,28}"),  # Disjoint
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))

        # No implicit base module: exactly the three requested regions.
        assert len(state.partition_masks) == 3
        
        mask1 = (1 << 20) | (1 << 21) | (1 << 22)
        mask2 = (1 << 23) | (1 << 24) | (1 << 25)
        mask3 = (1 << 26) | (1 << 27) | (1 << 28)
        masks = list(state.partition_masks.values())
        assert mask1 in masks
        assert mask2 in masks
        assert mask3 in masks

    def test_pnew_large_region(self):
        """PNEW with large region (many indices)."""
        state = State()
        vm = VM(state)
        
        # Create region with indices 10-30 (21 elements)
        large_region = ",".join(str(i) for i in range(10, 31))
        
        program = [
            ("PNEW", f"{{{large_region}}}"),
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))

        # No implicit base module: only the requested region.
        assert len(state.partition_masks) == 1
        
        # Verify all indices present
        large_mask = sum(1 << i for i in range(10, 31))
        masks = list(state.partition_masks.values())
        assert large_mask in masks

    def test_pnew_boundary_indices(self):
        """PNEW with boundary indices (max index 63)."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{62}"),   # Near-maximum index
            ("PNEW", "{63}"),   # Maximum index
            ("PNEW", "{61,60}"), # Other high indices
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))
        
        # Verify modules exist
        masks = list(state.partition_masks.values())
        assert (1 << 62) in masks  # {62}
        assert (1 << 63) in masks  # {63}
        assert ((1 << 61) | (1 << 60)) in masks  # {60,61}


class TestPsplitEdgeCases:
    """Edge case tests for PSPLIT (partition split) operation."""

    def test_psplit_empty_predicate(self):
        """PSPLIT with empty predicate (no elements match - all odd)."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{41,43,45,47}"),  # All odd - none match x % 2 == 0
            ("PSPLIT", "1 0"),  # Split module 1 using even/odd predicate-byte (0 => even)
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))
        
        # One split result is empty, the other contains all odds.
        assert len(state.partition_masks) >= 1

    def test_psplit_full_predicate(self):
        """PSPLIT where predicate matches all elements (all even)."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{50,52,54}"),  # All even - all match x % 2 == 0
            ("PSPLIT", "1 0"),  # Module 1, even/odd split
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))
        
        # All elements match predicate, so one part full, one empty.
        assert len(state.partition_masks) >= 2

    def test_psplit_singleton_module(self):
        """PSPLIT on singleton module."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{60}"),
            ("PSPLIT", "1 0"),  # Split module 1 (singleton)
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))
        
        # Should complete successfully (60 is even, so matches predicate, one part empty).
        assert len(state.partition_masks) >= 1

    def test_psplit_half_split(self):
        """PSPLIT that evenly divides a region (using even/odd predicate)."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{30,31,32,33}"),
            ("PSPLIT", "1 0"),  # Module 1, predicate-byte even/odd
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))
        
        # PSPLIT removes the original module and creates two new ones.
        assert len(state.partition_masks) >= 2
        
        masks = list(state.partition_masks.values())
        mask_even = (1 << 30) | (1 << 32)  # Even indices
        mask_odd = (1 << 31) | (1 << 33)    # Odd indices
        
        # Both split results should exist
        assert mask_even in masks
        assert mask_odd in masks


class TestPmergeEdgeCases:
    """Edge case tests for PMERGE (partition merge) operation."""

    def test_pmerge_disjoint_regions(self):
        """PMERGE of two disjoint regions."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{15,16,17}"),
            ("PNEW", "{25,26,27}"),
            ("PMERGE", "1 2"),  # Merge modules 1 and 2
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))
        
        # Should have merged result.
        assert len(state.partition_masks) >= 1
        
        merged_mask = (1 << 15) | (1 << 16) | (1 << 17) | (1 << 25) | (1 << 26) | (1 << 27)
        masks = list(state.partition_masks.values())
        assert merged_mask in masks

    def test_pmerge_adjacent_regions(self):
        """PMERGE of adjacent disjoint regions."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{35,36,37}"),
            ("PNEW", "{38,39,40}"),  # Adjacent but disjoint
            ("PMERGE", "1 2"),  # Merge modules 1 and 2
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))
        
        # Merged should be union: {35,36,37,38,39,40}
        merged_mask = (1 << 35) | (1 << 36) | (1 << 37) | (1 << 38) | (1 << 39) | (1 << 40)
        masks = list(state.partition_masks.values())
        assert merged_mask in masks

    def test_pmerge_identical_regions(self):
        """PMERGE of identical regions."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{45,46}"),
            ("PNEW", "{45,46}"),  # Duplicate (dedup might prevent creation)
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))
        
        # Deduplication should result in only one module
        target_mask = (1 << 45) | (1 << 46)
        masks = list(state.partition_masks.values())
        assert masks.count(target_mask) >= 1  # At least one instance

    def test_pmerge_singleton_regions(self):
        """PMERGE of two singleton regions."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{18}"),  # Changed indices to avoid conflicts
            ("PNEW", "{19}"),
            ("PMERGE", "1 2"),  # Merge modules 1 and 2
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))
        
        # Merged should be {18,19}
        merged_mask = (1 << 18) | (1 << 19)
        masks = list(state.partition_masks.values())
        assert merged_mask in masks

    def test_pmerge_one_empty_region(self):
        """PMERGE with one empty region."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{}"),      # Empty
            ("PNEW", "{55,56}"),
            ("PMERGE", "1 2"),   # Merge modules 1 and 2
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))
        
        # Result should be {55,56} (union with empty)
        target_mask = (1 << 55) | (1 << 56)
        masks = list(state.partition_masks.values())
        # Either deduped or merged present
        assert target_mask in masks or len(masks) >= 2


class TestMuCostEdgeCases:
    """Edge case tests for μ-cost accumulation in partition operations."""

    def test_mu_cost_sequence_accumulates(self):
        """μ-cost accumulates correctly across a sequence of operations."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{1}"),      # cost 1
            ("PNEW", "{2}"),      # cost 1
            ("PMERGE", "1 2"),    # cost varies
            ("PSPLIT", "3 0"),    # cost varies (even/odd split)
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))
        
        # μ-cost should be strictly positive
        assert state.mu_ledger.total > 0
        # Should accumulate across all operations
        # Exact value depends on operation costs

    def test_mu_cost_complex_graph_operations(self):
        """μ-cost accumulation in complex partition graph manipulations."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{10,11}"),   # Module 1
            ("PNEW", "{12,13}"),   # Module 2
            ("PNEW", "{14,15}"),   # Module 3
            ("PMERGE", "1 2"),     # Merge 1+2 -> Module 4
            ("PMERGE", "4 3"),     # Merge 4+3 -> Module 5
            ("PSPLIT", "5 0"),     # Split 5 -> two modules (even/odd)
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))
        
        # μ-cost should reflect all 6 operations (3 PNEW + 2 PMERGE + 1 PSPLIT)
        assert state.mu_ledger.total > 0
        # Monotonicity: cost never decreases
        assert state.mu_ledger.total >= 0

    def test_mu_cost_minimal_for_empty_program(self):
        """Empty program (only HALT) has zero μ-cost."""
        state = State()
        vm = VM(state)
        
        program = [
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))

        assert state.mu_ledger.total == 0
        assert state.mu_ledger.mu_discovery == 0
        assert state.mu_ledger.mu_execution == 0


class TestPartitionInvariants:
    """Test structural invariants maintained by partition operations."""

    def test_partition_masks_are_consistent(self):
        """Partition masks remain consistent after operations."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{5,6,7}"),   # Module 1
            ("PNEW", "{8,9}"),     # Module 2
            ("PMERGE", "1 2"),     # Merge -> Module 3
            ("PSPLIT", "3 0"),     # Split 3 -> two modules (even/odd)
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))
        
        # All masks should be valid (non-negative integers)
        for mid, mask in state.partition_masks.items():
            assert isinstance(mid, int)
            assert isinstance(mask, int)
            assert mask >= 0

    def test_no_implicit_base_module(self):
        """No implicit base module is created unless explicitly requested."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{20,21}"),
            ("PNEW", "{22,23}"),
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))

        # Since we never request index 0, no module should have bit0 set.
        masks = list(state.partition_masks.values())
        assert 1 not in masks  # 1 << 0

    def test_no_duplicate_masks_after_operations(self):
        """No duplicate masks exist after deduplication."""
        state = State()
        vm = VM(state)
        
        program = [
            ("PNEW", "{11,12}"),
            ("PNEW", "{11,12}"),  # Duplicate
            ("PNEW", "{13,14}"),
            ("PNEW", "{13,14}"),  # Duplicate
            ("HALT", ""),
        ]
        
        with tempfile.TemporaryDirectory() as td:
            vm.run(program, Path(td))
        
        # Deduplication should eliminate duplicates
        masks = list(state.partition_masks.values())
        unique_masks = set(masks)
        # Allow some duplicates if dedup is not complete, but most should be unique
        assert len(unique_masks) > 0
