# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""
Tests for μ-cost accounting as defined in spec/thiele_machine_spec.md.

These tests verify that the μ-ledger is updated correctly for each
operation and that the μ-values match between Python VM and spec.
"""

import pytest
from thielecpu.state import (
    State,
    MuLedger,
    MASK_WIDTH,
    MAX_MODULES,
    mask_of_indices,
    indices_of_mask,
    mask_union,
    mask_intersection,
    mask_disjoint,
    mask_popcount,
)
from thielecpu._types import ModuleId


class TestMaskHelpers:
    """Test bitmask helper functions."""
    
    def test_mask_of_indices_empty(self):
        """Empty set → zero mask."""
        assert mask_of_indices(set()) == 0
    
    def test_mask_of_indices_single(self):
        """Single element → single bit."""
        assert mask_of_indices({0}) == 1
        assert mask_of_indices({1}) == 2
        assert mask_of_indices({5}) == 32
    
    def test_mask_of_indices_multiple(self):
        """Multiple elements → multiple bits."""
        assert mask_of_indices({0, 1, 2}) == 0b111
        assert mask_of_indices({0, 2, 4}) == 0b10101
    
    def test_indices_of_mask_empty(self):
        """Zero mask → empty set."""
        assert indices_of_mask(0) == set()
    
    def test_indices_of_mask_single(self):
        """Single bit → single element."""
        assert indices_of_mask(1) == {0}
        assert indices_of_mask(2) == {1}
        assert indices_of_mask(32) == {5}
    
    def test_indices_of_mask_multiple(self):
        """Multiple bits → multiple elements."""
        assert indices_of_mask(0b111) == {0, 1, 2}
        assert indices_of_mask(0b10101) == {0, 2, 4}
    
    def test_mask_roundtrip(self):
        """Converting indices → mask → indices should be identity."""
        for indices in [{0}, {1, 2, 3}, {0, 5, 10, 20}, set()]:
            assert indices_of_mask(mask_of_indices(indices)) == indices
    
    def test_mask_union(self):
        """Union of masks."""
        a = mask_of_indices({0, 1})
        b = mask_of_indices({2, 3})
        assert mask_union(a, b) == mask_of_indices({0, 1, 2, 3})
    
    def test_mask_intersection(self):
        """Intersection of masks."""
        a = mask_of_indices({0, 1, 2})
        b = mask_of_indices({1, 2, 3})
        assert mask_intersection(a, b) == mask_of_indices({1, 2})
    
    def test_mask_disjoint_true(self):
        """Disjoint masks have no overlap."""
        a = mask_of_indices({0, 1})
        b = mask_of_indices({2, 3})
        assert mask_disjoint(a, b) is True
    
    def test_mask_disjoint_false(self):
        """Non-disjoint masks have overlap."""
        a = mask_of_indices({0, 1, 2})
        b = mask_of_indices({2, 3})
        assert mask_disjoint(a, b) is False
    
    def test_mask_popcount(self):
        """Count set bits."""
        assert mask_popcount(0) == 0
        assert mask_popcount(1) == 1
        assert mask_popcount(0b111) == 3
        assert mask_popcount(0b10101) == 3
        assert mask_popcount((1 << 64) - 1) == 64


class TestMuLedger:
    """Test MuLedger dataclass."""
    
    def test_initial_values(self):
        """Initial μ-ledger has zero costs."""
        ledger = MuLedger()
        assert ledger.mu_discovery == 0
        assert ledger.mu_execution == 0
        assert ledger.total == 0
    
    def test_total_property(self):
        """Total is sum of discovery and execution."""
        ledger = MuLedger(mu_discovery=10, mu_execution=20)
        assert ledger.total == 30
    
    def test_snapshot(self):
        """Snapshot returns dictionary."""
        ledger = MuLedger(mu_discovery=5, mu_execution=15)
        snap = ledger.snapshot()
        # Allow for additional snapshot fields (e.g., landauer entropy) while
        # asserting the essential μ-values match expected results.
        assert snap["mu_discovery"] == 5
        assert snap["mu_execution"] == 15
        assert snap["mu_total"] == 20
        assert snap.get("landauer_entropy", 0) == 0
    
    def test_copy(self):
        """Copy creates independent instance."""
        ledger = MuLedger(mu_discovery=5, mu_execution=15)
        copy = ledger.copy()
        assert copy.mu_discovery == 5
        assert copy.mu_execution == 15
        
        # Modify original
        ledger.mu_discovery = 100
        assert copy.mu_discovery == 5  # Copy unchanged


class TestPnewMuCost:
    """Test μ-cost for PNEW operation."""
    
    def test_pnew_mu_discovery_single(self):
        """PNEW with single element costs 1 μ-bit discovery."""
        state = State()
        initial_mu = state.mu_ledger.mu_discovery
        
        state.pnew({0})
        
        # Cost = popcount(region) = 1
        assert state.mu_ledger.mu_discovery == initial_mu + 1
        assert state.mu_ledger.mu_execution == 0  # PNEW only affects discovery
    
    def test_pnew_mu_discovery_multiple(self):
        """PNEW with multiple elements costs popcount μ-bits."""
        state = State()
        
        state.pnew({0, 1, 2, 3, 4})
        
        # Cost = popcount({0,1,2,3,4}) = 5
        assert state.mu_ledger.mu_discovery == 5
    
    def test_pnew_existing_no_cost(self):
        """PNEW for existing region has no additional cost."""
        state = State()
        
        state.pnew({0, 1, 2})
        initial_mu = state.mu_ledger.mu_discovery
        
        # Create same region again
        state.pnew({0, 1, 2})
        
        # No additional cost
        assert state.mu_ledger.mu_discovery == initial_mu


class TestPsplitMuCost:
    """Test μ-cost for PSPLIT operation."""
    
    def test_psplit_mu_execution(self):
        """PSPLIT costs MASK_WIDTH μ-bits execution."""
        state = State()
        mid = state.pnew({0, 1, 2, 3, 4, 5})
        initial_mu_exec = state.mu_ledger.mu_execution
        
        state.psplit(mid, lambda x: x < 3)
        
        # PSPLIT costs MASK_WIDTH
        assert state.mu_ledger.mu_execution == initial_mu_exec + MASK_WIDTH
    
    def test_psplit_mu_discovery_unchanged(self):
        """PSPLIT does not affect discovery cost."""
        state = State()
        mid = state.pnew({0, 1, 2, 3})
        initial_mu_disc = state.mu_ledger.mu_discovery
        
        state.psplit(mid, lambda x: x < 2)
        
        # Discovery unchanged
        assert state.mu_ledger.mu_discovery == initial_mu_disc


class TestPmergeMuCost:
    """Test μ-cost for PMERGE operation."""
    
    def test_pmerge_mu_execution(self):
        """PMERGE costs 4 μ-bits execution."""
        state = State()
        m1 = state.pnew({0, 1})
        m2 = state.pnew({2, 3})
        initial_mu_exec = state.mu_ledger.mu_execution
        
        state.pmerge(m1, m2)
        
        # PMERGE costs 4
        assert state.mu_ledger.mu_execution == initial_mu_exec + 4
    
    def test_pmerge_mu_discovery_unchanged(self):
        """PMERGE does not affect discovery cost."""
        state = State()
        m1 = state.pnew({0, 1})
        m2 = state.pnew({2, 3})

        before_merge_discovery = state.mu_ledger.mu_discovery

        state.pmerge(m1, m2)

        # Discovery should NOT increase from PMERGE
        # PMERGE only costs execution, not discovery
        assert state.mu_ledger.mu_discovery == before_merge_discovery


class TestMuMonotonicity:
    """Test that μ-values are monotonically non-decreasing."""
    
    def test_mu_never_decreases_pnew(self):
        """μ never decreases after PNEW."""
        state = State()
        
        for i in range(MAX_MODULES):
            prev_total = state.mu_ledger.total
            state.pnew({i})
            assert state.mu_ledger.total >= prev_total
    
    def test_mu_never_decreases_operations(self):
        """μ never decreases after any operation."""
        state = State()
        
        # PNEW
        m1 = state.pnew({0, 1, 2})
        total1 = state.mu_ledger.total
        
        # PSPLIT
        m_left, m_right = state.psplit(m1, lambda x: x < 2)
        total2 = state.mu_ledger.total
        assert total2 >= total1
        
        # PNEW again
        m2 = state.pnew({10, 11})
        total3 = state.mu_ledger.total
        assert total3 >= total2
        
        # PMERGE (use new modules that don't overlap)
        m3 = state.pnew({20, 21})
        m4 = state.pnew({22, 23})
        total4 = state.mu_ledger.total
        state.pmerge(m3, m4)
        total5 = state.mu_ledger.total
        assert total5 >= total4


class TestMaxModulesLimit:
    """Test MAX_MODULES enforcement."""
    
    def test_max_modules_limit(self):
        """Cannot create more than MAX_MODULES (now 64 by default, configurable)."""
        state = State()

        # Create MAX_MODULES modules
        for i in range(MAX_MODULES):
            state.pnew({i})

        # Verify we created MAX_MODULES modules
        assert state.num_modules == MAX_MODULES, f"Expected {MAX_MODULES} modules, got {state.num_modules}"

        # Next should fail
        with pytest.raises(ValueError, match="max modules"):
            state.pnew({MAX_MODULES})


class TestStateSnapshot:
    """Test state snapshot for tracing."""
    
    def test_snapshot_format(self):
        """Snapshot has expected format."""
        state = State()
        state.pnew({0, 1, 2})
        
        snap = state.get_state_snapshot()
        
        assert "num_modules" in snap
        assert "partition_masks" in snap
        assert "mu" in snap
        assert "step_count" in snap
    
    def test_snapshot_partition_masks_length(self):
        """Partition masks always has MAX_MODULES entries."""
        state = State()
        state.pnew({0, 1})
        
        snap = state.get_state_snapshot()
        
        assert len(snap["partition_masks"]) == MAX_MODULES


class TestMuCostReferenceTable:
    """Test μ-costs against reference values from spec."""
    
    REFERENCE_TABLE = [
        # (operation, region/args, expected_discovery_delta, expected_execution_delta)
        ("PNEW", {0}, 1, 0),
        ("PNEW", {0, 1, 2, 3}, 4, 0),
        ("PNEW", set(), 0, 0),  # Empty region
        ("PSPLIT", None, 0, MASK_WIDTH),  # PSPLIT always costs MASK_WIDTH
        ("PMERGE", None, 0, 4),  # PMERGE costs 4 execution, 0 discovery
    ]
    
    def test_pnew_costs_match_reference(self):
        """PNEW costs match reference table."""
        for op, region, exp_disc, exp_exec in self.REFERENCE_TABLE:
            if op != "PNEW":
                continue
            
            state = State()
            state.pnew(region)
            
            assert state.mu_ledger.mu_discovery == exp_disc, f"PNEW {region}: discovery mismatch"
            assert state.mu_ledger.mu_execution == exp_exec, f"PNEW {region}: execution mismatch"
    
    def test_psplit_costs_match_reference(self):
        """PSPLIT costs match reference table."""
        state = State()
        mid = state.pnew({0, 1, 2, 3})
        
        # Reset execution to measure PSPLIT cost
        disc_before = state.mu_ledger.mu_discovery
        exec_before = state.mu_ledger.mu_execution
        
        state.psplit(mid, lambda x: x < 2)
        
        disc_delta = state.mu_ledger.mu_discovery - disc_before
        exec_delta = state.mu_ledger.mu_execution - exec_before
        
        # PSPLIT should not add to discovery (only execution)
        assert disc_delta == 0
        assert exec_delta == MASK_WIDTH
    
    def test_pmerge_costs_match_reference(self):
        """PMERGE execution cost matches reference table."""
        state = State()
        m1 = state.pnew({0, 1})
        m2 = state.pnew({2, 3})
        
        exec_before = state.mu_ledger.mu_execution
        
        state.pmerge(m1, m2)
        
        exec_delta = state.mu_ledger.mu_execution - exec_before
        
        assert exec_delta == 4  # PMERGE costs 4


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
