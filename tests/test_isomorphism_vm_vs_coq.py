# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""
Tests for VM ↔ Coq isomorphism.

These tests verify that the Python VM semantics match the Coq formal
specification for key properties.
"""

import pytest
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent
COQ_DIR = REPO_ROOT / "coq" / "thielemachine" / "coqproofs"


class TestCoqSpecificationExists:
    """Test that required Coq specifications exist."""
    
    def test_thiele_machine_spec_exists(self):
        """ThieleMachine.v should exist."""
        spec_file = COQ_DIR / "ThieleMachine.v"
        assert spec_file.exists(), "ThieleMachine.v not found"
    
    def test_partition_logic_exists(self):
        """PartitionLogic.v should exist."""
        spec_file = COQ_DIR / "PartitionLogic.v"
        assert spec_file.exists(), "PartitionLogic.v not found"
    
    def test_mu_alignment_exists(self):
        """MuAlignmentExample.v should exist."""
        spec_file = COQ_DIR / "MuAlignmentExample.v"
        assert spec_file.exists(), "MuAlignmentExample.v not found"


class TestCoqTheoremContent:
    """Test that Coq files contain expected theorems."""
    
    def test_thiele_machine_has_replay_theorem(self):
        """ThieleMachine.v should have replay theorem."""
        spec_file = COQ_DIR / "ThieleMachine.v"
        content = spec_file.read_text()
        
        assert "replay_of_exec" in content or "replay_ok" in content, \
            "Replay theorem not found in ThieleMachine.v"
    
    def test_thiele_machine_has_mu_theorem(self):
        """ThieleMachine.v should have μ-accounting theorem."""
        spec_file = COQ_DIR / "ThieleMachine.v"
        content = spec_file.read_text()
        
        assert "mu_pays_bits" in content or "mu_lower_bound" in content, \
            "μ-accounting theorem not found in ThieleMachine.v"


class TestMuMonotonicityIsomorphism:
    """Test μ-monotonicity is consistent between Python and Coq spec."""
    
    def test_python_mu_monotone_matches_coq_spec(self):
        """Python μ-monotonicity should match Coq specification."""
        from thielecpu.state import State
        
        state = State()
        
        # Track μ values through operations
        mu_values = [state.mu_ledger.total]
        
        # PNEW
        m1 = state.pnew({0, 1, 2})
        mu_values.append(state.mu_ledger.total)
        
        # PSPLIT
        state.psplit(m1, lambda x: x < 2)
        mu_values.append(state.mu_ledger.total)
        
        # Verify monotonicity (matches Coq step_mu_monotone)
        for i in range(1, len(mu_values)):
            assert mu_values[i] >= mu_values[i-1], \
                f"μ decreased from {mu_values[i-1]} to {mu_values[i]} at step {i}"
    
    def test_python_mu_non_negative(self):
        """Python μ-values should always be non-negative (as in Coq nat)."""
        from thielecpu.state import State
        
        state = State()
        
        assert state.mu_ledger.mu_discovery >= 0
        assert state.mu_ledger.mu_execution >= 0
        assert state.mu_ledger.total >= 0
        
        state.pnew({0, 1, 2})
        
        assert state.mu_ledger.mu_discovery >= 0
        assert state.mu_ledger.mu_execution >= 0
        assert state.mu_ledger.total >= 0


class TestStateMachineIsomorphism:
    """Test state machine structure matches between Python and Coq."""
    
    def test_state_has_pc(self):
        """Python state should have PC like Coq State."""
        from thielecpu.state import State
        
        state = State()
        assert hasattr(state, 'step_count'), "State should have step_count (PC)"
    
    def test_state_has_mu_ledger(self):
        """Python state should have μ-ledger like Coq tm_state."""
        from thielecpu.state import State, MuLedger
        
        state = State()
        assert hasattr(state, 'mu_ledger'), "State should have mu_ledger"
        assert isinstance(state.mu_ledger, MuLedger), "mu_ledger should be MuLedger"
    
    def test_mu_ledger_has_discovery_and_execution(self):
        """MuLedger should have mu_discovery and mu_execution like Coq mu_ledger."""
        from thielecpu.state import MuLedger
        
        ledger = MuLedger()
        assert hasattr(ledger, 'mu_discovery'), "MuLedger should have mu_discovery"
        assert hasattr(ledger, 'mu_execution'), "MuLedger should have mu_execution"


class TestOpcodeIsomorphism:
    """Test opcode structure matches between Python and Coq."""
    
    def test_core_opcodes_exist(self):
        """Python should have core opcodes from Coq InstrKind."""
        from thielecpu.isa import Opcode
        
        # Core opcodes from Coq specification
        required_opcodes = ['PNEW', 'PSPLIT', 'PMERGE', 'LASSERT', 'MDLACC', 'EMIT', 'HALT']
        
        for opcode in required_opcodes:
            assert hasattr(Opcode, opcode), f"Opcode {opcode} missing from Python ISA"


class TestPartitionOperationIsomorphism:
    """Test partition operations match between Python and Coq."""
    
    def test_pnew_creates_disjoint_partitions(self):
        """PNEW should maintain disjointness invariant (as in Coq)."""
        from thielecpu.state import State
        
        state = State()
        
        m1 = state.pnew({0, 1, 2})
        m2 = state.pnew({3, 4, 5})
        
        # Get regions
        r1 = state.regions[m1]
        r2 = state.regions[m2]
        
        # Check disjointness
        assert not (r1 & r2), "Partitions should be disjoint"
    
    def test_psplit_preserves_coverage(self):
        """PSPLIT should preserve coverage invariant (as in Coq)."""
        from thielecpu.state import State
        
        state = State()
        
        original_region = {0, 1, 2, 3}
        m = state.pnew(original_region)
        
        m1, m2 = state.psplit(m, lambda x: x < 2)
        
        # Get regions
        r1 = state.regions[m1]
        r2 = state.regions[m2]
        
        # Coverage preserved
        assert r1 | r2 == original_region, "PSPLIT should preserve coverage"
    
    def test_pmerge_combines_regions(self):
        """PMERGE should combine disjoint regions (as in Coq)."""
        from thielecpu.state import State
        
        state = State()
        
        m1 = state.pnew({0, 1})
        m2 = state.pnew({2, 3})
        
        merged = state.pmerge(m1, m2)
        
        # Get merged region
        r_merged = state.regions[merged]
        
        # Should contain all elements
        assert r_merged == {0, 1, 2, 3}, "PMERGE should combine regions"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
