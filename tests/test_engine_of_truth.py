#!/usr/bin/env python3
"""
Test suite for the Engine of Truth system.
"""

import pytest
import sys
from pathlib import Path

# Add base directory to path
BASE_DIR = Path(__file__).parent.parent
sys.path.insert(0, str(BASE_DIR))

from tools.known_universe import KnownUniverse, FundamentalLaw, UNIVERSE
from tools.evaluation_functions import evaluate_strategy_minimality


class TestKnownUniverse:
    """Test the Known Universe library."""
    
    def test_universe_initialization(self):
        """Test that the universe initializes with laws."""
        universe = KnownUniverse()
        
        assert len(universe.get_all_laws()) > 0, "Universe should contain laws"
        assert len(universe.get_laws_by_domain('mathematics')) > 0, "Should have math laws"
        assert len(universe.get_laws_by_domain('physics')) > 0, "Should have physics laws"
    
    def test_law_structure(self):
        """Test that laws have required structure."""
        universe = KnownUniverse()
        
        for law in universe.get_all_laws():
            assert hasattr(law, 'name'), "Law should have name"
            assert hasattr(law, 'domain'), "Law should have domain"
            assert hasattr(law, 'description'), "Law should have description"
            assert hasattr(law, 'computational_signature'), "Law should have signature"
            
            sig = law.computational_signature
            assert 'type' in sig, "Signature should have type"
            assert 'properties' in sig, "Signature should have properties"
            assert 'pattern' in sig, "Signature should have pattern"
            assert 'essence' in sig, "Signature should have essence"
    
    def test_specific_laws_present(self):
        """Test that expected laws are in the library."""
        universe = KnownUniverse()
        law_names = [law.name for law in universe.get_all_laws()]
        
        # Check for some key laws
        assert any('Fourier' in name for name in law_names), "Should have Fourier Transform"
        assert any('Entropy' in name for name in law_names), "Should have entropy law"
        assert any('Least Action' in name for name in law_names), "Should have least action"
    
    def test_singleton(self):
        """Test that UNIVERSE is accessible."""
        assert UNIVERSE is not None, "UNIVERSE singleton should exist"
        assert len(UNIVERSE.get_all_laws()) > 0, "UNIVERSE should have laws"


class TestEvaluationFunctions:
    """Test the minimality evaluation function."""
    
    def test_minimality_simple_code(self):
        """Test minimality scoring on simple code."""
        simple_code = "prim_simple()\nreturn result"
        score = evaluate_strategy_minimality(simple_code, "test", {})
        
        assert 0.0 <= score <= 1.0, "Score should be in [0, 1]"
        # Simple code should have non-zero minimality
        assert score > 0.0, "Simple code should have positive minimality"
    
    def test_minimality_complex_code(self):
        """Test minimality scoring on complex code."""
        complex_code = "\n".join([
            "prim_1()",
            "prim_2()",
            "if condition:",
            "    for i in range(10):",
            "        prim_3()",
            "        prim_4()",
            "        while True:",
            "            prim_5()",
        ])
        
        score = evaluate_strategy_minimality(complex_code, "test", {})
        
        assert 0.0 <= score <= 1.0, "Score should be in [0, 1]"
        assert score < 0.3, "Complex code should have low minimality"
    
    def test_minimality_comparison(self):
        """Test that simpler code gets higher minimality score."""
        simple = "return x"  # Minimal
        complex = "\n".join([f"prim_{i}()" for i in range(50)])  # Very complex
        
        score_simple = evaluate_strategy_minimality(simple, "test", {"preserve_effectiveness": False})
        score_complex = evaluate_strategy_minimality(complex, "test", {})
        
        assert score_simple > score_complex, "Simpler code should score higher"
    
    def test_minimality_preserve_effectiveness(self):
        """Test preserve_effectiveness parameter."""
        too_simple = "x"  # Just one line
        
        score_with = evaluate_strategy_minimality(
            too_simple, "test", {"preserve_effectiveness": True}
        )
        score_without = evaluate_strategy_minimality(
            too_simple, "test", {"preserve_effectiveness": False}
        )
        
        assert score_with < score_without, "preserve_effectiveness should penalize too-simple code"


class TestIsomorphismHunter:
    """Test the isomorphism hunting functionality."""
    
    def test_import(self):
        """Test that isomorphism_hunter can be imported."""
        from tools.isomorphism_hunter import IsomorphismHunter, StrategySignature
        
        assert IsomorphismHunter is not None
        assert StrategySignature is not None
    
    def test_strategy_signature_extraction(self):
        """Test signature extraction from strategy."""
        from tools.isomorphism_hunter import StrategySignature
        from tools.forge import StrategyDNA
        
        # Create a simple test strategy
        strategy = StrategyDNA(
            name="test_strategy",
            sequence=["partition = PDISCOVER(graph)", "return partition"],
            metadata={}
        )
        
        sig = StrategySignature(strategy)
        
        assert sig.signature is not None
        assert 'type' in sig.signature
        assert 'properties' in sig.signature
        assert 'pattern' in sig.signature
        assert 'essence' in sig.signature
    
    def test_similarity_computation(self):
        """Test similarity computation between signatures."""
        from tools.isomorphism_hunter import IsomorphismHunter
        
        hunter = IsomorphismHunter()
        
        # Identical signatures
        sig1 = {
            'type': 'optimization',
            'properties': ['linear', 'global'],
            'pattern': 'finds_optimal_path',
            'essence': 'nature_chooses_extremal_paths'
        }
        sig2 = sig1.copy()
        
        similarity = hunter.compute_similarity(sig1, sig2)
        assert similarity == 1.0, "Identical signatures should have similarity 1.0"
    
    def test_hunter_initialization(self):
        """Test that hunter initializes with universe."""
        from tools.isomorphism_hunter import IsomorphismHunter
        
        hunter = IsomorphismHunter()
        
        assert hunter.universe is not None
        assert len(hunter.universe.get_all_laws()) > 0


class TestObjectiveMinimizeSelf:
    """Test the Minimize Self objective."""
    
    def test_objective_file_exists(self):
        """Test that objective file was created."""
        objective_path = BASE_DIR / 'forge' / 'objectives' / 'objective_minimize_self.thiele'
        
        assert objective_path.exists(), "objective_minimize_self.thiele should exist"
    
    def test_objective_structure(self):
        """Test that objective has correct structure."""
        import json
        
        objective_path = BASE_DIR / 'forge' / 'objectives' / 'objective_minimize_self.thiele'
        
        with open(objective_path, 'r') as f:
            objective = json.load(f)
        
        assert objective['name'] == "Minimize Self v1.0"
        assert objective['function'] == "evaluate_strategy_minimality"
        assert 'parameters' in objective


def test_engine_of_truth_script_exists():
    """Test that the main script was created."""
    script_path = (
        BASE_DIR
        / 'demos'
        / 'research-demos'
        / 'architecture'
        / 'run_engine_of_truth.sh'
    )

    assert script_path.exists(), "run_engine_of_truth.sh should exist"
    # On Windows the Unix execute bit isn't reliable; only assert executable
    # permission on POSIX platforms.
    import os
    if os.name != "nt":
        assert script_path.stat().st_mode & 0o111, "Script should be executable"


def test_documentation_exists():
    """Test that documentation was created."""
    doc_path = BASE_DIR / 'docs' / 'archive' / 'ENGINE_OF_TRUTH_README.md'

    assert doc_path.exists(), "ENGINE_OF_TRUTH_README.md should exist"
    
    with open(doc_path, 'r') as f:
        content = f.read()
    
    assert 'Engine of Truth' in content
    assert 'Phase 1' in content
    assert 'Phase 2' in content
    assert 'Phase 3' in content


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v"])
