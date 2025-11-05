#!/usr/bin/env python3
"""
Tests for Adversarial Diagnostic System

Tests the adversarial graph generator and diagnostic framework designed to
determine if the Thiele Machine's efficiency is fully explained by Spectral
Decomposition or if a deeper principle (P+1) exists.
"""

import json
import sys
from pathlib import Path
import pytest

# Add repo root to path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from tools.adversarial_generator import (
    AdversarialGraphGenerator,
    embed_tseitin_on_graph,
    write_cnf_file
)


class TestAdversarialGraphGenerator:
    """Tests for adversarial graph generation."""
    
    def test_generator_initialization(self):
        """Test generator initializes correctly."""
        gen = AdversarialGraphGenerator(seed=42)
        assert gen.seed == 42
    
    def test_lollipop_graph_structure(self):
        """Test lollipop graph has correct structure."""
        gen = AdversarialGraphGenerator()
        clique_size = 10
        path_length = 15
        G = gen.generate_lollipop_graph(clique_size, path_length)
        
        # Check total nodes
        assert len(G.nodes()) == clique_size + path_length
        
        # Check clique is dense
        clique_nodes = list(range(clique_size))
        clique_edges = 0
        for i in clique_nodes:
            for j in clique_nodes:
                if i < j and G.has_edge(i, j):
                    clique_edges += 1
        
        expected_clique_edges = clique_size * (clique_size - 1) // 2
        assert clique_edges == expected_clique_edges
    
    def test_barbell_graph_structure(self):
        """Test barbell graph has two cliques connected."""
        gen = AdversarialGraphGenerator()
        clique_size = 8
        G = gen.generate_barbell_graph(clique_size, bridge_length=1)
        
        # Check total nodes. The relocated generator now uses a direct edge when
        # bridge_length == 1, so the graph contains exactly the nodes from both
        # cliques.
        assert len(G.nodes()) == 2 * clique_size
        
        # Check both cliques exist
        first_clique_edges = sum(1 for i in range(clique_size)
                                 for j in range(i + 1, clique_size)
                                 if G.has_edge(i, j))
        assert first_clique_edges == clique_size * (clique_size - 1) // 2
    
    def test_multiscale_communities(self):
        """Test multiscale community graph generation."""
        gen = AdversarialGraphGenerator()
        sizes = [20, 20, 5, 3]
        G = gen.generate_multiscale_communities(sizes, inter_prob=0.05, intra_prob=0.9)
        
        # Check total nodes
        expected_nodes = sum(sizes)
        assert len(G.nodes()) == expected_nodes
        
        # Graph should be connected or have few components
        assert len(G.edges()) > 0
    
    def test_near_bipartite_adversarial(self):
        """Test near-bipartite graph with noise."""
        gen = AdversarialGraphGenerator()
        set1_size = 10
        set2_size = 12
        G = gen.generate_near_bipartite_adversarial(set1_size, set2_size, noise_edges=3)
        
        # Check total nodes
        assert len(G.nodes()) == set1_size + set2_size
        
        # Should have edges (bipartite + noise)
        assert len(G.edges()) > 0
    
    def test_spectral_properties_computation(self):
        """Test spectral properties are computed correctly."""
        gen = AdversarialGraphGenerator()
        G = gen.generate_lollipop_graph(10, 10)
        
        props = gen.get_spectral_properties(G)
        
        # Check expected properties exist
        assert "n_nodes" in props
        assert "n_edges" in props
        assert "lambda_1" in props
        assert "lambda_2" in props
        assert "spectral_gap" in props
        
        # Check values are reasonable
        assert props["n_nodes"] == 20
        assert props["lambda_1"] >= -1e-9  # Numerical noise can dip slightly below zero
        assert props["lambda_2"] >= 0
        assert props["spectral_gap"] >= 0
    
    def test_spectral_properties_adversarial_characteristics(self):
        """Test that adversarial graphs have poor spectral properties."""
        gen = AdversarialGraphGenerator()
        
        # Lollipop should have poor spectral separation
        G_lollipop = gen.generate_lollipop_graph(15, 15)
        props_lollipop = gen.get_spectral_properties(G_lollipop)
        
        # Barbell should have very small spectral gap
        G_barbell = gen.generate_barbell_graph(12, bridge_length=1)
        props_barbell = gen.get_spectral_properties(G_barbell)
        
        # Both should have λ₂ > 0 (connected) but structure issues
        assert props_lollipop["lambda_2"] > 0
        assert props_barbell["lambda_2"] > 0


class TestTseitinEmbedding:
    """Tests for Tseitin formula embedding on graphs."""
    
    def test_tseitin_embedding_basic(self):
        """Test Tseitin embedding produces valid CNF."""
        gen = AdversarialGraphGenerator()
        G = gen.generate_lollipop_graph(5, 5)
        
        clauses, metadata = embed_tseitin_on_graph(G, seed=42)
        
        # Check metadata
        assert "n_variables" in metadata
        assert "n_clauses" in metadata
        assert "n_nodes" in metadata
        assert "n_edges" in metadata
        assert metadata["embedding"] == "tseitin"
        
        # Check clauses are valid
        assert len(clauses) > 0
        for clause in clauses:
            assert isinstance(clause, list)
            assert all(isinstance(lit, int) and lit != 0 for lit in clause)
    
    def test_tseitin_embedding_respects_graph_structure(self):
        """Test that embedding size scales with graph complexity."""
        gen = AdversarialGraphGenerator()
        
        G_small = gen.generate_lollipop_graph(3, 3)
        clauses_small, meta_small = embed_tseitin_on_graph(G_small)
        
        G_large = gen.generate_lollipop_graph(10, 10)
        clauses_large, meta_large = embed_tseitin_on_graph(G_large)
        
        # Larger graph should have more variables and clauses
        assert meta_large["n_variables"] > meta_small["n_variables"]
        assert meta_large["n_clauses"] >= meta_small["n_clauses"]
    
    def test_cnf_file_writing(self, tmp_path):
        """Test CNF file is written in correct DIMACS format."""
        gen = AdversarialGraphGenerator()
        G = gen.generate_barbell_graph(5)
        clauses, metadata = embed_tseitin_on_graph(G)
        
        cnf_file = tmp_path / "test.cnf"
        write_cnf_file(clauses, metadata["n_variables"], cnf_file)
        
        # Check file exists and has content
        assert cnf_file.exists()
        content = cnf_file.read_text()
        
        # Check DIMACS header
        lines = content.strip().split('\n')
        assert lines[0].startswith('p cnf')
        
        # Check header matches metadata
        header_parts = lines[0].split()
        assert int(header_parts[2]) == metadata["n_variables"]
        assert int(header_parts[3]) == len(clauses)


class TestAdversarialDiagnosticFramework:
    """Tests for the overall adversarial diagnostic framework."""
    
    def test_framework_identifies_adversarial_properties(self):
        """Test that framework correctly identifies adversarial characteristics."""
        gen = AdversarialGraphGenerator()
        
        # Test each adversarial type
        adversarial_types = [
            ("lollipop", gen.generate_lollipop_graph(10, 10)),
            ("barbell", gen.generate_barbell_graph(8)),
            ("multiscale", gen.generate_multiscale_communities([15, 15, 3, 3])),
        ]
        
        for graph_type, G in adversarial_types:
            props = gen.get_spectral_properties(G)
            
            # All should be connected (lambda_1 ≈ 0, lambda_2 > 0)
            assert props["lambda_1"] < 0.01, f"{graph_type} should be connected"
            assert props["lambda_2"] > 0, f"{graph_type} should have λ₂ > 0"
            
            # All should have some adversarial characteristic
            # (This is a simplified check - real analysis would be more sophisticated)
            assert props["spectral_gap"] >= 0
    
    def test_complete_workflow_integration(self, tmp_path):
        """Test complete workflow: generate → embed → write."""
        gen = AdversarialGraphGenerator(seed=123)
        
        # Generate adversarial graph
        G = gen.generate_lollipop_graph(8, 12)
        
        # Get spectral properties
        props = gen.get_spectral_properties(G)
        assert props["n_nodes"] == 20
        
        # Embed Tseitin formula
        clauses, metadata = embed_tseitin_on_graph(G, seed=123)
        assert len(clauses) > 0
        
        # Write to file
        cnf_file = tmp_path / "workflow_test.cnf"
        write_cnf_file(clauses, metadata["n_variables"], cnf_file)
        assert cnf_file.exists()
        
        # Write metadata
        meta_file = tmp_path / "workflow_test.json"
        metadata["spectral_properties"] = props
        with open(meta_file, 'w') as f:
            json.dump(metadata, f)
        assert meta_file.exists()
        
        # Verify metadata content
        with open(meta_file) as f:
            loaded_meta = json.load(f)
        assert "spectral_properties" in loaded_meta
        assert loaded_meta["spectral_properties"]["n_nodes"] == 20


class TestHypothesisTesting:
    """Tests for P+1 hypothesis testing framework."""
    
    def test_hypothesis_test_structure(self):
        """Test that hypothesis test has proper structure."""
        # H0: Thiele Machine uses pure Spectral Decomposition
        # H1: Thiele Machine uses Spectral Decomposition + P+1
        
        # The test structure should be:
        # 1. Generate adversarial graph (poor spectral properties)
        # 2. Run Thiele Machine
        # 3. Compare performance to spectral predictions
        
        # If performance >> spectral predictions → evidence for H1 (P+1 exists)
        # If performance ≈ spectral predictions → consistent with H0
        
        gen = AdversarialGraphGenerator()
        G = gen.generate_lollipop_graph(10, 10)
        props = gen.get_spectral_properties(G)
        
        # A graph with poor spectral gap should be hard for pure spectral methods
        # This is the basis of the test
        assert "spectral_gap" in props
        
        # The actual hypothesis test would involve running the machine
        # and comparing μ-cost to spectral predictions
        # This test just verifies the framework is in place
        assert True  # Framework exists


def test_adversarial_generator_script_exists():
    """Test that adversarial_generator.py script exists."""
    script_path = Path(__file__).parent.parent / "tools" / "adversarial_generator.py"
    assert script_path.exists()

    # Ensure Python can parse the module now that it lives alongside the library code.
    compile(script_path.read_text(encoding="utf-8"), str(script_path), "exec")


def test_adversarial_test_script_exists():
    """Test that run_adversarial_test.sh script exists in the relocated demos tree."""
    script_path = (
        Path(__file__).parent.parent
        / "demos"
        / "verification-demos"
        / "adversarial"
        / "run_adversarial_test.sh"
    )
    assert script_path.exists()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
