#!/usr/bin/env python3
"""
Test suite for the Dialogue of the One system.

This validates the core components of the three-phase system:
1. Mitosis (divergent objectives)
2. Babel Engine (VAE language system)
3. Final Dialogue (impossible problem solver)
"""

import pytest
import sys
import json
import torch
from pathlib import Path

# Add base directory to path
BASE_DIR = Path(__file__).parent.parent
sys.path.insert(0, str(BASE_DIR))

from tools.dialogue_engine import (
    LanguageSystem, 
    LogOfSightEncoder, 
    LogOfSightDecoder,
    log_of_sight_to_tensor,
    tensor_to_log_of_sight
)


class TestDialogueEngine:
    """Test the Babel Engine components."""
    
    def test_encoder_architecture(self):
        """Test encoder creates correct latent dimensions."""
        encoder = LogOfSightEncoder(input_dim=2048, latent_dim=512)
        
        # Create dummy input
        x = torch.randn(1, 2048)
        
        # Forward pass
        z, mu, logvar = encoder(x)
        
        assert z.shape == (1, 512), f"Expected latent shape (1, 512), got {z.shape}"
        assert mu.shape == (1, 512), f"Expected mu shape (1, 512), got {mu.shape}"
        assert logvar.shape == (1, 512), f"Expected logvar shape (1, 512), got {logvar.shape}"
    
    def test_decoder_architecture(self):
        """Test decoder reconstructs correct dimensions."""
        decoder = LogOfSightDecoder(latent_dim=512, output_dim=2048)
        
        # Create dummy latent vector
        z = torch.randn(1, 512)
        
        # Forward pass
        recon = decoder(z)
        
        assert recon.shape == (1, 2048), f"Expected output shape (1, 2048), got {recon.shape}"
    
    def test_log_of_sight_conversion(self):
        """Test Log of Sight to tensor conversion."""
        # Create sample log
        log = {
            "strategy": "test",
            "primitives": ["A", "B", "C"],
            "fitness": 0.85
        }
        
        # Convert to tensor
        tensor = log_of_sight_to_tensor(log, target_dim=2048)
        
        assert tensor.shape == (2048,), f"Expected shape (2048,), got {tensor.shape}"
        assert tensor.dtype == torch.float32, f"Expected float32, got {tensor.dtype}"
    
    def test_language_system_initialization(self):
        """Test language system initializes correctly."""
        lang_system = LanguageSystem(input_dim=2048, latent_dim=512, device='cpu')
        
        assert lang_system.alpha_encoder is not None
        assert lang_system.alpha_decoder is not None
        assert lang_system.beta_encoder is not None
        assert lang_system.beta_decoder is not None
    
    def test_language_system_training_step(self):
        """Test a single training step doesn't crash."""
        lang_system = LanguageSystem(input_dim=2048, latent_dim=512, device='cpu')
        
        # Create dummy data
        batch = torch.randn(4, 2048)
        
        # Train Alpha -> Beta
        loss_a2b = lang_system.train_step_alpha_to_beta(batch)
        assert isinstance(loss_a2b, float), "Loss should be a float"
        assert loss_a2b >= 0, "Loss should be non-negative"
        
        # Train Beta -> Alpha
        loss_b2a = lang_system.train_step_beta_to_alpha(batch)
        assert isinstance(loss_b2a, float), "Loss should be a float"
        assert loss_b2a >= 0, "Loss should be non-negative"


class TestObjectiveDefinitions:
    """Test the objective genomes for Alpha and Beta."""
    
    def test_alpha_objective_structure(self):
        """Test Alpha's elegance objective is well-formed."""
        objective_file = BASE_DIR / 'alpha' / 'objectives' / 'objective_alpha.thiele'
        
        if not objective_file.exists():
            pytest.skip("Alpha objective file not found")
        
        with open(objective_file, 'r') as f:
            objective = json.load(f)
        
        assert objective['name'] == "Elegance Maximization v1.0"
        assert objective['function'] == "weighted_sum"
        assert 'accuracy' in objective['components']
        assert 'elegance' in objective['components']
        assert objective['components']['accuracy']['weight'] == 0.8
        assert objective['components']['elegance']['weight'] == 0.2
    
    def test_beta_objective_structure(self):
        """Test Beta's novelty objective is well-formed."""
        objective_file = BASE_DIR / 'beta' / 'objectives' / 'objective_beta.thiele'
        
        if not objective_file.exists():
            pytest.skip("Beta objective file not found")
        
        with open(objective_file, 'r') as f:
            objective = json.load(f)
        
        assert objective['name'] == "Novelty Maximization v1.0"
        assert objective['function'] == "weighted_sum"
        assert 'accuracy' in objective['components']
        assert 'novelty' in objective['components']
        assert objective['components']['accuracy']['weight'] == 0.8
        assert objective['components']['novelty']['weight'] == 0.2


class TestImpossibleProblem:
    """Test the synthesis challenge definition."""
    
    def test_problem_definition(self):
        """Test the impossible problem is well-defined."""
        problem_file = BASE_DIR / 'problems' / 'synthesis_challenge.thiele'
        
        if not problem_file.exists():
            pytest.skip("Problem file not found")
        
        with open(problem_file, 'r') as f:
            problem = json.load(f)
        
        assert problem['name'] == "Synthesis Challenge"
        assert problem['type'] == "graph_coloring"
        assert 'constraints' in problem
        assert 'elegance_requirement' in problem['constraints']
        assert 'novelty_requirement' in problem['constraints']
        assert 'validity_requirement' in problem['constraints']
    
    def test_problem_contradictory_constraints(self):
        """Verify the problem has contradictory constraints."""
        problem_file = BASE_DIR / 'problems' / 'synthesis_challenge.thiele'
        
        if not problem_file.exists():
            pytest.skip("Problem file not found")
        
        with open(problem_file, 'r') as f:
            problem = json.load(f)
        
        constraints = problem['constraints']
        
        # Elegance should minimize primitive count
        assert constraints['elegance_requirement']['target'] == "minimize"
        
        # Novelty should maximize primitive novelty
        assert constraints['novelty_requirement']['target'] == "maximize"
        
        # These are contradictory: minimizing primitives means reusing proven ones (low novelty)


class TestEvaluationFunctions:
    """Test custom evaluation functions."""
    
    def test_primitive_novelty_function_exists(self):
        """Test that Beta has the evaluate_primitive_novelty function."""
        # Import from Beta's tools directory
        import importlib.util
        
        beta_eval_file = BASE_DIR / 'beta' / 'tools' / 'evaluation_functions.py'
        
        if not beta_eval_file.exists():
            pytest.skip("Beta evaluation functions file not found")
        
        # Load the module directly
        spec = importlib.util.spec_from_file_location("beta_evaluation_functions", beta_eval_file)
        beta_eval = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(beta_eval)
        
        # Check the function exists
        assert hasattr(beta_eval, 'evaluate_primitive_novelty'), \
            "evaluate_primitive_novelty not found in Beta's evaluation_functions"
        
        # Test with sample data
        strategy_code = "prim_A\nprim_B\nprim_C"
        score = beta_eval.evaluate_primitive_novelty(
            strategy_code, "test", {"history_file": "nonexistent.json"}
        )
        
        # Should return 1.0 when no history exists (all primitives are novel)
        assert score == 1.0, f"Expected score 1.0 for novel primitives, got {score}"


def test_end_to_end_integration():
    """Test that the full system can run without errors."""
    # This is a minimal integration test
    # Full E2E test would require running all three phases
    
    # Test that we can create a language system
    lang_system = LanguageSystem(input_dim=512, latent_dim=128, device='cpu')
    
    # Test that we can create a Log of Sight and convert it
    log = {"test": "data", "value": 42}
    tensor = log_of_sight_to_tensor(log, target_dim=512)
    
    # Test that we can encode and decode
    batch = tensor.unsqueeze(0)
    
    with torch.no_grad():
        # Alpha encodes
        z, _, _ = lang_system.alpha_encoder(batch)
        
        # Beta decodes
        recon = lang_system.beta_decoder(z)
    
    assert recon.shape == batch.shape, "Reconstruction shape should match input"


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v"])
