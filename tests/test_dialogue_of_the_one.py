#!/usr/bin/env python3
"""
Test suite for the Dialogue of the One system.

This validates the core components of the three-phase system:
1. Mitosis (divergent objectives)
2. Babel Engine (VAE language system)
3. Final Dialogue (impossible problem solver)
"""

import sys
import json
from pathlib import Path

import pytest

torch = pytest.importorskip("torch", reason="PyTorch not available in test environment")

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


