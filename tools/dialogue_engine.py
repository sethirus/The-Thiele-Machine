#!/usr/bin/env python3
"""
The Babel Engine - The Invention of Language

This module implements the neural network-based language system that allows
Alpha and Beta to communicate through compressed latent representations of
their internal "Logs of Sight".

The system uses Variational Autoencoders (VAE) to:
1. Encode high-dimensional Log of Sight JSON objects into low-dimensional latent vectors
2. Decode latent vectors back into Log of Sight representations

Through iterative training, the two minds develop a shared language optimized
for lossless communication of their internal states.
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
import json
import numpy as np
from pathlib import Path
from typing import Dict, Any, List, Tuple, Optional


class _SimpleAdam:
    def __init__(
        self,
        params,
        lr: float = 0.001,
        betas: Tuple[float, float] = (0.9, 0.999),
        eps: float = 1e-8,
    ):
        self._params = [p for p in params if p.requires_grad]
        self._lr = lr
        self._beta1, self._beta2 = betas
        self._eps = eps
        self._state: Dict[int, Dict[str, Any]] = {}

    def zero_grad(self) -> None:
        for p in self._params:
            p.grad = None

    @torch.no_grad()
    def step(self) -> None:
        for p in self._params:
            if p.grad is None:
                continue
            sid = id(p)
            st = self._state.get(sid)
            if st is None:
                st = {
                    "t": 0,
                    "m": torch.zeros_like(p),
                    "v": torch.zeros_like(p),
                }
                self._state[sid] = st

            st["t"] += 1
            t = st["t"]
            g = p.grad
            m = st["m"]
            v = st["v"]

            m.mul_(self._beta1).add_(g, alpha=1.0 - self._beta1)
            v.mul_(self._beta2).addcmul_(g, g, value=1.0 - self._beta2)

            m_hat = m / (1.0 - (self._beta1**t))
            v_hat = v / (1.0 - (self._beta2**t))
            p.addcdiv_(m_hat, v_hat.sqrt().add_(self._eps), value=-self._lr)


class LogOfSightEncoder(nn.Module):
    """
    Encoder network that compresses a Log of Sight into a latent vector.
    
    Architecture:
    - Input: Flattened representation of Log of Sight (variable size)
    - Hidden layers: Progressive dimensionality reduction
    - Output: Latent vector (512 dimensions)
    """
    
    def __init__(self, input_dim: int = 2048, latent_dim: int = 512, hidden_dims: List[int] = None):
        """
        Initialize the encoder.
        
        Args:
            input_dim: Dimension of flattened input
            latent_dim: Dimension of latent space (the "word" size)
            hidden_dims: List of hidden layer dimensions
        """
        super(LogOfSightEncoder, self).__init__()
        
        if hidden_dims is None:
            hidden_dims = [1024, 768, 512]
        
        self.input_dim = input_dim
        self.latent_dim = latent_dim
        
        # Build encoder layers
        layers = []
        prev_dim = input_dim
        
        for hidden_dim in hidden_dims:
            layers.append(nn.Linear(prev_dim, hidden_dim))
            layers.append(nn.ReLU())
            layers.append(nn.Dropout(0.2))
            prev_dim = hidden_dim
        
        self.encoder = nn.Sequential(*layers)
        
        # VAE parameters: mean and log variance
        self.fc_mu = nn.Linear(prev_dim, latent_dim)
        self.fc_logvar = nn.Linear(prev_dim, latent_dim)
    
    def forward(self, x: torch.Tensor) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        """
        Forward pass through encoder.
        
        Args:
            x: Input tensor (batch_size, input_dim)
        
        Returns:
            Tuple of (encoded latent vector, mu, logvar)
        """
        h = self.encoder(x)
        mu = self.fc_mu(h)
        logvar = self.fc_logvar(h)
        
        # Reparameterization trick
        std = torch.exp(0.5 * logvar)
        eps = torch.randn_like(std)
        z = mu + eps * std
        
        return z, mu, logvar


class LogOfSightDecoder(nn.Module):
    """
    Decoder network that reconstructs a Log of Sight from a latent vector.
    
    Architecture:
    - Input: Latent vector (512 dimensions)
    - Hidden layers: Progressive dimensionality expansion
    - Output: Reconstructed Log of Sight (variable size)
    """
    
    def __init__(self, latent_dim: int = 512, output_dim: int = 2048, hidden_dims: List[int] = None):
        """
        Initialize the decoder.
        
        Args:
            latent_dim: Dimension of latent space
            output_dim: Dimension of output (matches encoder input_dim)
            hidden_dims: List of hidden layer dimensions (in reverse order from encoder)
        """
        super(LogOfSightDecoder, self).__init__()
        
        if hidden_dims is None:
            hidden_dims = [512, 768, 1024]
        
        self.latent_dim = latent_dim
        self.output_dim = output_dim
        
        # Build decoder layers
        layers = []
        prev_dim = latent_dim
        
        for hidden_dim in hidden_dims:
            layers.append(nn.Linear(prev_dim, hidden_dim))
            layers.append(nn.ReLU())
            layers.append(nn.Dropout(0.2))
            prev_dim = hidden_dim
        
        layers.append(nn.Linear(prev_dim, output_dim))
        
        self.decoder = nn.Sequential(*layers)
    
    def forward(self, z: torch.Tensor) -> torch.Tensor:
        """
        Forward pass through decoder.
        
        Args:
            z: Latent vector (batch_size, latent_dim)
        
        Returns:
            Reconstructed output (batch_size, output_dim)
        """
        return self.decoder(z)


class LanguageSystem:
    """
    Complete language system managing encoder/decoder pairs for both minds.
    """
    
    def __init__(self, input_dim: int = 2048, latent_dim: int = 512, device: str = 'cpu'):
        """
        Initialize the language system.
        
        Args:
            input_dim: Dimension of Log of Sight representation
            latent_dim: Dimension of latent "word" space
            device: Device to run on ('cpu' or 'cuda')
        """
        self.device = device
        self.input_dim = input_dim
        self.latent_dim = latent_dim
        
        # Create encoder/decoder for Alpha
        self.alpha_encoder = LogOfSightEncoder(input_dim, latent_dim).to(device)
        self.alpha_decoder = LogOfSightDecoder(latent_dim, input_dim).to(device)
        
        # Create encoder/decoder for Beta
        self.beta_encoder = LogOfSightEncoder(input_dim, latent_dim).to(device)
        self.beta_decoder = LogOfSightDecoder(latent_dim, input_dim).to(device)

        # Optimizers
        # Lazily constructed on first training step. This avoids importing
        # optional/fragile torch subsystems (e.g., dynamo) during simple
        # initialization and test-time construction.
        self.alpha_optimizer = None
        self.beta_optimizer = None

    def _ensure_optimizers(self) -> None:
        if self.alpha_optimizer is None:
            self.alpha_optimizer = _SimpleAdam(
                list(self.alpha_encoder.parameters()) + list(self.alpha_decoder.parameters()),
                lr=0.001,
            )
        if self.beta_optimizer is None:
            self.beta_optimizer = _SimpleAdam(
                list(self.beta_encoder.parameters()) + list(self.beta_decoder.parameters()),
                lr=0.001,
            )
    
    def vae_loss(self, recon_x: torch.Tensor, x: torch.Tensor, 
                 mu: torch.Tensor, logvar: torch.Tensor) -> torch.Tensor:
        """
        VAE loss function combining reconstruction loss and KL divergence.
        
        Args:
            recon_x: Reconstructed output
            x: Original input
            mu: Mean of latent distribution
            logvar: Log variance of latent distribution
        
        Returns:
            Total loss
        """
        # Reconstruction loss (MSE)
        recon_loss = F.mse_loss(recon_x, x, reduction='sum')
        
        # KL divergence loss
        kl_loss = -0.5 * torch.sum(1 + logvar - mu.pow(2) - logvar.exp())
        
        return recon_loss + kl_loss
    
    def train_step_alpha_to_beta(self, log_of_sight: torch.Tensor) -> float:
        """
        Train on Alpha encoding -> Beta decoding.
        
        Args:
            log_of_sight: Input Log of Sight tensor
        
        Returns:
            Loss value
        """
        self.alpha_encoder.train()
        self.beta_decoder.train()

        self._ensure_optimizers()
        
        # Alpha encodes
        z, mu, logvar = self.alpha_encoder(log_of_sight)
        
        # Beta decodes
        recon = self.beta_decoder(z)
        
        # Compute loss
        loss = self.vae_loss(recon, log_of_sight, mu, logvar)
        
        # Backprop through both networks
        self.alpha_optimizer.zero_grad()
        self.beta_optimizer.zero_grad()
        loss.backward()
        self.alpha_optimizer.step()
        self.beta_optimizer.step()
        
        return loss.item()
    
    def train_step_beta_to_alpha(self, log_of_sight: torch.Tensor) -> float:
        """
        Train on Beta encoding -> Alpha decoding.
        
        Args:
            log_of_sight: Input Log of Sight tensor
        
        Returns:
            Loss value
        """
        self.beta_encoder.train()
        self.alpha_decoder.train()

        self._ensure_optimizers()
        
        # Beta encodes
        z, mu, logvar = self.beta_encoder(log_of_sight)
        
        # Alpha decodes
        recon = self.alpha_decoder(z)
        
        # Compute loss
        loss = self.vae_loss(recon, log_of_sight, mu, logvar)
        
        # Backprop through both networks
        self.alpha_optimizer.zero_grad()
        self.beta_optimizer.zero_grad()
        loss.backward()
        self.alpha_optimizer.step()
        self.beta_optimizer.step()
        
        return loss.item()
    
    def save_models(self, output_dir: Path):
        """
        Save all models to disk.
        
        Args:
            output_dir: Directory to save models
        """
        output_dir.mkdir(parents=True, exist_ok=True)
        
        torch.save(self.alpha_encoder.state_dict(), output_dir / 'alpha_encoder.pth')
        torch.save(self.alpha_decoder.state_dict(), output_dir / 'alpha_decoder.pth')
        torch.save(self.beta_encoder.state_dict(), output_dir / 'beta_encoder.pth')
        torch.save(self.beta_decoder.state_dict(), output_dir / 'beta_decoder.pth')
        
        # Save configuration
        config = {
            'input_dim': self.input_dim,
            'latent_dim': self.latent_dim,
            'device': self.device
        }
        with open(output_dir / 'language_config.json', 'w') as f:
            json.dump(config, f, indent=2)
    
    def load_models(self, model_dir: Path):
        """
        Load all models from disk.
        
        Args:
            model_dir: Directory containing saved models
        """
        self.alpha_encoder.load_state_dict(torch.load(model_dir / 'alpha_encoder.pth'))
        self.alpha_decoder.load_state_dict(torch.load(model_dir / 'alpha_decoder.pth'))
        self.beta_encoder.load_state_dict(torch.load(model_dir / 'beta_encoder.pth'))
        self.beta_decoder.load_state_dict(torch.load(model_dir / 'beta_decoder.pth'))


def log_of_sight_to_tensor(log_dict: Dict[str, Any], target_dim: int = 2048) -> torch.Tensor:
    """
    Convert a Log of Sight dictionary to a fixed-size tensor.
    
    This flattens and pads/truncates the log to a standard size.
    
    Args:
        log_dict: Dictionary representing the Log of Sight
        target_dim: Target dimensionality
    
    Returns:
        Tensor of shape (target_dim,)
    """
    # Convert to JSON string and then to bytes
    json_str = json.dumps(log_dict, sort_keys=True)
    json_bytes = json_str.encode('utf-8')
    
    # Convert bytes to numpy array
    byte_array = np.frombuffer(json_bytes, dtype=np.uint8)
    
    # Normalize to [0, 1]
    normalized = byte_array.astype(np.float32) / 255.0
    
    # Pad or truncate to target dimension
    if len(normalized) < target_dim:
        # Pad with zeros
        padded = np.zeros(target_dim, dtype=np.float32)
        padded[:len(normalized)] = normalized
        return torch.from_numpy(padded)
    else:
        # Truncate
        return torch.from_numpy(normalized[:target_dim])


def tensor_to_log_of_sight(tensor: torch.Tensor) -> Dict[str, Any]:
    """
    Convert a tensor back to a Log of Sight dictionary (best effort).
    
    This is an approximate reconstruction.
    
    Args:
        tensor: Tensor representation
    
    Returns:
        Dictionary (may not be valid JSON)
    """
    # Convert back to bytes
    denormalized = (tensor.cpu().numpy() * 255.0).astype(np.uint8)
    
    # Find where padding starts (first long run of zeros)
    nonzero = np.where(denormalized > 0)[0]
    if len(nonzero) > 0:
        end_idx = nonzero[-1] + 1
        denormalized = denormalized[:end_idx]
    
    # Try to decode as JSON
    try:
        json_str = denormalized.tobytes().decode('utf-8', errors='ignore')
        return json.loads(json_str)
    except (json.JSONDecodeError, UnicodeDecodeError):
        # Return a placeholder if decoding fails
        return {
            "error": "Reconstruction failed",
            "raw_data": denormalized.tolist()[:100]  # First 100 bytes
        }


if __name__ == "__main__":
    # Test the language system
    print("Testing Babel Engine...")
    
    # Create a sample Log of Sight
    sample_log = {
        "strategy": "test_strategy",
        "primitives_used": ["PARTITION", "CLUSTER", "REFINE"],
        "fitness": 0.85,
        "metadata": {
            "generation": 42,
            "parent": "strategy_alpha"
        }
    }
    
    # Convert to tensor
    log_tensor = log_of_sight_to_tensor(sample_log)
    print(f"Log tensor shape: {log_tensor.shape}")
    
    # Create language system
    lang_system = LanguageSystem()
    
    # Test encoding/decoding
    log_batch = log_tensor.unsqueeze(0)  # Add batch dimension
    
    with torch.no_grad():
        # Alpha encodes
        z_alpha, _, _ = lang_system.alpha_encoder(log_batch)
        print(f"Alpha latent vector shape: {z_alpha.shape}")
        
        # Beta decodes
        recon_beta = lang_system.beta_decoder(z_alpha)
        print(f"Beta reconstruction shape: {recon_beta.shape}")
    
    print("\nBabel Engine test complete.")
