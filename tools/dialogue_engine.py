"""Lightweight, test-friendly implementations of the Dialogue-of-the-One components.
These are intentionally import-safe: importing this module does not require torch to be
installed. All torch-dependent behavior is performed lazily inside functions/methods so
pytest.importorskip("torch") can correctly skip tests when torch is absent.
"""
from typing import Any, Dict


def _get_torch():
    try:
        import torch
        import torch.nn as nn
        return torch, nn
    except Exception:
        return None, None


def log_of_sight_to_tensor(log: Dict[str, Any], target_dim: int = 2048):
    """Convert a simple log-of-sight dictionary to a deterministic tensor-like list.
    If torch is present, returns a torch.FloatTensor; otherwise returns a list of floats.
    """
    torch, _ = _get_torch()
    s = str(sorted(log.items()))
    # Deterministic byte-based expansion
    data = [float((ord(c) % 256) / 255.0) for c in s]
    out = [0.0] * target_dim
    for i, v in enumerate(data):
        out[i % target_dim] += v
    if torch:
        return torch.tensor(out, dtype=torch.float32)
    return out


def tensor_to_log_of_sight(tensor) -> Dict[str, Any]:
    torch, _ = _get_torch()
    if torch and hasattr(tensor, 'tolist'):
        arr = tensor.tolist()
    else:
        arr = list(tensor)
    # Reduce to a small summary
    return {"sum": sum(arr), "len": len(arr)}


class LogOfSightEncoder:
    def __init__(self, input_dim: int = 2048, latent_dim: int = 512):
        self.input_dim = input_dim
        self.latent_dim = latent_dim

    def __call__(self, x):
        torch, _ = _get_torch()
        if torch is None:
            raise RuntimeError("PyTorch is required to run encoder forward.")
        # Simple deterministic projection for tests
        if x.shape[-1] != self.input_dim:
            raise ValueError("Unexpected input dim")
        mu = x[:, : self.latent_dim].float()
        logvar = x[:, : self.latent_dim].float() * 0.0
        z = mu
        return z, mu, logvar


class LogOfSightDecoder:
    def __init__(self, latent_dim: int = 512, output_dim: int = 2048):
        self.latent_dim = latent_dim
        self.output_dim = output_dim

    def __call__(self, z):
        torch, _ = _get_torch()
        if torch is None:
            raise RuntimeError("PyTorch is required to run decoder forward.")
        if z.shape[-1] != self.latent_dim:
            raise ValueError("Unexpected latent dim")
        # Expand by repeating
        rep = (self.output_dim + self.latent_dim - 1) // self.latent_dim
        out = z.repeat(1, rep)[:, : self.output_dim]
        return out


class LanguageSystem:
    def __init__(self, input_dim: int = 2048, latent_dim: int = 512, device: str = 'cpu'):
        # lightweight composition for tests
        self.alpha_encoder = LogOfSightEncoder(input_dim=input_dim, latent_dim=latent_dim)
        self.beta_encoder = LogOfSightEncoder(input_dim=input_dim, latent_dim=latent_dim)
        self.alpha_decoder = LogOfSightDecoder(latent_dim=latent_dim, output_dim=input_dim)
        self.beta_decoder = LogOfSightDecoder(latent_dim=latent_dim, output_dim=input_dim)
        self.device = device

    def train_step_alpha_to_beta(self, batch):
        torch, _ = _get_torch()
        if torch is None:
            raise RuntimeError("PyTorch required for training step")
        z, mu, logvar = self.alpha_encoder(batch)
        recon = self.beta_decoder(z)
        # Simple MSE surrogate
        loss = ((recon - batch) ** 2).mean().item()
        return float(loss)

    def train_step_beta_to_alpha(self, batch):
        torch, _ = _get_torch()
        if torch is None:
            raise RuntimeError("PyTorch required for training step")
        z, mu, logvar = self.beta_encoder(batch)
        recon = self.alpha_decoder(z)
        loss = ((recon - batch) ** 2).mean().item()
        return float(loss)


__all__ = [
    "LanguageSystem",
    "LogOfSightEncoder",
    "LogOfSightDecoder",
    "log_of_sight_to_tensor",
    "tensor_to_log_of_sight",
]
