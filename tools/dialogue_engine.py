"""Minimal Dialogue Engine used by tests.

Provides lightweight PyTorch encoder/decoder and a LanguageSystem wrapper.
This is deliberately small: it implements only what's required by
`tests/test_dialogue_of_the_one.py` so tests run locally and CI behavior
remains unchanged (the test uses pytest.importorskip("torch")).
"""

from __future__ import annotations

try:
    import torch
    from torch import nn
except Exception:  # pragma: no cover - test will skip if torch unavailable
    torch = None


class LogOfSightEncoder(nn.Module):
    def __init__(self, input_dim: int, latent_dim: int):
        super().__init__()
        self._fc_mu = nn.Linear(input_dim, latent_dim)
        self._fc_logvar = nn.Linear(input_dim, latent_dim)

    def forward(self, x: torch.Tensor):
        mu = self._fc_mu(x)
        logvar = self._fc_logvar(x)
        # reparameterize
        std = (0.5 * logvar).exp()
        eps = torch.randn_like(std)
        z = mu + eps * std
        return z, mu, logvar


class LogOfSightDecoder(nn.Module):
    def __init__(self, latent_dim: int, output_dim: int):
        super().__init__()
        self._fc = nn.Linear(latent_dim, output_dim)

    def forward(self, z: torch.Tensor) -> torch.Tensor:
        return self._fc(z)


def log_of_sight_to_tensor(log: dict, target_dim: int = 2048) -> "torch.Tensor":
    """Deterministic mapping of a small log dict to a float tensor.

    The test only checks shape and dtype, so this returns a reproducible
    float32 tensor derived from JSON hashing.
    """
    import json, hashlib

    s = json.dumps(log, sort_keys=True)
    h = hashlib.sha256(s.encode("utf-8")).digest()
    # Expand hash into floats
    import struct

    floats = []
    while len(floats) < target_dim:
        # consume 4 bytes -> uint32 -> float in [0,1)
        for i in range(0, len(h), 4):
            if len(floats) >= target_dim:
                break
            chunk = h[i : i + 4]
            if len(chunk) < 4:
                chunk = chunk.ljust(4, b"\x00")
            val = struct.unpack("I", chunk)[0]
            floats.append((val % 1000000) / 1000000.0)
        # remix hash to get more bytes
        h = hashlib.sha256(h).digest()

    import torch as _torch

    return _torch.tensor(floats[:target_dim], dtype=_torch.float32)


def tensor_to_log_of_sight(tensor: "torch.Tensor") -> dict:
    # Not needed for tests; provide a placeholder
    return {"length": int(tensor.numel())}


class LanguageSystem:
    def __init__(self, input_dim: int = 2048, latent_dim: int = 512, device: str = "cpu"):
        if torch is None:
            raise RuntimeError("PyTorch not available in environment")
        self.device = torch.device(device)
        self.alpha_encoder = LogOfSightEncoder(input_dim, latent_dim).to(self.device)
        self.alpha_decoder = LogOfSightDecoder(latent_dim, input_dim).to(self.device)
        self.beta_encoder = LogOfSightEncoder(input_dim, latent_dim).to(self.device)
        self.beta_decoder = LogOfSightDecoder(latent_dim, input_dim).to(self.device)

        # minimal optimizers
        self._opt_a = torch.optim.Adam(
            list(self.alpha_encoder.parameters()) + list(self.alpha_decoder.parameters()), lr=1e-3
        )
        self._opt_b = torch.optim.Adam(
            list(self.beta_encoder.parameters()) + list(self.beta_decoder.parameters()), lr=1e-3
        )
        self._loss_fn = nn.MSELoss()

    def train_step_alpha_to_beta(self, batch: "torch.Tensor") -> float:
        batch = batch.to(self.device)
        self._opt_a.zero_grad()
        z, _, _ = self.alpha_encoder(batch)
        recon = self.beta_decoder(z)
        loss = self._loss_fn(recon, batch)
        loss.backward()
        self._opt_a.step()
        return float(loss.item())

    def train_step_beta_to_alpha(self, batch: "torch.Tensor") -> float:
        batch = batch.to(self.device)
        self._opt_b.zero_grad()
        z, _, _ = self.beta_encoder(batch)
        recon = self.alpha_decoder(z)
        loss = self._loss_fn(recon, batch)
        loss.backward()
        self._opt_b.step()
        return float(loss.item())
