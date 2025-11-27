# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""Monte Carlo probe of self-referential density in the Thiele instruction space."""

from __future__ import annotations

import random
from typing import Iterable, Tuple

import pytest

from thielecpu.isa import Opcode, decode


def _chunk_bytes(data: bytes, size: int = 4) -> Iterable[bytes]:
    for idx in range(0, len(data), size):
        yield data[idx : idx + size]


def _decode_program(data: bytes) -> list[Tuple[Opcode, int, int]] | None:
    """Decode a program as 4-byte instruction words.

    Returns ``None`` if any instruction fails to decode or if the payload is
    not a multiple of 4 bytes.
    """

    if len(data) % 4 != 0:
        return None
    decoded: list[Tuple[Opcode, int, int]] = []
    try:
        for word in _chunk_bytes(data, 4):
            decoded.append(decode(word))
    except ValueError:
        return None
    return decoded


def sample_density(n_bits: int, samples: int = 20000, seed: int = 20251120) -> tuple[int, int, float]:
    rng = random.Random(seed + n_bits)
    valid = 0
    self_referential = 0
    byte_len = n_bits // 8

    for _ in range(samples):
        payload = bytearray(rng.getrandbits(n_bits).to_bytes(byte_len, byteorder="big"))
        # Normalise the reserved byte of every instruction word so randomly
        # generated payloads have a non-negligible chance of being decodable.
        for word_start in range(0, len(payload), 4):
            if word_start + 3 < len(payload):
                payload[word_start + 3] = 0

        decoded = _decode_program(payload)
        if decoded is None:
            continue
        valid += 1
        # Treat EMIT-bearing programs as the interaction surface: they can
        # project information out of the manifold in the current toolchain.
        if any(opcode is Opcode.EMIT for opcode, _, _ in decoded):
            self_referential += 1

    ratio = self_referential / valid if valid else 0.0
    return valid, self_referential, ratio


@pytest.mark.parametrize("n_bits", [16, 32, 64])
def test_self_reference_density_not_trivial(n_bits: int) -> None:
    valid, self_ref, ratio = sample_density(n_bits)

    if valid == 0:
        pytest.skip(f"no valid programs encountered at length {n_bits} bits")

    assert self_ref > 0, f"no EMIT-bearing programs found among {valid} valid samples at {n_bits} bits"
    assert 0.0 < ratio < 1.0, f"density must be a non-trivial ratio, got {ratio}"
    assert ratio < 0.2, f"density {ratio} unexpectedly large for random sampling at {n_bits} bits"
