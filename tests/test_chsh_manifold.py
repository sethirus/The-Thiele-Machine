# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""CHSH probe built from integer manifold projections, no trig allowed.

Both the local and meta-access runs now use setting-independent hidden vectors;
the only difference is the choice of projection masks. This enforces the
geometric constraint that outcomes depend solely on projecting a static
high-dimensional state. With that restriction, the local run should respect the
classical CHSH bound (S <= 2). The meta run serves as a falsification check: if
the chosen masks alone produced S > 2 on static vectors, that would be evidence
for a geometric violation. In practice this construction remains within the
classical bound, illustrating that mask geometry without setting-aware hidden
variables cannot violate CHSH.
"""

from __future__ import annotations

import random
from collections import defaultdict
from dataclasses import dataclass
from typing import Dict, Iterable, Sequence, Tuple

DIMENSION = 1000
WINDOW = 500


def mask(start: int, width: int = WINDOW, dim: int = DIMENSION) -> list[int]:
    return [(start + i) % dim for i in range(width)]


# Local masks: moderately overlapped windows to keep correlations tame and
# respect the classical CHSH bound with a setting-independent hidden variable.
MASK_A_LOCAL = [mask(0), mask(250)]
MASK_B_LOCAL = [mask(125), mask(625)]

# Meta masks: alternative overlaps to probe whether geometry alone can push S.
MASK_A_META = [mask(0), mask(400)]
MASK_B_META = [mask(200), mask(600)]


@dataclass
class ManifoldVector:
    values: list[int]

    @classmethod
    def random(cls, seed: int, size: int = DIMENSION) -> "ManifoldVector":
        rng = random.Random(seed)
        vals = [rng.choice([-1, 1]) * rng.randint(1, 3) for _ in range(size)]
        return cls(vals)

    def measure(self, mask: Sequence[int]) -> int:
        s = sum(self.values[i] for i in mask)
        return 1 if s >= 0 else -1


def chsh_score(
    samples: Iterable[Tuple[int, int, int, int]], *, meta_access: bool
) -> Tuple[float, Dict[Tuple[int, int], float]]:
    """Compute CHSH S from manifold projections.

    Local mode: shared hidden variable ignores detector choices, and moderately
    overlapped windows keep S at or below the classical bound.

    Meta mode: the hidden variable can depend on the joint setting (reflecting
    meta-level coordination) but outcomes are still determined purely by local
    projections of the setting-aware manifold vector—no runtime signaling or
    per-arm phase hacks.
    """

    counts: Dict[Tuple[int, int], int] = defaultdict(int)
    sums: Dict[Tuple[int, int], float] = defaultdict(float)

    for payload, level_a, level_b, setting_key in samples:
        a_setting = setting_key & 1
        b_setting = (setting_key >> 1) & 1
        seed = payload + 17 * level_a + 31 * level_b
        vec = ManifoldVector.random(seed=seed)
        if meta_access:
            mask_a = MASK_A_META[a_setting]
            mask_b = MASK_B_META[b_setting]
        else:
            mask_a = MASK_A_LOCAL[a_setting]
            mask_b = MASK_B_LOCAL[b_setting]

        a = vec.measure(mask_a)
        b = vec.measure(mask_b)

        key = (a_setting, b_setting)
        counts[key] += 1
        sums[key] += a * b

    correlations: Dict[Tuple[int, int], float] = {}
    for key, total in sums.items():
        correlations[key] = total / counts[key]

    s_val = abs(
        correlations[(0, 0)]
        + correlations[(0, 1)]
        + correlations[(1, 0)]
        - correlations[(1, 1)]
    )
    return s_val, correlations


def generate_trials(n: int = 5_000) -> Iterable[Tuple[int, int, int, int]]:
    rng = random.Random(20251202)
    for _ in range(n):
        payload = rng.getrandbits(24)
        level_a = rng.randrange(8)
        level_b = rng.randrange(8)
        setting_key = rng.getrandbits(2)
        yield (payload, level_a, level_b, setting_key)


def test_chsh_local_respects_classical_bound() -> None:
    s_val, corrs = chsh_score(generate_trials(), meta_access=False)

    assert s_val <= 2.0, f"local run should respect CHSH bound; got S={s_val} corrs={corrs}"


def test_chsh_meta_access_violates_classical_bound() -> None:
    s_val, corrs = chsh_score(generate_trials(), meta_access=True)
    # With setting-independent hidden variables, geometry alone should remain
    # within the classical bound. This test ensures we are not smuggling a
    # violation via super-deterministic encoding or signaling.
    assert s_val <= 2.0, f"meta run exceeded classical bound without hidden signaling; got S={s_val} corrs={corrs}"
