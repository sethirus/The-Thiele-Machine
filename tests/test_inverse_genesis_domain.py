from __future__ import annotations

import math

from tools.nusd_domains import InverseGenesisDomain


def test_inverse_genesis_discovers_stable_invariant() -> None:
    domain = InverseGenesisDomain(
        seed=20251226,
        steps=512,
        dt=0.01,
        noise_std=0.0015,
        trajectories=4,
        max_terms=6,
        min_gain_bits=0.1,
        bits_per_sample=64.0,
        record_entries=True,
    )
    result = domain.run()

    assert result.detail["dataset"]["samples_total"] == 512 * 4
    candidate = result.detail["candidate"]

    # Falsifiable: invariant should be meaningfully more compressive than raw samples.
    assert float(candidate["compression_ratio"]) > 5.0

    # It doesn't have to be perfect (noisy data), but it should be stable.
    rel_std = float(candidate.get("relative_std", 1.0))
    assert rel_std < 0.15

    # Ensure we actually discovered a non-trivial expression.
    assert len(candidate.get("terms", [])) >= 2
    assert "expression" in candidate


def test_inverse_genesis_replay_is_deterministic() -> None:
    params = {
        "system": "double_pendulum",
        "seed": 7,
        "steps": 256,
        "dt": 0.02,
        "noise_std": 0.0,
        "trajectories": 3,
        "max_terms": 5,
        "min_gain_bits": 0.1,
        "bits_per_sample": 64.0,
    }

    a = InverseGenesisDomain.from_parameters(params, record_entries=False).run()
    b = InverseGenesisDomain.from_parameters(params, record_entries=False).run()

    assert math.isclose(float(a.mdl["total_bits"]), float(b.mdl["total_bits"]), rel_tol=0.0, abs_tol=0.0)
    assert a.detail["candidate"]["terms"] == b.detail["candidate"]["terms"]
    assert a.detail["candidate"]["coefficients"] == b.detail["candidate"]["coefficients"]
    assert a.detail["dataset"]["digest"] == b.detail["dataset"]["digest"]
