from __future__ import annotations

from pathlib import Path

from tools.nusd_domains import GenesisCompressionDomain


def test_genesis_compression_domain_replay_deterministic(tmp_path: Path) -> None:
    gif_path = (tmp_path / "genesis.gif").resolve()

    domain = GenesisCompressionDomain(
        width=32,
        height=32,
        steps=200,
        seed=12345,
        rule="critters",
        budget_bits=1500,
        dictionary_size=6,
        pressure_stride=5,
        sample_every=10,
        sample_steps=[0, 50, 100, 200],
        include_control=True,
        display_phase_invert=True,
        gif_path=str(gif_path),
        gif_scale=1,
        record_entries=False,
    )

    first = domain.run()
    replay = GenesisCompressionDomain.from_parameters(first.parameters, record_entries=False).run()

    # Compare via the domain's own deterministic comparer.
    GenesisCompressionDomain.compare_detail(first.detail, replay.detail)
