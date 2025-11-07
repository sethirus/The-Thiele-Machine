"""Focused unit tests for verifier.signature_utils trust manifest helpers."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from verifier.signature_utils import (
    TrustManifest,
    TrustManifestError,
    load_trust_manifest,
)


@pytest.fixture
def manifest_path(tmp_path: Path) -> Path:
    return tmp_path / "trust_manifest.json"


def write_manifest(path: Path, payload: dict) -> Path:
    path.write_text(json.dumps(payload), encoding="utf-8")
    return path


def test_load_trust_manifest_requires_trusted_keys(manifest_path: Path) -> None:
    write_manifest(manifest_path, {"unexpected": {}})
    with pytest.raises(TrustManifestError, match="must contain a 'trusted_keys'"):
        load_trust_manifest(manifest_path)


def test_load_trust_manifest_rejects_non_object_entries(manifest_path: Path) -> None:
    write_manifest(manifest_path, {"trusted_keys": {"alpha": []}})
    with pytest.raises(TrustManifestError, match="must be an object"):
        load_trust_manifest(manifest_path)


def test_load_trust_manifest_single_pattern(manifest_path: Path) -> None:
    payload = {
        "trusted_keys": {
            "alpha": {
                "public_key": "11" * 32,
                "patterns": "receipts/*.json",
            }
        }
    }
    manifest = load_trust_manifest(write_manifest(manifest_path, payload))
    assert len(manifest.entries) == 1
    entry = manifest.entries[0]
    assert entry.key_id == "alpha"
    assert entry.public_key == "11" * 32
    assert entry.patterns == ["receipts/*.json"]


def test_load_trust_manifest_list_patterns(manifest_path: Path) -> None:
    payload = {
        "trusted_keys": {
            "beta": {
                "public_key": "22" * 32,
                "patterns": ["*.json", "subdir/*.json"],
            }
        }
    }
    manifest = load_trust_manifest(write_manifest(manifest_path, payload))
    entry = manifest.entries[0]
    assert entry.patterns == ["*.json", "subdir/*.json"]


def test_load_trust_manifest_rejects_invalid_patterns(manifest_path: Path) -> None:
    payload = {
        "trusted_keys": {
            "gamma": {
                "public_key": "33" * 32,
                "patterns": 123,
            }
        }
    }
    with pytest.raises(TrustManifestError, match="must be a list of glob strings"):
        load_trust_manifest(write_manifest(manifest_path, payload))


def make_manifest(tmp_path: Path, entries: list[tuple[str, str, list[str] | None]]) -> TrustManifest:
    payload = {"trusted_keys": {}}
    for key_id, public_key, patterns in entries:
        payload["trusted_keys"][key_id] = {
            "public_key": public_key,
        }
        if patterns is not None:
            payload["trusted_keys"][key_id]["patterns"] = patterns
    path = write_manifest(tmp_path / "trust_manifest.json", payload)
    return load_trust_manifest(path)


def test_select_entry_with_matching_key_id(tmp_path: Path) -> None:
    manifest = make_manifest(tmp_path, [("alpha", "11" * 32, ["*.json"])])
    receipt_path = tmp_path / "example.json"
    receipt_path.write_text("{}", encoding="utf-8")
    entry = manifest.select_entry(receipt_path, {"key_id": "alpha"})
    assert entry.key_id == "alpha"


def test_select_entry_rejects_unknown_key_id(tmp_path: Path) -> None:
    manifest = make_manifest(tmp_path, [("alpha", "11" * 32, ["*.json"])])
    receipt_path = tmp_path / "example.json"
    receipt_path.write_text("{}", encoding="utf-8")
    with pytest.raises(TrustManifestError, match="not present"):
        manifest.select_entry(receipt_path, {"key_id": "missing"})


def test_select_entry_rejects_mismatched_path(tmp_path: Path) -> None:
    manifest = make_manifest(tmp_path, [("alpha", "11" * 32, ["trusted/*.json"])])
    receipt_path = tmp_path / "example.json"
    receipt_path.write_text("{}", encoding="utf-8")
    with pytest.raises(TrustManifestError, match="does not match patterns"):
        manifest.select_entry(receipt_path, {"key_id": "alpha"})


def test_select_entry_matches_via_public_key(tmp_path: Path) -> None:
    entries = [
        ("alpha", "11" * 32, ["*.json"]),
        ("beta", "22" * 32, ["*.json"]),
    ]
    manifest = make_manifest(tmp_path, entries)
    receipt_path = tmp_path / "example.json"
    receipt_path.write_text("{}", encoding="utf-8")
    chosen = manifest.select_entry(
        receipt_path,
        {
            "public_key": "22" * 32,
        },
    )
    assert chosen.key_id == "beta"


def test_select_entry_requires_disambiguation_without_public_key(tmp_path: Path) -> None:
    entries = [
        ("alpha", "11" * 32, ["*.json"]),
        ("beta", "22" * 32, ["*.json"]),
    ]
    manifest = make_manifest(tmp_path, entries)
    receipt_path = tmp_path / "example.json"
    receipt_path.write_text("{}", encoding="utf-8")
    with pytest.raises(TrustManifestError, match="Multiple trust entries"):
        manifest.select_entry(receipt_path, {})
