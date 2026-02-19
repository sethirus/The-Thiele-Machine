"""Utilities for discovering external datasets."""

from importlib import import_module
from typing import Dict, Tuple

__all__ = [
    "AnchorEvidence",
    "AnchoringResult",
    "extract_anchors",
    "result_to_protocol_dict",
    "OSFSearchConfig",
    "OSFCandidate",
    "OSFFile",
    "discover_osf_candidates",
    "serialise_osf_candidates",
    "FigshareSearchConfig",
    "FigshareCandidate",
    "FigshareFile",
    "discover_figshare_candidates",
    "serialise_figshare_candidates",
    "DryadSearchConfig",
    "DryadCandidate",
    "DryadFile",
    "discover_dryad_candidates",
    "serialise_dryad_candidates",
    "DownloadConfig",
    "DownloadError",
    "DownloadOutcome",
    "download_selected_candidate",
    "slugify",
    "verify_manifest",
    "ZenodoSearchConfig",
    "ZenodoCandidate",
    "ZenodoFile",
    "discover_zenodo_candidates",
    "serialise_zenodo_candidates",
    "JHTDBSample",
    "DEFAULT_BASE_URL",
    "DEFAULT_METADATA_ENDPOINT",
    "DEFAULT_SAMPLE_ENDPOINT",
    "fetch_metadata",
    "fetch_samples",
    "write_sample_bundle",
]

_EXPORTS: Dict[str, Tuple[str, str]] = {
    "AnchorEvidence": (".anchors", "AnchorEvidence"),
    "AnchoringResult": (".anchors", "AnchoringResult"),
    "extract_anchors": (".anchors", "extract_anchors"),
    "result_to_protocol_dict": (".anchors", "result_to_protocol_dict"),
    "OSFSearchConfig": (".osf", "OSFSearchConfig"),
    "OSFCandidate": (".osf", "OSFCandidate"),
    "OSFFile": (".osf", "OSFFile"),
    "discover_osf_candidates": (".osf", "discover_osf_candidates"),
    "serialise_osf_candidates": (".osf", "serialise_candidates"),
    "FigshareSearchConfig": (".figshare", "FigshareSearchConfig"),
    "FigshareCandidate": (".figshare", "FigshareCandidate"),
    "FigshareFile": (".figshare", "FigshareFile"),
    "discover_figshare_candidates": (".figshare", "discover_figshare_candidates"),
    "serialise_figshare_candidates": (".figshare", "serialise_candidates"),
    "DryadSearchConfig": (".dryad", "DryadSearchConfig"),
    "DryadCandidate": (".dryad", "DryadCandidate"),
    "DryadFile": (".dryad", "DryadFile"),
    "discover_dryad_candidates": (".dryad", "discover_dryad_candidates"),
    "serialise_dryad_candidates": (".dryad", "serialise_candidates"),
    "DownloadConfig": (".download", "DownloadConfig"),
    "DownloadError": (".download", "DownloadError"),
    "DownloadOutcome": (".download", "DownloadOutcome"),
    "download_selected_candidate": (".download", "download_selected_candidate"),
    "slugify": (".download", "slugify"),
    "verify_manifest": (".download", "verify_manifest"),
    "ZenodoSearchConfig": (".zenodo", "ZenodoSearchConfig"),
    "ZenodoCandidate": (".zenodo", "ZenodoCandidate"),
    "ZenodoFile": (".zenodo", "ZenodoFile"),
    "discover_zenodo_candidates": (".zenodo", "discover_zenodo_candidates"),
    "serialise_zenodo_candidates": (".zenodo", "serialise_candidates"),
    "JHTDBSample": (".jhtdb", "JHTDBSample"),
    "DEFAULT_BASE_URL": (".jhtdb", "DEFAULT_BASE_URL"),
    "DEFAULT_METADATA_ENDPOINT": (".jhtdb", "DEFAULT_METADATA_ENDPOINT"),
    "DEFAULT_SAMPLE_ENDPOINT": (".jhtdb", "DEFAULT_SAMPLE_ENDPOINT"),
    "fetch_metadata": (".jhtdb", "fetch_metadata"),
    "fetch_samples": (".jhtdb", "fetch_samples"),
    "write_sample_bundle": (".jhtdb", "write_sample_bundle"),
}


def __getattr__(name: str):
    if name not in _EXPORTS:
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
    module_name, attr_name = _EXPORTS[name]
    module = import_module(module_name, __name__)
    value = getattr(module, attr_name)
    globals()[name] = value
    return value

