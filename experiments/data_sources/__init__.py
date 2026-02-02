"""Utilities for discovering external datasets."""

from .anchors import AnchorEvidence, AnchoringResult, extract_anchors, result_to_protocol_dict  # noqa: F401
from .osf import OSFSearchConfig, OSFCandidate, OSFFile, discover_osf_candidates, serialise_candidates as serialise_osf_candidates  # noqa: F401
from .figshare import FigshareSearchConfig, FigshareCandidate, FigshareFile, discover_figshare_candidates, serialise_candidates as serialise_figshare_candidates  # noqa: F401
from .dryad import DryadSearchConfig, DryadCandidate, DryadFile, discover_dryad_candidates, serialise_candidates as serialise_dryad_candidates  # noqa: F401
from .download import (  # noqa: F401
    DownloadConfig,
    DownloadError,
    DownloadOutcome,
    download_selected_candidate,
    slugify,
    verify_manifest,
)
from .zenodo import ZenodoSearchConfig, ZenodoCandidate, ZenodoFile, discover_zenodo_candidates, serialise_candidates as serialise_zenodo_candidates  # noqa: F401
from .jhtdb import (  # noqa: F401
    JHTDBSample,
    DEFAULT_BASE_URL,
    DEFAULT_METADATA_ENDPOINT,
    DEFAULT_SAMPLE_ENDPOINT,
    fetch_metadata,
    fetch_samples,
    write_sample_bundle,
)

