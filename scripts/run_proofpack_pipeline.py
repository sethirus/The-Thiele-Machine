"""End-to-end proofpack orchestration for the zero-trust workflow."""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Iterable, Mapping, Sequence, Tuple

import yaml

from experiments.run_cross_domain import main as cross_domain_main
from experiments.run_cwd import main as cwd_main
from experiments.run_einstein import main as einstein_main
from experiments.run_entropy import main as entropy_main
from experiments.run_landauer import main as landauer_main
from experiments.public_data import PROTOCOLS as PUBLIC_DATA_PROTOCOLS
from experiments.public_data import run_dataset as run_public_dataset
from tools.proofpack_bundler import BundleResult, bundle_proofpack
from experiments.turbulence import PROTOCOLS as TURBULENCE_PROTOCOLS
from experiments.turbulence import run_dataset as run_turbulence_dataset
from scripts.keys import get_or_create_signing_key


@dataclass(frozen=True)
class ProfileConfig:
    """Structured overrides loaded from a profile configuration file."""

    profile_arguments: Mapping[str, Mapping[str, Sequence[object] | object]]
    turbulence_allowlists: Mapping[str, Tuple[str, ...]]

DEFAULT_OUTPUT_ROOT = Path("artifacts") / "experiments"
DEFAULT_SIGNING_KEY = Path("kernel_secret.key")
TURBULENCE_ALLOWLIST_PATH = Path("experiments") / "data" / "turbulence" / "allowlist.json"
FALLBACK_TURBULENCE_ALLOWLIST: Tuple[str, ...] = (
    "isotropic1024_8pt",
    "isotropic1024_12pt",
)
FALLBACK_TURBULENCE_EXPANDED: Tuple[str, ...] = ()
FALLBACK_TURBULENCE_ROTATIONS: Mapping[str, Tuple[Tuple[str, ...], ...]] = {}
LANDUAER_PROTOCOLS: Sequence[str] = ("sighted", "blind")
EINSTEIN_PROTOCOLS: Sequence[str] = ("sighted",)
ENTROPY_PROTOCOLS: Sequence[str] = ("sighted", "blind")
CWD_PROTOCOLS: Sequence[str] = ("sighted", "blind", "destroyed")
CROSS_DOMAIN_PROTOCOLS: Sequence[str] = ("sighted", "blind", "destroyed")
PUBLIC_DATA_PROTOCOLS: Sequence[str] = tuple(PUBLIC_DATA_PROTOCOLS)
TURBULENCE_PROTOCOLS: Sequence[str] = tuple(TURBULENCE_PROTOCOLS)


@dataclass(frozen=True)
class TurbulenceAllowlistConfig:
    """Container for default, expanded, and rotation allowlists."""

    default: Tuple[str, ...]
    expanded: Tuple[str, ...]
    rotations: Mapping[str, Tuple[Tuple[str, ...], ...]]


def _coerce_slug_sequence(value: Sequence[object] | object, *, label: str) -> Tuple[str, ...]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes)):
        raise ValueError(f"Turbulence allowlist '{label}' must be an array of dataset slugs")
    return tuple(str(entry) for entry in value)


def _load_turbulence_allowlist_config(
    path: Path = TURBULENCE_ALLOWLIST_PATH,
) -> TurbulenceAllowlistConfig:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return TurbulenceAllowlistConfig(
            default=FALLBACK_TURBULENCE_ALLOWLIST,
            expanded=FALLBACK_TURBULENCE_EXPANDED,
            rotations=FALLBACK_TURBULENCE_ROTATIONS,
        )
    except json.JSONDecodeError as exc:  # pragma: no cover - defensive guard
        raise ValueError(f"Invalid turbulence allowlist JSON: {path}") from exc

    if not isinstance(data, Mapping):
        raise ValueError("Turbulence allowlist file must contain a JSON object")

    default_raw = data.get("default", FALLBACK_TURBULENCE_ALLOWLIST)
    if isinstance(default_raw, (str, bytes)):
        default = (str(default_raw),)
    else:
        default = _coerce_slug_sequence(default_raw, label="default")

    expanded_raw = data.get("expanded", FALLBACK_TURBULENCE_EXPANDED)
    if isinstance(expanded_raw, (str, bytes)):
        expanded = (str(expanded_raw),)
    elif expanded_raw:
        expanded = _coerce_slug_sequence(expanded_raw, label="expanded")
    else:
        expanded = FALLBACK_TURBULENCE_EXPANDED

    rotations_raw = data.get("rotations", FALLBACK_TURBULENCE_ROTATIONS)
    rotations: dict[str, Tuple[Tuple[str, ...], ...]] = {}
    if rotations_raw:
        if not isinstance(rotations_raw, Mapping):
            raise ValueError("Turbulence rotations must map schedule names to dataset groups")
        for schedule, groups in rotations_raw.items():
            if groups is None:
                rotations[str(schedule)] = ()
                continue
            if isinstance(groups, (str, bytes)):
                groups_sequence = ((groups.decode() if isinstance(groups, bytes) else groups,),)
            else:
                if not isinstance(groups, Sequence):
                    raise ValueError("Rotation groups must be arrays of dataset slugs")
                group_payload: list[Tuple[str, ...]] = []
                for index, group in enumerate(groups):
                    if isinstance(group, (str, bytes)):
                        group_payload.append((group.decode() if isinstance(group, bytes) else group,))
                    else:
                        group_payload.append(
                            _coerce_slug_sequence(group, label=f"rotations[{schedule}][{index}]")
                        )
                groups_sequence = tuple(group_payload)
            rotations[str(schedule)] = tuple(groups_sequence)

    return TurbulenceAllowlistConfig(default=default, expanded=expanded, rotations=rotations)


DEFAULT_TURBULENCE_ALLOWLISTS = _load_turbulence_allowlist_config()
DEFAULT_TURBULENCE_DATASETS: Sequence[str] = DEFAULT_TURBULENCE_ALLOWLISTS.default

def _normalize_profile_mapping(
    mapping: Mapping[str, Mapping[str, Sequence[object] | object]]
) -> dict[str, dict[str, Tuple[str, ...]]]:
    normalized: dict[str, dict[str, Tuple[str, ...]]] = {}
    for profile_name, phase_overrides in mapping.items():
        if not isinstance(phase_overrides, Mapping):
            raise ValueError("Profile definitions must map to per-phase argument lists")
        normalized_phases: dict[str, Tuple[str, ...]] = {}
        for phase_name, args in phase_overrides.items():
            if args is None:
                normalized_phases[str(phase_name)] = ()
                continue
            if isinstance(args, Mapping):
                raise ValueError("Per-phase overrides must be a sequence or scalar of CLI arguments")
            if isinstance(args, (str, bytes)):
                seq = (args.decode() if isinstance(args, bytes) else args,)
            else:
                try:
                    seq = tuple(str(item) for item in args)  # type: ignore[arg-type]
                except TypeError as exc:  # pragma: no cover - defensive
                    raise ValueError("Per-phase overrides must be iterable") from exc
            normalized_phases[str(phase_name)] = tuple(seq)
        normalized[str(profile_name)] = normalized_phases
    return normalized


def _normalize_allowlists(
    mapping: Mapping[str, Sequence[object] | object] | None,
) -> dict[str, Tuple[str, ...]]:
    if mapping is None:
        return {}
    if not isinstance(mapping, Mapping):
        raise ValueError("Turbulence allowlists must map profiles to dataset slugs")

    normalized: dict[str, Tuple[str, ...]] = {}
    for profile, values in mapping.items():
        if values is None:
            normalized[str(profile)] = ()
            continue
        if isinstance(values, (str, bytes)):
            seq = (values.decode() if isinstance(values, bytes) else values,)
        else:
            try:
                seq = tuple(str(item) for item in values)  # type: ignore[arg-type]
            except TypeError as exc:  # pragma: no cover - defensive
                raise ValueError("Allowlist entries must be iterable") from exc
        normalized[str(profile)] = tuple(seq)
    return normalized


def _derive_rotation_index(run_tag: str, created_at: str | None, schedule_length: int) -> int:
    if schedule_length <= 0:
        return 0
    if created_at:
        try:
            timestamp = datetime.fromisoformat(created_at.replace("Z", "+00:00"))
        except ValueError:
            timestamp = None
        else:
            return timestamp.toordinal()
    try:
        timestamp = datetime.fromisoformat(run_tag.replace("Z", "+00:00"))
    except ValueError:
        digest = hashlib.sha256(run_tag.encode("utf-8")).digest()
        return int.from_bytes(digest[:4], "big")
    return timestamp.toordinal()


def _select_turbulence_datasets(
    *,
    explicit: Sequence[str] | None,
    profile: str,
    profile_config: ProfileConfig | None,
    rotation_schedule: str | None,
    rotation_index: int | None,
    run_tag: str,
    created_at: str | None,
) -> Tuple[str, ...]:
    if explicit:
        return tuple(explicit)

    if profile_config:
        profile_allowlist = profile_config.turbulence_allowlists.get(profile)
        if profile_allowlist:
            return profile_allowlist

    if rotation_schedule:
        rotation_groups = DEFAULT_TURBULENCE_ALLOWLISTS.rotations.get(rotation_schedule)
        if not rotation_groups:
            available = ", ".join(sorted(DEFAULT_TURBULENCE_ALLOWLISTS.rotations)) or "none"
            raise ValueError(
                f"Unknown turbulence rotation schedule: {rotation_schedule}. Available schedules: {available}"
            )
        index_source = rotation_index
        if index_source is None:
            index_source = _derive_rotation_index(run_tag, created_at, len(rotation_groups))
        selected_group = rotation_groups[index_source % len(rotation_groups)]
        return selected_group

    if DEFAULT_TURBULENCE_ALLOWLISTS.default:
        return DEFAULT_TURBULENCE_ALLOWLISTS.default

    return FALLBACK_TURBULENCE_ALLOWLIST


DEFAULT_PROFILE_ARGUMENTS: Mapping[str, Mapping[str, Tuple[str, ...]]] = _normalize_profile_mapping(
    {
        "quick": {
            "landauer": ("--seeds", "0", "--temps", "0.5", "1.0", "--trials-per-condition", "3", "--steps", "18"),
            "einstein": (
                "--seeds",
                "0",
                "--temps",
                "0.75",
                "1.25",
                "--trials-per-condition",
                "2",
                "--steps",
                "24",
                "--dt",
                "0.5",
                "--mobility",
                "0.4",
                "--force",
                "0.6",
            ),
            "entropy": (
                "--seeds",
                "0",
                "--temps",
                "0.75",
                "1.25",
                "--trials-per-condition",
                "2",
                "--steps",
                "24",
                "--dt",
                "0.5",
                "--mobility",
                "0.4",
                "--force",
                "0.6",
                "--entropy-smoothing",
                "0.04",
            ),
            "cwd": (
                "--seeds",
                "0",
                "--temps",
                "0.85",
                "--trials-per-condition",
                "1",
                "--modules",
                "3",
                "--steps-per-module",
                "4",
                "--mu-base",
                "0.18",
                "--mu-jitter",
                "0.02",
                "--penalty-scale",
                "1.5",
            ),
            "cross_domain": (
                "--seeds",
                "0",
                "1",
                "--trials-per-condition",
                "3",
                "--modules",
                "5",
                "--mu-base",
                "0.24",
                "--mu-jitter",
                "0.03",
                "--runtime-base",
                "1.1",
                "--runtime-scale",
                "0.75",
            ),
        },
        "standard": {},
    }
)


def _merge_profile_arguments(
    base: Mapping[str, Mapping[str, Tuple[str, ...]]],
    overrides: Mapping[str, Mapping[str, Sequence[object] | object]] | None = None,
) -> dict[str, dict[str, Tuple[str, ...]]]:
    merged: dict[str, dict[str, Tuple[str, ...]]] = {
        profile: {phase: tuple(args) for phase, args in phases.items()}
        for profile, phases in base.items()
    }
    if not overrides:
        return merged
    override_normalized = _normalize_profile_mapping(overrides)
    for profile, phases in override_normalized.items():
        merged[profile] = dict(phases)
    return merged


@dataclass
class PipelineResult:
    run_tag: str
    proofpack_dir: Path
    bundle_result: BundleResult

    @property
    def bundle_dir(self) -> Path:
        return self.bundle_result.manifest_path.parent


@dataclass
class _PhaseSpec:
    name: str
    main: Callable[[Sequence[str]], None]
    metadata: str
    protocols: Sequence[str]


PHASES: Sequence[_PhaseSpec] = (
    _PhaseSpec("landauer", landauer_main, "landauer_metadata.json", LANDUAER_PROTOCOLS),
    _PhaseSpec("einstein", einstein_main, "einstein_metadata.json", EINSTEIN_PROTOCOLS),
    _PhaseSpec("entropy", entropy_main, "entropy_metadata.json", ENTROPY_PROTOCOLS),
    _PhaseSpec("cwd", cwd_main, "cwd_metadata.json", CWD_PROTOCOLS),
    _PhaseSpec("cross_domain", cross_domain_main, "cross_domain_metadata.json", CROSS_DOMAIN_PROTOCOLS),
)


def _discover_public_datasets(root: Path) -> Sequence[Tuple[str, Path]]:
    root = Path(root)
    if not root.exists():
        return ()

    datasets: list[Tuple[str, Path]] = []
    for source_dir in sorted(path for path in root.iterdir() if path.is_dir()):
        for dataset_dir in sorted(path for path in source_dir.iterdir() if path.is_dir()):
            if (dataset_dir / "anchors.json").exists():
                datasets.append((source_dir.name, dataset_dir))
    return tuple(datasets)


def _discover_turbulence_samples(
    root: Path,
    *,
    allowlist: Sequence[str] | None = None,
) -> Sequence[Tuple[Path, Path]]:
    root = Path(root)
    if not root.exists():
        return ()

    samples: list[Tuple[Path, Path]] = []
    allowed_names = {Path(entry).name for entry in allowlist or ()}
    for sample_path in sorted(root.rglob("jhtdb_samples.json")):
        dataset_dir = sample_path.parent
        try:
            relative = dataset_dir.relative_to(root)
        except ValueError:
            continue
        if allowed_names and relative.name not in allowed_names:
            continue
        samples.append((relative, dataset_dir))
    return tuple(samples)


def _validate_root(path: Path) -> Path:
    resolved = Path(path).resolve()
    parts = resolved.parts
    try:
        idx = parts.index("artifacts")
    except ValueError as exc:  # pragma: no cover - defensive guard
        raise ValueError("Output root must include artifacts/experiments") from exc
    if idx + 1 >= len(parts) or parts[idx + 1] != "experiments":
        raise ValueError("Output root must include artifacts/experiments")
    return resolved


def _profile_args(
    profile: str,
    phase: str,
    profile_arguments: Mapping[str, Mapping[str, Tuple[str, ...]]],
) -> Sequence[str]:
    try:
        overrides = profile_arguments[profile]
    except KeyError as exc:
        available = ", ".join(sorted(profile_arguments))
        raise ValueError(
            f"Unsupported profile: {profile}. Available profiles: {available}"
        ) from exc
    return tuple(overrides.get(phase, ()))


def _timestamp() -> str:
    now = datetime.now(timezone.utc)
    return now.replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _ensure_signing_key(path: Path) -> Path:
    public_candidate = path.with_name("kernel_public.key") if path.name == "kernel_secret.key" else None
    get_or_create_signing_key(path, public_key_path=public_candidate)
    return path.resolve()


def _load_profile_config(path: Path) -> ProfileConfig:
    if not path.exists():
        raise FileNotFoundError(f"Profile config not found: {path}")
    text = path.read_text(encoding="utf-8")
    suffix = path.suffix.lower()
    if suffix == ".json":
        data = json.loads(text)
    elif suffix in {".yaml", ".yml"}:
        data = yaml.safe_load(text)
    else:
        raise ValueError("Profile config must be a JSON or YAML file")
    if not isinstance(data, Mapping):
        raise ValueError("Profile config must contain a mapping of profile definitions")

    if "profiles" in data:
        profiles_raw = data["profiles"]
    else:
        profiles_raw = {
            str(key): value
            for key, value in data.items()
            if key not in {"turbulence_allowlists"}
        }
    if not isinstance(profiles_raw, Mapping):
        raise ValueError("Profile definitions must be a mapping")

    profiles: dict[str, dict[str, Sequence[object] | object]] = {}
    for profile, overrides in profiles_raw.items():
        if not isinstance(overrides, Mapping):
            raise ValueError("Each profile must map to per-phase overrides")
        profiles[str(profile)] = dict(overrides)

    turbulence_allowlists = _normalize_allowlists(
        data.get("turbulence_allowlists") if "turbulence_allowlists" in data else None
    )

    return ProfileConfig(profile_arguments=profiles, turbulence_allowlists=turbulence_allowlists)


def _run_phase(
    spec: _PhaseSpec,
    proofpack_root: Path,
    profile: str,
    profile_arguments: Mapping[str, Mapping[str, Tuple[str, ...]]],
) -> None:
    base_dir = proofpack_root / spec.name
    overrides = _profile_args(profile, spec.name, profile_arguments)

    for protocol in spec.protocols:
        run_dir = base_dir / protocol
        metadata_path = run_dir / spec.metadata
        if metadata_path.exists():
            continue
        run_dir.mkdir(parents=True, exist_ok=True)
        args = ["--output-dir", str(run_dir)]
        if protocol:
            args.extend(["--protocol", protocol])
        args.extend(overrides)
        spec.main(args)


def _run_public_data(
    proofpack_root: Path,
    dataset_specs: Sequence[Tuple[str, Path]],
    *,
    protocols: Sequence[str] | None,
    seed: int,
) -> None:
    if not dataset_specs:
        return

    protocol_arg: Sequence[str] | None = tuple(protocols) if protocols else None
    for source, dataset_dir in dataset_specs:
        output_dir = proofpack_root / "public_data" / source / dataset_dir.name
        run_public_dataset(dataset_dir, output_dir, protocols=protocol_arg, seed=seed)


def _run_turbulence_data(
    proofpack_root: Path,
    sample_specs: Sequence[Tuple[Path, Path]],
    *,
    seed: int,
    protocols: Sequence[str] | None = None,
) -> None:
    if not sample_specs:
        return

    protocol_arg: Sequence[str] | None = tuple(protocols) if protocols else None
    for relative, dataset_dir in sample_specs:
        output_dir = proofpack_root / "turbulence" / relative
        run_turbulence_dataset(dataset_dir, output_dir, protocols=protocol_arg, seed=seed)


def run_pipeline(
    *,
    output_root: Path | None = None,
    signing_key: Path | None = None,
    run_tag: str | None = None,
    profile: str = "quick",
    profile_config: ProfileConfig | None = None,
    notes: Sequence[str] | None = None,
    created_at: str | None = None,
    epsilon: float = 0.05,
    delta: float = 0.05,
    eta: float = 0.05,
    delta_aic: float = 10.0,
    public_data_root: Path | None = None,
    public_data_protocols: Sequence[str] | None = None,
    public_data_seed: int = 0,
    turbulence_protocols: Sequence[str] | None = None,
    turbulence_seed: int = 0,
    turbulence_datasets: Sequence[str] | None = None,
    turbulence_rotation_schedule: str | None = None,
    turbulence_rotation_index: int | None = None,
) -> PipelineResult:
    """Execute all builder phases and bundle the resulting proofpack."""

    merged_profiles = _merge_profile_arguments(
        DEFAULT_PROFILE_ARGUMENTS,
        profile_config.profile_arguments if profile_config else None,
    )

    root = _validate_root(output_root or DEFAULT_OUTPUT_ROOT)
    root.mkdir(parents=True, exist_ok=True)

    tag = run_tag or _timestamp()
    run_root = root / tag
    proofpack_dir = run_root / "proofpack"
    proofpack_dir.mkdir(parents=True, exist_ok=True)

    for spec in PHASES:
        _run_phase(spec, proofpack_dir, profile, merged_profiles)

    if public_data_root is not None:
        mirror_root = Path(public_data_root)
        if not mirror_root.exists():
            raise FileNotFoundError(f"Public data root does not exist: {mirror_root}")
        dataset_specs = _discover_public_datasets(mirror_root)
        _run_public_data(
            proofpack_dir,
            dataset_specs,
            protocols=public_data_protocols,
            seed=public_data_seed,
        )
        allowlist = _select_turbulence_datasets(
            explicit=turbulence_datasets,
            profile=profile,
            profile_config=profile_config,
            rotation_schedule=turbulence_rotation_schedule,
            rotation_index=turbulence_rotation_index,
            run_tag=tag,
            created_at=created_at,
        )
        turbulence_specs = _discover_turbulence_samples(mirror_root, allowlist=allowlist)
        _run_turbulence_data(
            proofpack_dir,
            turbulence_specs,
            seed=turbulence_seed,
            protocols=turbulence_protocols,
        )

    bundle_dir = run_root / "bundle"
    signing_key_path = _ensure_signing_key((signing_key or DEFAULT_SIGNING_KEY))

    bundle_result = bundle_proofpack(
        proofpack_dir,
        bundle_dir,
        signing_key_path=signing_key_path,
        run_tag=tag,
        notes=notes,
        created_at=created_at,
        epsilon=epsilon,
        delta=delta,
        eta=eta,
        delta_aic=delta_aic,
        spearman_threshold=0.9,
        pvalue_threshold=1e-6,
        oos_threshold=0.1,
    )

    return PipelineResult(run_tag=tag, proofpack_dir=proofpack_dir, bundle_result=bundle_result)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run the zero-trust proofpack pipeline")
    parser.add_argument(
        "--output-root",
        type=Path,
        default=DEFAULT_OUTPUT_ROOT,
        help="Root directory under artifacts/experiments where outputs are stored",
    )
    parser.add_argument(
        "--signing-key",
        type=Path,
        default=DEFAULT_SIGNING_KEY,
        help="Path to the Ed25519 signing key (defaults to kernel_secret.key)",
    )
    parser.add_argument("--run-tag", type=str, default=None, help="Run tag used for the proofpack")
    parser.add_argument(
        "--profile",
        default="quick",
        help="Execution profile controlling simulation parameters",
    )
    parser.add_argument(
        "--profile-config",
        type=Path,
        help=(
            "Optional JSON or YAML file defining profile overrides and "
            "turbulence dataset allowlists"
        ),
    )
    parser.add_argument(
        "--note",
        dest="notes",
        action="append",
        help="Additional notes recorded in the protocol and human summary",
    )
    parser.add_argument(
        "--created-at",
        type=str,
        default=None,
        help="Override manifest timestamp (ISO-8601)",
    )
    parser.add_argument("--epsilon", type=float, default=0.05, help="Landauer/CWD tolerance")
    parser.add_argument("--delta", type=float, default=0.05, help="Einstein tolerance")
    parser.add_argument("--eta", type=float, default=0.05, help="CWD penalty margin")
    parser.add_argument(
        "--delta-aic",
        type=float,
        default=10.0,
        dest="delta_aic",
        help="ΔAIC threshold for blind cross-domain runs",
    )
    parser.add_argument(
        "--public-data-root",
        type=Path,
        help="Mirror root containing public_data/<source>/<slug>/ datasets",
    )
    parser.add_argument(
        "--public-data-protocol",
        dest="public_data_protocols",
        action="append",
        choices=PUBLIC_DATA_PROTOCOLS,
        help="Restrict public data execution to selected protocols",
    )
    parser.add_argument(
        "--public-data-seed",
        type=int,
        default=0,
        help="Deterministic seed for destroyed public-data protocols",
    )
    parser.add_argument(
        "--turbulence-protocol",
        dest="turbulence_protocols",
        action="append",
        choices=TURBULENCE_PROTOCOLS,
        help="Restrict turbulence execution to selected protocols",
    )
    parser.add_argument(
        "--turbulence-seed",
        type=int,
        default=0,
        help="Deterministic seed for turbulence protocol shuffling",
    )
    parser.add_argument(
        "--turbulence-dataset",
        dest="turbulence_datasets",
        action="append",
        help=(
            "Limit turbulence execution to mirrored dataset slugs. "
            "Defaults are loaded from experiments/data/turbulence/allowlist.json."
        ),
    )
    parser.add_argument(
        "--turbulence-rotation-schedule",
        dest="turbulence_rotation_schedule",
        help=(
            "Select a named turbulence rotation schedule from "
            "experiments/data/turbulence/allowlist.json."
        ),
    )
    parser.add_argument(
        "--turbulence-rotation-index",
        dest="turbulence_rotation_index",
        type=int,
        help=(
            "Override the rotation index when using a rotation schedule. "
            "Defaults to a deterministic hash of the run tag or timestamp."
        ),
    )
    return parser


def main(argv: Iterable[str] | None = None) -> None:  # pragma: no cover - CLI entry
    parser = _build_parser()
    args = parser.parse_args(argv)

    try:
        profile_config = _load_profile_config(args.profile_config) if args.profile_config else None
        result = run_pipeline(
            output_root=args.output_root,
            signing_key=args.signing_key,
            run_tag=args.run_tag,
            profile=args.profile,
            profile_config=profile_config,
            notes=args.notes,
            created_at=args.created_at,
            epsilon=args.epsilon,
            delta=args.delta,
            eta=args.eta,
            delta_aic=args.delta_aic,
            public_data_root=args.public_data_root,
            public_data_protocols=args.public_data_protocols,
            public_data_seed=args.public_data_seed,
            turbulence_protocols=args.turbulence_protocols,
            turbulence_seed=args.turbulence_seed,
            turbulence_datasets=args.turbulence_datasets,
            turbulence_rotation_schedule=args.turbulence_rotation_schedule,
            turbulence_rotation_index=args.turbulence_rotation_index,
        )
    except Exception as exc:  # pragma: no cover - surfaced in integration tests
        # Print a clearer failure message and full traceback so CI logs capture the cause.
        import traceback

        print(f"PIPELINE_FAIL: {exc}")
        traceback.print_exc()
        # Also attempt to flush to stdout/stderr to ensure logs appear in CI.
        try:
            import sys

            sys.stdout.flush()
            sys.stderr.flush()
        except Exception:
            pass
        raise SystemExit(1)

    print(f"PIPELINE_OK: {result.bundle_dir}")
    print(f"THIELE_STATUS: {result.bundle_result.aggregated_payload.get('status')}")


if __name__ == "__main__":  # pragma: no cover
    main()
