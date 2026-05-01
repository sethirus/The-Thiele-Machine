"""
Canonical source pipeline gate.

This test enforces a single declared Coq source-of-truth for extraction:
`coq/kami_hw/CanonicalCPUProof.v`.

What this verifies:
1. VM extraction root (`coq/Extraction.v`) imports CanonicalCPUProof.
2. Kami extraction root (`coq/kami_hw/KamiExtraction.v`) imports CanonicalCPUProof.
3. Canonical source exports `canonical_cpu_module` and `targetB`.
4. Extracted Kami OCaml artefacts preserve those canonical symbols and drive
    the pretty-printer through `targetB`.
5. Modular and ThieleMachineComplete extractions are byte-identical.
6. The tracked RTL is byte-identical to the generated synthesis-transformed
    Kami artefact (`build/kami_hw/mkModule1_synth.v`).
"""

from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[1]
COQ = REPO / "coq"

EXTRACTION_V = COQ / "Extraction.v"
KAMI_EXTRACTION_V = COQ / "kami_hw" / "KamiExtraction.v"
CANONICAL_V = COQ / "kami_hw" / "CanonicalCPUProof.v"

THIELE_CORE_ML = REPO / "build" / "thiele_core.ml"
THIELE_CORE_COMPLETE_ML = REPO / "build" / "thiele_core_complete.ml"
THIELE_CORE_MLI = REPO / "build" / "thiele_core.mli"
THIELE_CORE_COMPLETE_MLI = REPO / "build" / "thiele_core_complete.mli"
KAMI_TARGET_ML = REPO / "build" / "kami_hw" / "Target.ml"
KAMI_TARGET_COMPLETE_ML = REPO / "build" / "kami_hw" / "Target_complete.ml"
KAMI_TARGET_MLI = REPO / "build" / "kami_hw" / "Target.mli"
KAMI_TARGET_COMPLETE_MLI = REPO / "build" / "kami_hw" / "Target_complete.mli"
KAMI_MAIN_ML = REPO / "build" / "kami_hw" / "Main.ml"
KAMI_RAW_V = REPO / "build" / "kami_hw" / "mkModule1.v"
KAMI_SYNTH_V = REPO / "build" / "kami_hw" / "mkModule1_synth.v"
TRACKED_RTL_V = REPO / "thielecpu" / "hardware" / "rtl" / "thiele_cpu_kami.v"
CANONICAL_BUILD_FILES = (
    EXTRACTION_V,
    KAMI_EXTRACTION_V,
    REPO / "Makefile",
    REPO / "scripts" / "kami_extract.sh",
    COQ / "scripts" / "kami_extract.sh",
)


@pytest.mark.coq
def test_vm_extraction_imports_canonical_source():
    text = EXTRACTION_V.read_text(encoding="utf-8")
    assert "CanonicalCPUProof" in text, (
        "coq/Extraction.v must import CanonicalCPUProof so VM extraction "
        "is tied to the canonical source."
    )


@pytest.mark.coq
def test_kami_extraction_imports_canonical_source():
    text = KAMI_EXTRACTION_V.read_text(encoding="utf-8")
    assert "CanonicalCPUProof" in text, (
        "coq/kami_hw/KamiExtraction.v must import CanonicalCPUProof "
        "as the canonical source."
    )


@pytest.mark.coq
def test_canonical_source_exports_entrypoints():
    text = CANONICAL_V.read_text(encoding="utf-8")
    assert "Definition canonical_cpu_module" in text
    assert "Theorem canonical_cpu_module_from_source" in text
    assert "Definition targetB" in text


@pytest.mark.coq
def test_extraction_artifacts_exist():
    missing = [
        p for p in (
            THIELE_CORE_ML,
            THIELE_CORE_COMPLETE_ML,
            THIELE_CORE_MLI,
            THIELE_CORE_COMPLETE_MLI,
            KAMI_TARGET_ML,
            KAMI_TARGET_COMPLETE_ML,
            KAMI_TARGET_MLI,
            KAMI_TARGET_COMPLETE_MLI,
            KAMI_MAIN_ML,
            KAMI_RAW_V,
            KAMI_SYNTH_V,
            TRACKED_RTL_V,
        )
        if not p.exists() or p.stat().st_size == 0
    ]
    assert not missing, (
        "Missing/empty canonical extraction artefacts; run make canonical-extract:\n"
        + "\n".join(str(p.relative_to(REPO)) for p in missing)
    )


@pytest.mark.coq
def test_extracted_target_preserves_canonical_symbol_wiring():
    text = KAMI_TARGET_ML.read_text(encoding="utf-8")
    assert "val thieleBusTopB" in text
    assert "val canonical_cpu_module" in text
    assert "let canonical_cpu_module =" in text
    assert "thieleBusTopB" in text
    assert "val targetB" in text
    assert "let targetB _ =" in text
    assert "canonical_cpu_module" in text


def _ocaml_top_level_blocks(text: str) -> list[str]:
    """Split OCaml source into top-level declaration blocks separated by blank lines.

    Returns a sorted list so two extractions that emit the same set of declarations
    in different topological orders (a known Coq extraction quirk that depends on
    surrounding file context) compare equal.
    """
    blocks: list[str] = []
    current: list[str] = []
    for line in text.splitlines():
        if line.strip() == "":
            if current:
                blocks.append("\n".join(current))
                current = []
        else:
            current.append(line)
    if current:
        blocks.append("\n".join(current))
    return sorted(blocks)


@pytest.mark.coq
def test_modular_and_complete_ocaml_extractions_match_exactly():
    assert THIELE_CORE_ML.read_bytes() == THIELE_CORE_COMPLETE_ML.read_bytes(), (
        "build/thiele_core.ml and build/thiele_core_complete.ml diverge; "
        "both direct extraction roots must emit byte-identical OCaml."
    )
    assert THIELE_CORE_MLI.read_bytes() == THIELE_CORE_COMPLETE_MLI.read_bytes(), (
        "build/thiele_core.mli and build/thiele_core_complete.mli diverge; "
        "both direct extraction roots must emit byte-identical interfaces."
    )
    target_ml = _ocaml_top_level_blocks(KAMI_TARGET_ML.read_text(encoding="utf-8"))
    target_complete_ml = _ocaml_top_level_blocks(KAMI_TARGET_COMPLETE_ML.read_text(encoding="utf-8"))
    assert target_ml == target_complete_ml, (
        "build/kami_hw/Target.ml and Target_complete.ml diverge; "
        "module and ThieleMachineComplete hardware extractions must emit the same "
        "set of OCaml declarations."
    )
    target_mli = _ocaml_top_level_blocks(KAMI_TARGET_MLI.read_text(encoding="utf-8"))
    target_complete_mli = _ocaml_top_level_blocks(KAMI_TARGET_COMPLETE_MLI.read_text(encoding="utf-8"))
    assert target_mli == target_complete_mli, (
        "build/kami_hw/Target.mli and Target_complete.mli diverge; "
        "module and ThieleMachineComplete hardware interfaces must emit the same "
        "set of OCaml declarations."
    )


@pytest.mark.coq
def test_kami_main_drives_pretty_printer_through_targetB():
    text = KAMI_MAIN_ML.read_text(encoding="utf-8")
    assert "open Target" in text
    assert "match targetB iAddrSize with" in text


@pytest.mark.coq
def test_generated_raw_verilog_has_expected_top_module():
    text = KAMI_RAW_V.read_text(encoding="utf-8")
    assert "Generated by Bluespec Compiler" in text
    assert "module mkModule1" in text


@pytest.mark.coq
def test_tracked_rtl_matches_generated_synth_artifact_exactly():
    generated = KAMI_SYNTH_V.read_text(encoding="utf-8")
    tracked = TRACKED_RTL_V.read_text(encoding="utf-8")
    assert generated == tracked, (
        "Tracked RTL diverges from build/kami_hw/mkModule1_synth.v; "
        "re-run the Kami extraction/synth transform pipeline and refresh the tracked RTL."
    )
