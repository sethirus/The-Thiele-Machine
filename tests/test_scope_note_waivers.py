"""Pin the exact set of proof files that waive the connectivity gates.

A proof file that does not import the foundation chain can say so in a SCOPE NOTE
(or a PROOF SCOPE: standalone algebra line). The Inquisitor and
tests/test_no_shortcuts_proof_connectivity.py then skip the connectivity rules for
that file. A free-text waiver with no ratchet would let any file escape by writing a
sentence, so the waived set is frozen here: a file that gains the marker without being
listed fails, and a listed file that loses it fails too (the list then shrinks on
purpose, in this file, in the same change). The marker must sit in the file's opening
comments, before its first declaration, where a reader meets it.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

WAIVER_RE = re.compile(
    r"(?:SCOPE NOTE.*proof[- ]?connect|"
    r"SCOPE NOTE.*(?:foundation connectivity|standalone proof scope)|"
    r"PROOF SCOPE:\s*standalone algebra)",
    re.IGNORECASE,
)
DECLARATION_RE = re.compile(
    r"(?m)^(?:Local\s+|Global\s+)?(?:Definition|Theorem|Lemma|Corollary|Proposition|Fact|"
    r"Remark|Example|Inductive|CoInductive|Record|Fixpoint|CoFixpoint|Section|Module|"
    r"Notation|Ltac|Parameter|Axiom|Hypothesis|Variable|Class|Instance|Program|Function)\b"
)

WAIVED_FILES = [
    # Generic audit interfaces and counterexamples state their own hypotheses
    # and claim no instruction semantics of any particular machine.
    "coq/audit/AdaptiveBlindness.v",
    # Generic behavioral minimization states its observation/reachability
    # hypotheses explicitly; it claims no machine semantics or physical price.
    "coq/audit/CanonicalObservation.v",
    "coq/audit/EnforcedRefinement.v",
    "coq/audit/ObservationContract.v",
    "coq/audit/PricingBoundary.v",
    "coq/audit/RepresentationCapacity.v",
    "coq/audit/TraceFactorization.v",
    "coq/audit/ValuationBoundary.v",
    # Abstract transition, history and counting files state their own interfaces.
    # Their opening scope comments explain why no record-system import applies.
    "coq/kernel/foundation/FiniteSums.v",
    "coq/kernel/foundation/LRecursion.v",
    "coq/kernel/foundation/NecFCups.v",
    "coq/kernel/foundation/NecWCT.v",
    "coq/kernel/foundation/NecWCasper.v",
    "coq/kernel/foundation/NecWLRice.v",
    "coq/kernel/foundation/NecWPointer.v",
    "coq/kernel/foundation/NecWWindow.v",
    "coq/kernel/foundation/ProbabilisticRecord.v",
    "coq/kernel/foundation/ProbabilisticRecordCore.v",
    "coq/kernel/foundation/ProperSubsumption.v",
    "coq/kernel/frontier/EcosystemGame.v",
    "coq/kernel/frontier/EcosystemGameTarget.v",
    "coq/kernel/frontier/ObservationPolicy.v",
    "coq/kernel/frontier/PointerObservable.v",
    "coq/kernel/frontier/PointerObservableCounterexamples.v",
    "coq/kernel/frontier/PointerObservableReductions.v",
    "coq/kernel/frontier/RecordProliferationSurvey.v",
    "coq/kernel/frontier/RecordProliferationSurveyTarget.v",
    "coq/kernel/nfi/CommitmentPredicateAdequacy.v",
    "coq/kernel/nfi/CostFrameworks.v",
    "coq/kernel/nfi/DecisionTreeBound.v",
    "coq/kernel/nfi/KnowledgeNarrowingMinimal.v",
    "coq/kernel/nfi/ShadowPricing.v",
    "coq/kernel/reductions/CasperFFG.v",
    "coq/kernel/reductions/CasperForkWitness.v",
    "coq/kernel/reductions/CasperRecordReading.v",
    "coq/kernel/reductions/ConcreteRAM.v",
    "coq/kernel/reductions/ConcreteRAMTarget.v",
    "coq/kernel/reductions/ConcreteRecordMachines.v",
    "coq/kernel/reductions/ConcreteRecordMachinesTarget.v",
    "coq/kernel/reductions/EVMStorageGas.v",
    "coq/kernel/reductions/GasMetering.v",
    "coq/kernel/reductions/NeculaPCC.v",
    "coq/kernel/reductions/NeculaPCCTarget.v",
    "coq/kernel/reductions/RFC9162Merkle.v",
    "coq/kernel/reductions/RFC9162MerkleTarget.v",
    "coq/kernel/reductions/RealSystemConsequences.v",
    "coq/kernel/reductions/RealSystemConsequencesTarget.v",
    "coq/kernel/reductions/TPMQuoteAuthenticity.v",
    "coq/kernel/reductions/TPMQuoteAuthenticityTarget.v",
    "coq/kernel/reductions/TPMQuoteGap.v",
    "coq/kernel/thermodynamic/CalorimeterProtocol.v",
    "coq/kernel/thermodynamic/CalorimeterProtocolTarget.v",
    "coq/kernel/thermodynamic/RelaxationContinuous.v",
    "coq/kernel/thermodynamic/RelaxationContinuousLimit.v",
    "coq/kernel/thermodynamic/RelaxationConvergence.v",
    "coq/kernel/thermodynamic/RelaxationEntropy.v",
    "coq/kernel/thermodynamic/RelaxationStretch.v",
    "coq/kernel/thermodynamic/RelaxationStretchContinuous.v",
    "minimal/AccountingBridge.v",
    "minimal/BrownianComputer.v",
    "minimal/CommutationObstruction.v",
    "minimal/CommutingGrid.v",
    "minimal/CompleteHost.v",
    "minimal/EditionCapacity.v",
    "minimal/EditionHistory.v",
    "minimal/Erasure.v",
    "minimal/Fibre.v",
    "minimal/GeometryLimits.v",
    "minimal/GibbsGap.v",
    "minimal/Grouping.v",
    "minimal/HaltingHole.v",
    "minimal/HeatOrRoom.v",
    "minimal/KeptDistinction.v",
    "minimal/MeterRepresentation.v",
    "minimal/Monitor.v",
    "minimal/MuCore.v",
    "minimal/MultiExecution.v",
    "minimal/Multiplicity.v",
    "minimal/Napkin.v",
    "minimal/NecTPartition.v",
    "minimal/NoisyChairs.v",
    "minimal/NondetChairs.v",
    "minimal/PassiveGeometry.v",
    "minimal/PeriodicIntersection.v",
    "minimal/QuantumChairs.v",
    "minimal/Recurrence.v",
    "minimal/Representation.v",
    "minimal/SharpHost.v",
    "minimal/SliceCore.v",
    "minimal/SlicedEstablishment.v",
    "minimal/StepLaw.v",
    "minimal/StructuralMeter.v",
    "minimal/SynchronizedCapacity.v",
    "minimal/Task.v",
    "minimal/TwoArms.v",
    "minimal/VerifierSmall.v",
    # The short checks beside the book state their machines as hypotheses on the
    # standard library alone; the book, not the foundation chain, is what they check.
    "monograph/checks/ch10_walking_arrow.v",
    "monograph/checks/ch16_four_doors.v",
    "monograph/checks/ch20_every_scale.v",
    "monograph/checks/ch20_walker.v",
    "monograph/checks/ch21_grid.v",
    "monograph/checks/ch21_levers.v",
    "monograph/checks/ch21_receipts.v",
    "monograph/checks/ch21_room.v",
    "monograph/checks/ch22_shown.v",
]


def proof_files() -> list[Path]:
    return sorted(
        list((REPO_ROOT / "coq").rglob("*.v"))
        + list((REPO_ROOT / "minimal").glob("*.v"))
        + list((REPO_ROOT / "monograph" / "checks").glob("*.v"))
    )


def waived_files() -> list[str]:
    out = []
    for path in proof_files():
        text = path.read_text(encoding="utf-8", errors="replace")
        if WAIVER_RE.search(text):
            out.append(path.relative_to(REPO_ROOT).as_posix())
    return out


def test_waiver_pattern_matches_the_inquisitor_and_the_connectivity_test() -> None:
    sys.path.insert(0, str(REPO_ROOT / "scripts"))
    try:
        import inquisitor  # type: ignore[import-not-found]
    finally:
        sys.path.pop(0)
    assert WAIVER_RE.pattern == inquisitor._PROOF_CONNECTIVITY_NOTE_RE.pattern
    assert WAIVER_RE.flags == inquisitor._PROOF_CONNECTIVITY_NOTE_RE.flags
    source = (REPO_ROOT / "tests" / "test_no_shortcuts_proof_connectivity.py").read_text()
    for fragment in (
        "SCOPE NOTE.*proof[- ]?connect",
        "SCOPE NOTE.*(?:foundation connectivity|standalone proof scope)",
        r"PROOF SCOPE:\s*standalone algebra",
    ):
        assert fragment in source


def test_the_waived_set_is_exactly_the_frozen_list() -> None:
    found = waived_files()
    gained = sorted(set(found) - set(WAIVED_FILES))
    lost = sorted(set(WAIVED_FILES) - set(found))
    assert not gained, (
        "files gained a connectivity waiver (connect them to the foundation chain, or "
        "justify the waiver and add them to WAIVED_FILES):\n" + "\n".join(gained)
    )
    assert not lost, (
        "files no longer carry a waiver (remove them from WAIVED_FILES):\n" + "\n".join(lost)
    )


def test_the_frozen_list_is_sorted_and_unique() -> None:
    assert WAIVED_FILES == sorted(set(WAIVED_FILES))


def test_every_waiver_sits_in_the_opening_comments() -> None:
    late = []
    for rel in WAIVED_FILES:
        text = (REPO_ROOT / rel).read_text(encoding="utf-8", errors="replace")
        match = DECLARATION_RE.search(text)
        head = text[: match.start()] if match else text
        if not WAIVER_RE.search(head):
            late.append(rel)
    assert not late, "waiver after the first declaration:\n" + "\n".join(late)
