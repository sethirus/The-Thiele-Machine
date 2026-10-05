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
    "coq/kernel/category/AlgebraicCoherence.v",
    "coq/kernel/foundation/CompilerChecker.v",
    "coq/kernel/foundation/CompilerCodes.v",
    "coq/kernel/foundation/CompilerGuest.v",
    "coq/kernel/foundation/CompilerGuestRun.v",
    "coq/kernel/foundation/CompilerIcomp.v",
    "coq/kernel/foundation/CompilerInstrument.v",
    "coq/kernel/foundation/CompilerLifts.v",
    "coq/kernel/foundation/CompilerRaBridge.v",
    "coq/kernel/foundation/LRecursion.v",
    "coq/kernel/foundation/MM2ComplementUndec.v",
    "coq/kernel/foundation/Presentation.v",
    "coq/kernel/foundation/PresentedDemo.v",
    "coq/kernel/foundation/PresentedUniversal.v",
    "coq/kernel/foundation/ProbabilisticRecord.v",
    "coq/kernel/foundation/ProbabilisticRecordCore.v",
    "coq/kernel/foundation/ProperSubsumption.v",
    "coq/kernel/foundation/SmBlock.v",
    "coq/kernel/foundation/SmChain.v",
    "coq/kernel/foundation/SmDecider.v",
    "coq/kernel/foundation/SmEvalL.v",
    "coq/kernel/foundation/SmFixed.v",
    "coq/kernel/foundation/SmFixedPoint.v",
    "coq/kernel/foundation/SmFuel.v",
    "coq/kernel/foundation/SmHostRice.v",
    "coq/kernel/foundation/SmKleene.v",
    "coq/kernel/foundation/SmMMAHost.v",
    "coq/kernel/foundation/SmMMAOff.v",
    "coq/kernel/foundation/SmNoExact.v",
    "coq/kernel/foundation/SmSmnAll.v",
    "coq/kernel/foundation/SmTallyL.v",
    "coq/kernel/foundation/UniversalBlocks.v",
    "coq/kernel/foundation/UniversalBridge.v",
    "coq/kernel/foundation/UniversalLayout.v",
    "coq/kernel/foundation/UniversalPBlocks.v",
    "coq/kernel/foundation/UniversalPBridge.v",
    "coq/kernel/foundation/UniversalPCodes.v",
    "coq/kernel/foundation/UniversalPLayout.v",
    "coq/kernel/foundation/UniversalPPhases.v",
    "coq/kernel/foundation/UniversalPRun.v",
    "coq/kernel/foundation/UniversalPSim.v",
    "coq/kernel/foundation/UniversalPhases.v",
    "coq/kernel/foundation/UniversalRun.v",
    "coq/kernel/foundation/UniversalSim.v",
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
    "coq/kernel/quantum/BoxCHSH.v",
    "coq/kernel/quantum/CHSHColumnCheck.v",
    "coq/kernel/quantum/CHSHCouplingBridge.v",
    "coq/kernel/quantum/CHSHStatisticalBridge.v",
    "coq/kernel/quantum/ConstructivePSD.v",
    "coq/kernel/quantum/ElliptopeCompletion.v",
    "coq/kernel/quantum/ElliptopeGate.v",
    "coq/kernel/quantum/GenRealizability.v",
    "coq/kernel/quantum/MinorConstraints.v",
    "coq/kernel/quantum/NPAMomentMatrix.v",
    "coq/kernel/quantum/QuantumPartitionPSD_1AB.v",
    "coq/kernel/quantum/SmallChshCheck.v",
    "coq/kernel/quantum/SmallChshMachine.v",
    "coq/kernel/quantum/TsirelsonFromAlgebra.v",
    "coq/kernel/quantum/TsirelsonGeneral.v",
    "coq/kernel/quantum/ValidCorrelation.v",
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
    "minimal/EarnedCore.v",
    "minimal/EarnedGeneric.v",
    "minimal/EarnedMulti.v",
    "minimal/EarnedMultiPriced.v",
    "minimal/EarnedPriced.v",
    "minimal/MuCore.v",
    "minimal/Napkin.v",
    "minimal/Presented.v",
    "minimal/PricedComplete.v",
    "minimal/SmCodes.v",
    "minimal/SmHostBlocks.v",
    "minimal/SmInterp.v",
    "minimal/SmLoops.v",
    "minimal/SmLoops2.v",
    "minimal/SmLoops3.v",
    "minimal/SmTally.v",
    "minimal/ThieleComplete.v",
    "minimal/ThieleCompleteWindow.v",
    "minimal/UniversalCodes.v",
    "minimal/UniversalNoCopy.v",
    "minimal/UniversalThiele.v",
]


def proof_files() -> list[Path]:
    return sorted(list((REPO_ROOT / "coq").rglob("*.v")) + list((REPO_ROOT / "minimal").glob("*.v")))


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
