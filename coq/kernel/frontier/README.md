# kernel/frontier

F1, F2, and F3 frontier closure files. Each addresses a named boundary in the
current claim surface. The filenames keep the frontier results distinct from
the public claim names in the root README.

These files either close or formally bound a frontier claim. Each file header
states the requirement it addresses and the exact theorem surface it supplies.

## F1: physical-reversibility / A2 derivation

| File | Purpose |
|---|---|
| `LogicalErasureCertFlip.v` | Single-step A2 from a cost-floor bridge premise over boolean macro-properties and a calibration premise (`mu_per_landauer_bit >= 1`) |
| `LandauerBridgeAbstractCost.v` | The F1 Landauer bridge abstracted over arbitrary cost functions `vm_instruction -> nat` |
| `LandauerDissipationStrongForm.v` | Factored implication plus the proof that its two premises are incompatible for the full ISA (`landauer_dissipation_premises_inconsistent`); no applicable physical derivation of A2 |
| `LandauerTraceLevelA2.v` | Multi-step extension via `universal_nfi_any_substrate` |

## F2: algebraic coherence vs. cost axioms

Settles whether NPA-1 minor inequalities follow from cost axioms alone.

| File | Purpose |
|---|---|
| `NPAMinorsIndependentOfCost.v` | **Negative result**: PR-box VMState satisfies cost axioms but violates `algebraically_coherent` |
| `NPAMinorsFromWitnessLocality.v` | **Positive**: cost axioms + witness-locality DO entail `algebraically_coherent` |
| `NPAPerMinorFromCostCoherence.v` | Per-minor existence form derivable from cost axioms alone |

## F3: non-separable cross-link inequalities

Single-conclusion Coq inequalities that compose multiple chain constants.

| File | Purpose |
|---|---|
| `LassertTsirelsonCrossLink.v` | LASSERT byte coefficient + Tsirelson constant in one bound |
| `LassertTsirelsonHierarchyCrossLink.v` | LASSERT + Tsirelson + μ-hierarchy in one bound |
| `MuLaplacianSum.v` | Sum-zero lemma for the discrete μ-Laplacian |
| `PartitionTopologyCrossLink.v` | Partition-topology cross-link |
| `TriangleAnglePlusOne.v` | Whether the +1 in `triangle_angle` is the +1 of the A2 cost floor |
| `CalibrationObstruction.v` | What calibration at every module forces on a well-formed triangulated state, and the closed obstruction (`connected_triangulation_not_calibrated`) for connected vertex links and distinct module numbers |
| `ReachableGeometry.v` | The geometry on states reachable from `init_state`: no two modules adjacent, no face-graph triangle, calibration residual 2π at every module (`reachable_calibrated_iff_no_modules`), and a well-formed triangulated reachable graph is a set of separate triangles (`reachable_triangulated_isolated`); one reachable example (`reachable_triangulated_exists`) |

## Pointer observables and ecosystems

| File | Purpose |
|---|---|
| `ObservationPolicy.v` | Observation, event pricing, and retained history; cost units are abstract naturals, not measured heat |
| `TraceStateDescent.v` | Exact descent conditions for the existing VM trace evaluator; results concern reachable states |
| `PointerObservable.v` | The pointer-observable criterion: definitions, the conjecture schema, and a non-vacuity witness |
| `PointerObservableReductions.v` | The five metering disciplines as pointer-observable ecosystems, one small model each |
| `PointerObservableCounterexamples.v` | Systems that resist forgery and do not proliferate records; the Coq models fix only the observer maps |
| `RecordProliferationSurveyTarget.v` | Twelve candidate events and a swapped winner, stated over standalone observer maps (definitions) |
| `RecordProliferationSurvey.v` | Checked measurements for the twelve candidate events and the swapped event (`twelve_candidate_measurements_checked`, `swapped_event_is_pointer_checked`) |
| `EcosystemGameTarget.v` | The coordinator-free ecosystem game: an abstract distributed observation game with consensus, authenticity, and coordinator-free update (definitions) |
| `EcosystemGame.v` | Proved outcomes for the ecosystem game: a toggle game with consensus, authenticity, and coordinator-free updates whose event is revoked (`toggle_game_refutes_strong_pointer_necessity`); a positive observer count, authenticity, and durable views imply the event is permanent (`durable_consensus_implies_permanence`); the VM certification game has a permanent event for every positive observer count (`vm_certification_is_permanent_consensus`) |

## Load-bearing exports

Each F-file is the closure of a documented frontier item; they don't get
re-imported elsewhere because the published statement is the export.

`TriangleAnglePlusOne.v` shows that the +1 in `triangle_angle` contributes a
correction that decays as 1/d (the signature of a Tikhonov regularizer), not a
fixed contribution independent of d (an A2 cost floor). The file does not
promote that interpretation to a physical derivation.

## Imports

`foundation/`, `mu_calculus/`, `nfi/`, plus quantum/curvature for cross-link
constants.
