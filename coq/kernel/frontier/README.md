# kernel/frontier

F1, F2, and F3 frontier closure files. Each addresses a named boundary in the
current claim surface. The filenames keep the frontier results distinct from
the public claim names in the root README.

These files either close or formally bound a frontier claim. Each file header
states the requirement it addresses and the exact theorem surface it supplies.

## F1: physical-reversibility / A2 derivation

| File | Purpose |
|---|---|
| `F1_LogicalErasure.v` | Single-step A2 from a cost-floor bridge premise over boolean macro-properties and a calibration premise (`mu_per_landauer_bit >= 1`) |
| `F1_AbstractedBridge.v` | The F1 Landauer bridge abstracted over arbitrary cost functions `vm_instruction -> nat` |
| `F1_StrongForm.v` | Factored implication plus the proof that its two premises are incompatible for the full ISA (`F1_physical_premises_incompatible`); no applicable physical derivation of A2 |
| `F1_TraceLevelA2.v` | Multi-step extension via `universal_nfi_any_substrate` |

## F2: algebraic coherence vs. cost axioms

Settles whether NPA-1 minor inequalities follow from cost axioms alone.

| File | Purpose |
|---|---|
| `F2_MinorIndependence.v` | **Negative result**: PR-box VMState satisfies cost axioms but violates `algebraically_coherent` |
| `F2_MinorFromWitnessLocality.v` | **Positive**: cost axioms + witness-locality DO entail `algebraically_coherent` |
| `F2_PerMinorFromCostCoherent.v` | Per-minor existence form derivable from cost axioms alone |

## F3: non-separable cross-link inequalities

Single-conclusion Coq inequalities that compose multiple chain constants.

| File | Purpose |
|---|---|
| `F3_CrossLink.v` | LASSERT byte coefficient + Tsirelson constant in one bound |
| `F3_TripleCrossLink.v` | LASSERT + Tsirelson + μ-hierarchy in one bound |
| `F3_MuLaplacianSum.v` | Sum-zero lemma for the discrete μ-Laplacian |
| `F3_PartitionTopologyCrossLink.v` | Partition-topology cross-link |
| `F3_PlusOneStructural.v` | Whether the +1 in `triangle_angle` is the +1 of the A2 cost floor |

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
| `EcosystemGame.v` | Closed outcomes for the ecosystem game: a toggle game with consensus, authenticity, and coordinator-free updates whose event is revoked (`toggle_game_refutes_strong_pointer_necessity`); a positive observer count, authenticity, and durable views imply the event is permanent (`durable_consensus_implies_permanence`); the VM certification game has a permanent event for every positive observer count (`vm_certification_is_permanent_consensus`) |

## Load-bearing exports

Each F-file is the closure of a documented frontier item; they don't get
re-imported elsewhere because the published statement is the export.

`F3_PlusOneStructural.v` shows that the +1 in `triangle_angle` contributes a
correction that decays as 1/d (the signature of a Tikhonov regularizer), not a
fixed contribution independent of d (an A2 cost floor). The file does not
promote that interpretation to a physical derivation.

## Imports

`foundation/`, `mu_calculus/`, `nfi/`, plus quantum/curvature for cross-link
constants.
