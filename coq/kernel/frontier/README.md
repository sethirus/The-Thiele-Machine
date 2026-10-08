# kernel/frontier

Files that bound a named boundary of the claims: observation and the window
theorem, the pointer-observable criterion, the record-proliferation survey,
and the ecosystem game.

Each file header states the requirement it addresses and the exact theorem
surface it supplies.

## Observation and pointer observables

| File | Purpose |
|---|---|
| `ObservationPolicy.v` | Observation, event pricing, and retained history; cost units are abstract naturals, not measured heat |
| `PointerObservable.v` | The pointer-observable criterion: definitions, the conjecture schema, and a non-vacuity witness |
| `PointerObservableReductions.v` | The five metering disciplines as pointer-observable ecosystems, one small model each |
| `PointerObservableCounterexamples.v` | Systems that resist forgery and do not proliferate records; the Coq models fix only the observer maps |
| `RecordProliferationSurveyTarget.v` | Twelve candidate events and a swapped winner, stated over standalone observer maps (definitions) |
| `RecordProliferationSurvey.v` | Checked measurements for the twelve candidate events and the swapped event (`twelve_candidate_measurements_checked`, `swapped_event_is_pointer_checked`) |
| `EcosystemGameTarget.v` | The coordinator-free ecosystem game: an abstract distributed observation game with consensus, authenticity, and coordinator-free update (definitions) |
| `EcosystemGame.v` | Proved outcomes for the ecosystem game: a toggle game with consensus, authenticity, and coordinator-free updates whose event is revoked (`toggle_game_refutes_strong_pointer_necessity`); a positive observer count, authenticity, and durable views imply the event is permanent (`durable_consensus_implies_permanence`) |

## Load-bearing exports

Each file's published statement is its export. `ObservationPolicy.v` is
also imported by the window example in `reductions/TPMQuoteGap.v`.

## Imports

The Coq standard library, and each other: the survey and the reductions
import `PointerObservable.v`, and the game imports its target file.
