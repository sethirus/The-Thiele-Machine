# Part 6, Round 2 results: ecosystem game

Date: 2026-10-01

| Statement | Outcome |
|---|---|
| `strong_pointer_necessity` | REFUTED |
| `durable_consensus_implies_permanence` | PROVED BUT BUILT IN |

`toggle_game_refutes_strong_pointer_necessity` is a closed counterexample with
two observers. Both views equal the event, so they agree and satisfy the
Boolean soundness/completeness contract. Their next views are computed by the
same local rule, `negb`, with no observer index or coordinator state. Starting
from `true`, the event nevertheless becomes `false`.

Consensus, authenticated observation, and coordinator-free evolution therefore
do not force the observed event to be a permanent commit. This is the direct
counterexample to the proposed theorem.

`durable_consensus_implies_permanence` proves the exact surviving boundary. If
at least one observer exists, every observer's view is sound and complete for
the event, and a true view is required to stay true, then the event is
permanent. The conclusion is useful for locating the missing premise, but the
result is structurally built into `durable_views`; it does not elevate the
pointer criterion from conjecture to theorem.

## Hollowness checks

- Definitional: the refutation is not a restatement. `event_permanent` is
  false for a concrete transition satisfying every antecedent. The surviving
  theorem is close to definitional and is labeled accordingly.
- Built in: the strong statement has no persistence premise. The surviving
  statement does, and the report identifies it as load-bearing.
- Vacuity: `toggle_game` has two observers and supplies closed witnesses for
  positivity, consensus, authenticity, and coordinator-free update.
- Swap: replacing `negb` by identity makes the event permanent; replacing the
  event's name changes nothing. The verdict follows from transition structure,
  not a certification label.
- Adversarial read: the formal no-forgery contract is Boolean observer
  soundness/completeness. No cryptographic unforgeability, network model,
  Byzantine threshold, or deployed-protocol correspondence is claimed.

The acceptance test was observed failing before `EcosystemGame.v` existed.
Both theorem assumption reports are closed under the global context, and the
existing twelve-event survey tests continue to pass.
