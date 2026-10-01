# Part 6, Round 2 freeze: ecosystem game

Date: 2026-10-01

## Definitions

An `EcosystemGame` has a state type, a positive finite observer count, a
Boolean event, one Boolean view per observer, and a state transition.

- `observer_consensus`: all in-range observers report the same value in every
  state.
- `observer_authenticity`: every in-range view equals the event. This is the
  exact Boolean no-forgery contract: no observer accepts a false event and no
  true event is hidden from it.
- `coordinator_free_update`: there is one local Boolean update rule that
  predicts every observer's next view from that observer's current view. No
  observer index or coordinator state is available to the rule.
- `event_permanent`: once the event is true, one transition cannot make it
  false.
- `durable_views`: once any in-range observer accepts, its next view remains
  true.

## Frozen statements

```coq
Definition strong_pointer_necessity : Prop :=
  forall g,
    0 < observer_count g ->
    observer_consensus g ->
    observer_authenticity g ->
    coordinator_free_update g ->
    event_permanent g.
```

The counterexample target is `~ strong_pointer_necessity` using two observers,
a Boolean event and view, and Boolean negation as the shared local transition.

The surviving theorem is:

```coq
forall g,
  0 < observer_count g ->
  observer_authenticity g ->
  durable_views g ->
  event_permanent g.
```

## Predicted outcome

- Strong pointer necessity: REFUTED.
- Durable-consensus implication: PROVED BUT BUILT IN. It identifies the exact
  missing premise but does not elevate the empirical pointer criterion.

## Success

A closed counterexample satisfies positivity, consensus, authenticity, and
the coordinator-free local update while exhibiting a true-to-false event
transition. The durable theorem closes without axioms, and its report labels
the durability premise as load-bearing rather than claiming a discovery.

## Failure

The counterexample fails one of the frozen antecedents, or the durable theorem
needs an additional premise. Weakening `observer_authenticity`, redefining
permanence, or adding permanence to the strong theorem's premises does not
count as refuting or proving the frozen statement.
